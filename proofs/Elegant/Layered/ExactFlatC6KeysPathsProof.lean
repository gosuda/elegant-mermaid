import Elegant.Layered.ExactFlatC6WProof
import Elegant.Layered.ExactFlatC7ExclusiveKey
import Elegant.Layered.ExactFlatC5
import Elegant.Layered.ExactFlatC5ChosenPart
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RunStageChainKeys
import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.Compound
import Elegant.Layered.CoordGraph
import Elegant.Model

set_option autoImplicit false


namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Endpoint projection of the pristine form of an edge (local copy). -/
private theorem x6kp_edge_original_tail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  unfold Edge.original
  split <;> simp_all
/-- Endpoint projection of the pristine form of an edge (local copy). -/
private theorem x6kp_edge_original_head (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  unfold Edge.original
  split <;> simp_all
/-- Component lookup at the position of a member (local copy). -/
private theorem x6kp_comp_idxOf_lookup {comp : List Nat} {x : Nat} (hmem : x ∈ comp) :
    comp[comp.idxOf x]? = some x :=
  (List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem)).trans
    (congrArg some (List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)))
/-- A self-loop index contributes no exact normalized edge (replay of
`selfLoop_edgesOf_empty` through `X_componentRun_normalized_source`). -/
private theorem x6kp_selfLoop_empty {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    {i : Nat} {edge : Edge}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hedge : cg.edges[i]? = some edge) (hself : edge.tail = edge.head) :
    (RouteImpl.edgesOf run.proper i) = [] := by
  obtain ⟨ranks, normalized, hn, he, _⟩ := X_componentRun_normalized_source hrun
  have hno : ∀ pe ∈ normalized.edges, pe.original ≠ i :=
    normalized_no_original_of_self hn hedge hself
  have hno' : ∀ pe ∈ run.proper.edges, pe.original ≠ i := by
    rw [he]
    exact hno
  exact List.eq_nil_iff_forall_not_mem.mpr fun j hj =>
    absurd (mem_edgesOf.mp hj).2 (hno' _ (edgeAt_mem (mem_edgesOf.mp hj).1))
/-- Reverse key lookup through `exactGraph`: an exact-graph node comes from
the measured-graph node at the same index with the same key fields (local copy). -/
private theorem x6kp_node_key_rev {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {g0 g : Graph}
    (h : exactGraph P exactIds inp o measured g0 = .ok g)
    {v : Nat} {nd : Node} (hv : g.nodes[v]? = some nd) :
    ∃ nd0, g0.nodes[v]? = some nd0 ∧ nd0.border = nd.border ∧
      nd0.clusterPath = nd.clusterPath ∧ nd0.decl = nd.decl := by
  have hlen : g.nodes.length = g0.nodes.length := exactGraph_length h
  have hvlt : v < g0.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hv).1
    omega
  have h0 : g0.nodes[v]? = some (g0.nodes[v]'hvlt) := List.getElem?_eq_getElem hvlt
  obtain ⟨nd', hnd', hnb, hnap, hnd⟩ := exactGraph_node_key h h0
  have heq : nd' = nd := Option.some.inj (hnd'.symm.trans hv)
  subst heq
  exact ⟨_, h0, hnb.symm, hnap.symm, hnd.symm⟩
/-- Endpoint case split on prepared boxes (local copy of the private
`alias_endpoint_cases` in both the plain and exact self-route proofs). -/
private theorem x6kp_endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases hbj : boxes[j]? with
    | none => exact Or.inl rfl
    | some target =>
      dsimp only
      by_cases hc : (box.role != .group || i == j) = true
      · rw [ite_eq_left hc]
        exact Or.inl rfl
      · rw [ite_eq_right hc]
        by_cases hd : (s == Compound.inside boxes box.id target.id) = true
        · rw [ite_eq_left hd]
          exact Or.inl rfl
        · rw [ite_eq_right hd]
          refine Or.inr ⟨rfl, ?_⟩
          intro box' hb'
          have heq : box' = box := (Option.some.inj hb').symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl
/-- Count monotonicity for the bottom-marker index argument (local copy). -/
private theorem x6kp_countP_take_add_one {α : Type} (p : α → Bool)
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
/-- Local copy of the bottom-marker list (definition matches `markExtras`). -/
private def x6kp_bottomNodesOf (full sub : List ModelBox) (off : Nat) : List Node :=
  (sub.zipIdx off).filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := Compound.path full q.1 ++ [q.2], border := 2 }
    else none
/-- Bottom-node declaration lookup (local copy). -/
private theorem x6kp_bottomNodesOf_getElem?_decl {full sub : List ModelBox} {off k : Nat}
    {x : Node} (hx : (x6kp_bottomNodesOf full sub off)[k]? = some x) :
    ∃ d g, sub[d]? = some g ∧ g.role = .group ∧ x.decl = d + off ∧
      ((sub.take d).filter fun b => b.role == .group).length = k := by
  induction sub generalizing off k with
  | nil => simp [x6kp_bottomNodesOf] at hx
  | cons b bs ih =>
    unfold x6kp_bottomNodesOf at hx
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
/-- The bottom node at `Compound.bottomIndex boxes i` declares `i` (local copy). -/
private theorem x6kp_bottom_node_decl {boxes : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {nodes : List Node} (hlen : nodes.length = boxes.length)
    {i j : Nat} {x : Node} {b : ModelBox}
    (hj : j = boxes.length + ((boxes.take i).filter fun b => b.role == .group).length)
    (hx : (Compound.markNodes boxes pad titles nodes)[j]? = some x)
    (hbi : boxes[i]? = some b) (hb : b.role = .group) :
    x.decl = i := by
  rw [markNodes_eq] at hx
  have htopLen : (nodes.zipIdx.map (markOne boxes pad titles)).length = nodes.length := by
    simp [List.length_map, List.length_zipIdx]
  have hjge : (nodes.zipIdx.map (markOne boxes pad titles)).length ≤ j := by
    rw [htopLen, hlen]; omega
  rw [List.getElem?_append_right hjge] at hx
  have hk : j - (nodes.zipIdx.map (markOne boxes pad titles)).length =
      ((boxes.take i).filter fun b => b.role == .group).length := by omega
  rw [hk] at hx
  have hme : markExtras boxes = x6kp_bottomNodesOf boxes boxes 0 := rfl
  rw [hme] at hx
  obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := x6kp_bottomNodesOf_getElem?_decl hx
  have hi : i < boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hcntI : ((boxes.take i).filter fun b => b.role == .group).length =
      j - (nodes.zipIdx.map (markOne boxes pad titles)).length := by omega
  have hidi : i = d := by
    rcases Nat.lt_trichotomy i d with hlt | heq | hgt
    · have hbdi : (fun b => b.role == .group) b = true := beq_iff_eq.mpr hb
      have hmono := x6kp_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := i) (n := d - i) (Nat.sub_ne_zero_of_lt hlt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hbi
          rw [heq]; exact hbdi)
      have hrewrite : i + (d - i) = d := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
    · exact heq
    · have hdi : d < boxes.length := (List.getElem?_eq_some_iff.mp hdg).1
      have hgid : (fun b => b.role == .group) g = true := beq_iff_eq.mpr hgg
      have hmono := x6kp_countP_take_add_one (p := fun b => b.role == .group)
        (l := boxes) (i := d) (n := i - d) (Nat.sub_ne_zero_of_lt hgt)
        (by omega) (by
          obtain ⟨_, heq⟩ := List.getElem_of_getElem? hdg
          rw [heq]; exact hgid)
      have hrewrite : d + (i - d) = i := by omega
      rw [hrewrite, List.countP_eq_length_filter,
        List.countP_eq_length_filter] at hmono
      omega
  subst hidi
  simpa using hdecl
/-- Exact alias declaration transport: an aliased endpoint's exact-graph node
carries a model endpoint declaration (mirror of the private `alias_pos_decl`
over `graph0`, transported through `exactGraph`). -/
private theorem x6kp_alias_decl {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (s : Bool)
    {pos other : Nat} {src tgt : ModelBox}
    (hsrc : inp.boxes[pos]? = some src)
    (_htgt : inp.boxes[other]? = some tgt)
    {a : Nat}
    (ha : a = Compound.endpoint
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) s pos other)
    {node : Node} (hnode : execution.graph.nodes[a]? = some node) :
    node.decl = pos := by
  obtain ⟨nodes0, _edges0, titles0, hprepared, hlen_nodes, hmeta⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := execution.lines_eq
    simp only [boxLines] at h
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
          (mapM_getElem? _ _ _ h).1
      _ = inp.boxes.length := List.length_zipIdx
  have hprep_len : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box).length = inp.boxes.length := by
    simp
  have hlen0 : nodes0.length =
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).length := by
    rw [hlen_nodes, hlines, hprep_len]
  have hbp : (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)[pos]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src) := by
    rw [List.getElem?_map, hsrc]
    simp
  obtain ⟨nd0, hnd0, _, _, hdecl0⟩ := x6kp_node_key_rev execution.graph_eq hnode
  have hnode0 : (Compound.prepare (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)
      execution.params.clusterPad titles0
      { nodes := nodes0, edges := _edges0, slot := execution.params.slot }).nodes[a]? =
      some nd0 := by
    rw [← hprepared]
    exact hnd0
  rw [← hdecl0]
  rcases x6kp_endpoint_cases (boxes := (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box)) s pos other with h | ⟨hbot, hgroup⟩
  · have haPos : a = pos := ha.trans h
    rw [haPos] at hnode0
    by_cases hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group
    · have hfixedFalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false := by
        cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
        | true =>
          simp only [hf, ↓reduceIte] at hpbG
          exact absurd hpbG (by intro hcon; cases hcon)
        | false => rfl
      have hsrcGroup : src.role = .group := by
        rw [hfixedFalse] at hpbG hbp
        simpa using hpbG
      have hbp' : (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box)[pos]? = some src := by
        simpa [hfixedFalse] using hbp
      have hi : pos < nodes0.length := by
        rw [hlen0, hprep_len]
        exact (List.getElem?_eq_some_iff.mp hsrc).1
      have hrec := Compound.prepare_group_title_record _ execution.params.clusterPad titles0
        { nodes := nodes0, edges := _edges0, slot := execution.params.slot }
        hi hbp' hsrcGroup
      have heq := Option.some.inj (hnode0.symm.trans hrec)
      have hdd : nd0.decl = (nodes0[pos]'hi).decl := by rw [heq]
      rw [hdd]
      exact (hmeta pos _ (List.getElem?_eq_getElem hi)).1
    · have hplain : ¬ (src.role = .group ∧
          inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false) := by
        intro ⟨hr, hf⟩
        simp [hf, hr] at hpbG
      have hng : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
          ({ src with role := .node } : ModelBox) else src).role ≠ .group := by
        by_cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = true
        · simp only [hf, ↓reduceIte]
          decide
        · have hf' : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false :=
            Bool.eq_false_iff.mpr hf
          simp only [hf']
          intro hrole
          exact hplain ⟨hrole, hf'⟩
      have hi : pos < nodes0.length := by
        rw [hlen0, hprep_len]
        exact (List.getElem?_eq_some_iff.mp hsrc).1
      have hrec := Compound.prepare_plain_node_record _ execution.params.clusterPad titles0
        { nodes := nodes0, edges := _edges0, slot := execution.params.slot }
        hi hbp hng
      have heq := Option.some.inj (hnode0.symm.trans hrec)
      have hdd : nd0.decl = (nodes0[pos]'hi).decl := by rw [heq]
      rw [hdd]
      exact (hmeta pos _ (List.getElem?_eq_getElem hi)).1
  · have haBot : a = Compound.bottomIndex
        (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) pos := ha.trans hbot
    have hpbG : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        ({ src with role := .node } : ModelBox) else src).role = .group := by
      have hb := hgroup _ hbp
      simpa using hb
    have hx : (Compound.markNodes (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)
        execution.params.clusterPad titles0 nodes0)[a]? = some nd0 := by
      have h2 := hnode0
      rw [Compound.prepare_nodes] at h2
      exact h2
    have hj : a = (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box).length +
        (((inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box).take pos).filter
          fun b => b.role == .group).length := by
      rw [haBot]; rfl
    exact x6kp_bottom_node_decl hlen0 hj hx hbp hpbG
/-- Exact alias declaration transport in disjunction form (mirror of
`AliasDeclTransport` over `SceneExecutionX`). -/
private theorem x6kp_alias_transport {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {route : ModelRoute} {raw : Edge}
    (_hroute : inp.routes[index]? = some route)
    (hraw : edgeOf inp route index = .ok raw)
    {a : Nat} {node : Node}
    (ha : a = (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail ∨
      a = (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head)
    (hnode : execution.graph.nodes[a]? = some node) :
    node.decl = raw.tail ∨ node.decl = raw.head := by
  obtain ⟨_hdecl₂, _hrev₂, src, tgt, hsrc, _hsrcId, htgt, _htgtId⟩ :=
    edgeOf_semantic_endpoints hraw
  rcases ha with haT | haH
  · have htail : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) true raw.tail raw.head := rfl
    have haTail : a = Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) true raw.tail raw.head := by
      rw [haT, htail]
    have hdeclEq := x6kp_alias_decl execution true hsrc htgt haTail hnode
    exact Or.inl hdeclEq
  · have hhead : (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head =
        Compound.endpoint (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) false raw.head raw.tail := rfl
    have haHead : a = Compound.endpoint (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) false raw.head raw.tail := by
      rw [haH, hhead]
    have hdeclEq := x6kp_alias_decl execution false htgt hsrc haHead hnode
    exact Or.inr hdeclEq
/-- Exact chain model source: the candidate edge resolves through the exact
graph to its model route/raw, with the pristine-endpoint `idxOf` equations
and component memberships (replay of the `X_self_route_ids` identification). -/
private theorem x6kp_chain_mid {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge) :
    ∃ (index : Nat) (route : ModelRoute) (raw : Edge),
      inp.routes[index]? = some route ∧ edgeOf inp route index = .ok raw ∧
      edge.decl = index ∧
      edge.original.tail = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).tail ∧
      edge.original.head = comp.idxOf
        (Compound.aliasEdge (inp.boxes.map fun box =>
          if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
            { box with role := .node } else box) raw).head ∧
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail ∈ comp ∧
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head ∈ comp := by
  have hmem : edge ∈ (componentCandidate execution.graph comp candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨index, route, raw, _source, _target, hroute, hrawOf, hdeclIdx,
    _hrawsource, _hsourceId, _hrawtarget, _htargetId, _⟩ :=
    X_candidate_model_endpoint_source execution.graph0_eq execution.graph_eq hmem
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ :=
    componentCandidate_semantic_source hmem
  have hgEdge0 : gEdge ∈ execution.graph0.edges := by
    rw [exactGraph_edges execution.graph_eq] at hgEdge
    exact hgEdge
  obtain ⟨index₂, route₂, raw₂, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph0_eq hgEdge0
  obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
  have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
  have hgeOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk tail head minLen decl reversed => cases hgeRev; rfl
  have hgeDeclIdx : edge.decl = index₂ := by
    have h1 : edge.decl = gEdge.decl := by
      have h := congrArg Edge.decl hsemG
      simpa only [Edge.original_decl] using h
    rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
  have hidx₂ : index₂ = index := hgeDeclIdx.symm.trans hdeclIdx
  rw [hidx₂] at hr2Route
  have hroute₂Eq : route₂ = route :=
    Option.some.inj (hr2Route.symm.trans hroute)
  rw [hidx₂, hroute₂Eq] at hr2EdgeOf
  have hrawEq : raw₂ = raw := Except.ok.inj (hr2EdgeOf.symm.trans hrawOf)
  rw [hrawEq] at hgeAlias
  have hbd : ∀ e ∈ execution.graph.edges ++ Compound.constraints execution.graph,
      e.tail < execution.graph.nodes.length ∧
        e.head < execution.graph.nodes.length :=
    sceneExecutionX_edges_bounded execution
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbd (List.mem_append.mpr (Or.inl hgEdge))
  have hcompEq : comp' = comp :=
    components_shared_member_eq hcomp'In hcomp hgTailC hgTailMem
  have htailEq : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail = gEdge.tail :=
    (congrArg Edge.tail hgeAlias).symm
  have hheadEq : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head = gEdge.head :=
    (congrArg Edge.head hgeAlias).symm
  have hgHeadMem : gEdge.head ∈ comp := by rw [← hcompEq]; exact hgHeadC
  have hmemT : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail ∈ comp := by
    rw [htailEq]; exact hgTailMem
  have hmemH : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head ∈ comp := by
    rw [hheadEq]; exact hgHeadMem
  have hsemTail : edge.original.tail = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  exact ⟨index, route, raw, hroute, hrawOf, hdeclIdx, hsemTail, hsemHead, hmemT, hmemH⟩
/-- Reversed-edge case of the exact chain keys (mirror of the `hr = true`
branch of `properChainEndpointKeys`). -/
private theorem x6kp_chain_rev_true {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge} {native : EdgeRoute}
    (_hnative : run.routes[i]? = some native) (_horig : native.original = i)
    (_hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    {index : Nat} {route : ModelRoute} {raw : Edge}
    (hroute : inp.routes[index]? = some route)
    (hraw : edgeOf inp route index = .ok raw)
    (hdecl' : edge.decl = index)
    (hsemTail : edge.original.tail = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail)
    (hsemHead : edge.original.head = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head)
    (hmemT : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail ∈ comp)
    (hmemH : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head ∈ comp)
    (hrev : edge.reversed = true)
    {i₀ i₁ : Nat}
    (htail : (RouteImpl.edgeAt run.proper i₀).tail = edge.tail)
    (hhead : (RouteImpl.edgeAt run.proper i₁).head = edge.head) :
    ∃ (tailKey headKey index' : Nat) (route₀ : ModelRoute) (raw' : Edge)
      (nT nH : Node),
      comp[(RouteImpl.edgeAt run.proper i₀).tail]? = some tailKey ∧
      comp[(RouteImpl.edgeAt run.proper i₁).head]? = some headKey ∧
      execution.graph.nodes[tailKey]? = some nT ∧
      execution.graph.nodes[headKey]? = some nH ∧
      (nT.decl = raw'.tail ∨ nT.decl = raw'.head) ∧
      (nH.decl = raw'.tail ∨ nH.decl = raw'.head) ∧
      inp.routes[index']? = some route₀ ∧
      edgeOf inp route₀ index' = .ok raw' ∧
      edge.decl = index' := by
  rw [x6kp_edge_original_tail] at hsemTail
  rw [x6kp_edge_original_head] at hsemHead
  simp only [hrev, ↓reduceIte] at hsemTail hsemHead
  have hT : comp[edge.tail]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head := by
    rw [hsemHead]
    exact x6kp_comp_idxOf_lookup hmemH
  have hH : comp[edge.head]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail := by
    rw [hsemTail]
    exact x6kp_comp_idxOf_lookup hmemT
  have hcompT : comp[(RouteImpl.edgeAt run.proper i₀).tail]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head := by
    rw [htail]
    exact hT
  have hcompH : comp[(RouteImpl.edgeAt run.proper i₁).head]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail := by
    rw [hhead]
    exact hH
  have hltT : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head <
      execution.graph.nodes.length :=
    comp_mem_lt hcomp hmemH
  have hltH : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail <
      execution.graph.nodes.length :=
    comp_mem_lt hcomp hmemT
  obtain ⟨nT, hnT⟩ : ∃ nT, execution.graph.nodes[
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head]? = some nT :=
    ⟨_, List.getElem?_eq_getElem hltT⟩
  obtain ⟨nH, hnH⟩ : ∃ nH, execution.graph.nodes[
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail]? = some nH :=
    ⟨_, List.getElem?_eq_getElem hltH⟩
  have hdeclT := x6kp_alias_transport execution hroute hraw (Or.inr rfl) hnT
  have hdeclH := x6kp_alias_transport execution hroute hraw (Or.inl rfl) hnH
  exact ⟨_, _, _, _, _, nT, nH, hcompT, hcompH, hnT, hnH,
    hdeclT, hdeclH, hroute, hraw, hdecl'⟩
/-- Non-reversed-edge case of the exact chain keys (mirror of the `hr = false`
branch of `properChainEndpointKeys`). -/
private theorem x6kp_chain_rev_false {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run}
    (_hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {i : Nat} {edge : Edge} {native : EdgeRoute}
    (_hnative : run.routes[i]? = some native) (_horig : native.original = i)
    (_hedge : (componentCandidate execution.graph comp candidate).edges[i]? = some edge)
    {index : Nat} {route : ModelRoute} {raw : Edge}
    (hroute : inp.routes[index]? = some route)
    (hraw : edgeOf inp route index = .ok raw)
    (hdecl' : edge.decl = index)
    (hsemTail : edge.original.tail = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail)
    (hsemHead : edge.original.head = comp.idxOf
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head)
    (hmemT : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail ∈ comp)
    (hmemH : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head ∈ comp)
    (hrev : edge.reversed = false)
    {i₀ i₁ : Nat}
    (htail : (RouteImpl.edgeAt run.proper i₀).tail = edge.tail)
    (hhead : (RouteImpl.edgeAt run.proper i₁).head = edge.head) :
    ∃ (tailKey headKey index' : Nat) (route₀ : ModelRoute) (raw' : Edge)
      (nT nH : Node),
      comp[(RouteImpl.edgeAt run.proper i₀).tail]? = some tailKey ∧
      comp[(RouteImpl.edgeAt run.proper i₁).head]? = some headKey ∧
      execution.graph.nodes[tailKey]? = some nT ∧
      execution.graph.nodes[headKey]? = some nH ∧
      (nT.decl = raw'.tail ∨ nT.decl = raw'.head) ∧
      (nH.decl = raw'.tail ∨ nH.decl = raw'.head) ∧
      inp.routes[index']? = some route₀ ∧
      edgeOf inp route₀ index' = .ok raw' ∧
      edge.decl = index' := by
  rw [x6kp_edge_original_tail] at hsemTail
  rw [x6kp_edge_original_head] at hsemHead
  simp [hrev] at hsemTail hsemHead
  have hT : comp[edge.tail]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail := by
    rw [hsemTail]
    exact x6kp_comp_idxOf_lookup hmemT
  have hH : comp[edge.head]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head := by
    rw [hsemHead]
    exact x6kp_comp_idxOf_lookup hmemH
  have hcompT : comp[(RouteImpl.edgeAt run.proper i₀).tail]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail := by
    rw [htail]
    exact hT
  have hcompH : comp[(RouteImpl.edgeAt run.proper i₁).head]? =
      some (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head := by
    rw [hhead]
    exact hH
  have hltT : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).tail <
      execution.graph.nodes.length :=
    comp_mem_lt hcomp hmemT
  have hltH : (Compound.aliasEdge (inp.boxes.map fun box =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
        { box with role := .node } else box) raw).head <
      execution.graph.nodes.length :=
    comp_mem_lt hcomp hmemH
  obtain ⟨nT, hnT⟩ : ∃ nT, execution.graph.nodes[
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).tail]? = some nT :=
    ⟨_, List.getElem?_eq_getElem hltT⟩
  obtain ⟨nH, hnH⟩ : ∃ nH, execution.graph.nodes[
      (Compound.aliasEdge (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) raw).head]? = some nH :=
    ⟨_, List.getElem?_eq_getElem hltH⟩
  have hdeclT := x6kp_alias_transport execution hroute hraw (Or.inl rfl) hnT
  have hdeclH := x6kp_alias_transport execution hroute hraw (Or.inr rfl) hnH
  exact ⟨_, _, _, _, _, nT, nH, hcompT, hcompH, hnT, hnH,
    hdeclT, hdeclH, hroute, hraw, hdecl'⟩
/-- Exact chain endpoint keys in W form: endpoints of an executed exact
component run resolve to model endpoint declarations (replay of
`properChainEndpointKeys` through the exact chain/model lemmas). -/
theorem X6_chainEndpointKeysW_holds (exactIds : List String) :
    X6_ChainEndpointKeysW exactIds := by
  intro _ _ _ execution _hwf _hfp comp candidate run hcomp hrun i edge native hnative
    horig hedge i₀ i₁ hfirst hlast
  by_cases hne : edge.tail = edge.head
  · have hempty' := x6kp_selfLoop_empty hrun hedge hne
    rw [horig] at hfirst
    rw [hempty'] at hfirst
    simp at hfirst
  · have hne' : edge.tail ≠ edge.head := hne
    obtain ⟨first, last, hfirst', hlast', htail, hhead⟩ :=
      X_componentRun_chain_endpoints hrun hedge hne'
    rw [horig] at hfirst hlast
    have hfi : i₀ = first := Option.some.inj (hfirst.symm.trans hfirst')
    have hla : i₁ = last := Option.some.inj (hlast.symm.trans hlast')
    subst hfi
    subst hla
    obtain ⟨index, route, raw, hroute, hraw, hdecl', hsemTail, hsemHead, hmemT, hmemH⟩ :=
      x6kp_chain_mid execution hcomp hedge
    cases hr : edge.reversed with
    | true =>
      exact x6kp_chain_rev_true execution hcomp hrun hnative horig hedge hroute hraw
        hdecl' hsemTail hsemHead hmemT hmemH hr htail hhead
    | false =>
      exact x6kp_chain_rev_false execution hcomp hrun hnative horig hedge hroute hraw
        hdecl' hsemTail hsemHead hmemT hmemH hr htail hhead
/-- Residual (run-level cluster-path provenance, W form): every index occurring
in the cluster path of a proper node of an executed exact component run is
the index of a group-role box of the input. Strictly simpler than the
endpoint exclusion (a per-node path-membership fact, not a route statement).
True on all probes in `wip/Probe/X6KeysPathsTProbe.lean`. -/
def X6_RunPathGroupsW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ (i : Nat) (nd : ProperNode),
      run.proper.nodes[i]? = some nd →
      ∀ (k : Nat), k ∈ nd.node.clusterPath → ∀ (b : ModelBox),
        inp.boxes[k]? = some b → b.role = .group
/-- Exact exclusive-declaration path exclusion in W form, modulo the
run-level path residual `X6_RunPathGroupsW`: an exclusive declaration occurs
in no endpoint cluster path (mirror of
`exclusiveDeclOutsideEndpointPaths_of_clusterPath`; the run-node declaration
premise is already closed by `x_exclusiveRunNodeDecl_holds`). -/
theorem X6_declOutsidePathsW_holds (exactIds : List String)
    (hgroups : X6_RunPathGroupsW exactIds) :
    X6_DeclOutsidePathsW exactIds := by
  intro inp o _res execution _hwf _hfp comp candidate run hcomp hrun v key hdecl hexcl i
    edge native hnative hedge i₀ i₁ hfirst hlast
  obtain ⟨source, hsource, hexcl'⟩ : ∃ source : ModelBox,
      inp.boxes[key]? = some source ∧ source.exclusive = true :=
    Option.map_eq_some_iff.mp hexcl
  have hrole : source.role ≠ .group := by
    intro hg
    obtain ⟨_, _, _, _, _, _, hgroupbox⟩ := (wellFormed_iff (inputModel inp o)).mp _hwf
    have hcontra := hgroupbox source (List.mem_of_getElem? hsource) hg
    rw [hcontra] at hexcl'
    exact Bool.noConfusion hexcl'
  constructor
  · intro hmem
    cases hnode : run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]? with
    | none => simp [hnode] at hmem
    | some nd =>
      simp only [hnode, Option.map_some, Option.getD_some] at hmem
      exact hrole (hgroups execution _hwf _hfp comp candidate run hcomp hrun _ nd
        hnode key hmem source hsource)
  · intro hmem
    cases hnode : run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]? with
    | none => simp [hnode] at hmem
    | some nd =>
      simp only [hnode, Option.map_some, Option.getD_some] at hmem
      exact hrole (hgroups execution _hwf _hfp comp candidate run hcomp hrun _ nd
        hnode key hmem source hsource)
end PipelineImpl
end Layered
end Elegant
