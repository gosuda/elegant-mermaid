import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! ### Decision on the standing `GroupAnchors` hypothesis

`GroupAnchors` (FamilyC5.lean:50) is **false**.  `measuredGraph` (Pipeline.lean:256) builds
every graph edge as `Compound.aliasEdge prepared raw` over the raw `edgeOf` endpoint indices
(`edgeOf_semantic_endpoints`, ExecutedPortsFacts.lean:438), and `Compound.endpoint`
(Compound.lean:39) rewrites a group endpoint to the synthetic bottom-node index
`Compound.bottomIndex boxes i` whenever the other endpoint lies outside the group.
The bottom nodes are appended after the original `boxes.length` nodes (Compound.lean:66),
so for a route whose `fromId` names a group and whose `toId` lies outside that group the
candidate-local tail resolves through `q.1.1` to a global index of at least
`inp.boxes.length`; `inp.boxes[idxF]?` is `none` and the final conjuncts of `GroupAnchors`
are unsatisfiable.  The symmetric case (`toId` the group, `fromId` outside) fails through
`idxT`.  Endpoints that stay inside the group are *not* rewritten to members
(`Compound.endpoint` keeps `index` when `source == contains`), so the member rewrite the
docstring feared does not occur; the failure is the bottom-node alias.
`group_alias_tail_out_of_boxes` below is a computed witness of the rewrite, and
`measuredGraph_edge_source` (ExecutedPortsFacts.lean:541) proves that `measuredGraph`
applies it to every edge.

`GroupAnchorsWeak` restricts `GroupAnchors` to routes whose two endpoint boxes are
effective nodes (plain or fixed-size); `groupAnchorsWeak_holds` proves it.
`GroupAnchorsAlias` is the true general statement: each candidate edge endpoint resolves
through `q.1.1` and `execution.graph.nodes` to a node that still names, through
`Node.decl`, the model box carrying the route endpoint id.  `groupAnchorsAlias_holds`
proves it for every successful flat execution.  Aliased group-boundary endpoints resolve
to the synthetic bottom node (border 2) of the group box named by the route endpoint. -/

/-- The box named by `id` is an effective node: a plain box or a fixed-size one. -/
def endpointPlain (inp : Input) (id : String) : Prop :=
  ∀ b : ModelBox, b ∈ inp.boxes → b.id = id →
    b.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true

/-- `GroupAnchors` restricted to routes whose two endpoint boxes are effective
nodes.  Every other premise and the conclusion are the original ones. -/
def GroupAnchorsWeak : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    ∀ (execution : SceneExecution inp o res) (packed : Pack.State),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int},
    componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        = .ok loops →
    q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } →
    ∀ {i : Nat} {edge : Edge},
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.tail ≠ edge.head →
    ∀ (rF : ModelRoute), inp.routes[edge.decl]? = some rF →
      endpointPlain inp rF.fromId → endpointPlain inp rF.toId →
      ∃ (idxF idxT : Nat) (sF sT : ModelBox),
        q.1.1[(if edge.reversed then edge.head else edge.tail)]? = some idxF ∧
        inp.boxes[idxF]? = some sF ∧
        q.1.1[(if edge.reversed then edge.tail else edge.head)]? = some idxT ∧
        inp.boxes[idxT]? = some sT ∧
        sF.id = rF.fromId ∧ sT.id = rF.toId

theorem groupAnchorsWeak_holds : GroupAnchorsWeak := by
  intro inp o res execution _packed _hpacked _c _q _hselected candidate run _loops _area
    hrun _hloops _hpart i edge hedge _hne rF hrouteF hplainF hplainT
  obtain ⟨index, route, raw, source, target, hroute, hdecl, hsource, hsourceId, htarget,
    htargetId, hkeys⟩ :=
    componentCandidate_effective_node_model_keys execution.graph_eq hrun hedge
  have hrouteAt : inp.routes[edge.decl]? = some route := by
    rw [hdecl]
    exact hroute
  have hrouteEq : route = rF :=
    Option.some.inj (hrouteAt.symm.trans hrouteF)
  have hmemS : source ∈ inp.boxes := List.mem_of_getElem? hsource
  have hmemT : target ∈ inp.boxes := List.mem_of_getElem? htarget
  have hsPlain := hplainF source hmemS
    (hsourceId.trans (congrArg ModelRoute.fromId hrouteEq))
  have htPlain := hplainT target hmemT
    (htargetId.trans (congrArg ModelRoute.toId hrouteEq))
  obtain ⟨hfromKey, htoKey⟩ := hkeys hsPlain htPlain
  exact ⟨raw.tail, raw.head, source, target, hfromKey, hsource, htoKey, htarget,
    hsourceId.trans (congrArg ModelRoute.fromId hrouteEq),
    htargetId.trans (congrArg ModelRoute.toId hrouteEq)⟩

/-- The two-box witness of the falsifying normalization: with `G` a group and `B` a
plain node outside it, the aliased tail of the raw edge `G → B` is the synthetic
bottom index, which is at least `boxes.length`, while the head stays at the plain
endpoint.  `measuredGraph` applies exactly this `aliasEdge` to every edge
(`measuredGraph_edge_source`), so a route anchored at `G` and leaving the group
has no `inp.boxes` preimage for its `from` endpoint. -/
private def aliasWitnessBoxes : List ModelBox :=
  [{ id := "G", role := .group, exclusive := false }, { id := "B" }]

private def aliasWitnessRaw : Edge := ⟨0, 1, 1, 0, false⟩

theorem group_alias_tail_out_of_boxes :
    aliasWitnessBoxes.length ≤
      (Compound.aliasEdge aliasWitnessBoxes aliasWitnessRaw).tail ∧
    (Compound.aliasEdge aliasWitnessBoxes aliasWitnessRaw).head = 1 := by
  refine ⟨?_, rfl⟩
  decide


/-! ### Synthetic bottom nodes of `markNodes`

The counting lemma below feeds `bottom_node_decl`: the synthetic bottom node that
`Compound.markNodes` places at `Compound.bottomIndex boxes i` declares the group box
index `i`. -/

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

/-- The synthetic bottom (border-2) nodes `Compound.markNodes` appends for the
group boxes of `sub`, with declaration indices offset by `off` and paths
computed against the full box list `full`.  `markExtras boxes` is
`bottomNodesOf boxes boxes 0`. -/
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

/-- The bottom node at `Compound.bottomIndex boxes i` is the synthetic marker
of group box `i` itself: its declaration is `i`. -/
private theorem bottom_node_decl {boxes : List ModelBox} {pad : Int}
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
  have hme : markExtras boxes = bottomNodesOf boxes boxes 0 := rfl
  rw [hme] at hx
  obtain ⟨d, g, hdg, hgg, hdecl, hcount⟩ := bottomNodesOf_getElem?_decl hx
  have hi : i < boxes.length := (List.getElem?_eq_some_iff.mp hbi).1
  have hcntI : ((boxes.take i).filter fun b => b.role == .group).length =
      j - (nodes.zipIdx.map (markOne boxes pad titles)).length := by omega
  have hidi : i = d := by
    rcases Nat.lt_trichotomy i d with hlt | heq | hgt
    · have hbdi : (fun b => b.role == .group) b = true := beq_iff_eq.mpr hb
      have hmono := countP_take_add_one (p := fun b => b.role == .group)
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
      have hmono := countP_take_add_one (p := fun b => b.role == .group)
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

/-- `Compound.endpoint` always lands on either the original index or the
synthetic bottom index of that index's group box; in the latter case the
looked-up box is a group. -/
private theorem endpoint_cases {boxes : List ModelBox} (s : Bool) (i j : Nat) :
    Compound.endpoint boxes s i j = i ∨
      (Compound.endpoint boxes s i j = Compound.bottomIndex boxes i ∧
        ∀ box, boxes[i]? = some box → box.role = .group) := by
  unfold Compound.endpoint
  cases hbi : boxes[i]? with
  | none => exact Or.inl rfl
  | some box =>
    cases _hbj : boxes[j]? with
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
          have heq : box' = box := by
            have h4 : box = box' := Option.some.inj hb'
            exact h4.symm
          rw [heq]
          cases hbr : box.role
          · exfalso
            have h1 : (box.role != .group || i == j) = true := by
              rw [hbr]
              cases hij : (i == j) <;> rfl
            exact hc h1
          · rfl

/-- One candidate-edge endpoint resolved to its model identity: either a plain
box preimage (`inp.boxes[n.decl]?` is an effective node whose id is the route
endpoint), or the group proxy node of a group box `G` whose id is the route
endpoint.  `n.decl` is the model box index for top nodes and the group box
index for bottom proxies. -/
def endpointWitness (inp : Input) (r : ModelRoute) (isFrom : Bool) (_v : Nat)
    (n : Node) : Prop :=
  ∃ b : ModelBox,
    inp.boxes[n.decl]? = some b ∧
    b.id = (if isFrom then r.fromId else r.toId) ∧
    ((n.border = 0 ∧ (b.role = .node ∨
        inp.fixedSizes.any (fun fixed => fixed.1 == b.id) = true)) ∨
      ((n.border = -2 ∨ n.border = 2) ∧ b.role = .group))

/-- The prepared box list used by `measuredGraph`: fixed-size boxes are
effective nodes. -/
def preparedBoxes (inp : Input) : List ModelBox :=
  inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box

/-- The aliased edge `measuredGraph` builds from the raw `edgeOf` result. -/
def aliasEdgeOf (inp : Input) (raw : Edge) : Edge :=
  Compound.aliasEdge (preparedBoxes inp) raw

/-- Lookup through the prepared list: the box at the same index, with its role
rewritten when fixed-size. -/
theorem preparedBoxes_lookup {inp : Input} {j : Nat} {src : ModelBox}
    (hsrc : inp.boxes[j]? = some src) :
    (preparedBoxes inp)[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src) := by
  unfold preparedBoxes
  rw [List.getElem?_map, hsrc]
  simp

/-- Inside `markNodes`, the node at an original index `j` keeps the declaration
`j` and is either the border-0 node of a non-group box or the border-(-2)
title node of a group box; in both cases the input box at index `j` carries
the identity needed by `endpointWitness`. -/
private theorem model_node_witness {inp : Input} {r : ModelRoute} (isFrom : Bool)
    {prepared : List ModelBox} {graph : Graph} {pad : Int} {titles : List (Int × Int)}
    {nodes0 : List Node}
    (hlen0 : nodes0.length = prepared.length)
    (hmeta : ∀ (i : Nat) (n : Node), nodes0[i]? = some n → n.decl = i ∧ n.border = 0)
    (hmark : graph.nodes = Compound.markNodes prepared pad titles nodes0)
    {j : Nat} {src : ModelBox} (hsrc : inp.boxes[j]? = some src)
    (hbp : prepared[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src))
    (hid : src.id = (if isFrom then r.fromId else r.toId))
    {v : Nat} {n : Node} (hnode : graph.nodes[v]? = some n)
    (hvj : v = j) :
    endpointWitness inp r isFrom v n := by
  have hjp : j < prepared.length := by
    have := (List.getElem?_eq_some_iff.mp hbp).1
    omega
  have hjn : j < nodes0.length := by rw [hlen0]; exact hjp
  have hmetaJ := hmeta j (nodes0[j]'hjn) (List.getElem?_eq_getElem hjn)
  rw [hvj, hmark] at hnode
  let g0 : Graph := { nodes := nodes0, edges := [], slot := 0 }
  have hprep : (Compound.prepare prepared pad titles g0).nodes =
      Compound.markNodes prepared pad titles nodes0 :=
    Compound.prepare_nodes prepared pad titles g0
  rw [← hprep] at hnode
  cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
  | true =>
    rw [hf] at hbp
    simp only [↓reduceIte] at hbp
    have hbox : prepared[j]? = some { src with role := .node } := hbp
    have hng : ({ src with role := .node } : ModelBox).role ≠ .group := by
      intro hcon; cases hcon
    have hrec := Compound.prepare_plain_node_record prepared pad titles g0 hjn
      hbox hng
    have hnEq : n = { nodes0[j]'hjn with
        clusterPath := Compound.path prepared { src with role := .node } } :=
      Option.some.inj (hnode.symm.trans hrec)
    subst hnEq
    refine ⟨src, ?_, hid, Or.inl ⟨hmetaJ.2, Or.inr hf⟩⟩
    show inp.boxes[(nodes0[j]'hjn).decl]? = some src
    rw [hmetaJ.1]
    exact hsrc
  | false =>
    rw [hf] at hbp
    cases hs : src.role with
    | node =>
      have hbox : prepared[j]? = some src := hbp
      have hng : src.role ≠ .group := by
        rw [hs]; intro hcon; cases hcon
      have hrec := Compound.prepare_plain_node_record prepared pad titles g0 hjn
        hbox hng
      have hnEq : n = { nodes0[j]'hjn with
          clusterPath := Compound.path prepared src } :=
        Option.some.inj (hnode.symm.trans hrec)
      subst hnEq
      refine ⟨src, ?_, hid, Or.inl ⟨hmetaJ.2, Or.inl hs⟩⟩
      show inp.boxes[(nodes0[j]'hjn).decl]? = some src
      rw [hmetaJ.1]
      exact hsrc
    | group =>
      have hbox : prepared[j]? = some src := hbp
      have hrec := Compound.prepare_group_title_record prepared pad titles g0 hjn
        hbox hs
      have hnEq : n = { nodes0[j]'hjn with
          clusterPath := Compound.path prepared src ++ [j], border := -2,
          w := (titles.getD j (0, 0)).1,
          h := if (nodes0[j]'hjn).loopExtent == 0 then (titles.getD j (0, 0)).2 + pad
               else max ((titles.getD j (0, 0)).2 + pad) (nodes0[j]'hjn).h } :=
        Option.some.inj (hnode.symm.trans hrec)
      subst hnEq
      refine ⟨src, ?_, hid, Or.inr ⟨Or.inl rfl, hs⟩⟩
      show inp.boxes[(nodes0[j]'hjn).decl]? = some src
      rw [hmetaJ.1]
      exact hsrc

/-- Inside `markNodes`, the synthetic bottom node at `Compound.bottomIndex
prepared j` (border 2) declares the group box index `j`; the input box at
index `j` carries the identity needed by `endpointWitness`. -/
private theorem model_bottom_witness {inp : Input} {r : ModelRoute} (isFrom : Bool)
    {prepared : List ModelBox} {graph : Graph} {pad : Int} {titles : List (Int × Int)}
    {nodes0 : List Node}
    (hlen0 : nodes0.length = prepared.length)
    (hmark : graph.nodes = Compound.markNodes prepared pad titles nodes0)
    {j : Nat} {src : ModelBox} (hsrc : inp.boxes[j]? = some src)
    (hbp : prepared[j]? =
      some (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
        { src with role := .node } else src))
    (hbpg : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
      { src with role := .node } else src).role = .group)
    (hid : src.id = (if isFrom then r.fromId else r.toId))
    {v : Nat} {n : Node} (hnode : graph.nodes[v]? = some n)
    (hvj : v = Compound.bottomIndex prepared j) :
    endpointWitness inp r isFrom v n := by
  have hfFalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false := by
    cases hf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
    | true =>
      rw [hf] at hbpg
      simp only [↓reduceIte] at hbpg
      exact absurd hbpg (by intro hcon; cases hcon)
    | false => rfl
  have hpbEq : (if inp.fixedSizes.any (fun fixed => fixed.1 == src.id) then
      { src with role := .node } else src) = src := by
    rw [hfFalse]; simp
  have hsrole : src.role = .group := by rw [← hpbEq]; exact hbpg
  have hbpj : prepared[j]? = some src := by rw [hpbEq] at hbp; exact hbp
  have hvGe : nodes0.length ≤ v := by
    rw [hvj, hlen0]
    unfold Compound.bottomIndex
    omega
  have hnode' : (Compound.markNodes prepared pad titles nodes0)[v]? = some n := by
    rw [← hmark]; exact hnode
  obtain ⟨hb2, _, _, _, _⟩ :=
    Compound.markNodes_getElem?_bottom prepared pad titles nodes0 v hvGe hnode'
  have hdeclEq : n.decl = j := by
    rw [hvj] at hnode'
    exact bottom_node_decl hlen0 rfl hnode' hbpj hsrole
  refine ⟨src, by rw [hdeclEq]; exact hsrc, hid, Or.inr ⟨Or.inr hb2, hsrole⟩⟩

/-- The true anchor identification: in every successful flat execution, for
every component part and every proper candidate edge, each endpoint resolves
either to the plain model box of the route endpoint or to the top/bottom proxy
node of the group box named by the route endpoint.  `Compound.aliasEdge` may
rewrite a group endpoint to the synthetic bottom index; that node still names
the same group box through `Node.decl`.  `edge.original.tail`/`head` are the
semantic (route-order) endpoints: `Edge.original` already undoes reversal. -/
def GroupAnchorsAlias : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult},
    ∀ (execution : SceneExecution inp o res) (packed : Pack.State),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    ∀ {c : Nat} {q : (List Nat × Part) × Rect},
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q →
    ∀ {candidate : Nat} {run : Run} {loops : List (Nat × LoopPlacement)} {area : Int},
    componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    componentLoops execution.params
      (componentCandidate execution.graph q.1.1 candidate) run execution.measured
        = .ok loops →
    q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured loops
      with area := area } →
    ∀ {i : Nat} {edge : Edge},
    (componentCandidate execution.graph q.1.1 candidate).edges[i]? = some edge →
    edge.tail ≠ edge.head →
    ∃ (r : ModelRoute), inp.routes[edge.decl]? = some r ∧
      ∀ (pos : Nat) (v : Nat) (n : Node),
        q.1.1[pos]? = some v →
        execution.graph.nodes[v]? = some n →
        if pos = edge.original.tail then endpointWitness inp r true v n
          else if pos = edge.original.head then endpointWitness inp r false v n
            else True

theorem groupAnchorsAlias_holds : GroupAnchorsAlias := by
  intro inp o res execution packed _hpack c q hq candidate run loops area hrun
    hloops _hqplace i edge hedge _hne
  have hedges : edge ∈ (componentCandidate execution.graph q.1.1 candidate).edges :=
    List.mem_of_getElem? hedge
  obtain ⟨routeIndex, route, raw, source, target, hrouteIdx, hedgeroute, hdecl,
    hrawsource, hsourceId, hrawtarget, htargetId, _hsem⟩ :=
    componentCandidate_model_endpoint_source execution.graph_eq hedges
  obtain ⟨hpartsMap, _⟩ :=
    actual_components_parts_geometry (by rfl) execution.components_eq
  obtain ⟨hqin, _⟩ := List.of_mem_zip (List.mem_of_getElem? hq)
  have hcompIn : q.1.1 ∈ components execution.graph := by
    have hmap : q.1.1 ∈
        execution.componentsAcc.parts.map (fun part : List Nat × Part => part.1) :=
      List.mem_map_of_mem hqin
    rw [hpartsMap] at hmap
    exact hmap
  obtain ⟨nodes0, edges0, titles, hprepared, hnodeLen, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph_eq
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hle := execution.lines_eq
    unfold boxLines at hle
    have := (mapM_getElem? _ _ _ hle).1
    simpa [List.length_zipIdx] using this
  have hlen0 : nodes0.length = (preparedBoxes inp).length := by
    rw [hnodeLen, hlinesLen, preparedBoxes, List.length_map]
  have hgraphNodes : execution.graph.nodes =
      Compound.markNodes (preparedBoxes inp) execution.params.clusterPad titles nodes0 := by
    rw [hprepared]
    exact Compound.prepare_nodes _ _ _ _
  obtain ⟨gEdge, hgEdge, hgTailMem, hsemG⟩ := componentCandidate_semantic_source hedges
  obtain ⟨index2, route2, raw2, hr2Route, hr2EdgeOf, hgeAlias⟩ :=
    measuredGraph_edge_source execution.graph_eq hgEdge
  obtain ⟨h2Decl, h2Rev, _, _, _, _⟩ := edgeOf_semantic_endpoints hr2EdgeOf
  have hgeRev : gEdge.reversed = false := by rw [hgeAlias]; exact h2Rev
  have hgeOrig : gEdge.original = gEdge := by
    cases gEdge with
    | mk _ _ _ _ rev => cases hgeRev; rfl
  have hgeDeclIdx : edge.decl = index2 := by
    have h1 : edge.decl = gEdge.decl := by
      have h := congrArg Edge.decl hsemG
      simpa only [Edge.original_decl] using h
    rw [h1, hgeAlias, Compound.aliasEdge_decl, h2Decl]
  have hidx2 : index2 = routeIndex := hgeDeclIdx.symm.trans hdecl
  have hroute2Eq : route2 = route := by
    rw [hidx2] at hr2Route
    exact Option.some.inj (hr2Route.symm.trans hrouteIdx)
  rw [hroute2Eq, hidx2] at hr2EdgeOf
  have hrawEq : raw2 = raw := Except.ok.inj (hr2EdgeOf.symm.trans hedgeroute)
  rw [hrawEq] at hgeAlias
  have hgTailMem2 : (aliasEdgeOf inp raw).tail ∈ q.1.1 := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailMem
  have hbdAll := sceneExecution_edges_bounded execution
  obtain ⟨comp', hcomp'In, hgTailC, hgHeadC⟩ :=
    components_edge_endpoints hbdAll
      (List.mem_append.mpr (Or.inl hgEdge))
  have hgTailC' : (aliasEdgeOf inp raw).tail ∈ comp' := by
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgTailC
  have hcompEq : comp' = q.1.1 :=
    components_shared_member_eq hcomp'In hcompIn hgTailC' hgTailMem2
  have hgHeadMem : (aliasEdgeOf inp raw).head ∈ q.1.1 := by
    rw [← hcompEq]
    simpa only [hgeAlias, aliasEdgeOf, preparedBoxes] using hgHeadC
  have hlookupT : q.1.1[q.1.1.idxOf (aliasEdgeOf inp raw).tail]? =
      some (aliasEdgeOf inp raw).tail := by
    have hlt : q.1.1.idxOf (aliasEdgeOf inp raw).tail < q.1.1.length :=
      List.idxOf_lt_length_of_mem hgTailMem2
    rw [List.getElem?_eq_getElem hlt]
    exact congrArg some (List.getElem_idxOf hlt)
  have hlookupH : q.1.1[q.1.1.idxOf (aliasEdgeOf inp raw).head]? =
      some (aliasEdgeOf inp raw).head := by
    have hlt : q.1.1.idxOf (aliasEdgeOf inp raw).head < q.1.1.length :=
      List.idxOf_lt_length_of_mem hgHeadMem
    rw [List.getElem?_eq_getElem hlt]
    exact congrArg some (List.getElem_idxOf hlt)
  have hsemTail : edge.original.tail = q.1.1.idxOf (aliasEdgeOf inp raw).tail := by
    have h := congrArg Edge.tail hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  have hsemHead : edge.original.head = q.1.1.idxOf (aliasEdgeOf inp raw).head := by
    have h := congrArg Edge.head hsemG
    rw [hgeOrig, hgeAlias] at h
    exact h
  refine ⟨route, by rw [hdecl]; exact hrouteIdx, ?_⟩
  intro pos v n hpos hnode
  by_cases hpT : pos = edge.original.tail
  · rw [ite_eq_left hpT]
    rw [hpT, hsemTail] at hpos
    have hvEq : v = (aliasEdgeOf inp raw).tail :=
      Option.some.inj (hpos.symm.trans hlookupT)
    subst hvEq
    rcases endpoint_cases (boxes := preparedBoxes inp) true raw.tail raw.head
      with hflat | ⟨hbot, hgrp⟩
    · refine model_node_witness true hlen0 hmetadata hgraphNodes hrawsource
        (preparedBoxes_lookup hrawsource) hsourceId hnode ?_
      rw [show (aliasEdgeOf inp raw).tail =
          Compound.endpoint (preparedBoxes inp) true raw.tail raw.head from rfl]
      exact hflat
    · refine model_bottom_witness true hlen0 hgraphNodes hrawsource
        (preparedBoxes_lookup hrawsource)
        (hgrp _ (preparedBoxes_lookup hrawsource)) hsourceId hnode ?_
      rw [show (aliasEdgeOf inp raw).tail =
          Compound.endpoint (preparedBoxes inp) true raw.tail raw.head from rfl]
      exact hbot
  · rw [ite_eq_right hpT]
    by_cases hpH : pos = edge.original.head
    · rw [ite_eq_left hpH]
      rw [hpH, hsemHead] at hpos
      have hvEq : v = (aliasEdgeOf inp raw).head :=
        Option.some.inj (hpos.symm.trans hlookupH)
      subst hvEq
      rcases endpoint_cases (boxes := preparedBoxes inp) false raw.head raw.tail
        with hflat | ⟨hbot, hgrp⟩
      · refine model_node_witness false hlen0 hmetadata hgraphNodes hrawtarget
          (preparedBoxes_lookup hrawtarget) htargetId hnode ?_
        rw [show (aliasEdgeOf inp raw).head =
            Compound.endpoint (preparedBoxes inp) false raw.head raw.tail from rfl]
        exact hflat
      · refine model_bottom_witness false hlen0 hgraphNodes hrawtarget
          (preparedBoxes_lookup hrawtarget)
          (hgrp _ (preparedBoxes_lookup hrawtarget)) htargetId hnode ?_
        rw [show (aliasEdgeOf inp raw).head =
            Compound.endpoint (preparedBoxes inp) false raw.head raw.tail from rfl]
        exact hbot
    · rw [ite_eq_right hpH]
      exact True.intro

end Elegant.Layered.PipelineImpl
