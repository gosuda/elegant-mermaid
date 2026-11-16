import Elegant.Model
import Elegant.Layered.Cycles

set_option autoImplicit false

namespace Elegant.Layered.Compound

/-- Proper ancestor indices in outermost-first order. Fuel bounds malformed input too. -/
def ancestors (boxes : List ModelBox) : Nat → String → List Nat
  | 0, _ => []
  | _ + 1, "" => []
  | fuel + 1, id =>
    match boxes.findIdx? (fun box => box.id == id) with
    | none => []
    | some index =>
      match boxes[index]? with
      | none => []
      | some box => ancestors boxes fuel box.parent ++ [index]
def path (boxes : List ModelBox) (box : ModelBox) : List Nat :=
  ancestors boxes boxes.length box.parent

/-- Boundary identity is deliberately not included among proper descendants. -/
def inside (boxes : List ModelBox) (group endpoint : String) : Bool :=
  match boxes.find? (fun box => box.id == endpoint),
      boxes.findIdx? (fun box => box.id == group) with
  | some box, some index => (path boxes box).contains index
  | _, _ => false

def crosses (boxes : List ModelBox) (routes : List ModelRoute) (group : String) : Bool :=
  routes.any fun route => inside boxes group route.fromId != inside boxes group route.toId

def independent (boxes : List ModelBox) (routes : List ModelRoute) (box : ModelBox) : Bool :=
  box.role == .group && box.direction != "" && !crosses boxes routes box.id


def bottomIndex (boxes : List ModelBox) (index : Nat) : Nat :=
  boxes.length + ((boxes.take index).filter fun box => box.role == .group).length

def endpoint (boxes : List ModelBox) (source : Bool) (index other : Nat) : Nat :=
  match boxes[index]?, boxes[other]? with
  | some box, some target =>
    if box.role != .group || index == other then index
    else
      let contains := inside boxes box.id target.id
      if source == contains then index else bottomIndex boxes index
  | _, _ => index

def aliasEdge (boxes : List ModelBox) (edge : Edge) : Edge :=
  { edge with
    tail := endpoint boxes true edge.tail edge.head
    head := endpoint boxes false edge.head edge.tail }
def markNodes (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (nodes : List Node) : List Node :=
  let marked := nodes.zipIdx.map fun q =>
    match boxes[q.2]? with
    | none => q.1
    | some box =>
      if box.role == .group then
        let title := titles.getD q.2 (0, 0)
        { q.1 with
          clusterPath := path boxes box ++ [q.2]
          border := -2
          w := title.1
          h := if q.1.loopExtent == 0 then title.2 + pad else max (title.2 + pad) q.1.h }
      else { q.1 with clusterPath := path boxes box }
  marked ++ (boxes.zipIdx.filterMap fun q =>
    if q.1.role == .group then
      some {
        decl := q.2, w := 0, h := 0
        clusterPath := path boxes q.1 ++ [q.2], border := 2 }
    else none)

def constraints (g : Graph) : List Edge :=
  let tops := g.nodes.zipIdx.filter fun q => q.1.border == -2
  tops.flatMap fun top =>
    match g.nodes.zipIdx.find? (fun q => q.1.border == 2 && q.1.decl == top.1.decl) with
    | none => []
    | some bottom =>
      let members := g.nodes.zipIdx.filter fun q =>
        q.1.border == 0 && q.1.clusterPath.contains top.1.decl
      let children := tops.filter fun q =>
        q.1.clusterPath.dropLast == top.1.clusterPath
      let nested := children.flatMap fun child =>
        match g.nodes.zipIdx.find? (fun q =>
          q.1.border == 2 && q.1.decl == child.1.decl) with
        | none => []
        | some childBottom =>
          [⟨top.2, child.2, 1, 0, false⟩, ⟨childBottom.2, bottom.2, 1, 0, false⟩]
      let leaves := members.flatMap fun member =>
        [⟨top.2, member.2, 1, 0, false⟩, ⟨member.2, bottom.2, 1, 0, false⟩]
      if members.isEmpty && children.isEmpty then [⟨top.2, bottom.2, 1, 0, false⟩]
      else leaves ++ nested

def protect (g : Graph) : Graph :=
  ProtectedCycles.breakWithHierarchy g (constraints g)

def rankingGraph (g : Graph) : Graph :=
  { g with edges := g.edges.filter (fun edge => edge.tail != edge.head) ++
      (constraints g).zipIdx.map (fun q => { q.1 with decl := g.edges.length + q.2 }) }

def prepare (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int)) (g : Graph) : Graph :=
  { g with
    nodes := markNodes boxes pad titles g.nodes
    edges := g.edges.map (aliasEdge boxes) }

theorem aliasEdge_decl (boxes : List ModelBox) (edge : Edge) :
    (aliasEdge boxes edge).decl = edge.decl := rfl

theorem protect_decls (g : Graph) :
    (protect g).edges.map (·.decl) = g.edges.map (·.decl) := by
  exact ProtectedCycles.semantic_declarations g (constraints g)
theorem prepare_decls (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int)) (g : Graph) :
    (prepare boxes pad titles g).edges.map (·.decl) = g.edges.map (·.decl) := by
  unfold prepare
  simp only [List.map_map]
  rfl

/-! ### Construction facts for the group (title) nodes that `markNodes` creates

`Pipeline.componentTitles` reads, for each node of the prepared graph with `border = -2`,
the record fields `w` and `h - clusterPad`. These theorems fix what `markNodes` and `prepare`
actually store: the title node created for source box `i` keeps the original declaration
(`decl`), carries the supplied title width `w = (titles.getD i (0, 0)).1` — the `getD`
fallback `(0, 0)` covers short and empty title lists — and stores
`h ≥ (titles.getD i (0, 0)).2 + pad`, with exact equality in the zero-loop-extent branch.
Ordinary (non-group) nodes keep every field except `clusterPath`, and every synthetic
border-2 node of the appended section is a `w = h = 0` record whose `decl` is the index of
a group box. -/

private theorem filterMap_some_map {α β : Type} (p : α → Bool) (g : α → β) (l : List α) :
    (l.filterMap fun a => if p a then some (g a) else none) = (l.filter p).map g := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

private theorem zipIdx_map_lt_length {α β : Type} {f : α × Nat → β} {l : List α} {i : Nat}
    (hi : i < l.length) : i < (l.zipIdx.map f).length := by
  simp only [List.length_map, List.length_zipIdx]
  exact hi

theorem markNodes_length_ge (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) :
    nodes.length ≤ (markNodes boxes pad titles nodes).length := by
  unfold markNodes
  dsimp only
  simp only [List.length_append, List.length_map, List.length_zipIdx]
  exact Nat.le_add_right _ _

theorem markNodes_length (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) :
    (markNodes boxes pad titles nodes).length =
      nodes.length + (boxes.zipIdx.filter (fun q => q.1.role == .group)).length := by
  unfold markNodes
  dsimp only
  rw [filterMap_some_map]
  simp

private theorem markNodes_getElem?_missing (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) {i : Nat} (hi : i < nodes.length)
    (hb : boxes[i]? = none) :
    (markNodes boxes pad titles nodes)[i]? = some (nodes[i]'hi) := by
  unfold markNodes
  dsimp only
  rw [List.getElem?_append_left (zipIdx_map_lt_length hi)]
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
    Option.map_some, Nat.zero_add, hb]

theorem markNodes_getElem?_group (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) {i : Nat} (hi : i < nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hg : box.role = .group) :
    (markNodes boxes pad titles nodes)[i]? =
      some { nodes[i]'hi with
             clusterPath := path boxes box ++ [i]
             border := -2
             w := (titles.getD i (0, 0)).1
             h := if nodes[i].loopExtent == 0 then (titles.getD i (0, 0)).2 + pad
                  else max ((titles.getD i (0, 0)).2 + pad) nodes[i].h } := by
  unfold markNodes
  dsimp only
  rw [List.getElem?_append_left (zipIdx_map_lt_length hi)]
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
    Option.map_some, Nat.zero_add, hb]
  simp [hg]

private theorem markNodes_getElem?_node (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) {i : Nat} (hi : i < nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hng : box.role ≠ .group) :
    (markNodes boxes pad titles nodes)[i]? =
      some { nodes[i]'hi with clusterPath := path boxes box } := by
  unfold markNodes
  dsimp only
  rw [List.getElem?_append_left (zipIdx_map_lt_length hi)]
  simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi,
    Option.map_some, Nat.zero_add, hb]
  cases hrole : box.role with
  | node => simp
  | group => exact absurd hrole hng

theorem markNodes_bottom_exists (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) {i : Nat} {box : ModelBox}
    (hb : boxes[i]? = some box) (hg : box.role = .group) :
    ({ decl := i, w := 0, h := 0
       clusterPath := path boxes box ++ [i], border := 2 } : Node) ∈
      markNodes boxes pad titles nodes := by
  unfold markNodes
  dsimp only
  refine List.mem_append.mpr (Or.inr ?_)
  refine List.mem_filterMap.mpr ⟨(box, i), List.mk_mem_zipIdx_iff_getElem?.mpr hb, ?_⟩
  simp [hg]

theorem markNodes_getElem?_bottom (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (nodes : List Node) (j : Nat) (hj : nodes.length ≤ j)
    {x : Node} (hx : (markNodes boxes pad titles nodes)[j]? = some x) :
    x.border = 2 ∧ x.w = 0 ∧ x.h = 0 ∧ x.decl < boxes.length ∧
      ∃ box : ModelBox, boxes[x.decl]? = some box ∧ box.role = .group ∧
        x.clusterPath = path boxes box ++ [x.decl] := by
  unfold markNodes at hx
  dsimp only at hx
  rw [List.getElem?_append_right (by
    simp only [List.length_map, List.length_zipIdx]
    exact hj)] at hx
  have hmem : x ∈ boxes.zipIdx.filterMap (fun q : ModelBox × Nat =>
      if q.1.role == .group then
        some ({ decl := q.2, w := 0, h := 0
                clusterPath := path boxes q.1 ++ [q.2], border := 2 } : Node)
      else none) := by
    obtain ⟨hidx, heq⟩ := List.getElem?_eq_some_iff.mp hx
    rw [← heq]
    exact List.getElem_mem hidx
  obtain ⟨q, hq, hfx⟩ := List.mem_filterMap.mp hmem
  have hbrole : (q.1.role == .group) = true := by
    by_cases h : (q.1.role == .group) = true
    · exact h
    · simp [h] at hfx
  have hrole : q.1.role = .group := of_decide_eq_true hbrole
  have hz : boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hq
  have hi2 : q.2 < boxes.length := (List.getElem?_eq_some_iff.mp hz).1
  have hrec : ({
      decl := q.2
      w := 0
      h := 0
      clusterPath := path boxes q.1 ++ [q.2]
      border := 2 } : Node) = x := by
    simp only [hbrole, ↓reduceIte] at hfx
    exact Option.some.inj hfx
  cases hrec
  exact ⟨rfl, rfl, rfl, hi2, ⟨q.1, hz, hrole, rfl⟩⟩

theorem prepare_nodes (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (g : Graph) :
    (prepare boxes pad titles g).nodes = markNodes boxes pad titles g.nodes := rfl

theorem protect_nodes (g : Graph) : (protect g).nodes = g.nodes := rfl

theorem prepare_nodes_length_ge (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) :
    g.nodes.length ≤ (prepare boxes pad titles g).nodes.length :=
  markNodes_length_ge boxes pad titles g.nodes

/-- Main construction fact: the title node that `prepare` stores at index `i` for group box
`i` keeps the original declaration, carries `border = -2` and the cluster path of that box
extended by the box index, and its dimensions are the supplied title dimensions — exactly the
title width, and the title height plus `pad` (exactly so in the zero-loop-extent branch,
otherwise the maximum with the loop height). -/
theorem prepare_group_title_record (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hg : box.role = .group) :
    (prepare boxes pad titles g).nodes[i]? =
      some { g.nodes[i]'hi with
             clusterPath := path boxes box ++ [i]
             border := -2
             w := (titles.getD i (0, 0)).1
             h := if g.nodes[i].loopExtent == 0 then (titles.getD i (0, 0)).2 + pad
                  else max ((titles.getD i (0, 0)).2 + pad) g.nodes[i].h } :=
  markNodes_getElem?_group boxes pad titles g.nodes hi hb hg

theorem prepare_group_width (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (g : Graph) {i : Nat} (hi : i < g.nodes.length) {box : ModelBox}
    (hb : boxes[i]? = some box) (hg : box.role = .group) {n : Node}
    (hn : (prepare boxes pad titles g).nodes[i]? = some n) :
    n.w = (titles.getD i (0, 0)).1 := by
  have h := prepare_group_title_record boxes pad titles g hi hb hg
  rw [hn] at h
  injection h with h'
  subst h'
  rfl

theorem prepare_group_height_ge (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hg : box.role = .group) {n : Node}
    (hn : (prepare boxes pad titles g).nodes[i]? = some n) :
    (titles.getD i (0, 0)).2 + pad ≤ n.h := by
  have h := prepare_group_title_record boxes pad titles g hi hb hg
  rw [hn] at h
  injection h with h'
  subst h'
  dsimp only
  split
  · omega
  · exact Int.le_max_left _ _

theorem prepare_group_height_eq_of_loopExtent_zero (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hg : box.role = .group) {n : Node}
    (hn : (prepare boxes pad titles g).nodes[i]? = some n)
    (h0 : g.nodes[i].loopExtent = 0) :
    n.h = (titles.getD i (0, 0)).2 + pad := by
  have h := prepare_group_title_record boxes pad titles g hi hb hg
  rw [hn] at h
  injection h with h'
  subst h'
  dsimp only
  simp [h0]

theorem prepare_group_decl (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (g : Graph) {i : Nat} (hi : i < g.nodes.length) {box : ModelBox}
    (hb : boxes[i]? = some box) (hg : box.role = .group) {n : Node}
    (hn : (prepare boxes pad titles g).nodes[i]? = some n) :
    n.decl = g.nodes[i].decl := by
  have h := prepare_group_title_record boxes pad titles g hi hb hg
  rw [hn] at h
  injection h with h'
  subst h'
  rfl

theorem prepare_group_clusterPath (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {box : ModelBox} (hb : boxes[i]? = some box) (hg : box.role = .group) {n : Node}
    (hn : (prepare boxes pad titles g).nodes[i]? = some n) :
    n.clusterPath = path boxes box ++ [i] := by
  have h := prepare_group_title_record boxes pad titles g hi hb hg
  rw [hn] at h
  injection h with h'
  subst h'
  rfl

/-- Ordinary-node indexed association: a non-group source box leaves its node's declaration
and intrinsic dimensions (width, height, loop extent) untouched by `prepare`. Stated field by
field so the statement also holds under a later extension of `markNodes` to structural
non-group parents, which may change internal bookkeeping such as `border` or `clusterPath`. -/
theorem prepare_node_dims_decl (boxes : List ModelBox) (pad : Int) (titles : List (Int × Int))
    (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {n : Node} (hn : (prepare boxes pad titles g).nodes[i]? = some n)
    {box : ModelBox} (hb : boxes[i]? = some box) (hng : box.role ≠ .group) :
    n.decl = g.nodes[i].decl ∧ n.w = g.nodes[i].w ∧ n.h = g.nodes[i].h ∧
      n.loopExtent = g.nodes[i].loopExtent := by
  have hrec := markNodes_getElem?_node boxes pad titles g.nodes hi hb hng
  have heq : some n = some { g.nodes[i]'hi with clusterPath := path boxes box } :=
    hn.symm.trans hrec
  injection heq with heq'
  subst heq'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Consumer-facing discriminator for `Pipeline.componentTitles`: a `border = -2` node of the
prepared graph whose input record did not already carry `border = -2` is the actual title node
of the group box at its index — original declaration, exact title width, height at least title
height + `pad` (exactly so in the zero-loop-extent branch), and that box's cluster path. -/
theorem prepare_group_title_of_border (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} (hi : i < g.nodes.length)
    {n : Node} (hn : (prepare boxes pad titles g).nodes[i]? = some n)
    (hb : n.border = -2) (hnb : g.nodes[i].border ≠ -2) :
    ∃ box : ModelBox, boxes[i]? = some box ∧ box.role = .group ∧
      n.decl = g.nodes[i].decl ∧
      n.w = (titles.getD i (0, 0)).1 ∧
      (titles.getD i (0, 0)).2 + pad ≤ n.h ∧
      (g.nodes[i].loopExtent = 0 → n.h = (titles.getD i (0, 0)).2 + pad) ∧
      n.clusterPath = path boxes box ++ [i] := by
  cases hbx : boxes[i]? with
  | none =>
    have hmis := markNodes_getElem?_missing boxes pad titles g.nodes hi hbx
    have heq : some n = some (g.nodes[i]'hi) := hn.symm.trans hmis
    injection heq with heq'
    subst heq'
    exact absurd hb hnb
  | some b =>
    cases hrole : b.role with
    | group =>
      have hgrp := markNodes_getElem?_group boxes pad titles g.nodes hi hbx hrole
      have heq : some n = some { g.nodes[i]'hi with
          clusterPath := path boxes b ++ [i], border := -2,
          w := (titles.getD i (0, 0)).1,
          h := if g.nodes[i].loopExtent == 0 then (titles.getD i (0, 0)).2 + pad
               else max ((titles.getD i (0, 0)).2 + pad) g.nodes[i].h } := hn.symm.trans hgrp
      injection heq with heq'
      subst heq'
      refine ⟨b, rfl, hrole, rfl, rfl, ?_, ?_, rfl⟩
      · dsimp only
        split
        · omega
        · exact Int.le_max_left _ _
      · intro h0
        simp [h0]
    | node =>
      have hnod := markNodes_getElem?_node boxes pad titles g.nodes hi hbx
        (by rw [hrole]; decide)
      have heq : some n = some { g.nodes[i]'hi with clusterPath := path boxes b } :=
        hn.symm.trans hnod
      injection heq with heq'
      subst heq'
      exact absurd hb hnb

theorem prepare_bottom_exists (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) {i : Nat} {box : ModelBox}
    (hb : boxes[i]? = some box) (hg : box.role = .group) :
    ({ decl := i, w := 0, h := 0
       clusterPath := path boxes box ++ [i], border := 2 } : Node) ∈
      (prepare boxes pad titles g).nodes :=
  markNodes_bottom_exists boxes pad titles g.nodes hb hg

theorem prepare_bottom_of_index (boxes : List ModelBox) (pad : Int)
    (titles : List (Int × Int)) (g : Graph) (j : Nat) (hj : g.nodes.length ≤ j)
    {x : Node} (hx : (prepare boxes pad titles g).nodes[j]? = some x) :
    x.border = 2 ∧ x.w = 0 ∧ x.h = 0 ∧ x.decl < boxes.length ∧
      ∃ box : ModelBox, boxes[x.decl]? = some box ∧ box.role = .group ∧
        x.clusterPath = path boxes box ++ [x.decl] :=
  markNodes_getElem?_bottom boxes pad titles g.nodes j hj hx

end Elegant.Layered.Compound
