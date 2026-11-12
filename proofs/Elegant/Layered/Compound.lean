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

end Elegant.Layered.Compound
