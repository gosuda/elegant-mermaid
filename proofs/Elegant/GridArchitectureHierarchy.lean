import Elegant.GridArchitecturePlacement

set_option autoImplicit false

namespace Elegant.Grid.Architecture

structure Input where
  parents : List Int
  groups : List Group
  edges : List Edge
  deriving Repr

structure LiftedEdge where
  a : Unit
  b : Unit
  sideA : Side
  sideB : Side
  deriving Repr

structure Placement where
  localNodes : List Cell
  localGroups : List Cell
  relative : List Span
  fuel : Nat
  budgetExhausted : Bool := false
  deriving Repr

def virtualParents (input : Input) : List Int :=
  input.parents ++ ((List.range input.groups.length).filter fun (g : Nat) =>
    !input.parents.contains (Int.ofNat g) &&
      !input.groups.any (fun entry => entry.parent == Int.ofNat g)).map Int.ofNat

def groupChain (groups : List Group) : Nat → Int → List Unit
  | 0, _ => []
  | fuel + 1, g =>
    if g < 0 then [] else
    groupChain groups fuel (groups.getD g.toNat default).parent ++ [⟨-1, g⟩]

def chainOf (input : Input) (v : Nat) : List Unit :=
  groupChain input.groups input.groups.length ((virtualParents input).getD v (-1)) ++ [⟨v, -1⟩]

def divergent : List Unit → List Unit → Int → Option (Int × Unit × Unit)
  | a :: as, b :: bs, parent =>
    if a = b then divergent as bs a.group else some (parent, a, b)
  | _, _, _ => none

def lifted (input : Input) (parent : Int) : List LiftedEdge :=
  input.edges.filterMap fun e =>
    if e.a = e.b then none else
    match divergent (chainOf input e.a) (chainOf input e.b) (-1) with
    | some (g, a, b) =>
      if g = parent then some ⟨a, b, e.sideA, e.sideB⟩ else none
    | none => none

def firstNodes (input : Input) : List Int :=
  (List.range input.groups.length).reverse.foldl (fun (first : List Int) (g : Nat) =>
    let nodes := (virtualParents input).zipIdx |>.filter (fun q => q.1 == Int.ofNat g)
    let children := input.groups.zipIdx |>.filter (fun q => q.1.parent == Int.ofNat g)
    let key := nodes.foldl (fun acc q => min acc (Int.ofNat q.2))
      (Int.ofNat ((virtualParents input).length + g))
    first.set g (children.foldl (fun acc q => min acc (first.getD q.2 0)) key))
      (List.replicate input.groups.length 0)

def levelOf (input : Input) (p : Params) (relative : List Span) (parent : Int) : Level :=
  let parents := virtualParents input
  let nodes := (parents.zipIdx.filter (fun q => q.1 == parent)).map fun q => (⟨q.2, -1⟩ : Unit)
  let groups := (input.groups.zipIdx.filter (fun q => q.1.parent == parent)).map fun q =>
    (⟨-1, q.2⟩ : Unit)
  let first := firstNodes input
  let key := fun (u : Unit) => if u.group < 0 then u.node else first.getD u.group.toNat 0
  let units := (nodes ++ groups).mergeSort fun a b => decide (key a ≤ key b)
  let rects := units.map fun u => if u.group < 0 then ⟨0, 0, p.pitchX, p.pitchY⟩
    else relative.getD u.group.toNat default
  let edges := (lifted input parent).map fun e =>
    (⟨(units.findIdx? (· == e.a)).getD 0, (units.findIdx? (· == e.b)).getD 0,
      e.sideA, e.sideB⟩ : Edge)
  ⟨units, rects, List.replicate units.length default, List.replicate units.length default,
    List.replicate units.length false, edges, emptySpan, false⟩

def arrangeParent (input : Input) (p : Params) (fp : FrameParams)
    (parent : Int) (state : Placement) : Placement :=
  let result := arrange p state.fuel (levelOf input p state.relative parent)
  let l := result.1
  let state := l.units.zipIdx.foldl (fun state q =>
    let c := l.cells.getD q.2 default
    if q.1.group < 0 then { state with localNodes := state.localNodes.set q.1.node.toNat c }
    else { state with localGroups := state.localGroups.set q.1.group.toNat c })
      { state with fuel := result.2, budgetExhausted := state.budgetExhausted || l.budgetExhausted }
  if parent < 0 then state else
    let content := l.absolute.foldl Span.union emptySpan
    { state with relative := state.relative.set parent.toNat (frameOf fp (input.groups.getD parent.toNat default) content) }

def placeHierarchy (input : Input) (p : Params) (fp : FrameParams) (fuel : Nat) : Placement :=
  let initial : Placement := ⟨List.replicate (virtualParents input).length default,
    List.replicate input.groups.length default, List.replicate input.groups.length default, fuel, false⟩
  let placed := (List.range input.groups.length).reverse.foldl
    (fun state (g : Nat) => arrangeParent input p fp (Int.ofNat g) state) initial
  arrangeParent input p fp (-1) placed

structure Resolved where
  nodes : List Cell
  frames : List Span
  deriving Repr

def resolveHierarchy (input : Input) (p : Params) (placed : Placement) : Resolved :=
  let origins := input.groups.zipIdx.foldl (fun origins q =>
    let base := if q.1.parent < 0 then default else origins.getD q.1.parent.toNat default
    let offset := placed.localGroups.getD q.2 default
    origins ++ [(⟨base.x + offset.x, base.y + offset.y⟩ : Cell)]) ([] : List Cell)
  let frames := placed.relative.zipIdx.map fun q =>
    let base := origins.getD q.2 default
    q.1.shift (base.x * p.pitchX) (base.y * p.pitchY)
  let nodes := (virtualParents input).zipIdx.map fun q =>
    let base := if q.1 < 0 then default else origins.getD q.1.toNat default
    let offset := placed.localNodes.getD q.2 default
    (⟨base.x + offset.x, base.y + offset.y⟩ : Cell)
  ⟨nodes, frames⟩

end Elegant.Grid.Architecture
