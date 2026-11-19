import Elegant.Layered.ExactPipeline

set_option autoImplicit false

/-! Concurrent regions. A region set names a composite (the parent) and the group boxes that
divide it (the regions), as Go's `layered.Input.RegionSets`. This file resolves the model sets
against an input, rebuilds the per-component region model from a prepared component graph, ranks
a component with every set's regions collapsed onto their first region (Go's `rankEquivalent`,
including the reachability orientation of the semantic edges), and solves the minimum widths and
shared rank spans a composite frame must reserve (Go's `solveRegions`). The placement that
consumes the solution lives in `RegionPlacement`. -/

namespace Elegant
namespace Layered
namespace RegionImpl

open PipelineImpl

/-- The region sets of an input resolved to ids, plus the oriented title dimensions the family
measured for its boxes. -/
structure RegionSpec where
  sets : List (String × List String)
  titles : List (Int × Int)
deriving Repr

def setAt {α : Type} : List α → Nat → α → List α
  | [], _, _ => []
  | _ :: as, 0, b => b :: as
  | a :: as, n + 1, b => a :: setAt as n b

def groupBoxIds (inp : Input) : List String :=
  inp.boxes.filterMap fun b => if b.role == .group then some b.id else none

def groupAtId (groups : List String) (index : Int) : Except LayoutError String :=
  if 0 ≤ index ∧ index < groups.length then .ok (groups.getD index.toNat "")
  else .error .domain

def resolveRegionSet (groups : List String) (set : ModelRegionSet) :
    Except LayoutError (String × List String) := do
  let parent ← groupAtId groups set.parent
  let regions ← set.regions.mapM (groupAtId groups)
  pure (parent, regions)

/-- Go's `graphRegions`: resolve every set's indices against the input's group boxes. -/
def graphRegions (inp : Input) (sets : List ModelRegionSet) :
    Except LayoutError (List (String × List String)) :=
  sets.mapM (resolveRegionSet (groupBoxIds inp))

def regionMemberId (sets : List (String × List String)) (id : String) : Bool :=
  sets.any fun s => s.2.contains id

/-! ### Per-component region model -/

structure RegionCluster where
  id : String
  decl : Nat
  node : Nat
  top : Nat
  bottom : Nat
  titleW : Int
  titleH : Int
  extent : Nat
deriving DecidableEq, Repr, Inhabited

structure LocalRegionSet where
  parent : Nat
  regions : List Nat
deriving DecidableEq, Repr, Inhabited

structure ComponentRegions where
  clusters : List RegionCluster
  parents : List Int
  sets : List LocalRegionSet
  lineH : Int
deriving Repr

def boxParent (inp : Input) (decl : Nat) : String :=
  ((inp.boxes[decl]?).map (·.parent)).getD ""

def boxId (inp : Input) (decl : Nat) : String :=
  ((inp.boxes[decl]?).map (·.id)).getD ""

def clusterRows (inp : Input) (spec : RegionSpec) (cg : Graph) : List RegionCluster :=
  cg.nodes.zipIdx.filterMap fun q =>
    if q.1.border != -2 then none
    else
      let bottom := match cg.nodes.zipIdx.find? (fun b =>
          b.1.border == 2 && b.1.decl == q.1.decl) with
        | some b => b.2
        | none => q.2
      let node := match cg.nodes.zipIdx.find? (fun b => b.1.decl == q.1.decl) with
        | some b => b.2
        | none => q.2
      let titles := spec.titles.getD q.1.decl (0, 0)
      some ({ id := boxId inp q.1.decl, decl := q.1.decl,
              node := node, top := q.2, bottom := bottom,
              titleW := q.1.w, titleH := titles.2, extent := q.1.loopExtent } : RegionCluster)

/-- Go's `newComponentRegions`: keep the sets whose parent cluster is in this component. -/
def newComponentRegions (spec : Option RegionSpec) (P : Params) (inp : Input) (cg : Graph) :
    Except LayoutError (Option ComponentRegions) :=
  match spec with
  | none => pure none
  | some spec => do
    if spec.sets.isEmpty then pure none
    else
      let clusters := clusterRows inp spec cg
      let clusterOfId (id : String) : Option Nat := clusters.findIdx? fun c => c.id == id
      let parents := clusters.map fun c =>
        match boxParent inp c.decl with
        | "" => -1
        | pid =>
          match clusterOfId pid with
          | some k => (k : Int)
          | none => -1
      let sets ← spec.sets.filterMapM fun s =>
        match clusterOfId s.1 with
        | none => pure none
        | some parent => do
          let regions ← s.2.mapM fun r =>
            match clusterOfId r with
            | some k => pure k
            | none => throw .domain
          pure (some ({ parent := parent, regions := regions } : LocalRegionSet))
      if sets.isEmpty then pure none
      else pure (some { clusters := clusters, parents := parents, sets := sets, lineH := P.lineH })

def parentGroup (rm : ComponentRegions) (g : Nat) : Nat :=
  let parent := rm.parents.getD g (-1)
  if 0 ≤ parent then parent.toNat else rm.clusters.length

/-! ### Region ranking -/

/-- Every region cluster's border nodes represent their set's first region, Go's
`representatives` assignment. -/
def representatives (n : Nat) (clusters : List RegionCluster) (sets : List LocalRegionSet) :
    List Nat :=
  sets.foldl (fun reps s =>
    let first := (s.regions.head?).getD 0
    match clusters[first]? with
    | none => reps
    | some lead =>
      s.regions.foldl (fun reps r =>
        match clusters[r]? with
        | none => reps
        | some c => setAt (setAt reps c.top lead.top) c.bottom lead.bottom) reps)
    (List.range n)

/-- Reachability over an adjacency that only grows, as Go's `reachability.path`. -/
def reaches (out : List (List Nat)) : Nat → Nat → Nat → List Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, origin, target, seen =>
    origin == target || (out.getD origin []).any fun w =>
      !seen.contains w && reaches out fuel w target (w :: seen)

def insertCond (out : List (List Nat)) (a b : Nat) : List (List Nat) :=
  setAt out a (out.getD a [] ++ [b])

structure CondEdge where
  tail : Nat
  head : Nat
  decl : Nat
  minLen : Int
  synthetic : Bool
  index : Nat
deriving Repr

/-- The ranking edges of a component graph: the non-loop semantic edges followed by the
compound constraints, exactly as `Compound.rankingGraph` orders them. -/
def regionRankingEdges (cg : Graph) : List Edge :=
  (cg.edges.filter fun edge => edge.tail != edge.head) ++
    (Compound.constraints cg).zipIdx.map fun q =>
      { q.1 with decl := cg.edges.length + q.2 }

/-- Go's `rankEquivalent` with `orientRankEdges`: collapse each set onto its first region,
orient the semantic edges against the constraint order, rank the condensed graph and expand the
ranks; the returned graph carries the final edge orientations. -/
def rankEquivalentR (rm : ComponentRegions) (cg : Graph) :
    Except LayoutError (List Int × Graph × Bool) := do
  let n := cg.nodes.length
  let reps := representatives n rm.clusters rm.sets
  if !(List.range n).all fun i => reps.getD (reps.getD i i) (reps.getD i i) == reps.getD i i then
    throw .domain
  let kept := (List.range n).filter fun i => reps.getD i i == i
  let remap (i : Nat) : Nat := kept.idxOf (reps.getD i i)
  let combined := regionRankingEdges cg
  let origCount := (cg.edges.filter fun e => e.tail != e.head).length
  let conds : List CondEdge ← combined.zipIdx.mapM fun q => do
    let t := remap q.1.tail
    let h := remap q.1.head
    if t == h then throw .domain
    else pure (CondEdge.mk t h q.1.decl q.1.minLen (origCount ≤ q.2) q.2)
  let out1 ← conds.foldlM (fun out ce =>
    if !ce.synthetic then pure out
    else if reaches out (kept.length + 1) ce.head ce.tail [] then throw .domain
    else pure (insertCond out ce.tail ce.head)) (List.replicate kept.length [])
  let flagsAndOut ← conds.foldlM (fun acc ce =>
    if ce.synthetic then pure (setAt acc.1 ce.index false, acc.2)
    else
      let flag0 := (combined.getD ce.index default).reversed
      if reaches acc.2 (kept.length + 1) ce.head ce.tail [] then
        pure (setAt acc.1 ce.index !flag0, insertCond acc.2 ce.head ce.tail)
      else
        pure (setAt acc.1 ce.index flag0, insertCond acc.2 ce.tail ce.head))
    (List.replicate combined.length false, out1)
  let flags := flagsAndOut.1
  let rankEdges := conds.map fun ce =>
    if ce.synthetic then Edge.mk ce.tail ce.head ce.minLen ce.decl false
    else
      let f := flags.getD ce.index false
      let flag0 := (combined.getD ce.index default).reversed
      if f != flag0 then Edge.mk ce.head ce.tail ce.minLen ce.decl f
      else Edge.mk ce.tail ce.head ce.minLen ce.decl f
  let ranked ← rankWithBudget
    { nodes := kept.map fun i => cg.nodes.getD i default, edges := rankEdges, slot := cg.slot }
  let ranks := (List.range n).map fun i => ranked.ranks.getD (remap i) 0
  let combinedIndex (i : Nat) : Nat :=
    ((cg.edges.take i).filter fun e => e.tail != e.head).length
  let edges := cg.edges.zipIdx.map fun q =>
    if q.1.tail == q.1.head then q.1
    else
      let f := flags.getD (combinedIndex q.2) false
      if f == q.1.reversed then q.1 else q.1.reverse
  pure (ranks, { cg with edges := edges }, ranked.budgetExhausted)

/-! ### Region constraints (Go's `solveRegions`) -/

structure RankSpan where
  first : Int
  last : Int
deriving DecidableEq, Repr

structure OptionalSpan where
  span : RankSpan
  ok : Bool
deriving DecidableEq, Repr

structure RegionReservation where
  group : Nat
  left : Int
  right : Int
  span : RankSpan
deriving Repr

structure FrameMinima where
  border : Int
  padding : Int
  title : Int
deriving Repr

structure RegionBand where
  group : Nat
  left : Int
  right : Int
  span : RankSpan
deriving Repr

structure RegionConstraints where
  widths : List Int
  spans : List OptionalSpan
  bands : List RegionBand
  origins : List Int
deriving Repr

def mergeSpans (a b : OptionalSpan) : OptionalSpan :=
  if a.ok && b.ok then
    ⟨⟨min a.span.first b.span.first, max a.span.last b.span.last⟩, true⟩
  else if a.ok then a else b

/-- Go's `childForest`: children lists by parent plus the roots, in group order. -/
def childForest (parents : List Int) :
    Except LayoutError (List (List Nat) × List Nat) :=
  let n := parents.length
  (List.range n).zipIdx.foldlM (fun acc q => do
    let parent := parents.getD q.2 0
    if parent < 0 then pure (acc.1, acc.2 ++ [q.2])
    else if n ≤ parent ∨ parent == q.2 then throw .domain
    else
      pure (setAt acc.1 parent.toNat (acc.1.getD parent.toNat [] ++ [q.2]), acc.2))
    (List.replicate n [], [])

/-- Go's `groupPreorder`: pop the stack top, then push the children in list order, so later
children and later roots are visited first. -/
def groupPreorderGo (children : List (List Nat)) : Nat → List Nat → List Nat →
    Except LayoutError (List Nat)
  | 0, _, order => if order.length == children.length then pure order else throw .domain
  | fuel + 1, stack, order =>
    match stack.getLast? with
    | none => if order.length == children.length then pure order else throw .domain
    | some g =>
      groupPreorderGo children fuel (stack.dropLast ++ children.getD g []) (order ++ [g])

/-- Go's `indexRegionSets`: one set per parent, every region owned once and parented by the
set's parent. -/
def indexRegionSets (parents : List Int) (sets : List LocalRegionSet) :
    Except LayoutError (List Int × Nat) := do
  let n := parents.length
  let out ← sets.zipIdx.foldlM (fun acc q => do
    let s := q.1
    if n ≤ s.parent ∨ s.regions.isEmpty ∨ 0 ≤ acc.1.getD s.parent (-1) then throw .domain
    else
      let byParent : List Int := setAt acc.1 s.parent (q.2 : Int)
      let owner ← s.regions.foldlM (fun owner r => do
        if n ≤ r ∨ parents.getD r 0 != s.parent ∨ 0 ≤ owner.getD r (-1) then throw .domain
        else pure (setAt owner r (q.2 : Int))) acc.2.1
      pure (byParent, owner, acc.2.2 + s.regions.length))
    (List.replicate n (-1), (List.replicate n (-1), 0))
  pure (out.1, out.2.2)

structure RegionWorkbook where
  children : List (List Nat)
  order : List Nat
  byParent : List Int
  bandCount : Nat
  inset : Int
  widths : List Int
  spans : List OptionalSpan
  lefts : List Int
  rights : List Int
  reserved : List Bool
  origins : List Int
  offsets : List Int
deriving Repr

def newRegionWorkbook (n : Nat) (children : List (List Nat)) (order : List Nat)
    (byParent : List Int) (bandCount : Nat) (inset minimum : Int) : RegionWorkbook :=
  { children := children, order := order, byParent := byParent, bandCount := bandCount,
    inset := inset, widths := List.replicate n minimum,
    spans := List.replicate n ⟨⟨0, 0⟩, false⟩,
    lefts := List.replicate n 2147483647, rights := List.replicate n (-2147483648),
    reserved := List.replicate n false, origins := List.replicate n inset,
    offsets := List.replicate n 0 }

def foldReservations (book : RegionWorkbook) (reservations : List RegionReservation) :
    Except LayoutError RegionWorkbook :=
  reservations.foldlM (fun book r => do
    if r.group ≥ book.widths.length ∨ r.left > r.right ∨ r.span.first < 0 ∨
        r.span.first > r.span.last then throw .domain
    else
      pure { book with
        lefts := setAt book.lefts r.group (min (book.lefts.getD r.group 0) r.left)
        rights := setAt book.rights r.group (max (book.rights.getD r.group 0) r.right)
        reserved := setAt book.reserved r.group true
        spans := setAt book.spans r.group
          (mergeSpans (book.spans.getD r.group ⟨⟨0, 0⟩, false⟩) ⟨r.span, true⟩) }) book

def absorbFootprint (g : Nat) (book : RegionWorkbook) : Except LayoutError RegionWorkbook :=
  if !book.reserved.getD g false then pure book
  else
    let width := book.rights.getD g 0 - book.lefts.getD g 0
    let width := width + 2 * book.inset
    pure { book with
      widths := setAt book.widths g (max (book.widths.getD g 0) width)
      origins := setAt book.origins g (book.inset - book.lefts.getD g 0) }

def absorbChildren (g : Nat) (book : RegionWorkbook) : Except LayoutError RegionWorkbook := do
  let pair ← (book.children.getD g []).foldlM (fun acc child => do
    if child ≥ book.widths.length then throw .domain
    else
      let span := mergeSpans (acc.1.getD g ⟨⟨0, 0⟩, false⟩) (acc.1.getD child ⟨⟨0, 0⟩, false⟩)
      let width := max (acc.2.getD g 0) (acc.2.getD child 0 + 2 * book.inset)
      pure (setAt acc.1 g span, setAt acc.2 g width))
    (book.spans, book.widths)
  pure { book with spans := pair.1, widths := pair.2 }

def layOutRegions (sets : List LocalRegionSet) (g : Nat) (book : RegionWorkbook) :
    Except LayoutError RegionWorkbook := do
  let index := book.byParent.getD g (-1)
  if index < 0 then pure book
  else
    let regions := (sets.getD index.toNat default).regions
    let pair ← regions.foldlM (fun acc r =>
      pure (setAt acc.1 r acc.2, acc.2 + book.widths.getD r 0))
      (book.offsets, book.inset)
    pure { book with
      offsets := pair.1
      widths := setAt book.widths g (max (book.widths.getD g 0) (pair.2 + book.inset)) }

def resolveNestedExtents (sets : List LocalRegionSet) (book : RegionWorkbook) :
    Except LayoutError RegionWorkbook :=
  book.order.reverse.foldlM (fun book g => do
    let book ← absorbFootprint g book
    let book ← absorbChildren g book
    layOutRegions sets g book) book

def shareCommonSpans (sets : List LocalRegionSet) (book : RegionWorkbook) : RegionWorkbook :=
  book.order.foldl (fun book g =>
    let index := book.byParent.getD g (-1)
    if index < 0 then book
    else
      let regions := (sets.getD index.toNat default).regions
      let span := regions.foldl (fun acc r =>
        mergeSpans acc (book.spans.getD r ⟨⟨0, 0⟩, false⟩)) ⟨⟨0, 0⟩, false⟩
      let span := if !span.ok then book.spans.getD g ⟨⟨0, 0⟩, false⟩ else span
      let span := { span with ok := true }
      { book with
        spans := regions.foldl (fun sp r => setAt sp r span) book.spans }) book

def regionBands (sets : List LocalRegionSet) (book : RegionWorkbook) :
    Except LayoutError (List RegionBand) :=
  sets.foldlM (fun out s =>
    s.regions.foldlM (fun out r => do
      let span := book.spans.getD r ⟨⟨0, 0⟩, false⟩
      if !span.ok then throw .domain
      else
        pure (out ++ [RegionBand.mk r (book.offsets.getD r 0)
          (book.offsets.getD r 0 + book.widths.getD r 0) span.span]))
      out) []

def frameMinimum (m : FrameMinima) : Except LayoutError (Int × Int) := do
  if m.border < 0 ∨ m.padding < 0 ∨ m.title < 0 then throw .domain
  let inset := m.border + m.padding
  if I32_MAX < inset then throw .overflow
  let minimum := 2 * inset + m.title
  if I32_MAX < minimum then throw .overflow
  pure (inset, max minimum 1)

def solveRegions (parents : List Int) (sets : List LocalRegionSet)
    (reservations : List RegionReservation) (minima : FrameMinima) :
    Except LayoutError RegionConstraints := do
  let (inset, minimum) ← frameMinimum minima
  let (children, roots) ← childForest parents
  let order ← groupPreorderGo children (children.length + 1) roots []
  let (byParent, bandCount) ← indexRegionSets parents sets
  let book0 := newRegionWorkbook parents.length children order byParent bandCount inset minimum
  let book ← foldReservations book0 reservations
  let book ← resolveNestedExtents sets book
  let book := shareCommonSpans sets book
  let bands ← regionBands sets book
  pure { widths := book.widths, spans := book.spans, bands := bands, origins := book.origins }

/-! ### The constrain phase -/

def clusterOfDecl (rm : ComponentRegions) (decl : Nat) : Option Nat :=
  rm.clusters.findIdx? fun c => c.decl == decl

/-- The innermost cluster of a proper node: the last entry of its cluster path. -/
def parentClusterOf (rm : ComponentRegions) (p : Proper) (v : Nat) :
    Except LayoutError (Option Nat) :=
  match (p.nodes.getD v default).node.clusterPath.getLast? with
  | none => pure none
  | some decl =>
    match clusterOfDecl rm decl with
    | some k => pure (some k)
    | none => throw .domain

/-- Go's `rowReservations`: the width every row of every cluster must hold. -/
def rowReservationsR (rm : ComponentRegions) (P : Params) (p : Proper) :
    Except LayoutError (List RegionReservation) := do
  let entries ← p.nodes.zipIdx.foldlM (fun acc q => do
    let group ← parentClusterOf rm p q.2
    match group with
    | none => pure acc
    | some g =>
      let width := q.1.node.w + P.nodeGap
      if I32_MAX < width then throw .overflow
      else
        let rank := rk p.rank q.2
        let hit := acc.any fun e => e.1 == g && e.2.1 == rank
        if hit then
          pure (acc.map fun e =>
            if e.1 == g && e.2.1 == rank then (e.1, e.2.1, e.2.2 + width) else e)
        else pure (acc ++ [(g, rank, width)])) []
  let sorted := entries.mergeSort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  pure (sorted.map fun e =>
    RegionReservation.mk e.1 0 e.2.2 ⟨e.2.1, e.2.1⟩)

/-- Go's `componentRegions.constrain`: the frame minimum of every cluster and row. -/
def constrainR (rm : ComponentRegions) (P : Params) (p : Proper) :
    Except LayoutError RegionConstraints := do
  let clusterReservations := rm.clusters.zipIdx.map fun q =>
    RegionReservation.mk q.2 0 q.1.titleW ⟨rk p.rank q.1.top, rk p.rank q.1.bottom⟩
  let rows ← rowReservationsR rm P p
  solveRegions rm.parents rm.sets (clusterReservations ++ rows)
    ⟨P.clusterBorderW, P.clusterPad, rm.lineH⟩

end RegionImpl
end Layered
end Elegant
