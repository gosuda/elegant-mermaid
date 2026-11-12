import ElegantGeometry.Basic
import Elegant.Gen.Layoutconst
import Elegant.Layered.Cycles
import Elegant.Layered.Rank
import Elegant.Layered.Normalize

set_option autoImplicit false

/-! Coordinate phases of the layered family (spec/layout/layered.md, steps 7 and 8).
`crossCoords` runs the four Brandes-Köpf passes (alignment C1, initial values C2, block placement C3
with an explicit stack and fuel `2n`, class offsets C4, mirrored passes C5), shifts each pass to
minimum 0, aligns the passes to the narrowest one and returns the balanced coordinate
`floor_div(second smallest + third smallest, 2)`. `rankCoords` places the rank bands. Both compute
the same integers as `internal/layout/layered/coords.go`.

Every pass is checked against the separation rule `coordSep` before it is used (`checkedPass`); a
pass that fails the check is `LayoutError.domain`. `coords_separated` is the soundness of that check.
The lemmas that make the check succeed on every accepted input (the block graph of a vertical
alignment is acyclic, the class dependencies of step C4 point to a smaller rank) are not proved here.
`balance_separated`, `coords_order_preserved`, `rankAxis_bands_disjoint` and `rankAxis_node_in_band`
are proved from the definitions. -/

namespace Elegant
namespace Layered
namespace CoordsImpl

def I64_MIN : Int := -9223372036854775808
def I64_MAX : Int := 9223372036854775807

def chk (o : Bool) (v : Int) : Bool := o || decide (v < I64_MIN) || decide (I64_MAX < v)

opaque defaultNodeGap : Option Int :=
  match layoutconst.find? (fun c => c.name == "vector.node_gap") with
  | some c => some c.value
  | none => none

opaque defaultRankGap : Option Int :=
  match layoutconst.find? (fun c => c.name == "vector.rank_gap") with
  | some c => some c.value
  | none => none

def nodeW (p : Proper) (v : Nat) : Int :=
  match p.nodes[v]? with
  | some n => n.node.w
  | none => 0

def nodeH (p : Proper) (v : Nat) : Int :=
  match p.nodes[v]? with
  | some n => n.node.h
  | none => 0

def coordSep (gap : Int) (p : Proper) (a b : Nat) : Int :=
  Int.fdiv (nodeW p a) 2 + Int.fdiv (nodeW p b) 2 + gap

def sizesNonneg (p : Proper) : Bool :=
  p.nodes.all fun n => decide (0 ≤ n.node.w ∧ 0 ≤ n.node.h)

def sizesFit (p : Proper) : Bool :=
  p.nodes.all fun n => decide (n.node.w ≤ I32_MAX ∧ n.node.h ≤ I32_MAX)

def checkSizes (p : Proper) : Except LayoutError Unit :=
  if I32_MAX < (p.nodes.length : Int) ∨ I32_MAX < (p.edges.length : Int) then .error .overflow
  else if !sizesNonneg p then .error .domain
  else if !sizesFit p then .error .overflow
  else .ok ()

def layersInRange (p : Proper) (layers : List (List Nat)) : Bool :=
  layers.all fun l => l.all fun v => decide (v < p.nodes.length)

def layerPositions (p : Proper) (layers : List (List Nat)) : Except LayoutError (Array Nat) := do
  let n := p.nodes.length
  let mut pos : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := Array.replicate n false
  let mut r : Nat := 0
  for layer in layers do
    let mut j : Nat := 0
    for v in layer do
      if n ≤ v ∨ seen[v]! ∨ rk p.rank v ≠ (r : Int) then throw .domain
      seen := seen.set! v true
      pos := pos.set! v j
      j := j + 1
    r := r + 1
  if seen.any (fun b => !b) then throw .domain
  return pos

def checkEdges (p : Proper) : Except LayoutError Unit := do
  let n := p.nodes.length
  for e in p.edges do
    if n ≤ e.tail ∨ n ≤ e.head then throw .domain
    if rk p.rank e.head ≠ rk p.rank e.tail + 1 then throw .domain

def checkLayers (p : Proper) (layers : List (List Nat)) : Except LayoutError (Array Nat) :=
  if p.rank.length ≠ p.nodes.length then .error .domain
  else
    match checkSizes p with
    | .error e => .error e
    | .ok _ =>
      if !layersInRange p layers then .error .domain
      else
        match layerPositions p layers with
        | .error e => .error e
        | .ok pos =>
          match checkEdges p with
          | .error e => .error e
          | .ok _ => .ok pos

def isDummy (p : Proper) (v : Nat) : Bool :=
  match p.nodes[v]? with
  | some n => n.dummy
  | none => false

def crossesInner (p : Proper) (pos : Array Nat) (e : ProperEdge) : Bool :=
  p.edges.any fun f =>
    rk p.rank e.tail == rk p.rank f.tail && isDummy p f.tail && isDummy p f.head &&
      decide (((pos[e.tail]! : Int) - pos[f.tail]!) * ((pos[e.head]! : Int) - pos[f.head]!) < 0)

def typeOneConflicts (p : Proper) (pos : Array Nat) : Array Bool :=
  (p.edges.map fun e =>
    !(isDummy p e.tail && isDummy p e.head) && crossesInner p pos e).toArray

structure Ctx where
  edges : Array ProperEdge
  marked : Array Bool
  widths : Array Int
  layersK : Array (Array Nat)
  rankK : Array Nat
  posK : Array Nat
  root : Array Nat
  align : Array Nat
  gap : Int

def Ctx.sep (c : Ctx) (a b : Nat) : Int :=
  Int.fdiv c.widths[a]! 2 + Int.fdiv c.widths[b]! 2 + c.gap

def passLayers (layers : Array (Array Nat)) (k : Nat) : Array (Array Nat) :=
  let m := layers.size
  (Array.range m).map fun i =>
    let l := layers[if 2 ≤ k then m - 1 - i else i]!
    if k % 2 = 1 then l.reverse else l

def rankAndPos (n : Nat) (ls : Array (Array Nat)) : Array Nat × Array Nat := Id.run do
  let mut rank : Array Nat := Array.replicate n 0
  let mut pos : Array Nat := Array.replicate n 0
  for i in [0:ls.size] do
    let l := ls[i]!
    for j in [0:l.size] do
      rank := rank.set! l[j]! i
      pos := pos.set! l[j]! j
  return (rank, pos)

def otherEnd (e : ProperEdge) (v : Nat) : Nat :=
  if e.tail == v then e.head else e.tail

def upperEdges (edges : Array ProperEdge) (rank pos : Array Nat) (v : Nat) : List Nat :=
  let cands := (List.range edges.size).filter fun i =>
    (edges[i]!.head == v && rank[edges[i]!.tail]! < rank[v]!) ||
      (edges[i]!.tail == v && rank[edges[i]!.head]! < rank[v]!)
  let keyed := cands.map fun i => (pos[otherEnd edges[i]! v]!, i)
  (keyed.mergeSort fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))).map (·.2)

def alignment (n : Nat) (edges : Array ProperEdge) (marked : Array Bool) (ls : Array (Array Nat))
    (rank pos : Array Nat) : Array Nat × Array Nat := Id.run do
  let mut root : Array Nat := Array.range n
  let mut align : Array Nat := Array.range n
  for layer in ls do
    let mut last : Int := -1
    for v in layer do
      let es := upperEdges edges rank pos v
      if es.isEmpty then continue
      for kk in [(es.length - 1) / 2, es.length / 2] do
        let e := es[kk]!
        let w := otherEnd edges[e]! v
        if align[v]! == v && !marked[e]! && decide (last < (pos[w]! : Int)) then
          align := align.set! w v
          align := align.set! v root[w]!
          root := root.set! v root[w]!
          last := pos[w]!
  return (root, align)

structure PState where
  x : Array Int
  sink : Array Nat
  isSet : Array Bool
  ovf : Bool
  fuel : Nat

def placeAfter (c : Ctx) (st : PState) (v w pr : Nat) : PState :=
  let u := c.root[pr]!
  let sink := if st.sink[v]! == v then st.sink.set! v st.sink[u]! else st.sink
  if sink[v]! == sink[u]! then
    let val := st.x[u]! + c.sep pr w
    { st with sink := sink, x := st.x.set! v (max st.x[v]! val), ovf := chk st.ovf val }
  else { st with sink := sink }

def finishBlock (c : Ctx) (st : PState) (v : Nat) : PState := Id.run do
  let mut st := st
  let mut m := c.align[v]!
  for _ in [0:c.align.size] do
    if m == v then break
    st := { st with x := st.x.set! m st.x[v]!, sink := st.sink.set! m st.sink[v]!,
                    isSet := st.isSet.set! m true }
    m := c.align[m]!
  return st

def advance (c : Ctx) (st : PState) (v w : Nat) (rest : List (Nat × Nat)) :
    List (Nat × Nat) × PState :=
  let nxt := c.align[w]!
  if nxt == v then (rest, finishBlock c st v) else ((v, nxt) :: rest, st)

def placeStep (c : Ctx) (st : PState) : List (Nat × Nat) → List (Nat × Nat) × PState
  | [] => ([], st)
  | (v, w) :: rest =>
    if c.posK[w]! == 0 then advance c st v w rest
    else
      let pr := c.layersK[c.rankK[w]!]![c.posK[w]! - 1]!
      let u := c.root[pr]!
      if st.isSet[u]! then advance c (placeAfter c st v w pr) v w rest
      else ((u, u) :: (v, w) :: rest, { st with isSet := st.isSet.set! u true })

def placeRoot (c : Ctx) (st0 : PState) (r : Nat) : Except LayoutError PState := do
  let mut st := { st0 with isSet := st0.isSet.set! r true }
  let mut stack : List (Nat × Nat) := [(r, r)]
  let mut used : Nat := 0
  for _ in [0:st0.fuel] do
    if stack.isEmpty then break
    let (stack', st') := placeStep c st stack
    stack := stack'
    st := st'
    used := used + 1
  if !stack.isEmpty then throw .domain
  return { st with fuel := st0.fuel - used }

def placeAll (c : Ctx) (st0 : PState) : Except LayoutError PState := do
  let mut st := st0
  for layer in c.layersK do
    for v in layer do
      if c.root[v]! != v || st.isSet[v]! then continue
      st ← placeRoot c st v
  return st

def offsets (c : Ctx) (st : PState) : Array Int × Bool := Id.run do
  let m := c.layersK.size
  let n := st.x.size
  let mut pairs : Array (Array (Nat × Nat)) := Array.replicate m #[]
  for layer in c.layersK do
    for i in [1:layer.size] do
      let a := layer[i - 1]!
      let b := layer[i]!
      if st.sink[a]! != st.sink[b]! then
        pairs := pairs.modify c.rankK[st.sink[b]!]! (·.push (a, b))
  let mut shift : Array Int := Array.replicate n 0
  let mut shifted : Array Bool := Array.replicate n false
  let mut ovf := st.ovf
  for i in [0:m] do
    let layer := c.layersK[i]!
    if layer.isEmpty then continue
    let s := layer[0]!
    if st.sink[s]! == s && !shifted[s]! then shifted := shifted.set! s true
    for (a, b) in pairs[i]! do
      let sa := st.sink[a]!
      let sb := st.sink[b]!
      let t1 := shift[sb]! + st.x[b]!
      let t2 := t1 - st.x[a]!
      let d := t2 - c.sep a b
      ovf := chk (chk (chk ovf t1) t2) d
      if !shifted[sa]! || d < shift[sa]! then
        shift := shift.set! sa d
        shifted := shifted.set! sa true
  let mut x := st.x
  for v in [0:n] do
    let val := st.x[v]! + shift[st.sink[v]!]!
    ovf := chk ovf val
    x := x.set! v val
  return (x, ovf)

def runPass (c : Ctx) (odd : Bool) (n : Nat) : Except LayoutError (Array Int) := do
  let st0 : PState :=
    { x := Array.replicate n 0, sink := Array.range n, isSet := Array.replicate n false,
      ovf := false, fuel := 2 * n }
  let st ← placeAll c st0
  let (x0, ovf0) := offsets c st
  let mut x := x0
  let mut ovf := ovf0
  if odd then
    for i in [0:n] do
      let v := 0 - x[i]!
      ovf := chk ovf v
      x := x.set! i v
  if 0 < n then
    let lo := x.foldl min x[0]!
    for i in [0:n] do
      let v := x[i]! - lo
      ovf := chk ovf v
      x := x.set! i v
  if ovf then throw .overflow
  return x

def passSeparated (gap : Int) (p : Proper) (layers : List (List Nat)) (x : Array Int) : Bool :=
  layers.all fun layer =>
    (layer.zip layer.tail).all fun ab =>
      decide (coordSep gap p ab.1 ab.2 ≤ x[ab.2]! - x[ab.1]!)

def rawPass (gap : Int) (p : Proper) (layers : List (List Nat)) (marked : Array Bool) (k : Nat) :
    Except LayoutError (Array Int) :=
  let n := p.nodes.length
  let ls := passLayers (layers.map List.toArray).toArray k
  let (rank, pos) := rankAndPos n ls
  let edges := p.edges.toArray
  let (root, align) := alignment n edges marked ls rank pos
  let c : Ctx :=
    { edges := edges, marked := marked, widths := (List.range n).toArray.map (nodeW p),
      layersK := ls, rankK := rank, posK := pos, root := root, align := align, gap := gap }
  runPass c (k % 2 == 1) n

def checkedPass (gap : Int) (p : Proper) (layers : List (List Nat)) (marked : Array Bool)
    (k : Nat) : Except LayoutError (Array Int) :=
  match rawPass gap p layers marked k with
  | .error e => .error e
  | .ok x => if passSeparated gap p layers x then .ok x else .error .domain

def sort4 (a b c d : Int) : Int × Int × Int × Int :=
  (min (min a b) (min c d),
    min (min (max a b) (max c d)) (max (min a b) (min c d)),
    max (min (max a b) (max c d)) (max (min a b) (min c d)),
    max (max a b) (max c d))

def bal4 (a b c d : Int) : Int :=
  let s := sort4 a b c d
  Int.fdiv (s.2.1 + s.2.2.1) 2

def arrMax (x : Array Int) : Int := x.foldl max (x[0]!)

def bestPass (w0 w1 w2 w3 : Int) : Int :=
  let b1 := if w1 < w0 then w1 else w0
  let b2 := if w2 < b1 then w2 else b1
  if w3 < b2 then w3 else b2

structure Offsets where
  o0 : Int
  o1 : Int
  o2 : Int
  o3 : Int

def balanceOffsets (x0 x1 x2 x3 : Array Int) : Offsets :=
  let best := bestPass (arrMax x0) (arrMax x1) (arrMax x2) (arrMax x3)
  let d1 := best - arrMax x1
  let d3 := best - arrMax x3
  let low := min 0 (min d1 d3)
  { o0 := 0 - low, o1 := d1 - low, o2 := 0 - low, o3 := d3 - low }

def balanceValues (n : Nat) (x0 x1 x2 x3 : Array Int) : List Int :=
  let o := balanceOffsets x0 x1 x2 x3
  (List.range n).map fun i => bal4 (x0[i]! + o.o0) (x1[i]! + o.o1) (x2[i]! + o.o2) (x3[i]! + o.o3)

def balanceOverflow (n : Nat) (x0 x1 x2 x3 : Array Int) : Bool := Id.run do
  let best := bestPass (arrMax x0) (arrMax x1) (arrMax x2) (arrMax x3)
  let d1 := best - arrMax x1
  let d3 := best - arrMax x3
  let low := min 0 (min d1 d3)
  let mut ovf := chk (chk false d1) d3
  for i in [0:n] do
    let a := x0[i]!
    let b := x1[i]! + d1
    let c := x2[i]!
    let d := x3[i]! + d3
    ovf := chk (chk ovf b) d
    let s := sort4 (a - low) (b - low) (c - low) (d - low)
    ovf := chk (chk (chk (chk (chk ovf (a - low)) (b - low)) (c - low)) (d - low)) (s.2.1 + s.2.2.1)
  return ovf

def balance (n : Nat) (x0 x1 x2 x3 : Array Int) : Except LayoutError (List Int) :=
  if balanceOverflow n x0 x1 x2 x3 then .error .overflow
  else
    let out := balanceValues n x0 x1 x2 x3
    if out.any (fun v => decide (I32_MAX < v)) then .error .overflow else .ok out

def crossPasses (gap : Int) (p : Proper) (layers : List (List Nat)) :
    Except LayoutError (Array Int × Array Int × Array Int × Array Int) :=
  match checkLayers p layers with
  | .error e => .error e
  | .ok pos =>
    if gap < 1 then .error .domain
    else
      let marked := typeOneConflicts p pos
      match checkedPass gap p layers marked 0 with
      | .error e => .error e
      | .ok x0 =>
        match checkedPass gap p layers marked 1 with
        | .error e => .error e
        | .ok x1 =>
          match checkedPass gap p layers marked 2 with
          | .error e => .error e
          | .ok x2 =>
            match checkedPass gap p layers marked 3 with
            | .error e => .error e
            | .ok x3 => .ok (x0, x1, x2, x3)

def crossCoordsWith (gap : Int) (p : Proper) (layers : List (List Nat)) :
    Except LayoutError (List Int) :=
  if p.nodes.length = 0 then
    match checkLayers p layers with
    | .error e => .error e
    | .ok _ => if gap < 1 then .error .domain else .ok []
  else
    match crossPasses gap p layers with
    | .error e => .error e
    | .ok (x0, x1, x2, x3) => balance p.nodes.length x0 x1 x2 x3

def crossCoords (p : Proper) (layers : List (List Nat)) : Except LayoutError (List Int) :=
  match defaultNodeGap, defaultRankGap, NormalizeImpl.defaultSlot with
  | some g, some r, some s =>
    if 1 ≤ r ∧ 1 ≤ s then crossCoordsWith g p layers else .error .domain
  | _, _, _ => .error .domain

def layerHeight (p : Proper) (layer : List Nat) : Int :=
  layer.foldl (fun m v => max m (nodeH p v)) 0

def topsFrom (rankGap slot : Int) : Int → List Int → List Int → List Int
  | t, [_], [] => [t]
  | t, h :: hs, s :: ss => t :: topsFrom rankGap slot (t + h + rankGap + slot * s) hs ss
  | _, _, _ => []

def rankCoordsWith (rankGap slot : Int) (p : Proper) (layers : List (List Nat)) (slots : List Int) :
    Except LayoutError (List Int × List Int) :=
  match checkLayers p layers with
  | .error e => .error e
  | .ok _ =>
    if rankGap < 1 ∨ slot < 1 then .error .domain
    else if slots.length ≠ layers.length - 1 then .error .domain
    else if slots.any (fun s => decide (s < 0)) then .error .domain
    else
      let heights := layers.map (layerHeight p)
      let tops := topsFrom rankGap slot 0 heights slots
      if tops.any (fun t => decide (I32_MAX < t)) then .error .overflow
      else
        let y := (List.range p.nodes.length).map fun v =>
          tops.getD (rk p.rank v).toNat 0 +
            Int.fdiv (heights.getD (rk p.rank v).toNat 0 - nodeH p v) 2
        if y.any (fun t => decide (I32_MAX < t)) then .error .overflow else .ok (y, tops)

def rankCoords (p : Proper) (layers : List (List Nat)) (slots : List Int) :
    Except LayoutError (List Int × List Int) :=
  match defaultNodeGap, defaultRankGap, NormalizeImpl.defaultSlot with
  | some g, some r, some s =>
    if 1 ≤ g then rankCoordsWith r s p layers slots else .error .domain
  | _, _, _ => .error .domain


theorem mem_zip_tail {α : Type} : ∀ (l : List α) (i : Nat) (a b : α),
    l[i]? = some a → l[i + 1]? = some b → (a, b) ∈ l.zip l.tail := by
  intro l
  induction l with
  | nil => intro i a b h; simp at h
  | cons c rest ih =>
    intro i a b ha hb
    cases rest with
    | nil => simp at hb
    | cons d rest' =>
      cases i with
      | zero =>
        simp at ha hb
        subst ha
        subst hb
        simp [List.tail, List.zip_cons_cons]
      | succ i =>
        have := ih i a b (by simpa using ha) (by simpa using hb)
        simp [List.tail, List.zip_cons_cons] at this ⊢
        exact Or.inr this

theorem passSeparated_spec {gap : Int} {p : Proper} {layers : List (List Nat)} {x : Array Int}
    (h : passSeparated gap p layers x = true) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      coordSep gap p a b ≤ x[b]! - x[a]! := by
  intro layer hl i a b ha hb
  unfold passSeparated at h
  rw [List.all_eq_true] at h
  have h1 := h layer hl
  rw [List.all_eq_true] at h1
  have h2 := h1 (a, b) (mem_zip_tail layer i a b ha hb)
  simpa using h2

theorem checkSizes_nonneg {p : Proper} (h : checkSizes p = .ok ()) : sizesNonneg p = true := by
  unfold checkSizes at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next _ h2 => simpa using h2

theorem checkLayers_spec {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    (h : checkLayers p layers = .ok pos) :
    layersInRange p layers = true ∧ sizesNonneg p = true := by
  unfold checkLayers at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next hs =>
      split at h
      · simp at h
      · next hr =>
        exact ⟨by simpa using hr, checkSizes_nonneg hs⟩

theorem checkedPass_spec {gap : Int} {p : Proper} {layers : List (List Nat)} {marked : Array Bool}
    {k : Nat} {x : Array Int} (h : checkedPass gap p layers marked k = .ok x) :
    passSeparated gap p layers x = true := by
  unfold checkedPass at h
  split at h
  · simp at h
  · next x' _ =>
    split at h
    · next hs =>
      simp only [Except.ok.injEq] at h
      subst h
      exact hs
    · simp at h

theorem crossPasses_spec {gap : Int} {p : Proper} {layers : List (List Nat)}
    {x0 x1 x2 x3 : Array Int} (h : crossPasses gap p layers = .ok (x0, x1, x2, x3)) :
    1 ≤ gap ∧ layersInRange p layers = true ∧ sizesNonneg p = true ∧
      passSeparated gap p layers x0 = true ∧ passSeparated gap p layers x1 = true ∧
      passSeparated gap p layers x2 = true ∧ passSeparated gap p layers x3 = true := by
  unfold crossPasses at h
  split at h
  · simp at h
  · next pos hpos =>
    split at h
    · simp at h
    · next hg =>
      dsimp only at h
      split at h
      · simp at h
      · next y0 h0 =>
        split at h
        · simp at h
        · next y1 h1 =>
          split at h
          · simp at h
          · next y2 h2 =>
            split at h
            · simp at h
            · next y3 h3 =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              have hc := checkLayers_spec hpos
              exact ⟨by omega, hc.1, hc.2, checkedPass_spec h0, checkedPass_spec h1,
                checkedPass_spec h2, checkedPass_spec h3⟩

theorem min_mono_add {s a b a' b' : Int} (h0 : a + s ≤ a') (h1 : b + s ≤ b') :
    min a b + s ≤ min a' b' := by omega

theorem max_mono_add {s a b a' b' : Int} (h0 : a + s ≤ a') (h1 : b + s ≤ b') :
    max a b + s ≤ max a' b' := by omega

theorem bal4_mono (s a b c d a' b' c' d' : Int) (h0 : a + s ≤ a') (h1 : b + s ≤ b')
    (h2 : c + s ≤ c') (h3 : d + s ≤ d') : bal4 a b c d + s ≤ bal4 a' b' c' d' := by
  have e5 := min_mono_add (max_mono_add h0 h1) (max_mono_add h2 h3)
  have e6 := max_mono_add (min_mono_add h0 h1) (min_mono_add h2 h3)
  have m2 := min_mono_add e5 e6
  have m3 := max_mono_add e5 e6
  unfold bal4 sort4
  dsimp only
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem balance_ok {n : Nat} {x0 x1 x2 x3 : Array Int} {xs : List Int}
    (h : balance n x0 x1 x2 x3 = .ok xs) : xs = balanceValues n x0 x1 x2 x3 := by
  unfold balance at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      exact h.symm

theorem balanceValues_getD (n : Nat) (x0 x1 x2 x3 : Array Int) {i : Nat} (hi : i < n) :
    (balanceValues n x0 x1 x2 x3).getD i 0 =
      bal4 (x0[i]! + (balanceOffsets x0 x1 x2 x3).o0) (x1[i]! + (balanceOffsets x0 x1 x2 x3).o1)
        (x2[i]! + (balanceOffsets x0 x1 x2 x3).o2) (x3[i]! + (balanceOffsets x0 x1 x2 x3).o3) := by
  unfold balanceValues
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]


theorem layers_mem_lt {p : Proper} {layers : List (List Nat)} (h : layersInRange p layers = true)
    {layer : List Nat} (hl : layer ∈ layers) {i a : Nat} (ha : layer[i]? = some a) :
    a < p.nodes.length := by
  unfold layersInRange at h
  rw [List.all_eq_true] at h
  have h1 := h layer hl
  rw [List.all_eq_true] at h1
  simpa using h1 a (List.mem_of_getElem? ha)

theorem nodeW_nonneg {p : Proper} (h : sizesNonneg p = true) (v : Nat) : 0 ≤ nodeW p v := by
  unfold nodeW
  split
  · next n hn =>
    have hm := List.mem_of_getElem? hn
    unfold sizesNonneg at h
    rw [List.all_eq_true] at h
    have := h n hm
    simp at this
    exact this.1
  · exact Int.le_refl 0

theorem nodeH_nonneg {p : Proper} (h : sizesNonneg p = true) (v : Nat) : 0 ≤ nodeH p v := by
  unfold nodeH
  split
  · next n hn =>
    have hm := List.mem_of_getElem? hn
    unfold sizesNonneg at h
    rw [List.all_eq_true] at h
    have := h n hm
    simp at this
    exact this.2
  · exact Int.le_refl 0

theorem coordSep_pos {gap : Int} {p : Proper} (hg : 1 ≤ gap) (hs : sizesNonneg p = true)
    (a b : Nat) : 1 ≤ coordSep gap p a b := by
  have ha := nodeW_nonneg hs a
  have hb := nodeW_nonneg hs b
  unfold coordSep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem crossCoordsWith_spec {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) :
    1 ≤ gap ∧ layersInRange p layers = true ∧ sizesNonneg p = true ∧
      ((p.nodes.length = 0 ∧ xs = []) ∨
        ∃ x0 x1 x2 x3, crossPasses gap p layers = .ok (x0, x1, x2, x3) ∧
          xs = balanceValues p.nodes.length x0 x1 x2 x3) := by
  unfold crossCoordsWith at h
  split at h
  · next h0 =>
    split at h
    · simp at h
    · next pos hpos =>
      split at h
      · simp at h
      · next hg =>
        simp only [Except.ok.injEq] at h
        have hc := checkLayers_spec hpos
        exact ⟨by omega, hc.1, hc.2, Or.inl ⟨h0, h.symm⟩⟩
  · next h0 =>
    split at h
    · simp at h
    · next x0 x1 x2 x3 hp =>
      have hs := crossPasses_spec hp
      exact ⟨hs.1, hs.2.1, hs.2.2.1, Or.inr ⟨x0, x1, x2, x3, hp, balance_ok h⟩⟩

theorem balance_separated {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      coordSep gap p a b ≤ xs.getD b 0 - xs.getD a 0 := by
  intro layer hl i a b ha hb
  obtain ⟨_, hr, _, hcase⟩ := crossCoordsWith_spec h
  have ha' := layers_mem_lt hr hl ha
  have hb' := layers_mem_lt hr hl hb
  rcases hcase with ⟨h0, _⟩ | ⟨x0, x1, x2, x3, hp, hx⟩
  · omega
  · obtain ⟨_, _, _, s0, s1, s2, s3⟩ := crossPasses_spec hp
    subst hx
    rw [balanceValues_getD _ _ _ _ _ ha', balanceValues_getD _ _ _ _ _ hb']
    have d0 := passSeparated_spec s0 layer hl i a b ha hb
    have d1 := passSeparated_spec s1 layer hl i a b ha hb
    have d2 := passSeparated_spec s2 layer hl i a b ha hb
    have d3 := passSeparated_spec s3 layer hl i a b ha hb
    have key := bal4_mono (coordSep gap p a b)
      (x0[a]! + (balanceOffsets x0 x1 x2 x3).o0) (x1[a]! + (balanceOffsets x0 x1 x2 x3).o1)
      (x2[a]! + (balanceOffsets x0 x1 x2 x3).o2) (x3[a]! + (balanceOffsets x0 x1 x2 x3).o3)
      (x0[b]! + (balanceOffsets x0 x1 x2 x3).o0) (x1[b]! + (balanceOffsets x0 x1 x2 x3).o1)
      (x2[b]! + (balanceOffsets x0 x1 x2 x3).o2) (x3[b]! + (balanceOffsets x0 x1 x2 x3).o3)
      (by omega) (by omega) (by omega) (by omega)
    omega

theorem coords_order_preserved {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      xs.getD a 0 ≤ xs.getD b 0 := by
  intro layer hl i a b ha hb
  have h1 := balance_separated h layer hl i a b ha hb
  obtain ⟨hg, _, hs, _⟩ := crossCoordsWith_spec h
  have h2 := coordSep_pos hg hs a b
  omega

theorem coords_separated {gap : Int} {p : Proper} {layers : List (List Nat)}
    {x0 x1 x2 x3 : Array Int} (h : crossPasses gap p layers = .ok (x0, x1, x2, x3)) :
    ∀ x ∈ [x0, x1, x2, x3], ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a →
      layer[i + 1]? = some b → coordSep gap p a b ≤ x[b]! - x[a]! := by
  obtain ⟨_, _, _, s0, s1, s2, s3⟩ := crossPasses_spec h
  intro x hx layer hl i a b ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact passSeparated_spec s0 layer hl i a b ha hb
  · exact passSeparated_spec s1 layer hl i a b ha hb
  · exact passSeparated_spec s2 layer hl i a b ha hb
  · exact passSeparated_spec s3 layer hl i a b ha hb


theorem foldl_max_ge_init (f : Nat → Int) :
    ∀ (l : List Nat) (acc : Int), acc ≤ l.foldl (fun m v => max m (f v)) acc := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons v vs ih =>
    intro acc
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem foldl_max_ge_mem (f : Nat → Int) :
    ∀ (l : List Nat) (acc : Int) (v : Nat), v ∈ l → f v ≤ l.foldl (fun m v => max m (f v)) acc := by
  intro l
  induction l with
  | nil => intro acc v hv; simp at hv
  | cons u us ih =>
    intro acc v hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Int.le_trans (Int.le_max_right _ _) (foldl_max_ge_init f us _)
    · exact ih _ v hv'

theorem layerHeight_nonneg (p : Proper) (l : List Nat) : 0 ≤ layerHeight p l :=
  foldl_max_ge_init (nodeH p) l 0

theorem layerHeight_ge {p : Proper} {l : List Nat} {v : Nat} (hv : v ∈ l) :
    nodeH p v ≤ layerHeight p l :=
  foldl_max_ge_mem (nodeH p) l 0 v hv

theorem topsFrom_length (rankGap slot : Int) :
    ∀ (hs ss : List Int) (t : Int), ss.length + 1 = hs.length →
      (topsFrom rankGap slot t hs ss).length = hs.length := by
  intro hs
  induction hs with
  | nil => intro ss t h; simp at h
  | cons h0 hs' ih =>
    intro ss t h
    cases ss with
    | nil =>
      cases hs' with
      | nil => simp [topsFrom]
      | cons _ _ => simp at h
    | cons s ss' =>
      simp only [topsFrom, List.length_cons]
      have := ih ss' (t + h0 + rankGap + slot * s) (by simpa using h)
      omega

theorem topsFrom_ge (rankGap slot : Int) (hg : 0 ≤ rankGap) (hsl : 0 ≤ slot) :
    ∀ (hs ss : List Int) (t : Int), (∀ h ∈ hs, 0 ≤ h) → (∀ s ∈ ss, 0 ≤ s) →
      ∀ e ∈ topsFrom rankGap slot t hs ss, t ≤ e := by
  intro hs
  induction hs with
  | nil => intro ss t _ _ e he; simp [topsFrom] at he
  | cons h0 hs' ih =>
    intro ss t hh hss e he
    cases ss with
    | nil =>
      cases hs' with
      | nil => simp [topsFrom] at he; omega
      | cons _ _ => simp [topsFrom] at he
    | cons s ss' =>
      simp only [topsFrom, List.mem_cons] at he
      have h0' := hh h0 (by simp)
      have s' := hss s (by simp)
      have hm := Int.mul_nonneg hsl s'
      rcases he with he | he
      · omega
      · have := ih ss' (t + h0 + rankGap + slot * s)
          (fun h hm => hh h (by simp [hm])) (fun s hm => hss s (by simp [hm])) e he
        omega

theorem topsFrom_disjoint (rankGap slot : Int) (hg : 0 ≤ rankGap) (hsl : 0 ≤ slot) :
    ∀ (hs ss : List Int) (t : Int), (∀ h ∈ hs, 0 ≤ h) → (∀ s ∈ ss, 0 ≤ s) →
      ss.length + 1 = hs.length →
      ∀ (r r' : Nat) (a b h : Int), r < r' → (topsFrom rankGap slot t hs ss)[r]? = some a →
        (topsFrom rankGap slot t hs ss)[r']? = some b → hs[r]? = some h → a + h ≤ b := by
  intro hs
  induction hs with
  | nil => intro ss t _ _ hl r r' a b h _ _ _ hh; simp at hh
  | cons h0 hs' ih =>
    intro ss t hh hss hl r r' a b h hr ha hb hh'
    cases ss with
    | nil =>
      cases hs' with
      | nil =>
        have e : topsFrom rankGap slot t [h0] [] = [t] := rfl
        rw [e] at hb
        cases r' with
        | zero => omega
        | succ r1 => simp at hb
      | cons _ _ => simp at hl
    | cons s ss' =>
      have h0' := hh h0 (by simp)
      have s' := hss s (by simp)
      have hm := Int.mul_nonneg hsl s'
      have hh1 : ∀ h ∈ hs', 0 ≤ h := fun h hm => hh h (by simp [hm])
      have hss1 : ∀ s ∈ ss', 0 ≤ s := fun s hm => hss s (by simp [hm])
      cases r with
      | zero =>
        cases r' with
        | zero => omega
        | succ r1 =>
          simp only [topsFrom, List.getElem?_cons_zero, Option.some.injEq] at ha
          simp only [topsFrom, List.getElem?_cons_succ] at hb
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hh'
          have := topsFrom_ge rankGap slot hg hsl hs' ss' (t + h0 + rankGap + slot * s) hh1 hss1 b
            (List.mem_of_getElem? hb)
          omega
      | succ r1 =>
        cases r' with
        | zero => omega
        | succ r2 =>
          simp only [topsFrom, List.getElem?_cons_succ] at ha hb
          simp only [List.getElem?_cons_succ] at hh'
          exact ih ss' (t + h0 + rankGap + slot * s) hh1 hss1 (by simpa using hl) r1 r2 a b h
            (by omega) ha hb hh'

theorem rankCoordsWith_spec {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    1 ≤ rankGap ∧ 1 ≤ slot ∧ slots.length = layers.length - 1 ∧ (∀ s ∈ slots, 0 ≤ s) ∧
      sizesNonneg p = true ∧ top = topsFrom rankGap slot 0 (layers.map (layerHeight p)) slots ∧
      y = (List.range p.nodes.length).map (fun v =>
        top.getD (rk p.rank v).toNat 0 +
          Int.fdiv ((layers.map (layerHeight p)).getD (rk p.rank v).toNat 0 - nodeH p v) 2) := by
  unfold rankCoordsWith at h
  split at h
  · simp at h
  · next pos hpos =>
    split at h
    · simp at h
    · next hg =>
      split at h
      · simp at h
      · next hlen =>
        split at h
        · simp at h
        · next hany =>
          dsimp only at h
          split at h
          · simp at h
          · 
            split at h
            · simp at h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hnn : ∀ s ∈ slots, 0 ≤ s := by
                intro s hs
                have hf : slots.any (fun s => decide (s < 0)) = false := by simpa using hany
                have := List.any_eq_false.mp hf s hs
                simp at this
                omega
              exact ⟨by omega, by omega, by simpa using hlen, hnn,
                (checkLayers_spec hpos).2, rfl, rfl⟩

theorem rankAxis_bands_disjoint {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    ∀ r r' (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
      top.getD r 0 + layerHeight p l ≤ top.getD r' 0 := by
  intro r r' l l' hr hl hl'
  obtain ⟨hg, hs, hlen, hnn, hsz, htop, _⟩ := rankCoordsWith_spec h
  have hlen' : slots.length + 1 = (layers.map (layerHeight p)).length := by
    have : r' < layers.length := (List.getElem?_eq_some_iff.mp hl').1
    simp
    omega
  have hh : ∀ x ∈ layers.map (layerHeight p), 0 ≤ x := by
    intro x hx
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    exact layerHeight_nonneg p m
  have hL := topsFrom_length rankGap slot (layers.map (layerHeight p)) slots 0 hlen'
  subst htop
  have hr'len : r' < (topsFrom rankGap slot 0 (layers.map (layerHeight p)) slots).length := by
    rw [hL]
    simpa using (List.getElem?_eq_some_iff.mp hl').1
  have hrlen : r < (topsFrom rankGap slot 0 (layers.map (layerHeight p)) slots).length := by
    omega
  have ha := List.getElem?_eq_getElem hrlen
  have hb := List.getElem?_eq_getElem hr'len
  have hH : (layers.map (layerHeight p))[r]? = some (layerHeight p l) := by
    simp [hl]
  have := topsFrom_disjoint rankGap slot (by omega) (by omega) (layers.map (layerHeight p)) slots 0
    hh hnn hlen' r r' _ _ _ hr ha hb hH
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ha, hb]
  simpa using this

theorem rankAxis_no_interior_point {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    ∀ r r' (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
      ¬ ∃ t : Int, top.getD r 0 < t ∧ t < top.getD r 0 + layerHeight p l ∧
        top.getD r' 0 < t ∧ t < top.getD r' 0 + layerHeight p l' := by
  intro r r' l l' hr hl hl' ⟨t, h1, h2, h3, _⟩
  have := rankAxis_bands_disjoint h r r' l l' hr hl hl'
  omega


theorem crossCoords_eq {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoords p layers = .ok xs) :
    ∃ gap, 1 ≤ gap ∧ crossCoordsWith gap p layers = .ok xs := by
  unfold crossCoords at h
  split at h
  · next g r s _ _ _ =>
    split at h
    · exact ⟨g, (crossCoordsWith_spec h).1, h⟩
    · simp at h
  · simp at h

theorem rankCoords_eq {p : Proper} {layers : List (List Nat)} {slots y top : List Int}
    (h : rankCoords p layers slots = .ok (y, top)) :
    ∃ rankGap slot, 1 ≤ rankGap ∧ 1 ≤ slot ∧
      rankCoordsWith rankGap slot p layers slots = .ok (y, top) := by
  unfold rankCoords at h
  split at h
  · next g r s _ _ _ =>
    split at h
    · have hs := rankCoordsWith_spec h
      exact ⟨r, s, hs.1, hs.2.1, h⟩
    · simp at h
  · simp at h

theorem crossCoordsWith_length {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) : xs.length = p.nodes.length := by
  obtain ⟨_, _, _, hcase⟩ := crossCoordsWith_spec h
  rcases hcase with ⟨h0, hx⟩ | ⟨x0, x1, x2, x3, _, hx⟩
  · subst hx
    simp [h0]
  · subst hx
    simp [balanceValues]

theorem rankCoordsWith_length {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    y.length = p.nodes.length ∧ top.length = layers.length := by
  obtain ⟨_, _, hlen, _, _, htop, hy⟩ := rankCoordsWith_spec h
  refine ⟨by subst hy; simp, ?_⟩
  subst htop
  cases layers with
  | nil => simp [topsFrom]
  | cons l ls =>
    have hlen' : slots.length + 1 = ((l :: ls).map (layerHeight p)).length := by
      simp at hlen ⊢
      omega
    rw [topsFrom_length rankGap slot _ slots 0 hlen']
    simp

theorem rankAxis_node_in_band {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top))
    {r : Nat} {l : List Nat} {v : Nat} (hl : layers[r]? = some l) (hv : v ∈ l)
    (hvn : v < p.nodes.length) (hrk : rk p.rank v = (r : Int)) :
    top.getD r 0 ≤ y.getD v 0 ∧ y.getD v 0 + nodeH p v ≤ top.getD r 0 + layerHeight p l := by
  obtain ⟨_, _, _, _, hsz, _, hy⟩ := rankCoordsWith_spec h
  have hd : y.getD v 0 = top.getD r 0 +
      Int.fdiv (layerHeight p l - nodeH p v) 2 := by
    rw [hy]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hvn, hrk, hl]
  have h1 := nodeH_nonneg hsz v
  have h2 := layerHeight_ge (p := p) hv
  rw [hd, Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega


end CoordsImpl

export CoordsImpl (crossCoords crossCoordsWith crossPasses rankCoords rankCoordsWith coordSep
  layerHeight crossCoords_eq rankCoords_eq crossCoordsWith_length rankCoordsWith_length
  rankAxis_node_in_band)

theorem coords_separated {gap : Int} {p : Proper} {layers : List (List Nat)}
    {x0 x1 x2 x3 : Array Int} (h : crossPasses gap p layers = .ok (x0, x1, x2, x3)) :
    ∀ x ∈ [x0, x1, x2, x3], ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a →
      layer[i + 1]? = some b → coordSep gap p a b ≤ x[b]! - x[a]! :=
  CoordsImpl.coords_separated h

theorem balance_separated {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      coordSep gap p a b ≤ xs.getD b 0 - xs.getD a 0 :=
  CoordsImpl.balance_separated h

theorem coords_order_preserved {gap : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsWith gap p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      xs.getD a 0 ≤ xs.getD b 0 :=
  CoordsImpl.coords_order_preserved h

theorem rankAxis_bands_disjoint {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    ∀ r r' (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
      top.getD r 0 + layerHeight p l ≤ top.getD r' 0 :=
  CoordsImpl.rankAxis_bands_disjoint h

theorem rankAxis_no_interior_point {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
    {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
    ∀ r r' (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
      ¬ ∃ t : Int, top.getD r 0 < t ∧ t < top.getD r 0 + layerHeight p l ∧
        top.getD r' 0 < t ∧ t < top.getD r' 0 + layerHeight p l' :=
  CoordsImpl.rankAxis_no_interior_point h

end Layered
end Elegant
