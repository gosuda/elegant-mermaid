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

The four passes are plain functional algorithms: alignment, block placement and class offsets are
recursions over the layers, with the fuel of step C3 on the block recursion. No pass is checked at
run time. `rawPass_separated` proves that every pass returned by `rawPass` keeps the separation
rule `coordSep` for adjacent nodes of every layer, from the facts that `checkLayers` establishes
(the layers partition the nodes, ranks follow the layer index, every edge joins adjacent ranks):
the block graph of a vertical alignment is acyclic and the class dependencies of step C4 point to
a smaller rank (Brandes, Walter, Zink 2020, Lemma 1). `coords_separated`, `balance_separated`,
`coords_order_preserved`, `rankAxis_bands_disjoint` and `rankAxis_node_in_band` follow from it. -/

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
  | some n => n.node.w + 2 * (n.node.loopExtent : Int)
  | none => 0

def nodeH (p : Proper) (v : Nat) : Int :=
  match p.nodes[v]? with
  | some n => n.node.h
  | none => 0

theorem nodeW_ge_width (p : Proper) (v : Nat) :
    (match p.nodes[v]? with | some n => n.node.w | none => 0) ≤ nodeW p v :=
  match h : p.nodes[v]? with
  | none => by simp [nodeW, h]
  | some n => by
    simp only [nodeW, h]
    exact Int.le_add_of_nonneg_right
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
def coordSep (gap : Int) (p : Proper) (a b : Nat) : Int :=
  Int.fdiv (nodeW p a) 2 + Int.fdiv (nodeW p b) 2 + gap

def sizesNonneg (p : Proper) : Bool :=
  p.nodes.all fun n => decide (0 ≤ n.node.w ∧ 0 ≤ n.node.h)

def sizesFit (p : Proper) : Bool :=
  p.nodes.all fun n => decide (n.node.w + 2 * (n.node.loopExtent : Int) ≤ I32_MAX ∧ n.node.h ≤ I32_MAX)

def checkSizes (p : Proper) : Except LayoutError Unit :=
  if I32_MAX < (p.nodes.length : Int) ∨ I32_MAX < (p.edges.length : Int) then .error .overflow
  else if !sizesNonneg p then .error .domain
  else if !sizesFit p then .error .overflow
  else .ok ()

def layersInRange (p : Proper) (layers : List (List Nat)) : Bool :=
  layers.all fun l => l.all fun v => decide (v < p.nodes.length)

def layerStep (p : Proper) (n r : Nat) :
    Nat → List Nat → Array Nat × Array Bool → Except LayoutError (Array Nat × Array Bool)
  | _, [], s => .ok s
  | j, v :: vs, s =>
    if n ≤ v ∨ s.2[v]! ∨ rk p.rank v ≠ (r : Int) then .error .domain
    else layerStep p n r (j + 1) vs (s.1.set! v j, s.2.set! v true)

def layersStep (p : Proper) (n : Nat) :
    Nat → List (List Nat) → Array Nat × Array Bool → Except LayoutError (Array Nat × Array Bool)
  | _, [], s => .ok s
  | r, l :: ls, s =>
    match layerStep p n r 0 l s with
    | .error e => .error e
    | .ok s' => layersStep p n (r + 1) ls s'

def layerPositions (p : Proper) (layers : List (List Nat)) : Except LayoutError (Array Nat) :=
  match layersStep p p.nodes.length 0 layers
      (Array.replicate p.nodes.length 0, Array.replicate p.nodes.length false) with
  | .error e => .error e
  | .ok s => if s.2.any (fun b => !b) then .error .domain else .ok s.1

def checkEdges (p : Proper) : Except LayoutError Unit :=
  if p.edges.all (fun e =>
      decide (e.tail < p.nodes.length) && decide (e.head < p.nodes.length) &&
        decide (rk p.rank e.head = rk p.rank e.tail + 1)) then .ok ()
  else .error .domain

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

def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun j => if j = i then v else f j

def oor (v : Int) : Bool := decide (v < I64_MIN) || decide (I64_MAX < v)

def posStep (i : Nat) : Nat → List Nat → Array Nat × Array Nat → Array Nat × Array Nat
  | _, [], acc => acc
  | j, v :: vs, acc => posStep i (j + 1) vs (acc.1.set! v i, acc.2.set! v j)

def rankStep : Nat → List (List Nat) → Array Nat × Array Nat → Array Nat × Array Nat
  | _, [], acc => acc
  | i, l :: ls, acc => rankStep (i + 1) ls (posStep i 0 l acc)

def rankPos (n : Nat) (ls : List (List Nat)) : Array Nat × Array Nat :=
  rankStep 0 ls (Array.replicate n 0, Array.replicate n 0)

structure Ctx where
  n : Nat
  edges : Array ProperEdge
  marked : Array Bool
  widths : Array Int
  gap : Int
  layers : List (List Nat)
  rank : Array Nat
  pos : Array Nat
  pairGap : Option (Nat → Nat → Int) := none

def Ctx.sep (c : Ctx) (a b : Nat) : Int :=
  Int.fdiv c.widths[a]! 2 + Int.fdiv c.widths[b]! 2 +
    (match c.pairGap with | none => c.gap | some f => f a b)

def passLayers (layers : List (List Nat)) (k : Nat) : List (List Nat) :=
  (if 2 ≤ k then layers.reverse else layers).map fun l => if k % 2 = 1 then l.reverse else l

def otherEnd (e : ProperEdge) (v : Nat) : Nat :=
  if e.tail == v then e.head else e.tail

def upperEdges (edges : Array ProperEdge) (rank pos : Array Nat) (v : Nat) : List Nat :=
  let cands := (List.range edges.size).filter fun i =>
    (edges[i]!.head == v && rank[edges[i]!.tail]! < rank[v]!) ||
      (edges[i]!.tail == v && rank[edges[i]!.head]! < rank[v]!)
  let keyed := cands.map fun i => (pos[otherEnd edges[i]! v]!, i)
  (keyed.mergeSort fun a b => decide (a.1 < b.1) || (a.1 == b.1 && decide (a.2 ≤ b.2))).map (·.2)

structure Al where
  up : Nat → Option Nat
  down : Nat → Option Nat
  root : Nat → Nat

def Al.init : Al := { up := fun _ => none, down := fun _ => none, root := fun v => v }

def alignPick (c : Ctx) (v : Nat) (last : Int) : Option Nat :=
  let es := upperEdges c.edges c.rank c.pos v
  [(es.length - 1) / 2, es.length / 2].findSome? fun kk =>
    es[kk]?.bind fun e =>
      let w := otherEnd c.edges[e]! v
      if !c.marked[e]! && decide (last < (c.pos[w]! : Int)) then some w else none

def alignNode (c : Ctx) (st : Al × Int) (v : Nat) : Al × Int :=
  match alignPick c v st.2 with
  | some w =>
    ({ up := upd st.1.up v (some w), down := upd st.1.down w (some v),
       root := upd st.1.root v (st.1.root w) }, (c.pos[w]! : Int))
  | none => st

def alignLayer (c : Ctx) (a : Al) (layer : List Nat) : Al :=
  (layer.foldl (alignNode c) (a, -1)).1

def alignAll (c : Ctx) : Al := c.layers.foldl (alignLayer c) Al.init

structure PS where
  x : Nat → Int
  sink : Nat → Nat
  isSet : Nat → Bool
  ovf : Bool

def PS.init : PS := { x := fun _ => 0, sink := fun v => v, isSet := fun _ => false, ovf := false }

def Ctx.pred (c : Ctx) (w : Nat) : Option Nat :=
  if c.pos[w]! = 0 then none
  else
    match c.layers[c.rank[w]!]? with
    | some l => l[c.pos[w]! - 1]?
    | none => none

def members (a : Al) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, m =>
    m :: match a.down m with
      | some m' => members a f m'
      | none => []

def Ctx.firstPred (c : Ctx) (ms : List Nat) : Option Nat := ms.findSome? c.pred

def blockSink (c : Ctx) (a : Al) (st : PS) (v : Nat) (ms : List Nat) : Nat :=
  match c.firstPred ms with
  | some pr => st.sink (a.root pr)
  | none => v

def blockX (c : Ctx) (a : Al) (st : PS) (sk : Nat) (ms : List Nat) : Int :=
  (ms.filterMap fun w =>
      (c.pred w).bind fun pr =>
        if st.sink (a.root pr) = sk then some (st.x (a.root pr) + c.sep pr w) else none).foldl
    max 0

def blockOvf (c : Ctx) (a : Al) (st : PS) (sk : Nat) (ms : List Nat) : Bool :=
  ms.any fun w =>
    match c.pred w with
    | some pr => decide (st.sink (a.root pr) = sk) && oor (st.x (a.root pr) + c.sep pr w)
    | none => false

def commit (c : Ctx) (a : Al) (F : Nat) (st : PS) (v : Nat) : PS :=
  let ms := members a F v
  let sk := blockSink c a st v ms
  let xv := blockX c a st sk ms
  { x := fun j => if ms.contains j then xv else st.x j,
    sink := fun j => if ms.contains j then sk else st.sink j,
    isSet := fun j => if ms.contains j then true else st.isSet j,
    ovf := st.ovf || blockOvf c a st sk ms }

def placePreds (c : Ctx) (a : Al) (rec : PS → Nat → Option PS) : List Nat → PS → Option PS
  | [], st => some st
  | w :: ws, st =>
    match c.pred w with
    | none => placePreds c a rec ws st
    | some pr =>
      if st.isSet (a.root pr) then placePreds c a rec ws st
      else
        match rec st (a.root pr) with
        | none => none
        | some st' => placePreds c a rec ws st'

def placeBlock (c : Ctx) (a : Al) : Nat → PS → Nat → Option PS
  | 0, _, _ => none
  | d + 1, st, v =>
    (placePreds c a (placeBlock c a d) (members a c.layers.length v)
        { st with isSet := upd st.isSet v true }).map
      fun st1 => commit c a c.layers.length st1 v

def placeRoots (c : Ctx) (a : Al) (fuel : Nat) : List Nat → PS → Option PS
  | [], st => some st
  | v :: vs, st =>
    if a.root v != v || st.isSet v then placeRoots c a fuel vs st
    else
      match placeBlock c a fuel st v with
      | none => none
      | some st' => placeRoots c a fuel vs st'

structure OS where
  shift : Nat → Int
  shifted : Nat → Bool
  ovf : Bool

def allPairs (c : Ctx) (st : PS) : List (Nat × Nat) :=
  (c.layers.flatMap fun l => l.zip l.tail).filter fun ab => st.sink ab.1 != st.sink ab.2

def offStep (c : Ctx) (st : PS) (os : OS) (ab : Nat × Nat) : OS :=
  let sa := st.sink ab.1
  let sb := st.sink ab.2
  let t1 := os.shift sb + st.x ab.2
  let t2 := t1 - st.x ab.1
  let d := t2 - c.sep ab.1 ab.2
  let o := os.ovf || oor t1 || oor t2 || oor d
  if !os.shifted sa || decide (d < os.shift sa) then
    { shift := upd os.shift sa d, shifted := upd os.shifted sa true, ovf := o }
  else { os with ovf := o }

def offLayer (c : Ctx) (st : PS) (pairs : List (Nat × Nat)) (os : OS) (i : Nat) : OS :=
  match c.layers[i]? with
  | some (s :: _) =>
    let os1 :=
      if st.sink s = s && !os.shifted s then { os with shifted := upd os.shifted s true } else os
    (pairs.filter fun ab => c.rank[st.sink ab.2]! == i).foldl (offStep c st) os1
  | _ => os

def offsetsOf (c : Ctx) (st : PS) : OS :=
  (List.range c.layers.length).foldl (offLayer c st (allPairs c st))
    { shift := fun _ => 0, shifted := fun _ => false, ovf := st.ovf }

def finalX (st : PS) (os : OS) (odd : Bool) (v : Nat) : Int :=
  let xo := st.x v + os.shift (st.sink v)
  if odd then 0 - xo else xo

def lowest (c : Ctx) (st : PS) (os : OS) (odd : Bool) : Int :=
  (List.range c.n).foldl (fun m v => min m (finalX st os odd v)) (finalX st os odd 0)

def runPass (c : Ctx) (odd : Bool) : Except LayoutError (Array Int) :=
  match placeRoots c (alignAll c) (c.n + 1) c.layers.flatten PS.init with
  | none => .error .domain
  | some st =>
    let os := offsetsOf c st
    let lo := lowest c st os odd
    let ovf := os.ovf ||
      (List.range c.n).any fun v =>
        oor (st.x v + os.shift (st.sink v)) || oor (finalX st os odd v) ||
          oor (finalX st os odd v - lo)
    if ovf then .error .overflow
    else .ok ((List.range c.n).toArray.map fun v => finalX st os odd v - lo)

def mkCtx (gap : Int) (p : Proper) (layers : List (List Nat)) (marked : Array Bool) (k : Nat) :
    Ctx :=
  let ls := passLayers layers k
  let n := p.nodes.length
  let rp := rankPos n ls
  { n := n, edges := p.edges.toArray, marked := marked,
    widths := (List.range n).toArray.map (nodeW p), gap := gap, layers := ls,
    rank := rp.1, pos := rp.2 }

def rawPass (gap : Int) (p : Proper) (layers : List (List Nat)) (marked : Array Bool) (k : Nat) :
    Except LayoutError (Array Int) :=
  runPass (mkCtx gap p layers marked k) (k % 2 == 1)

def passSeparated (gap : Int) (p : Proper) (layers : List (List Nat)) (x : Array Int) : Bool :=
  layers.all fun layer =>
    (layer.zip layer.tail).all fun ab =>
      decide (coordSep gap p ab.1 ab.2 ≤ x[ab.2]! - x[ab.1]!)


theorem mem_allPairs {c : Ctx} {st : PS} {ab : Nat × Nat} :
    ab ∈ allPairs c st ↔ (∃ l ∈ c.layers, ab ∈ l.zip l.tail) ∧ st.sink ab.1 ≠ st.sink ab.2 := by
  unfold allPairs
  simp only [List.mem_filter, List.mem_flatMap, bne_iff_ne, ne_eq]

theorem offStep_other {c : Ctx} {st : PS} {os : OS} {ab : Nat × Nat} {s : Nat}
    (hs : s ≠ st.sink ab.1) :
    (offStep c st os ab).shift s = os.shift s ∧ (offStep c st os ab).shifted s = os.shifted s := by
  unfold offStep
  dsimp only
  split <;> simp [upd, hs]

theorem offStep_mono {c : Ctx} {st : PS} {os : OS} {ab : Nat × Nat} {s : Nat}
    (h : os.shifted s = true) :
    (offStep c st os ab).shifted s = true ∧ (offStep c st os ab).shift s ≤ os.shift s := by
  unfold offStep
  dsimp only
  by_cases hs : s = st.sink ab.1
  · subst hs
    split
    · next hc =>
      simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc
      simp [upd]
      omega
    · simp [h]
  · split <;> simp [upd, hs, h]

theorem offStep_tgt {c : Ctx} {st : PS} {os : OS} {ab : Nat × Nat}
    (hne : st.sink ab.1 ≠ st.sink ab.2) :
    (offStep c st os ab).shifted (st.sink ab.1) = true ∧
      (offStep c st os ab).shift (st.sink ab.1) ≤
        (offStep c st os ab).shift (st.sink ab.2) + st.x ab.2 - st.x ab.1 - c.sep ab.1 ab.2 := by
  unfold offStep
  dsimp only
  have hne' : st.sink ab.2 ≠ st.sink ab.1 := fun h => hne h.symm
  split
  · simp [upd, hne']
  · next hc =>
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hc
    obtain ⟨h1, h2⟩ := hc
    simp [h1]
    omega

def Good (c : Ctx) (st : PS) (os : OS) (q : Nat × Nat) : Prop :=
  os.shifted (st.sink q.1) = true ∧
    os.shift (st.sink q.1) ≤ os.shift (st.sink q.2) + st.x q.2 - st.x q.1 - c.sep q.1 q.2

def PairRank (c : Ctx) (st : PS) (q : Nat × Nat) : Prop :=
  c.rank[st.sink q.2]! < c.rank[st.sink q.1]! ∧
    ∃ s rest, c.layers[c.rank[st.sink q.2]!]? = some (s :: rest)

theorem offFold_spec {c : Ctx} {st : PS} {i : Nat} :
    ∀ (ps : List (Nat × Nat)) (os : OS),
      (∀ q ∈ ps, st.sink q.1 ≠ st.sink q.2 ∧ c.rank[st.sink q.2]! = i ∧
        i < c.rank[st.sink q.1]!) →
      (∀ s, c.rank[s]! ≤ i → (ps.foldl (offStep c st) os).shift s = os.shift s) ∧
      (∀ s, os.shifted s = true → (ps.foldl (offStep c st) os).shifted s = true ∧
          (ps.foldl (offStep c st) os).shift s ≤ os.shift s) ∧
      (∀ q ∈ ps, Good c st (ps.foldl (offStep c st) os) q) := by
  intro ps
  induction ps with
  | nil =>
    intro os _
    refine ⟨fun s _ => rfl, fun s h => ⟨h, Int.le_refl _⟩, fun q hq => by simp at hq⟩
  | cons q ps ih =>
    intro os h
    obtain ⟨hne, hq2, hq1⟩ := h q (by simp)
    obtain ⟨F, M, G⟩ := ih (offStep c st os q) (fun q' hq' => h q' (by simp [hq']))
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · intro s hs
      have hs' : s ≠ st.sink q.1 := by
        intro e
        subst e
        omega
      rw [F s hs, (offStep_other hs').1]
    · intro s hs
      have h1 := offStep_mono (c := c) (st := st) (ab := q) hs
      have h2 := M s h1.1
      exact ⟨h2.1, Int.le_trans h2.2 h1.2⟩
    · intro q' hq'
      rcases List.mem_cons.mp hq' with rfl | hq'
      · have ht := offStep_tgt (c := c) (st := st) (os := os) (ab := q') hne
        have hm := M (st.sink q'.1) ht.1
        have hf := F (st.sink q'.2) (by omega)
        refine ⟨hm.1, ?_⟩
        rw [hf]
        have := hm.2
        have h3 := ht.2
        rw [(offStep_other (c := c) (st := st) (os := os) (ab := q') (s := st.sink q'.2) (by
          intro e; exact hne e.symm)).1] at h3
        omega
      · exact G q' hq'

theorem offLayer_spec {c : Ctx} {st : PS} (os : OS) (i : Nat)
    (hP : ∀ q ∈ allPairs c st, PairRank c st q) :
    (∀ s, c.rank[s]! ≤ i → (offLayer c st (allPairs c st) os i).shift s = os.shift s) ∧
    (∀ s, os.shifted s = true → (offLayer c st (allPairs c st) os i).shifted s = true ∧
        (offLayer c st (allPairs c st) os i).shift s ≤ os.shift s) ∧
    (∀ q ∈ allPairs c st, c.rank[st.sink q.2]! = i →
        Good c st (offLayer c st (allPairs c st) os i) q) := by
  unfold offLayer
  split
  · next s tl hl =>
    dsimp only
    have hps : ∀ q ∈ (allPairs c st).filter (fun ab => c.rank[st.sink ab.2]! == i),
        st.sink q.1 ≠ st.sink q.2 ∧ c.rank[st.sink q.2]! = i ∧ i < c.rank[st.sink q.1]! := by
      intro q hq
      simp only [List.mem_filter, beq_iff_eq] at hq
      obtain ⟨hq1, hq2⟩ := hq
      have hm := mem_allPairs.mp hq1
      have hr := hP q hq1
      exact ⟨hm.2, hq2, by have := hr.1; omega⟩
    have hos1 : ∀ s', (if st.sink s = s && !os.shifted s then
          ({ os with shifted := upd os.shifted s true } : OS) else os).shift s' = os.shift s' ∧
        (os.shifted s' = true → (if st.sink s = s && !os.shifted s then
          ({ os with shifted := upd os.shifted s true } : OS) else os).shifted s' = true) := by
      intro s'
      split
      · refine ⟨rfl, fun h => ?_⟩
        simp [upd, h]
      · exact ⟨rfl, fun h => h⟩
    obtain ⟨F, M, G⟩ := offFold_spec _ (if st.sink s = s && !os.shifted s then
          ({ os with shifted := upd os.shifted s true } : OS) else os) hps
    refine ⟨?_, ?_, ?_⟩
    · intro s' hs'
      rw [F s' hs', (hos1 s').1]
    · intro s' hs'
      have h1 := (hos1 s').2 hs'
      have h2 := M s' h1
      exact ⟨h2.1, by have := h2.2; rw [(hos1 s').1] at this; exact this⟩
    · intro q hq hqi
      apply G
      simp only [List.mem_filter, beq_iff_eq]
      exact ⟨hq, hqi⟩
  · next hne =>
    refine ⟨fun _ _ => rfl, fun s h => ⟨h, Int.le_refl _⟩, ?_⟩
    intro q hq hqi
    obtain ⟨_, s, rest, hs⟩ := hP q hq
    rw [hqi] at hs
    exact absurd hs (hne s rest)

theorem offsets_spec {c : Ctx} {st : PS} (hP : ∀ q ∈ allPairs c st, PairRank c st q) :
    ∀ q ∈ allPairs c st, Good c st (offsetsOf c st) q := by
  have key : ∀ k, ∀ q ∈ allPairs c st, c.rank[st.sink q.2]! < k →
      Good c st ((List.range k).foldl (offLayer c st (allPairs c st))
        { shift := fun _ => 0, shifted := fun _ => false, ovf := st.ovf }) q := by
    intro k
    induction k with
    | zero => intro q _ h; omega
    | succ k ih =>
      intro q hq hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨F, M, G⟩ := offLayer_spec
        ((List.range k).foldl (offLayer c st (allPairs c st))
          { shift := fun _ => 0, shifted := fun _ => false, ovf := st.ovf }) k hP
      by_cases hk' : c.rank[st.sink q.2]! = k
      · exact G q hq hk'
      · have hlt : c.rank[st.sink q.2]! < k := by omega
        obtain ⟨g1, g2⟩ := ih q hq hlt
        have hm := M (st.sink q.1) g1
        have hf := F (st.sink q.2) (by omega)
        refine ⟨hm.1, ?_⟩
        rw [hf]
        have := hm.2
        omega
  intro q hq
  obtain ⟨_, s, rest, hs⟩ := hP q hq
  have hlt : c.rank[st.sink q.2]! < c.layers.length :=
    (List.getElem?_eq_some_iff.mp hs).1
  exact key c.layers.length q hq hlt

structure PassFacts (c : Ctx) (st : PS) : Prop where
  same : ∀ l ∈ c.layers, ∀ ab ∈ l.zip l.tail, st.sink ab.1 = st.sink ab.2 →
    st.x ab.1 + c.sep ab.1 ab.2 ≤ st.x ab.2
  rank : ∀ q ∈ allPairs c st, PairRank c st q

theorem xo_separated {c : Ctx} {st : PS} (hf : PassFacts c st) :
    ∀ l ∈ c.layers, ∀ ab ∈ l.zip l.tail,
      c.sep ab.1 ab.2 ≤ (st.x ab.2 + (offsetsOf c st).shift (st.sink ab.2)) -
        (st.x ab.1 + (offsetsOf c st).shift (st.sink ab.1)) := by
  intro l hl ab hab
  by_cases hs : st.sink ab.1 = st.sink ab.2
  · have := hf.same l hl ab hab hs
    rw [hs]
    omega
  · have hmem : ab ∈ allPairs c st := mem_allPairs.mpr ⟨⟨l, hl, hab⟩, hs⟩
    have hg := (offsets_spec hf.rank) ab hmem
    have := hg.2
    omega

theorem runPass_ok {c : Ctx} {odd : Bool} {x : Array Int} (h : runPass c odd = .ok x) :
    ∃ st, placeRoots c (alignAll c) (c.n + 1) c.layers.flatten PS.init = some st ∧
      x = (List.range c.n).toArray.map fun v =>
        finalX st (offsetsOf c st) odd v - lowest c st (offsetsOf c st) odd := by
  unfold runPass at h
  split at h
  · simp at h
  · next st hst =>
    dsimp only at h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      exact ⟨st, hst, h.symm⟩

theorem array_map_range_get {n : Nat} (f : Nat → Int) {v : Nat} (hv : v < n) :
    ((List.range n).toArray.map f)[v]! = f v := by
  simp [hv]

theorem mem_zip_tail_iff {l : List Nat} {a b : Nat} :
    (a, b) ∈ l.zip l.tail ↔ ∃ i, l[i]? = some a ∧ l[i + 1]? = some b := by
  induction l with
  | nil => simp
  | cons c rest ih =>
    cases rest with
    | nil => simp
    | cons d rest' =>
      simp only [List.tail, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | h)
        · exact ⟨0, by simp, by simp⟩
        · obtain ⟨i, hi⟩ := ih.mp h
          exact ⟨i + 1, by simpa using hi.1, by simpa using hi.2⟩
      · rintro ⟨i, h1, h2⟩
        cases i with
        | zero =>
          simp at h1 h2
          left
          exact ⟨h1.symm, h2.symm⟩
        | succ i =>
          right
          exact ih.mpr ⟨i, by simpa using h1, by simpa using h2⟩

theorem mem_zip_tail_reverse {l : List Nat} {a b : Nat} :
    (a, b) ∈ l.reverse.zip l.reverse.tail ↔ (b, a) ∈ l.zip l.tail := by
  rw [mem_zip_tail_iff, mem_zip_tail_iff]
  constructor
  · rintro ⟨i, h1, h2⟩
    have hi : i + 1 < l.reverse.length := (List.getElem?_eq_some_iff.mp h2).1
    rw [List.length_reverse] at hi
    rw [List.getElem?_reverse (by omega)] at h1 h2
    refine ⟨l.length - 1 - (i + 1), ?_, ?_⟩
    · exact h2
    · have : l.length - 1 - (i + 1) + 1 = l.length - 1 - i := by omega
      rw [this]
      exact h1
  · rintro ⟨j, h1, h2⟩
    have hj : j + 1 < l.length := (List.getElem?_eq_some_iff.mp h2).1
    refine ⟨l.length - 1 - (j + 1), ?_, ?_⟩
    · rw [List.getElem?_reverse (by omega)]
      have : l.length - 1 - (l.length - 1 - (j + 1)) = j + 1 := by omega
      rw [this]
      exact h2
    · rw [List.getElem?_reverse (by omega)]
      have : l.length - 1 - (l.length - 1 - (j + 1) + 1) = j := by omega
      rw [this]
      exact h1

theorem layer_node_lt {p : Proper} {layers : List (List Nat)} (h : layersInRange p layers = true)
    {l : List Nat} (hl : l ∈ layers) {v : Nat} (hv : v ∈ l) : v < p.nodes.length := by
  unfold layersInRange at h
  rw [List.all_eq_true] at h
  have h1 := h l hl
  rw [List.all_eq_true] at h1
  simpa using h1 v hv

theorem mkCtx_sep {gap : Int} {p : Proper} {layers : List (List Nat)} {marked : Array Bool}
    {k : Nat} {a b : Nat} (ha : a < p.nodes.length) (hb : b < p.nodes.length) :
    (mkCtx gap p layers marked k).sep a b = coordSep gap p a b := by
  unfold Ctx.sep coordSep mkCtx
  simp only []
  rw [array_map_range_get (nodeW p) ha, array_map_range_get (nodeW p) hb]

theorem rawPass_separated_of_facts {gap : Int} {p : Proper} {layers : List (List Nat)}
    {marked : Array Bool} {k : Nat} {x : Array Int} (hr : layersInRange p layers = true)
    (h : rawPass gap p layers marked k = .ok x)
    (hf : ∀ st, placeRoots (mkCtx gap p layers marked k) (alignAll (mkCtx gap p layers marked k))
        ((mkCtx gap p layers marked k).n + 1) (mkCtx gap p layers marked k).layers.flatten
        PS.init = some st → PassFacts (mkCtx gap p layers marked k) st) :
    passSeparated gap p layers x = true := by
  unfold passSeparated
  rw [List.all_eq_true]
  intro l hl
  rw [List.all_eq_true]
  rintro ⟨a, b⟩ hab
  rw [decide_eq_true_iff]
  have h' := h
  unfold rawPass at h'
  obtain ⟨st, hst, hx⟩ := runPass_ok h'
  have hO := xo_separated (hf st hst)
  obtain ⟨i, hia, hib⟩ := mem_zip_tail_iff.mp hab
  have ha : a < p.nodes.length := layer_node_lt hr hl (List.mem_of_getElem? hia)
  have hb : b < p.nodes.length := layer_node_lt hr hl (List.mem_of_getElem? hib)
  have hxa : x[a]! = finalX st (offsetsOf (mkCtx gap p layers marked k) st) (k % 2 == 1) a -
      lowest (mkCtx gap p layers marked k) st (offsetsOf (mkCtx gap p layers marked k) st)
        (k % 2 == 1) := by
    rw [hx]
    exact array_map_range_get _ ha
  have hxb : x[b]! = finalX st (offsetsOf (mkCtx gap p layers marked k) st) (k % 2 == 1) b -
      lowest (mkCtx gap p layers marked k) st (offsetsOf (mkCtx gap p layers marked k) st)
        (k % 2 == 1) := by
    rw [hx]
    exact array_map_range_get _ hb
  have hlay : (mkCtx gap p layers marked k).layers = passLayers layers k := rfl
  have hmem : l ∈ (if 2 ≤ k then layers.reverse else layers) := by
    split
    · exact List.mem_reverse.mpr hl
    · exact hl
  by_cases hk : k % 2 = 1
  · have hl' : l.reverse ∈ (mkCtx gap p layers marked k).layers := by
      rw [hlay]
      unfold passLayers
      exact List.mem_map.mpr ⟨l, hmem, by simp [hk]⟩
    have hz : (b, a) ∈ l.reverse.zip l.reverse.tail := mem_zip_tail_reverse.mpr hab
    have h1 := hO l.reverse hl' (b, a) hz
    simp only [] at h1
    rw [mkCtx_sep hb ha] at h1
    rw [hxa, hxb]
    simp only [finalX, hk, beq_self_eq_true, ite_true]
    unfold coordSep at h1 ⊢
    omega
  · have hk0 : k % 2 = 0 := by omega
    have hl' : l ∈ (mkCtx gap p layers marked k).layers := by
      rw [hlay]
      unfold passLayers
      exact List.mem_map.mpr ⟨l, hmem, by simp [hk0]⟩
    have h1 := hO l hl' (a, b) hab
    simp only [] at h1
    rw [mkCtx_sep ha hb] at h1
    rw [hxa, hxb]
    simp [finalX, hk0]
    omega

def mem (c : Ctx) (a : Al) (r : Nat) : List Nat := members a c.layers.length r

def Cons (c : Ctx) (p q : Nat) : Prop := ∃ l ∈ c.layers, (p, q) ∈ l.zip l.tail

def BG (c : Ctx) (a : Al) (u v : Nat) : Prop := ∃ p q, Cons c p q ∧ a.root p = u ∧ a.root q = v

structure Wf (c : Ctx) (a : Al) : Prop where
  pred_cons : ∀ q p, c.pred q = some p → Cons c p q
  cons_pred : ∀ p q, Cons c p q → c.pred q = some p
  mem_root : ∀ r m, a.root r = r → m ∈ mem c a r → a.root m = r
  node_root : ∀ p, p ∈ c.layers.flatten →
    a.root p ∈ c.layers.flatten ∧ a.root (a.root p) = a.root p ∧ p ∈ mem c a (a.root p)
  mem_node : ∀ r m, r ∈ c.layers.flatten → m ∈ mem c a r → m ∈ c.layers.flatten
  acyc : ∀ u, ¬ Relation.TransGen (BG c a) u u

def Closed (a : Al) (anc : List Nat) (st : PS) (r : Nat) : Prop :=
  a.root r = r ∧ st.isSet r = true ∧ r ∉ anc

def Done (c : Ctx) (a : Al) (st : PS) (r : Nat) : Prop :=
  ∀ m ∈ mem c a r, st.isSet m = true ∧ st.x m = st.x r ∧ st.sink m = st.sink r

inductive Chain (c : Ctx) (a : Al) : Nat → Nat → Prop
  | stop {r : Nat} : c.firstPred (mem c a r) = none → Chain c a r r
  | step {r pr s : Nat} : c.firstPred (mem c a r) = some pr → Chain c a (a.root pr) s →
      Chain c a r s

structure GInv (c : Ctx) (a : Al) (anc : List Nat) (st : PS) : Prop where
  inL : ∀ j, st.isSet j = true → j ∈ c.layers.flatten
  set_ : ∀ r, a.root r = r → st.isSet r = true → r ∈ anc ∨ Done c a st r
  fresh : ∀ r, a.root r = r → st.isSet r = false → st.x r = 0 ∧ st.sink r = r
  d2 : ∀ r, Closed a anc st r → ∀ p q, Cons c p q → a.root q = r →
    Closed a anc st (a.root p) ∧
      (st.sink (a.root p) = st.sink r → st.x (a.root p) + c.sep p q ≤ st.x r)
  sinks : ∀ r, Closed a anc st r →
    Closed a anc st (st.sink r) ∧ st.sink (st.sink r) = st.sink r
  fp : ∀ r, Closed a anc st r →
    (c.firstPred (mem c a r) = none ∧ st.sink r = r) ∨
    (∃ pr, c.firstPred (mem c a r) = some pr ∧ Closed a anc st (a.root pr) ∧
      st.sink r = st.sink (a.root pr))
  chain : ∀ r, Closed a anc st r → Chain c a r (st.sink r)

structure Ext (c : Ctx) (a : Al) (anc : List Nat) (st st' : PS) : Prop where
  e1 : ∀ r, st.isSet r = true → st'.isSet r = true
  e2 : ∀ r, Closed a anc st r → ∀ m ∈ mem c a r, st'.x m = st.x m ∧ st'.sink m = st.sink m
  e3 : ∀ m, st'.isSet m = false →
    st.isSet m = false ∧ st'.x m = st.x m ∧ st'.sink m = st.sink m

theorem Closed.mono {a : Al} {anc : List Nat} {st st' : PS} {r : Nat}
    (h : Closed a anc st r) (hm : st.isSet r = true → st'.isSet r = true) : Closed a anc st' r :=
  ⟨h.1, hm h.2.1, h.2.2⟩

theorem Ext.refl (c : Ctx) (a : Al) (anc : List Nat) (st : PS) : Ext c a anc st st :=
  ⟨fun _ h => h, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem Ext.trans {c : Ctx} {a : Al} {anc : List Nat} {s1 s2 s3 : PS}
    (h12 : Ext c a anc s1 s2) (h23 : Ext c a anc s2 s3) : Ext c a anc s1 s3 :=
  ⟨fun r h => h23.e1 r (h12.e1 r h),
   fun r hr m hm =>
     have h2 := h12.e2 r hr m hm
     have h3 := h23.e2 r (hr.mono (h12.e1 r)) m hm
     ⟨h3.1.trans h2.1, h3.2.trans h2.2⟩,
   fun m hm =>
     have h3 := h23.e3 m hm
     have h2 := h12.e3 m h3.1
     ⟨h2.1, h3.2.1.trans h2.2.1, h3.2.2.trans h2.2.2⟩⟩

theorem Ext.of_cons {c : Ctx} {a : Al} {anc : List Nat} {st st' : PS} {v : Nat}
    (hv : st.isSet v = false) (h : Ext c a (v :: anc) st st') : Ext c a anc st st' :=
  ⟨h.e1, fun r hr m hm =>
    h.e2 r ⟨hr.1, hr.2.1, by
      intro hin
      rcases List.mem_cons.mp hin with rfl | hin
      · rw [hr.2.1] at hv
        exact Bool.noConfusion hv
      · exact hr.2.2 hin⟩ m hm, h.e3⟩

theorem bg_of_pred {c : Ctx} {a : Al} (hW : Wf c a) {v w pr : Nat} (hv : a.root v = v)
    (hw : w ∈ mem c a v) (hp : c.pred w = some pr) : BG c a (a.root pr) v :=
  ⟨pr, w, hW.pred_cons w pr hp, rfl, hW.mem_root v w hv hw⟩

theorem pred_root_notin {c : Ctx} {a : Al} (hW : Wf c a) {v w pr : Nat} {anc : List Nat}
    (hv : a.root v = v) (hw : w ∈ mem c a v) (hp : c.pred w = some pr)
    (hvanc : ∀ u ∈ anc, Relation.TransGen (BG c a) v u) : a.root pr ∉ v :: anc := by
  have hb := bg_of_pred hW hv hw hp
  intro hin
  rcases List.mem_cons.mp hin with h | h
  · rw [h] at hb
    exact hW.acyc v (Relation.TransGen.single hb)
  · exact hW.acyc _ (Relation.TransGen.trans (Relation.TransGen.single hb) (hvanc _ h))

theorem commit_in {c : Ctx} {a : Al} (st : PS) {v j : Nat} (hj : j ∈ mem c a v) :
    (commit c a c.layers.length st v).x j =
        blockX c a st (blockSink c a st v (mem c a v)) (mem c a v) ∧
      (commit c a c.layers.length st v).sink j = blockSink c a st v (mem c a v) ∧
      (commit c a c.layers.length st v).isSet j = true := by
  have h' : (members a c.layers.length v).contains j = true := List.contains_iff_mem.mpr hj
  refine ⟨?_, ?_, ?_⟩ <;> simp only [commit, mem, ite_eq_left h']

theorem commit_out {c : Ctx} {a : Al} (st : PS) {v j : Nat} (hj : j ∉ mem c a v) :
    (commit c a c.layers.length st v).x j = st.x j ∧
      (commit c a c.layers.length st v).sink j = st.sink j ∧
      (commit c a c.layers.length st v).isSet j = st.isSet j := by
  have h' : ¬ (members a c.layers.length v).contains j = true := by
    intro h
    exact hj (List.contains_iff_mem.mp h)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [commit, ite_eq_right h']

theorem notin_mem {c : Ctx} {a : Al} (hW : Wf c a) {v r m : Nat} (hv : a.root v = v)
    (hr : a.root r = r) (hrv : r ≠ v) (hm : m ∈ mem c a r) : m ∉ mem c a v := by
  intro hmv
  have h1 := hW.mem_root r m hr hm
  have h2 := hW.mem_root v m hv hmv
  exact hrv (h1.symm.trans h2)

theorem le_foldl_max (l : List Int) (z : Int) : z ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => exact Int.le_refl z
  | cons x xs ih => exact Int.le_trans (Int.le_max_left z x) (ih (max z x))

theorem foldl_max_ge (l : List Int) (z e : Int) (he : e ∈ l) : e ≤ l.foldl max z := by
  induction l generalizing z with
  | nil => simp at he
  | cons x xs ih =>
    rcases List.mem_cons.mp he with rfl | h
    · exact Int.le_trans (Int.le_max_right z e) (le_foldl_max xs (max z e))
    · exact ih (max z x) h

theorem blockX_ge {c : Ctx} {a : Al} {st : PS} {sk : Nat} {ms : List Nat} {w pr : Nat}
    (hw : w ∈ ms) (hp : c.pred w = some pr) (hs : st.sink (a.root pr) = sk) :
    st.x (a.root pr) + c.sep pr w ≤ blockX c a st sk ms := by
  unfold blockX
  apply foldl_max_ge
  rw [List.mem_filterMap]
  refine ⟨w, hw, ?_⟩
  simp [hp, hs]

theorem firstPred_some {c : Ctx} {ms : List Nat} {pr : Nat} (h : c.firstPred ms = some pr) :
    ∃ w ∈ ms, c.pred w = some pr := by
  unfold Ctx.firstPred at h
  obtain ⟨w, hw, hp⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨w, hw, hp⟩

theorem commit_isSet_mono {c : Ctx} {a : Al} {st : PS} {v j : Nat} (h : st.isSet j = true) :
    (commit c a c.layers.length st v).isSet j = true := by
  by_cases hj : j ∈ mem c a v
  · exact (commit_in st hj).2.2
  · rw [(commit_out st hj).2.2]
    exact h

theorem cons_mem {c : Ctx} {p q : Nat} (h : Cons c p q) :
    p ∈ c.layers.flatten ∧ q ∈ c.layers.flatten := by
  obtain ⟨l, hl, hz⟩ := h
  have := List.of_mem_zip hz
  exact ⟨List.mem_flatten.mpr ⟨l, hl, this.1⟩,
    List.mem_flatten.mpr ⟨l, hl, List.mem_of_mem_tail this.2⟩⟩

theorem commit_spec {c : Ctx} {a : Al} (hW : Wf c a) {anc : List Nat} {st : PS} {v : Nat}
    (hG : GInv c a (v :: anc) st) (hv : a.root v = v) (hvn : v ∈ c.layers.flatten)
    (hvanc : v ∉ anc)
    (hpreds : ∀ w ∈ mem c a v, ∀ pr, c.pred w = some pr →
      Closed a (v :: anc) st (a.root pr)) :
    GInv c a anc (commit c a c.layers.length st v) ∧
      Closed a anc (commit c a c.layers.length st v) v ∧
      Ext c a (v :: anc) st (commit c a c.layers.length st v) := by
  have hvm : v ∈ mem c a v := by
    have := (hW.node_root v hvn).2.2
    rwa [hv] at this
  have hmsroot : ∀ j ∈ mem c a v, a.root j = v := fun j hj => hW.mem_root v j hv hj
  have hmsn : ∀ j ∈ mem c a v, j ∈ c.layers.flatten := fun j hj => hW.mem_node v j hvn hj
  have hnotms : ∀ s, a.root s = s → s ∉ v :: anc → s ∉ mem c a v := by
    intro s hs hsn hsm
    apply hsn
    have := hmsroot s hsm
    rw [hs] at this
    rw [this]
    exact List.mem_cons_self
  have hrootms : ∀ r, a.root r = r → r ∈ mem c a v → r = v := by
    intro r hr hrm
    have := hmsroot r hrm
    rwa [hr] at this
  have hfrozen : ∀ r, a.root r = r → r ≠ v → ∀ m ∈ mem c a r, m ∉ mem c a v :=
    fun r hr hrv m hm => notin_mem hW hv hr hrv hm
  have hcl : ∀ s, Closed a (v :: anc) st s →
      s ∉ mem c a v ∧ (commit c a c.layers.length st v).x s = st.x s ∧
        (commit c a c.layers.length st v).sink s = st.sink s ∧
        Closed a anc (commit c a c.layers.length st v) s := by
    intro s hs
    have h1 := hnotms s hs.1 hs.2.2
    have h2 := commit_out st h1
    refine ⟨h1, h2.1, h2.2.1, hs.1, commit_isSet_mono hs.2.1, ?_⟩
    intro hin
    exact hs.2.2 (List.mem_cons_of_mem _ hin)
  have hv' : (commit c a c.layers.length st v).x v =
        blockX c a st (blockSink c a st v (mem c a v)) (mem c a v) ∧
      (commit c a c.layers.length st v).sink v = blockSink c a st v (mem c a v) ∧
      (commit c a c.layers.length st v).isSet v = true := commit_in st hvm
  have hpredsrc : ∀ w ∈ mem c a v, ∀ pr, c.pred w = some pr →
      Closed a anc (commit c a c.layers.length st v) (a.root pr) ∧
        (commit c a c.layers.length st v).x (a.root pr) = st.x (a.root pr) ∧
        (commit c a c.layers.length st v).sink (a.root pr) = st.sink (a.root pr) :=
    fun w hw pr hp =>
      have h := hcl _ (hpreds w hw pr hp)
      ⟨h.2.2.2, h.2.1, h.2.2.1⟩
  have hsk : (∃ pr, c.firstPred (mem c a v) = some pr ∧
        blockSink c a st v (mem c a v) = st.sink (a.root pr)) ∨
      (c.firstPred (mem c a v) = none ∧ blockSink c a st v (mem c a v) = v) := by
    unfold blockSink
    cases h : c.firstPred (mem c a v) with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some pr => exact Or.inl ⟨pr, rfl, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hv, hv'.2.2, hvanc⟩, ⟨?_, ?_, ?_⟩⟩
  · intro j hj
    by_cases hjm : j ∈ mem c a v
    · exact hmsn j hjm
    · rw [(commit_out st hjm).2.2] at hj
      exact hG.inL j hj
  · intro r hr hset
    by_cases hrm : r ∈ mem c a v
    · have hrv := hrootms r hr hrm
      right
      intro m hm
      rw [hrv] at hm
      have h1 := commit_in st hm
      rw [hrv]
      exact ⟨h1.2.2, h1.1.trans hv'.1.symm, h1.2.1.trans hv'.2.1.symm⟩
    · rw [(commit_out st hrm).2.2] at hset
      have hrv : r ≠ v := fun h => hrm (h ▸ hvm)
      rcases hG.set_ r hr hset with hin | hdone
      · rcases List.mem_cons.mp hin with h | h
        · exact absurd h hrv
        · exact Or.inl h
      · right
        intro m hm
        have hmm := hfrozen r hr hrv m hm
        have h1 := commit_out st hmm
        have h2 := commit_out st hrm
        have h3 := hdone m hm
        rw [h1.1, h1.2.1, h1.2.2, h2.1, h2.2.1]
        exact h3
  · intro r hr hset
    have hrm : r ∉ mem c a v := by
      intro hrm
      have := (commit_in st hrm).2.2
      rw [this] at hset
      exact Bool.noConfusion hset
    have h1 := commit_out st hrm
    rw [h1.2.2] at hset
    rw [h1.1, h1.2.1]
    exact hG.fresh r hr hset
  · intro r hr p q hpq hq
    by_cases hrm : r ∈ mem c a v
    · have hrv := hrootms r hr.1 hrm
      have hqn := (cons_mem hpq).2
      have hqm : q ∈ mem c a v := by
        have := (hW.node_root q hqn).2.2
        rwa [hq, hrv] at this
      have hpq' := hW.cons_pred p q hpq
      have h := hpredsrc q hqm p hpq'
      rw [hrv]
      refine ⟨h.1, fun hs => ?_⟩
      rw [h.2.2, hv'.2.1] at hs
      rw [h.2.1, hv'.1]
      exact blockX_ge hqm hpq' hs
    · have hrv : r ≠ v := fun h => hrm (h ▸ hvm)
      have hset : st.isSet r = true := by
        have := hr.2.1
        rwa [(commit_out st hrm).2.2] at this
      have hnot : r ∉ v :: anc := by
        intro hin
        rcases List.mem_cons.mp hin with h | h
        · exact hrv h
        · exact hr.2.2 h
      obtain ⟨hc1, hc2⟩ := hG.d2 r ⟨hr.1, hset, hnot⟩ p q hpq hq
      obtain ⟨-, hx, hsk', hcl'⟩ := hcl _ hc1
      have hr1 := commit_out st hrm
      refine ⟨hcl', fun hs => ?_⟩
      rw [hsk', hr1.2.1] at hs
      rw [hx, hr1.1]
      exact hc2 hs
  · intro r hr
    by_cases hrm : r ∈ mem c a v
    · have hrv := hrootms r hr.1 hrm
      have e := hv'.2.1
      rw [hrv, e]
      rcases hsk with ⟨pr, hfp, hbs⟩ | ⟨hfp, hbs⟩
      · obtain ⟨w, hw, hwp⟩ := firstPred_some hfp
        have hcl1 := hpreds w hw pr hwp
        have hs := hG.sinks _ hcl1
        have hc2 := hcl _ hs.1
        rw [hbs]
        exact ⟨hc2.2.2.2, by rw [hc2.2.2.1]; exact hs.2⟩
      · rw [hbs]
        exact ⟨⟨hv, hv'.2.2, hvanc⟩, e.trans hbs⟩
    · have hrv : r ≠ v := fun h => hrm (h ▸ hvm)
      have hset : st.isSet r = true := by
        have := hr.2.1
        rwa [(commit_out st hrm).2.2] at this
      have hnot : r ∉ v :: anc := by
        intro hin
        rcases List.mem_cons.mp hin with h | h
        · exact hrv h
        · exact hr.2.2 h
      have hs := hG.sinks r ⟨hr.1, hset, hnot⟩
      have hc2 := hcl _ hs.1
      rw [(commit_out st hrm).2.1]
      exact ⟨hc2.2.2.2, by rw [hc2.2.2.1]; exact hs.2⟩
  · intro r hr
    by_cases hrm : r ∈ mem c a v
    · have hrv := hrootms r hr.1 hrm
      rw [hrv]
      rcases hsk with ⟨pr, hfp, hbs⟩ | ⟨hfp, hbs⟩
      · obtain ⟨w, hw, hwp⟩ := firstPred_some hfp
        have h := hpredsrc w hw pr hwp
        exact Or.inr ⟨pr, hfp, h.1, by rw [hv'.2.1, hbs, h.2.2]⟩
      · exact Or.inl ⟨hfp, hv'.2.1.trans hbs⟩
    · have hrv : r ≠ v := fun h => hrm (h ▸ hvm)
      have hset : st.isSet r = true := by
        have := hr.2.1
        rwa [(commit_out st hrm).2.2] at this
      have hnot : r ∉ v :: anc := by
        intro hin
        rcases List.mem_cons.mp hin with h | h
        · exact hrv h
        · exact hr.2.2 h
      rcases hG.fp r ⟨hr.1, hset, hnot⟩ with ⟨h1, h2⟩ | ⟨pr, h1, h2, h3⟩
      · exact Or.inl ⟨h1, by rw [(commit_out st hrm).2.1]; exact h2⟩
      · have hc := hcl _ h2
        exact Or.inr ⟨pr, h1, hc.2.2.2, by rw [(commit_out st hrm).2.1, h3, hc.2.2.1]⟩
  · intro r hr
    by_cases hrm : r ∈ mem c a v
    · have hrv := hrootms r hr.1 hrm
      rw [hrv, hv'.2.1]
      rcases hsk with ⟨pr, hfp, hbs⟩ | ⟨hfp, hbs⟩
      · obtain ⟨w, hw, hwp⟩ := firstPred_some hfp
        rw [hbs]
        exact Chain.step hfp (hG.chain _ (hpreds w hw pr hwp))
      · rw [hbs]
        exact Chain.stop hfp
    · have hrv : r ≠ v := fun h => hrm (h ▸ hvm)
      have hset : st.isSet r = true := by
        have := hr.2.1
        rwa [(commit_out st hrm).2.2] at this
      have hnot : r ∉ v :: anc := by
        intro hin
        rcases List.mem_cons.mp hin with h | h
        · exact hrv h
        · exact hr.2.2 h
      rw [(commit_out st hrm).2.1]
      exact hG.chain r ⟨hr.1, hset, hnot⟩
  · exact fun r h => commit_isSet_mono h
  · intro r hr m hm
    have hrv : r ≠ v := fun h => hr.2.2 (h ▸ List.mem_cons_self)
    have hmm := hfrozen r hr.1 hrv m hm
    have h := commit_out st hmm
    exact ⟨h.1, h.2.1⟩
  · intro m hm
    have hmm : m ∉ mem c a v := by
      intro hmv
      have := (commit_in st hmv).2.2
      rw [this] at hm
      exact Bool.noConfusion hm
    have h := commit_out st hmm
    rw [h.2.2] at hm
    exact ⟨hm, h.1, h.2.1⟩

theorem closed_mark {a : Al} {anc : List Nat} {st : PS} {v s : Nat} (hs : Closed a anc st s)
    (hu : st.isSet v = false) :
    Closed a (v :: anc) { st with isSet := upd st.isSet v true } s := by
  have hsv : s ≠ v := by
    intro h
    have := hs.2.1
    rw [h] at this
    rw [this] at hu
    exact Bool.noConfusion hu
  refine ⟨hs.1, ?_, ?_⟩
  · simp [upd, hs.2.1]
  · intro hin
    rcases List.mem_cons.mp hin with h | h
    · exact hsv h
    · exact hs.2.2 h

theorem closed_unmark {a : Al} {anc : List Nat} {st : PS} {v s : Nat}
    (hs : Closed a (v :: anc) { st with isSet := upd st.isSet v true } s) : Closed a anc st s := by
  have hsv : s ≠ v := fun h => hs.2.2 (h ▸ List.mem_cons_self)
  refine ⟨hs.1, ?_, fun h => hs.2.2 (List.mem_cons_of_mem _ h)⟩
  have := hs.2.1
  simpa [upd, hsv] using this

theorem ext_mark {c : Ctx} {a : Al} {anc : List Nat} {st : PS} {v : Nat} (hu : st.isSet v = false) :
    Ext c a (v :: anc) st { st with isSet := upd st.isSet v true } := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp [upd, hr]
  · intro r _ m _
    exact ⟨rfl, rfl⟩
  · intro m hm
    have hmv : m ≠ v := by
      intro h
      subst h
      simp [upd] at hm
    refine ⟨?_, rfl, rfl⟩
    simpa [upd, hmv] using hm

theorem ginv_mark {c : Ctx} {a : Al} {anc : List Nat} {st : PS} {v : Nat}
    (hG : GInv c a anc st) (hvn : v ∈ c.layers.flatten) (hu : st.isSet v = false) :
    GInv c a (v :: anc) { st with isSet := upd st.isSet v true } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjv : j = v
    · rw [hjv]
      exact hvn
    · apply hG.inL
      simpa [upd, hjv] using hj
  · intro r hr hset
    by_cases hrv : r = v
    · left
      rw [hrv]
      exact List.mem_cons_self
    · have hs : st.isSet r = true := by simpa [upd, hrv] using hset
      rcases hG.set_ r hr hs with hin | hdone
      · exact Or.inl (List.mem_cons_of_mem _ hin)
      · right
        intro m hm
        have h := hdone m hm
        refine ⟨?_, h.2.1, h.2.2⟩
        by_cases hmv : m = v
        · simp [upd, hmv]
        · simpa [upd, hmv] using h.1
  · intro r hr hset
    have hrv : r ≠ v := by
      intro h
      rw [h] at hset
      simp [upd] at hset
    have hs : st.isSet r = false := by simpa [upd, hrv] using hset
    exact hG.fresh r hr hs
  · intro r hr p q hpq hq
    have hr' := closed_unmark hr
    obtain ⟨h1, h2⟩ := hG.d2 r hr' p q hpq hq
    exact ⟨closed_mark h1 hu, h2⟩
  · intro r hr
    have hr' := closed_unmark hr
    obtain ⟨h1, h2⟩ := hG.sinks r hr'
    exact ⟨closed_mark h1 hu, h2⟩
  · intro r hr
    have hr' := closed_unmark hr
    rcases hG.fp r hr' with h | ⟨pr, h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨pr, h1, closed_mark h2 hu, h3⟩
  · intro r hr
    exact hG.chain r (closed_unmark hr)

theorem placePreds_spec {c : Ctx} {a : Al} (hW : Wf c a) {anc : List Nat} {v d : Nat}
    (hv : a.root v = v)
    (hvanc : ∀ u ∈ anc, Relation.TransGen (BG c a) v u)
    (IH : ∀ (st : PS) (u : Nat) (st' : PS), GInv c a (v :: anc) st → a.root u = u →
      u ∈ c.layers.flatten → st.isSet u = false → u ∉ v :: anc →
      (∀ x ∈ v :: anc, Relation.TransGen (BG c a) u x) →
      placeBlock c a d st u = some st' →
      GInv c a (v :: anc) st' ∧ Closed a (v :: anc) st' u ∧ Ext c a (v :: anc) st st') :
    ∀ (ms : List Nat) (st st1 : PS), (∀ w ∈ ms, w ∈ mem c a v) → GInv c a (v :: anc) st →
      st.isSet v = true → placePreds c a (placeBlock c a d) ms st = some st1 →
      GInv c a (v :: anc) st1 ∧ Ext c a (v :: anc) st st1 ∧ st1.isSet v = true ∧
        ∀ w ∈ ms, ∀ pr, c.pred w = some pr → Closed a (v :: anc) st1 (a.root pr) := by
  intro ms
  induction ms with
  | nil =>
    intro st st1 _ hG hv1 hrun
    simp only [placePreds, Option.some.injEq] at hrun
    subst hrun
    exact ⟨hG, Ext.refl c a _ _, hv1, fun w hw => by simp at hw⟩
  | cons w ws ih =>
    intro st st1 hms hG hv1 hrun
    have hws : ∀ w' ∈ ws, w' ∈ mem c a v := fun w' h => hms w' (List.mem_cons_of_mem _ h)
    have hwv : w ∈ mem c a v := hms w List.mem_cons_self
    cases hpw : c.pred w with
    | none =>
      simp only [placePreds, hpw] at hrun
      obtain ⟨hG1, hE1, hv2, hall⟩ := ih st st1 hws hG hv1 hrun
      refine ⟨hG1, hE1, hv2, ?_⟩
      intro w' hw' pr hp
      rcases List.mem_cons.mp hw' with rfl | h
      · rw [hpw] at hp
        cases hp
      · exact hall w' h pr hp
    | some pr =>
      have hnot := pred_root_notin hW hv hwv hpw hvanc
      have hcons := hW.pred_cons w pr hpw
      have hrn : a.root pr ∈ c.layers.flatten := (hW.node_root pr (cons_mem hcons).1).1
      have hroot : a.root (a.root pr) = a.root pr := (hW.node_root pr (cons_mem hcons).1).2.1
      have hbg := bg_of_pred hW hv hwv hpw
      have hTC : ∀ x ∈ v :: anc, Relation.TransGen (BG c a) (a.root pr) x := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Relation.TransGen.single hbg
        · exact Relation.TransGen.trans (Relation.TransGen.single hbg) (hvanc x hx)
      by_cases hs : st.isSet (a.root pr) = true
      · simp only [placePreds, hpw] at hrun
        rw [ite_eq_left hs] at hrun
        obtain ⟨hG1, hE1, hv2, hall⟩ := ih st st1 hws hG hv1 hrun
        refine ⟨hG1, hE1, hv2, ?_⟩
        intro w' hw' pr' hp
        rcases List.mem_cons.mp hw' with rfl | h
        · rw [hpw] at hp
          cases hp
          exact ⟨hroot, hE1.e1 _ hs, hnot⟩
        · exact hall w' h pr' hp
      · simp only [placePreds, hpw] at hrun
        rw [ite_eq_right hs] at hrun
        cases hrec : placeBlock c a d st (a.root pr) with
        | none =>
          rw [hrec] at hrun
          exact absurd hrun (by simp)
        | some st' =>
          rw [hrec] at hrun
          have hu : st.isSet (a.root pr) = false := by simpa using hs
          obtain ⟨hGa, hCa, hEa⟩ := IH st (a.root pr) st' hG hroot hrn hu hnot hTC hrec
          have hv1' : st'.isSet v = true := hEa.e1 v hv1
          have hws' := hrun
          obtain ⟨hG1, hE1, hv2, hall⟩ := ih st' st1 hws hGa hv1' hrun
          refine ⟨hG1, hEa.trans hE1, hv2, ?_⟩
          intro w' hw' pr' hp
          rcases List.mem_cons.mp hw' with rfl | h
          · rw [hpw] at hp
            cases hp
            exact hCa.mono (hE1.e1 _)
          · exact hall w' h pr' hp

theorem placeBlock_spec {c : Ctx} {a : Al} (hW : Wf c a) :
    ∀ (d : Nat) (anc : List Nat) (st : PS) (v : Nat) (st' : PS), GInv c a anc st →
      a.root v = v → v ∈ c.layers.flatten → st.isSet v = false → v ∉ anc →
      (∀ u ∈ anc, Relation.TransGen (BG c a) v u) →
      placeBlock c a d st v = some st' →
      GInv c a anc st' ∧ Closed a anc st' v ∧ Ext c a anc st st' := by
  intro d
  induction d with
  | zero =>
    intro anc st v st' _ _ _ _ _ _ hrun
    simp [placeBlock] at hrun
  | succ d ih =>
    intro anc st v st' hG hv hvn hu hvanc hTC hrun
    simp only [placeBlock] at hrun
    cases hpp : placePreds c a (placeBlock c a d) (members a c.layers.length v)
        { st with isSet := upd st.isSet v true } with
    | none =>
      rw [hpp] at hrun
      exact absurd hrun (by simp)
    | some st1 =>
      rw [hpp] at hrun
      simp only [Option.map_some, Option.some.injEq] at hrun
      subst hrun
      have hG0 := ginv_mark hG hvn hu
      have hset0 : ({ st with isSet := upd st.isSet v true } : PS).isSet v = true := by
        simp [upd]
      obtain ⟨hGp, hEp, hvp, hpreds⟩ := placePreds_spec hW hv hTC
        (fun st u st' hG' hu1 hun hunset hunot hTC' hrec =>
          ih (v :: anc) st u st' hG' hu1 hun hunset hunot hTC' hrec)
        (mem c a v) { st with isSet := upd st.isSet v true } st1 (fun w hw => hw) hG0 hset0 hpp
      obtain ⟨hGc, hCc, hEc⟩ := commit_spec hW hGp hv hvn hvanc hpreds
      refine ⟨hGc, hCc, ?_⟩
      exact Ext.of_cons hu ((ext_mark hu).trans (hEp.trans hEc))

theorem placeRoots_spec {c : Ctx} {a : Al} (hW : Wf c a) (fuel : Nat) :
    ∀ (vs : List Nat) (st st' : PS), (∀ v ∈ vs, v ∈ c.layers.flatten) → GInv c a [] st →
      placeRoots c a fuel vs st = some st' →
      GInv c a [] st' ∧ (∀ v ∈ vs, a.root v = v → st'.isSet v = true) ∧ Ext c a [] st st' := by
  intro vs
  induction vs with
  | nil =>
    intro st st' _ hG hrun
    simp only [placeRoots, Option.some.injEq] at hrun
    subst hrun
    exact ⟨hG, fun v hv => by simp at hv, Ext.refl c a _ _⟩
  | cons v vs ih =>
    intro st st' hvs hG hrun
    have hvs' : ∀ w ∈ vs, w ∈ c.layers.flatten := fun w h => hvs w (List.mem_cons_of_mem _ h)
    have hvn : v ∈ c.layers.flatten := hvs v List.mem_cons_self
    by_cases h : (a.root v != v || st.isSet v) = true
    · simp only [placeRoots] at hrun
      rw [ite_eq_left h] at hrun
      obtain ⟨hG1, hall, hE⟩ := ih st st' hvs' hG hrun
      refine ⟨hG1, ?_, hE⟩
      intro w hw hroot
      rcases List.mem_cons.mp hw with rfl | hw'
      · have hs : st.isSet w = true := by
          simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
          rcases h with h | h
          · exact absurd hroot h
          · exact h
        exact hE.e1 _ hs
      · exact hall w hw' hroot
    · simp only [placeRoots] at hrun
      rw [ite_eq_right h] at hrun
      have hh : a.root v = v ∧ st.isSet v = false := by
        refine ⟨Classical.byContradiction fun hne => h ?_, ?_⟩
        · simp [hne]
        · refine Classical.byContradiction fun hne => h ?_
          have hs : st.isSet v = true := by simpa using hne
          simp [hs]
      cases hpb : placeBlock c a fuel st v with
      | none =>
        rw [hpb] at hrun
        exact absurd hrun (by simp)
      | some st1 =>
        rw [hpb] at hrun
        obtain ⟨hG1, hC1, hE1⟩ := placeBlock_spec hW fuel [] st v st1 hG hh.1 hvn hh.2
          (by simp) (by simp) hpb
        obtain ⟨hG2, hall, hE2⟩ := ih st1 st' hvs' hG1 hrun
        refine ⟨hG2, ?_, hE1.trans hE2⟩
        intro w hw hroot
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hE2.e1 _ hC1.2.1
        · exact hall w hw' hroot

theorem exists_min (g : Nat → Nat) : ∃ m, ∀ i, g m ≤ g i := by
  have key : ∀ n, ∀ x, g x = n → ∃ m, ∀ i, g m ≤ g i := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro x hx
      by_cases h : ∃ i, g i < n
      · obtain ⟨i, hi⟩ := h
        exact ih (g i) hi i rfl
      · refine ⟨x, fun i => ?_⟩
        rw [hx]
        exact Nat.le_of_not_lt (fun hlt => h ⟨i, hlt⟩)
  exact key _ 0 rfl

theorem tc_path {β : Type} {R : β → β → Prop} {a b : β} (h : Relation.TransGen R a b) :
    ∃ (n : Nat) (f : Nat → β), f 0 = a ∧ f (n + 1) = b ∧ ∀ i ≤ n, R (f i) (f (i + 1)) := by
  induction h with
  | @single b' hab =>
    refine ⟨0, fun i => if i = 0 then a else b', by simp, by simp, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    simpa using hab
  | @tail b' c' _ hbc ih =>
    obtain ⟨n, f, h0, hn, hR⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n + 1 then f i else c', ?_, ?_, ?_⟩
    · simp [h0]
    · simp [show ¬ (n + 1 + 1 ≤ n + 1) by omega]
    · intro i hi
      by_cases hin : i ≤ n
      · have h1 : i + 1 ≤ n + 1 := by omega
        have h2 : i ≤ n + 1 := by omega
        simp only [h1, h2, ite_true]
        exact hR i hin
      · have : i = n + 1 := by omega
        subst this
        have h3 : ¬ (n + 1 + 1 ≤ n + 1) := by omega
        simp only [Nat.le_refl, h3, ite_true, ite_false]
        rw [hn]
        exact hbc

theorem succ_mod_cases (i m : Nat) (hm : 0 < m) :
    (i % m + 1 < m ∧ (i + 1) % m = i % m + 1) ∨ (i % m + 1 = m ∧ (i + 1) % m = 0) := by
  have h1 := Nat.mod_lt i hm
  have h2 : i + 1 = m * (i / m) + (i % m + 1) := by
    calc i + 1 = (m * (i / m) + i % m) + 1 := by rw [Nat.div_add_mod]
      _ = m * (i / m) + (i % m + 1) := by rw [Nat.add_assoc]
  have h3 : (i + 1) % m = (i % m + 1) % m := by
    rw [h2, Nat.mul_add_mod]
  rcases Nat.lt_or_ge (i % m + 1) m with hlt | hge
  · left
    exact ⟨hlt, by rw [h3, Nat.mod_eq_of_lt hlt]⟩
  · right
    have heq : i % m + 1 = m := by omega
    exact ⟨heq, by rw [h3, heq, Nat.mod_self]⟩

theorem abs_acyclic {β : Type} (Pres : β → Nat → Nat → Prop) (e : β → Nat)
    (hu : ∀ B ℓ p q, Pres B ℓ p → Pres B ℓ q → p = q)
    (hint : ∀ B ℓ ℓ' ℓ'', (∃ p, Pres B ℓ p) → (∃ p, Pres B ℓ' p) → ℓ ≤ ℓ'' → ℓ'' ≤ ℓ' →
      ∃ p, Pres B ℓ'' p)
    (hend : ∀ B ℓ p, Pres B ℓ p → ℓ ≤ e B ∧ ∃ q, Pres B (e B) q)
    (hcons : ∀ A B ℓ ℓ' p q p' q', A ≠ B → Pres A ℓ p → Pres B ℓ q → Pres A ℓ' p' →
      Pres B ℓ' q' → p < q → p' < q') :
    ∀ u, ¬ Relation.TransGen (fun A B => ∃ ℓ p q, Pres A ℓ p ∧ Pres B ℓ q ∧ p < q) u u := by
  have irrefl : ∀ A, ¬ (∃ ℓ p q, Pres A ℓ p ∧ Pres A ℓ q ∧ p < q) := by
    rintro A ⟨ℓ, p, q, h1, h2, hlt⟩
    have := hu A ℓ p q h1 h2
    omega
  have leftAt : ∀ A B, (∃ ℓ p q, Pres A ℓ p ∧ Pres B ℓ q ∧ p < q) →
      ∀ ℓ p q, Pres A ℓ p → Pres B ℓ q → p < q := by
    rintro A B ⟨ℓ0, p0, q0, h1, h2, hlt⟩ ℓ p q hp hq
    have hne : A ≠ B := by
      intro h
      subst h
      exact irrefl A ⟨ℓ0, p0, q0, h1, h2, hlt⟩
    exact hcons A B ℓ0 ℓ p0 q0 p q hne h1 h2 hp hq hlt
  have cyc : ∀ k : Nat, ∀ f : Nat → β,
      (∀ i, ∃ ℓ p q, Pres (f i) ℓ p ∧ Pres (f (i + 1)) ℓ q ∧ p < q) →
      (∀ i, f (i + (k + 1)) = f i) → False := by
    intro k
    induction k with
    | zero =>
      intro f hR hper
      have h1 : f (0 + 1) = f 0 := by simpa using hper 0
      have := hR 0
      rw [h1] at this
      exact irrefl _ this
    | succ k ih =>
      intro f hR hper
      obtain ⟨m, hmin0⟩ := exists_min (fun i => e (f i))
      have hmin : ∀ i, e (f m) ≤ e (f i) := hmin0
      let h : Nat → β := fun i => f (i + m)
      have hRh : ∀ i, ∃ ℓ p q, Pres (h i) ℓ p ∧ Pres (h (i + 1)) ℓ q ∧ p < q := by
        intro i
        have := hR (i + m)
        have e1 : i + m + 1 = i + 1 + m := by omega
        rw [e1] at this
        exact this
      have hperh : ∀ i, h (i + (k + 1 + 1)) = h i := by
        intro i
        have := hper (i + m)
        have e1 : i + (k + 1 + 1) + m = i + m + (k + 1 + 1) := by omega
        show f (i + (k + 1 + 1) + m) = f (i + m)
        rw [e1]
        exact this
      have hminh : ∀ i, e (h 0) ≤ e (h i) := by
        intro i
        show e (f (0 + m)) ≤ e (f (i + m))
        rw [Nat.zero_add]
        exact hmin (i + m)
      let g : Nat → β := fun i => h (1 + i % (k + 1))
      apply ih g
      · intro i
        rcases succ_mod_cases i (k + 1) (by omega) with ⟨hlt, hmod⟩ | ⟨heq, hmod⟩
        · have := hRh (1 + i % (k + 1))
          show ∃ ℓ p q, Pres (h (1 + i % (k + 1))) ℓ p ∧
            Pres (h (1 + (i + 1) % (k + 1))) ℓ q ∧ p < q
          rw [hmod, show 1 + (i % (k + 1) + 1) = 1 + i % (k + 1) + 1 by omega]
          exact this
        · show ∃ ℓ p q, Pres (h (1 + i % (k + 1))) ℓ p ∧
            Pres (h (1 + (i + 1) % (k + 1))) ℓ q ∧ p < q
          rw [hmod, show i % (k + 1) = k by omega]
          have hA := hRh (1 + k)
          have hA' : h (1 + k + 1) = h 0 := by
            have := hperh 0
            rw [show 1 + k + 1 = 0 + (k + 1 + 1) by omega]
            exact this
          rw [hA'] at hA
          obtain ⟨ℓa, pa, qa, ha1, ha2, halt⟩ := hA
          obtain ⟨ℓb, pb, qb, hb1, hb2, hblt⟩ := hRh 0
          obtain ⟨hle, q0, hq0⟩ := hend _ ℓa qa ha2
          have hmin1 := hminh (1 + k)
          have hmin2 := hminh 1
          have hrest : (h 0 = h 0) := rfl
          obtain ⟨pc, hpc⟩ := hint (h (1 + k)) ℓa (e (h (1 + k))) (e (h 0))
            ⟨pa, ha1⟩ (hend _ ℓa pa ha1).2 hle hmin1
          have hleb := (hend _ ℓb pb hb1).1
          have hb2' : Pres (h (0 + 1)) ℓb qb := hb2
          obtain ⟨qd, hqd⟩ := hint (h 1) ℓb (e (h 1)) (e (h 0))
            ⟨qb, hb2'⟩ (hend _ ℓb qb hb2').2 hleb hmin2
          have l1 : pc < q0 := leftAt (h (1 + k)) (h 0) ⟨ℓa, pa, qa, ha1, ha2, halt⟩ _ _ _ hpc hq0
          have l2 : q0 < qd := leftAt (h 0) (h (0 + 1)) ⟨ℓb, pb, qb, hb1, hb2, hblt⟩ _ _ _ hq0 hqd
          refine ⟨e (h 0), pc, qd, hpc, ?_, by omega⟩
          rw [show 1 + 0 = 0 + 1 by omega]
          exact hqd
      · intro i
        show h (1 + (i + (k + 1)) % (k + 1)) = h (1 + i % (k + 1))
        rw [Nat.add_mod_right]
  intro u hu
  obtain ⟨n, f, h0, hn, hR⟩ := tc_path hu
  apply cyc n (fun i => f (i % (n + 1)))
  · intro i
    rcases succ_mod_cases i (n + 1) (by omega) with ⟨hlt, hmod⟩ | ⟨heq, hmod⟩
    · show ∃ ℓ p q, Pres (f (i % (n + 1))) ℓ p ∧ Pres (f ((i + 1) % (n + 1))) ℓ q ∧ p < q
      rw [hmod]
      exact hR _ (by omega)
    · show ∃ ℓ p q, Pres (f (i % (n + 1))) ℓ p ∧ Pres (f ((i + 1) % (n + 1))) ℓ q ∧ p < q
      rw [hmod, show i % (n + 1) = n by omega]
      have := hR n (Nat.le_refl n)
      rw [hn, ← h0] at this
      exact this
  · intro i
    show f ((i + (n + 1)) % (n + 1)) = f (i % (n + 1))
    rw [Nat.add_mod_right]

structure Lay (c : Ctx) : Prop where
  idx : ∀ (i : Nat) (l : List Nat) (j v : Nat), c.layers[i]? = some l → l[j]? = some v →
    c.rank[v]! = i ∧ c.pos[v]! = j
  unset : ∀ v, v ∉ c.layers.flatten → c.pos[v]! = 0

structure AF (c : Ctx) (a : Al) : Prop where
  lay : Lay c
  up_rank : ∀ v w, a.up v = some w →
    c.rank[w]! + 1 = c.rank[v]! ∧ w ∈ c.layers.flatten ∧ v ∈ c.layers.flatten
  up_mono : ∀ v1 v2 w1 w2, a.up v1 = some w1 → a.up v2 = some w2 →
    c.rank[v1]! = c.rank[v2]! → c.pos[v1]! < c.pos[v2]! → c.pos[w1]! < c.pos[w2]!
  down_iff : ∀ v w, a.down w = some v ↔ a.up v = some w
  root_eq : ∀ v, v ∈ c.layers.flatten →
    a.root v = (match a.up v with | some w => a.root w | none => v)

theorem Lay.loc {c : Ctx} (hL : Lay c) {v : Nat} (hv : v ∈ c.layers.flatten) :
    ∃ l, c.layers[c.rank[v]!]? = some l ∧ l[c.pos[v]!]? = some v := by
  obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp hv
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvl
  have := hL.idx i l j v hi hj
  rw [this.1, this.2]
  exact ⟨l, hi, hj⟩

theorem Lay.rank_lt {c : Ctx} (hL : Lay c) {v : Nat} (hv : v ∈ c.layers.flatten) :
    c.rank[v]! < c.layers.length := by
  obtain ⟨l, hl, _⟩ := hL.loc hv
  exact (List.getElem?_eq_some_iff.mp hl).1

theorem Lay.pred_iff {c : Ctx} (hL : Lay c) {p q : Nat} : c.pred q = some p ↔ Cons c p q := by
  constructor
  · intro h
    unfold Ctx.pred at h
    by_cases h0 : c.pos[q]! = 0
    · rw [ite_eq_left h0] at h
      cases h
    · rw [ite_eq_right h0] at h
      have hq : q ∈ c.layers.flatten :=
        Classical.byContradiction fun hn => h0 (hL.unset q hn)
      obtain ⟨l, hl, hql⟩ := hL.loc hq
      rw [hl] at h
      simp only [] at h
      refine ⟨l, List.mem_of_getElem? hl, mem_zip_tail_iff.mpr ⟨c.pos[q]! - 1, h, ?_⟩⟩
      have : c.pos[q]! - 1 + 1 = c.pos[q]! := by omega
      rw [this]
      exact hql
  · rintro ⟨l, hl, hz⟩
    obtain ⟨i, hia, hib⟩ := mem_zip_tail_iff.mp hz
    obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hl
    have hidx := hL.idx i0 l (i + 1) q hi0 hib
    unfold Ctx.pred
    rw [hidx.1, hidx.2, ite_eq_right (by omega), hi0]
    simpa using hia

theorem members_root {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (f r m : Nat), m ∈ members a f r → a.root m = a.root r := by
  intro f
  induction f with
  | zero => intro r m h; simp [members] at h
  | succ f ih =>
    intro r m h
    cases hd : a.down r with
    | none =>
      simp only [members, hd, List.mem_singleton] at h
      rw [h]
    | some m' =>
      simp only [members, hd, List.mem_cons] at h
      rcases h with h | h
      · rw [h]
      · have h1 := ih m' m h
        have hup : a.up m' = some r := (hA.down_iff m' r).mp hd
        have hm' : m' ∈ c.layers.flatten := (hA.up_rank m' r hup).2.2
        have h2 := hA.root_eq m' hm'
        simp only [hup] at h2
        rw [h1, h2]

theorem members_flat {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (f r m : Nat), m ∈ members a f r → r ∈ c.layers.flatten → m ∈ c.layers.flatten := by
  intro f
  induction f with
  | zero => intro r m h; simp [members] at h
  | succ f ih =>
    intro r m h hr
    cases hd : a.down r with
    | none =>
      simp only [members, hd, List.mem_singleton] at h
      rw [h]
      exact hr
    | some m' =>
      simp only [members, hd, List.mem_cons] at h
      rcases h with h | h
      · rw [h]
        exact hr
      · have hup : a.up m' = some r := (hA.down_iff m' r).mp hd
        exact ih m' m h (hA.up_rank m' r hup).2.2

theorem members_rank {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (f r : Nat), r ∈ c.layers.flatten → ∀ (j m : Nat), (members a f r)[j]? = some m →
      c.rank[m]! = c.rank[r]! + j := by
  intro f
  induction f with
  | zero => intro r _ j m h; simp [members] at h
  | succ f ih =>
    intro r hr j m h
    cases hd : a.down r with
    | none =>
      simp only [members, hd] at h
      cases j with
      | zero =>
        simp at h
        subst h
        omega
      | succ j => simp at h
    | some m' =>
      simp only [members, hd] at h
      have hup : a.up m' = some r := (hA.down_iff m' r).mp hd
      have hr' := hA.up_rank m' r hup
      cases j with
      | zero =>
        simp at h
        subst h
        omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at h
        have := ih m' hr'.2.2 j m h
        omega

theorem members_fuel {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (f r : Nat), r ∈ c.layers.flatten →
      (∀ m ∈ members a f r, c.rank[m]! < c.rank[r]! + f) ∧
      (∀ m p, m ∈ members a f r → a.down m = some p → c.rank[m]! + 1 < c.rank[r]! + f →
        p ∈ members a f r) := by
  intro f
  induction f with
  | zero => intro r _; exact ⟨fun m h => by simp [members] at h, fun m p h => by simp [members] at h⟩
  | succ f ih =>
    intro r hr
    cases hd : a.down r with
    | none =>
      constructor
      · intro m h
        simp only [members, hd, List.mem_singleton] at h
        rw [h]
        omega
      · intro m p h hdm _
        simp only [members, hd, List.mem_singleton] at h
        rw [h, hd] at hdm
        cases hdm
    | some m' =>
      have hup : a.up m' = some r := (hA.down_iff m' r).mp hd
      have hr' := hA.up_rank m' r hup
      obtain ⟨ih1, ih2⟩ := ih m' hr'.2.2
      constructor
      · intro m h
        simp only [members, hd, List.mem_cons] at h
        rcases h with h | h
        · rw [h]
          omega
        · have := ih1 m h
          omega
      · intro m p h hdm hlt
        simp only [members, hd, List.mem_cons] at h
        simp only [members, hd, List.mem_cons]
        rcases h with rfl | h
        · rw [hd] at hdm
          cases hdm
          right
          cases f with
          | zero => omega
          | succ f' => simp [members]
        · right
          exact ih2 m p h hdm (by omega)

theorem root_top {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (n p : Nat), p ∈ c.layers.flatten → c.rank[p]! = n →
      a.root p ∈ c.layers.flatten ∧ a.up (a.root p) = none ∧ c.rank[a.root p]! ≤ c.rank[p]! := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p hp hn
    have h := hA.root_eq p hp
    cases hu : a.up p with
    | none =>
      simp only [hu] at h
      rw [h]
      exact ⟨hp, hu, Nat.le_refl _⟩
    | some w =>
      simp only [hu] at h
      have hr := hA.up_rank p w hu
      have := ih (c.rank[w]!) (by omega) w hr.2.1 rfl
      rw [h]
      exact ⟨this.1, this.2.1, by omega⟩

theorem node_mem {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ (n p : Nat), p ∈ c.layers.flatten → c.rank[p]! = n →
      p ∈ members a c.layers.length (a.root p) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p hp hn
    have h := hA.root_eq p hp
    have hlt := hA.lay.rank_lt hp
    cases hu : a.up p with
    | none =>
      simp only [hu] at h
      rw [h]
      cases hF : c.layers.length with
      | zero => omega
      | succ f => simp [members]
    | some w =>
      simp only [hu] at h
      have hr := hA.up_rank p w hu
      have hw := ih (c.rank[w]!) (by omega) w hr.2.1 rfl
      have hdown : a.down w = some p := (hA.down_iff p w).mpr hu
      have htop := root_top hA _ w hr.2.1 rfl
      have hfuel := (members_fuel hA c.layers.length (a.root w) htop.1).2 w p hw hdown (by omega)
      rw [h]
      exact hfuel

def Pres (c : Ctx) (a : Al) (B ℓ p : Nat) : Prop :=
  B ∈ c.layers.flatten ∧ a.root B = B ∧ ∃ m, m ∈ mem c a B ∧ c.rank[m]! = ℓ ∧ c.pos[m]! = p

def bEnd (c : Ctx) (a : Al) (B : Nat) : Nat := c.rank[B]! + (mem c a B).length - 1

theorem members_down {a : Al} :
    ∀ (f r j m m' : Nat), (members a f r)[j]? = some m → (members a f r)[j + 1]? = some m' →
      a.down m = some m' := by
  intro f
  induction f with
  | zero => intro r j m m' h; simp [members] at h
  | succ f ih =>
    intro r j m m' h1 h2
    cases hd : a.down r with
    | none =>
      simp only [members, hd] at h2
      simp at h2
    | some r' =>
      simp only [members, hd] at h1 h2
      cases j with
      | zero =>
        simp at h1
        rw [← h1]
        simp only [List.getElem?_cons_succ] at h2
        cases f with
        | zero => simp [members] at h2
        | succ f' =>
          simp only [members, List.getElem?_cons_zero, Option.some.injEq] at h2
          rw [← h2]
          exact hd
      | succ j =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih r' j m m' h1 h2

theorem Pres.idx {c : Ctx} {a : Al} (hA : AF c a) {B ℓ p : Nat} (h : Pres c a B ℓ p) :
    ∃ j m, (mem c a B)[j]? = some m ∧ c.rank[m]! = ℓ ∧ c.pos[m]! = p ∧
      ℓ = c.rank[B]! + j := by
  obtain ⟨hB, _, m, hm, hr, hp⟩ := h
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have := members_rank hA c.layers.length B hB j m hj
  exact ⟨j, m, hj, hr, hp, by omega⟩

theorem node_unique {c : Ctx} (hL : Lay c) {m1 m2 : Nat} (h1 : m1 ∈ c.layers.flatten)
    (h2 : m2 ∈ c.layers.flatten) (hr : c.rank[m1]! = c.rank[m2]!)
    (hp : c.pos[m1]! = c.pos[m2]!) : m1 = m2 := by
  obtain ⟨l1, hl1, hv1⟩ := hL.loc h1
  obtain ⟨l2, hl2, hv2⟩ := hL.loc h2
  rw [hr] at hl1
  rw [hl1] at hl2
  cases hl2
  rw [hp] at hv1
  rw [hv1] at hv2
  cases hv2
  rfl

theorem pres_unique {c : Ctx} {a : Al} (hA : AF c a) {B ℓ p q : Nat} (h1 : Pres c a B ℓ p)
    (h2 : Pres c a B ℓ q) : p = q := by
  obtain ⟨j1, m1, hj1, hr1, hp1, he1⟩ := Pres.idx hA h1
  obtain ⟨j2, m2, hj2, hr2, hp2, he2⟩ := Pres.idx hA h2
  have : j1 = j2 := by omega
  subst this
  rw [hj1] at hj2
  cases hj2
  rw [← hp1, ← hp2]

theorem pres_mid {c : Ctx} {a : Al} (hA : AF c a) {B ℓ ℓ' ℓ'' p p' : Nat}
    (h1 : Pres c a B ℓ p) (h2 : Pres c a B ℓ' p') (hl : ℓ ≤ ℓ'') (hr : ℓ'' ≤ ℓ') :
    ∃ q, Pres c a B ℓ'' q := by
  obtain ⟨j1, m1, hj1, hr1, hp1, he1⟩ := Pres.idx hA h1
  obtain ⟨j2, m2, hj2, hr2, hp2, he2⟩ := Pres.idx hA h2
  have hlen : j2 < (mem c a B).length := (List.getElem?_eq_some_iff.mp hj2).1
  have hlen' : ℓ'' - c.rank[B]! < (mem c a B).length := by omega
  have hget := List.getElem?_eq_getElem hlen'
  have hm := members_rank hA c.layers.length B h1.1 (ℓ'' - c.rank[B]!) _ hget
  refine ⟨c.pos[(mem c a B)[ℓ'' - c.rank[B]!]]!, h1.1, h1.2.1, (mem c a B)[ℓ'' - c.rank[B]!],
    List.mem_of_getElem? hget, ?_, rfl⟩
  omega

theorem pres_end {c : Ctx} {a : Al} (hA : AF c a) {B ℓ p : Nat} (h : Pres c a B ℓ p) :
    ℓ ≤ bEnd c a B ∧ ∃ q, Pres c a B (bEnd c a B) q := by
  obtain ⟨j, m, hj, hr, hp, he⟩ := Pres.idx hA h
  have hlen : j < (mem c a B).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlast : (mem c a B).length - 1 < (mem c a B).length := by omega
  have hget := List.getElem?_eq_getElem hlast
  have hm := members_rank hA c.layers.length B h.1 ((mem c a B).length - 1) _ hget
  refine ⟨by unfold bEnd; omega, c.pos[(mem c a B)[(mem c a B).length - 1]]!, h.1, h.2.1,
    (mem c a B)[(mem c a B).length - 1], List.mem_of_getElem? hget, ?_, rfl⟩
  unfold bEnd
  omega

theorem consec_up {c : Ctx} {a : Al} (hA : AF c a) {A m m' : Nat} (hf : A ∈ c.layers.flatten)
    (hm : m ∈ mem c a A) (hm' : m' ∈ mem c a A) (hr : c.rank[m']! = c.rank[m]! + 1) :
    a.up m' = some m := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hm'
  have h1 := members_rank hA c.layers.length A hf j m hj
  have h2 := members_rank hA c.layers.length A hf j' m' hj'
  have : j' = j + 1 := by omega
  subst this
  exact (hA.down_iff m' m).mp (members_down c.layers.length A j m m' hj hj')

theorem adj_cons {c : Ctx} {a : Al} (hA : AF c a) {A B mA mA' mB mB' : Nat} (hAB : A ≠ B)
    (hrA : a.root A = A) (hrB : a.root B = B) (hAf : A ∈ c.layers.flatten)
    (hBf : B ∈ c.layers.flatten) (hmA : mA ∈ mem c a A) (hmA' : mA' ∈ mem c a A)
    (hmB : mB ∈ mem c a B) (hmB' : mB' ∈ mem c a B)
    (hr1 : c.rank[mA']! = c.rank[mA]! + 1) (hr2 : c.rank[mB']! = c.rank[mB]! + 1)
    (hr3 : c.rank[mA]! = c.rank[mB]!) (hlt : c.pos[mA]! < c.pos[mB]!) :
    c.pos[mA']! < c.pos[mB']! := by
  have hupA := consec_up hA hAf hmA hmA' hr1
  have hupB := consec_up hA hBf hmB hmB' hr2
  have hrk : c.rank[mA']! = c.rank[mB']! := by omega
  rcases Nat.lt_trichotomy c.pos[mA']! c.pos[mB']! with h | h | h
  · exact h
  · exfalso
    have hf1 := members_flat hA c.layers.length A mA' hmA' hAf
    have hf2 := members_flat hA c.layers.length B mB' hmB' hBf
    have := node_unique hA.lay hf1 hf2 hrk h
    have e1 := members_root hA c.layers.length A mA' hmA'
    have e2 := members_root hA c.layers.length B mB' hmB'
    rw [this, e2, hrB] at e1
    exact hAB (by rw [hrA] at e1; exact e1.symm)
  · exfalso
    have := hA.up_mono mB' mA' mB mA hupB hupA hrk.symm h
    omega

theorem cons_dist {c : Ctx} {a : Al} (hA : AF c a) {A B : Nat} (hAB : A ≠ B) :
    ∀ (d ℓ p q p' q' : Nat), Pres c a A ℓ p → Pres c a B ℓ q → Pres c a A (ℓ + d) p' →
      Pres c a B (ℓ + d) q' → p < q → p' < q' := by
  intro d
  induction d with
  | zero =>
    intro ℓ p q p' q' h1 h2 h3 h4 hlt
    have e1 := pres_unique hA h1 h3
    have e2 := pres_unique hA h2 h4
    omega
  | succ d ih =>
    intro ℓ p q p' q' h1 h2 h3 h4 hlt
    obtain ⟨p'', hp''⟩ := pres_mid hA h1 h3 (show ℓ ≤ ℓ + d by omega) (by omega)
    obtain ⟨q'', hq''⟩ := pres_mid hA h2 h4 (show ℓ ≤ ℓ + d by omega) (by omega)
    have hlt'' := ih ℓ p q p'' q'' h1 h2 hp'' hq'' hlt
    obtain ⟨hAf, hrA, mA, hmA, hrkA, hpA⟩ := hp''
    obtain ⟨hBf, hrB, mB, hmB, hrkB, hpB⟩ := hq''
    obtain ⟨_, _, mA', hmA', hrkA', hpA'⟩ := h3
    obtain ⟨_, _, mB', hmB', hrkB', hpB'⟩ := h4
    have := adj_cons hA hAB hrA hrB hAf hBf hmA hmA' hmB hmB' (by omega) (by omega)
      (by omega) (by omega)
    omega

theorem pres_ne {c : Ctx} {a : Al} (hA : AF c a) {A B ℓ p : Nat} (hAB : A ≠ B)
    (h1 : Pres c a A ℓ p) (h2 : Pres c a B ℓ p) : False := by
  obtain ⟨hAf, hrA, mA, hmA, hrkA, hpA⟩ := h1
  obtain ⟨hBf, hrB, mB, hmB, hrkB, hpB⟩ := h2
  have hf1 := members_flat hA c.layers.length A mA hmA hAf
  have hf2 := members_flat hA c.layers.length B mB hmB hBf
  have := node_unique hA.lay hf1 hf2 (by omega) (by omega)
  have e1 := members_root hA c.layers.length A mA hmA
  have e2 := members_root hA c.layers.length B mB hmB
  rw [this, e2, hrB, hrA] at e1
  exact hAB e1.symm

theorem pres_cons {c : Ctx} {a : Al} (hA : AF c a) {A B : Nat} (hAB : A ≠ B) (ℓ ℓ' p q p' q' : Nat)
    (h1 : Pres c a A ℓ p) (h2 : Pres c a B ℓ q) (h3 : Pres c a A ℓ' p')
    (h4 : Pres c a B ℓ' q') (hlt : p < q) : p' < q' := by
  rcases Nat.le_total ℓ ℓ' with hle | hle
  · exact cons_dist hA hAB (ℓ' - ℓ) ℓ p q p' q' h1 h2 (by rwa [Nat.add_sub_cancel' hle])
      (by rwa [Nat.add_sub_cancel' hle]) hlt
  · rcases Nat.lt_trichotomy p' q' with h | h | h
    · exact h
    · exfalso
      exact pres_ne hA hAB (h ▸ h3) h4 |>.elim
    · exfalso
      have := cons_dist hA (Ne.symm hAB) (ℓ - ℓ') ℓ' q' p' q p h4 h3
        (by rwa [Nat.add_sub_cancel' hle]) (by rwa [Nat.add_sub_cancel' hle]) h
      omega

theorem tg_mono {β : Type} {R S : β → β → Prop} (h : ∀ x y, R x y → S x y) {a b : β}
    (t : Relation.TransGen R a b) : Relation.TransGen S a b := by
  induction t with
  | single hab => exact Relation.TransGen.single (h _ _ hab)
  | tail _ hbc ih => exact Relation.TransGen.tail ih (h _ _ hbc)


theorem root_root {c : Ctx} {a : Al} (hA : AF c a) {p : Nat} (hp : p ∈ c.layers.flatten) :
    a.root (a.root p) = a.root p := by
  have ht := root_top hA _ p hp rfl
  have h := hA.root_eq (a.root p) ht.1
  simp only [ht.2.1] at h
  exact h

def Rabs (c : Ctx) (a : Al) (x y : Nat) : Prop :=
  ∃ ℓ p q, Pres c a x ℓ p ∧ Pres c a y ℓ q ∧ p < q

theorem bg_rabs {c : Ctx} {a : Al} (hA : AF c a) {x y : Nat} (h : BG c a x y) : Rabs c a x y := by
  obtain ⟨p, q, hcons, hx, hy⟩ := h
  obtain ⟨hpn, hqn⟩ := cons_mem hcons
  obtain ⟨l, hl, hz⟩ := hcons
  obtain ⟨i, hia, hib⟩ := mem_zip_tail_iff.mp hz
  obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hl
  have h1 := hA.lay.idx i0 l i p hi0 hia
  have h2 := hA.lay.idx i0 l (i + 1) q hi0 hib
  refine ⟨i0, i, i + 1, ?_, ?_, by omega⟩
  · rw [← hx]
    exact ⟨(root_top hA _ p hpn rfl).1, root_root hA hpn, p, node_mem hA _ p hpn rfl, h1.1, h1.2⟩
  · rw [← hy]
    exact ⟨(root_top hA _ q hqn rfl).1, root_root hA hqn, q, node_mem hA _ q hqn rfl, h2.1, h2.2⟩

theorem rabs_acyc {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ u, ¬ Relation.TransGen (Rabs c a) u u :=
  abs_acyclic (Pres c a) (bEnd c a)
    (fun B ℓ p q h1 h2 => pres_unique hA h1 h2)
    (fun B ℓ ℓ' ℓ'' h1 h2 hl hr => by
      obtain ⟨p, hp⟩ := h1
      obtain ⟨p', hp'⟩ := h2
      exact pres_mid hA hp hp' hl hr)
    (fun B ℓ p h => pres_end hA h)
    (fun A B ℓ ℓ' p q p' q' hAB h1 h2 h3 h4 hlt => pres_cons hA hAB ℓ ℓ' p q p' q' h1 h2 h3 h4 hlt)

theorem af_acyc {c : Ctx} {a : Al} (hA : AF c a) :
    ∀ u, ¬ Relation.TransGen (BG c a) u u :=
  fun u hu => rabs_acyc hA u (tg_mono (fun _ _ h => bg_rabs hA h) hu)

theorem wf_of_af {c : Ctx} {a : Al} (hA : AF c a) : Wf c a where
  pred_cons q p h := hA.lay.pred_iff.mp h
  cons_pred p q h := hA.lay.pred_iff.mpr h
  mem_root r m hr hm := by
    rw [members_root hA _ r m hm, hr]
  node_root p hp := ⟨(root_top hA _ p hp rfl).1, root_root hA hp, node_mem hA _ p hp rfl⟩
  mem_node r m hr hm := members_flat hA _ r m hm hr
  acyc := af_acyc hA

theorem qleft {c : Ctx} {a : Al} (hA : AF c a) {Y X : Nat} {ℓ py px : Nat}
    (h : Relation.TransGen (BG c a) Y X) (hy : Pres c a Y ℓ py) (hx : Pres c a X ℓ px) :
    py < px := by
  have hne : Y ≠ X := by
    intro e
    subst e
    exact af_acyc hA Y h
  rcases Nat.lt_trichotomy py px with hlt | heq | hgt
  · exact hlt
  · exact (pres_ne hA hne (heq ▸ hy) hx).elim
  · exfalso
    have hr : Rabs c a X Y := ⟨ℓ, px, py, hx, hy, hgt⟩
    exact rabs_acyc hA X (Relation.TransGen.trans (Relation.TransGen.single hr)
      (tg_mono (fun _ _ h => bg_rabs hA h) h))

theorem findSome_spec {f : Nat → Option Nat} :
    ∀ (ms : List Nat) (b : Nat), ms.findSome? f = some b →
      ∃ (j x : Nat), ms[j]? = some x ∧ f x = some b ∧
        ∀ i, i < j → ∀ (y : Nat), ms[i]? = some y → f y = none := by
  intro ms
  induction ms with
  | nil => intro b h; simp at h
  | cons x xs ih =>
    intro b h
    cases hfx : f x with
    | some b' =>
      rw [List.findSome?_cons, hfx] at h
      cases h
      exact ⟨0, x, by simp, hfx, fun i hi => by omega⟩
    | none =>
      rw [List.findSome?_cons, hfx] at h
      obtain ⟨j, y, hj, hfy, hbef⟩ := ih b h
      refine ⟨j + 1, y, by simpa using hj, hfy, ?_⟩
      intro i hi z hz
      cases i with
      | zero =>
        simp at hz
        rw [← hz]
        exact hfx
      | succ i => exact hbef i (by omega) z (by simpa using hz)

theorem findSome_of {f : Nat → Option Nat} :
    ∀ (ms : List Nat) (j x b : Nat), ms[j]? = some x → f x = some b →
      (∀ i, i < j → ∀ (y : Nat), ms[i]? = some y → f y = none) → ms.findSome? f = some b := by
  intro ms
  induction ms with
  | nil => intro j x b h; simp at h
  | cons z zs ih =>
    intro j x b hj hf hbef
    cases j with
    | zero =>
      simp at hj
      rw [← hj] at hf
      rw [List.findSome?_cons, hf]
    | succ j =>
      have hz : f z = none := hbef 0 (by omega) z (by simp)
      rw [List.findSome?_cons, hz]
      exact ih j x b (by simpa using hj) hf (fun i hi y hy => hbef (i + 1) (by omega) y (by simpa using hy))

theorem mem_head {c : Ctx} {a : Al} (hA : AF c a) {n : Nat} (hn : n ∈ c.layers.flatten) :
    (mem c a n)[0]? = some n := by
  have hlt := hA.lay.rank_lt hn
  unfold mem
  cases hF : c.layers.length with
  | zero => omega
  | succ f => simp [members]

theorem left_exists {c : Ctx} (hL : Lay c) {n : Nat} (hn : n ∈ c.layers.flatten)
    (hpos : c.pos[n]! ≠ 0) :
    ∃ n', c.pred n = some n' ∧ n' ∈ c.layers.flatten ∧ c.rank[n']! = c.rank[n]! ∧
      c.pos[n']! + 1 = c.pos[n]! := by
  obtain ⟨l, hl, hnl⟩ := hL.loc hn
  obtain ⟨k, hk⟩ : ∃ k, c.pos[n]! = k + 1 := ⟨c.pos[n]! - 1, by omega⟩
  have hlen : c.pos[n]! < l.length := (List.getElem?_eq_some_iff.mp hnl).1
  have hk' : k < l.length := by omega
  have hget := List.getElem?_eq_getElem hk'
  have hn'mem : l[k] ∈ l := List.getElem_mem hk'
  have hlmem : l ∈ c.layers := List.mem_of_getElem? hl
  have hn'f : l[k] ∈ c.layers.flatten := List.mem_flatten.mpr ⟨l, hlmem, hn'mem⟩
  have hidx := hL.idx (c.rank[n]!) l k l[k] hl hget
  refine ⟨l[k], ?_, hn'f, hidx.1, by omega⟩
  rw [hL.pred_iff]
  refine ⟨l, hlmem, mem_zip_tail_iff.mpr ⟨k, hget, ?_⟩⟩
  rw [← hk]
  exact hnl

theorem pos_zero_of_pred_none {c : Ctx} (hL : Lay c) {s : Nat} (hs : s ∈ c.layers.flatten)
    (h : c.pred s = none) : c.pos[s]! = 0 := by
  by_cases h0 : c.pos[s]! = 0
  · exact h0
  · obtain ⟨n', hn', _⟩ := left_exists hL hs h0
    rw [h] at hn'
    cases hn'

theorem closed_root {c : Ctx} {a : Al} {st : PS} (hA : AF c a)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {n : Nat}
    (hn : n ∈ c.layers.flatten) : Closed a [] st (a.root n) :=
  ⟨root_root hA hn, hall _ (root_top hA _ n hn rfl).1 (root_root hA hn), by simp⟩

theorem sink_node {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {n : Nat}
    (hn : n ∈ c.layers.flatten) : st.sink n = st.sink (a.root n) := by
  have hc := closed_root hA hall hn
  rcases hG.set_ (a.root n) hc.1 hc.2.1 with hin | hdone
  · simp at hin
  · exact (hdone n (node_mem hA _ n hn rfl)).2.2

theorem fp_some {c : Ctx} {a : Al} {st : PS} (hG : GInv c a [] st) {r pr0 : Nat}
    (hr : Closed a [] st r) (h : c.firstPred (mem c a r) = some pr0) :
    st.sink r = st.sink (a.root pr0) := by
  rcases hG.fp r hr with ⟨h1, _⟩ | ⟨pr, h1, _, h3⟩
  · rw [h1] at h
    cases h
  · rw [h1] at h
    cases h
    exact h3

theorem new_root_sink {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {w w' : Nat}
    (hw : w ∈ c.layers.flatten) (hup : a.up w = none) (hpred : c.pred w = some w') :
    st.sink w = st.sink w' := by
  have hroot : a.root w = w := by
    have h := hA.root_eq w hw
    simp only [hup] at h
    exact h
  have hfp : c.firstPred (mem c a w) = some w' := by
    unfold Ctx.firstPred
    refine findSome_of (mem c a w) 0 w w' (mem_head hA hw) hpred ?_
    intro i hi
    omega
  have hcl := closed_root hA hall hw
  rw [hroot] at hcl
  have h1 := fp_some hG hcl hfp
  have hw'f : w' ∈ c.layers.flatten := (cons_mem (hA.lay.pred_iff.mp hpred)).1
  rw [h1, sink_node hA hG hall hw'f]

theorem cons_rank {c : Ctx} (hL : Lay c) {p q : Nat} (h : Cons c p q) :
    c.rank[p]! = c.rank[q]! ∧ c.pos[p]! + 1 = c.pos[q]! := by
  obtain ⟨l, hl, hz⟩ := h
  obtain ⟨i, hia, hib⟩ := mem_zip_tail_iff.mp hz
  obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.mp hl
  have h1 := hL.idx i0 l i p hi0 hia
  have h2 := hL.idx i0 l (i + 1) q hi0 hib
  omega

theorem mem_rank_ge {c : Ctx} {a : Al} (hA : AF c a) {Y m : Nat} (hY : Y ∈ c.layers.flatten)
    (hm : m ∈ mem c a Y) : c.rank[Y]! ≤ c.rank[m]! := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hm
  have := members_rank hA c.layers.length Y hY j m hj
  omega

theorem pres_top {c : Ctx} {a : Al} (hA : AF c a) {B : Nat} (hB : B ∈ c.layers.flatten)
    (hr : a.root B = B) : Pres c a B (c.rank[B]!) (c.pos[B]!) :=
  ⟨hB, hr, B, List.mem_of_getElem? (mem_head hA hB), rfl, rfl⟩

theorem pres_node {c : Ctx} {a : Al} (hA : AF c a) {n : Nat} (hn : n ∈ c.layers.flatten) :
    Pres c a (a.root n) (c.rank[n]!) (c.pos[n]!) :=
  ⟨(root_top hA _ n hn rfl).1, root_root hA hn, n, node_mem hA _ n hn rfl, rfl, rfl⟩

theorem chain_T {c : Ctx} {a : Al} (hA : AF c a) {c0 ℓ : Nat} (hc0 : c0 ∈ c.layers.flatten)
    (hr0 : a.root c0 = c0) (hrk : c.rank[c0]! = ℓ) (hp0 : c.pos[c0]! = 0) :
    ∀ Y s, Chain c a Y s → Y ∈ c.layers.flatten → a.root Y = Y →
      (Y = c0 ∨ Relation.TransGen (BG c a) Y c0) → ℓ ≤ c.rank[Y]! → ℓ ≤ c.rank[s]! := by
  intro Y s hch
  induction hch with
  | stop _ =>
    intro _ _ _ h
    exact h
  | @step r pr s hfp hch ih =>
    intro hrf hrr hrel hl
    obtain ⟨w, hw, hwp⟩ := firstPred_some hfp
    have hcons := hA.lay.pred_iff.mp hwp
    obtain ⟨hprf, hwf⟩ := cons_mem hcons
    have hB'f := (root_top hA _ pr hprf rfl).1
    have hB'r := root_root hA hprf
    have hbg : BG c a (a.root pr) r := bg_of_pred (wf_of_af hA) hrr hw hwp
    have hT : Relation.TransGen (BG c a) (a.root pr) c0 := by
      rcases hrel with h | h
      · rw [← h]
        exact Relation.TransGen.single hbg
      · exact Relation.TransGen.trans (Relation.TransGen.single hbg) h
    have hrw := mem_rank_ge hA hrf hw
    have hcr := (cons_rank hA.lay hcons).1
    have hlt : ℓ ≤ c.rank[a.root pr]! := by
      refine Classical.byContradiction fun hn => ?_
      have hP1 := pres_top hA hB'f hB'r
      have hP2 := pres_node hA hprf
      obtain ⟨q, hq⟩ := pres_mid hA hP1 hP2 (show c.rank[a.root pr]! ≤ ℓ by omega)
        (show ℓ ≤ c.rank[pr]! by omega)
      have hP0 : Pres c a c0 ℓ 0 := by
        have := pres_top hA hc0 hr0
        rw [hrk, hp0] at this
        exact this
      have := qleft hA hT hq hP0
      omega
    exact ih hB'f hB'r (Or.inr hT) hlt

theorem chain_U {c : Ctx} {a : Al} (hA : AF c a) {X ℓ px : Nat} (hX : Pres c a X ℓ px)
    (H1 : ∀ n, n ∈ c.layers.flatten → c.rank[n]! = ℓ → c.pos[n]! < px → a.up n = none) :
    ∀ Y s, Chain c a Y s → Y ∈ c.layers.flatten → a.root Y = Y →
      Relation.TransGen (BG c a) Y X → c.rank[Y]! + 1 ≤ ℓ → c.rank[s]! + 1 ≤ ℓ := by
  intro Y s hch
  induction hch with
  | stop _ =>
    intro _ _ _ h
    exact h
  | @step r pr s hfp hch ih =>
    intro hrf hrr hT hl
    obtain ⟨w, hw, hwp⟩ := firstPred_some hfp
    have hcons := hA.lay.pred_iff.mp hwp
    obtain ⟨hprf, hwf⟩ := cons_mem hcons
    have hB'f := (root_top hA _ pr hprf rfl).1
    have hB'r := root_root hA hprf
    have hbg : BG c a (a.root pr) r := bg_of_pred (wf_of_af hA) hrr hw hwp
    have hT' : Relation.TransGen (BG c a) (a.root pr) X :=
      Relation.TransGen.trans (Relation.TransGen.single hbg) hT
    have hcr := (cons_rank hA.lay hcons).1
    have hwl : c.rank[w]! + 1 ≤ ℓ := by
      refine Classical.byContradiction fun hn => ?_
      have hP1 := pres_top hA hrf hrr
      have hP2 : Pres c a r (c.rank[w]!) (c.pos[w]!) := ⟨hrf, hrr, w, hw, rfl, rfl⟩
      obtain ⟨q, hq⟩ := pres_mid hA hP1 hP2 (show c.rank[r]! ≤ ℓ by omega)
        (show ℓ ≤ c.rank[w]! by omega)
      have hlt := qleft hA hT hq hX
      obtain ⟨_, _, y, hy, hyr, hyp⟩ := hq
      have hyf := members_flat hA _ r y hy hrf
      have hup := H1 y hyf hyr (by omega)
      have hry := hA.root_eq y hyf
      simp only [hup] at hry
      have hy2 := members_root hA _ r y hy
      rw [hry, hrr] at hy2
      rw [hy2] at hyr
      omega
    have hB'rk : c.rank[a.root pr]! ≤ c.rank[pr]! := (root_top hA _ pr hprf rfl).2.2
    exact ih hB'f hB'r hT' (by omega)

theorem sink_up {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {v v0 : Nat}
    (hup : a.up v = some v0) : st.sink v = st.sink v0 := by
  have hr := hA.up_rank v v0 hup
  have h := hA.root_eq v hr.2.2
  simp only [hup] at h
  rw [sink_node hA hG hall hr.2.2, sink_node hA hG hall hr.2.1, h]

theorem run_eq {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {ℓ : Nat} :
    ∀ (d u w : Nat), u ∈ c.layers.flatten → w ∈ c.layers.flatten → c.rank[u]! = ℓ →
      c.rank[w]! = ℓ → c.pos[w]! = c.pos[u]! + d →
      (∀ z, z ∈ c.layers.flatten → c.rank[z]! = ℓ → c.pos[u]! < c.pos[z]! →
        c.pos[z]! ≤ c.pos[w]! → a.up z = none) → st.sink w = st.sink u := by
  intro d
  induction d with
  | zero =>
    intro u w hu hw hru hrw hp _
    have := node_unique hA.lay hw hu (by omega) (by omega)
    rw [this]
  | succ d ih =>
    intro u w hu hw hru hrw hp hz
    obtain ⟨w', hpred, hw'f, hw'r, hw'p⟩ := left_exists hA.lay hw (by omega)
    have hup := hz w hw hrw (by omega) (Nat.le_refl _)
    rw [new_root_sink hA hG hall hw hup hpred]
    exact ih u w' hu hw'f hru (by omega) (by omega)
      (fun z hzf hzr h1 h2 => hz z hzf hzr h1 (by omega))

theorem cont_case {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {ℓ : Nat}
    (hprev : ∀ u0 v0, u0 ∈ c.layers.flatten → v0 ∈ c.layers.flatten → c.rank[u0]! + 1 = ℓ →
      c.rank[v0]! + 1 = ℓ → c.pos[u0]! ≤ c.pos[v0]! → c.rank[st.sink v0]! ≤ c.rank[st.sink u0]!)
    {u v u0 : Nat} (hru : c.rank[u]! = ℓ) (hrv : c.rank[v]! = ℓ) (hup : a.up u = some u0)
    (hupv : a.up v ≠ none) (hlt : c.pos[u]! < c.pos[v]!) :
    c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
  cases hvv : a.up v with
  | none => exact absurd hvv hupv
  | some v0 =>
    have h1 := hA.up_rank u u0 hup
    have h2 := hA.up_rank v v0 hvv
    have hm := hA.up_mono u v u0 v0 hup hvv (by omega) hlt
    have := hprev u0 v0 h1.2.1 h2.2.1 (by omega) (by omega) (by omega)
    rw [sink_up hA hG hall hup, sink_up hA hG hall hvv]
    exact this

theorem root0_case {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {ℓ : Nat} {u v : Nat}
    (hu : u ∈ c.layers.flatten) (hv : v ∈ c.layers.flatten) (hru : c.rank[u]! = ℓ)
    (hrv : c.rank[v]! = ℓ) (hup : a.up u = none) (hpos0 : c.pos[u]! = 0)
    (hlt : c.pos[u]! < c.pos[v]!)
    (hbet : ∀ z, z ∈ c.layers.flatten → c.rank[z]! = ℓ → c.pos[u]! < c.pos[z]! →
      c.pos[z]! < c.pos[v]! → a.up z = none) :
    c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
  obtain ⟨vL, hpredv, hvLf, hvLr, hvLp⟩ := left_exists hA.lay hv (by omega)
  have hBf : a.root v ∈ c.layers.flatten := (root_top hA _ v hv rfl).1
  have hBr : a.root (a.root v) = a.root v := root_root hA hv
  have hvmem : v ∈ mem c a (a.root v) := node_mem hA _ v hv rfl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hvmem
  have hjrank := members_rank hA c.layers.length (a.root v) hBf j v hj
  have hfpne : ∃ pr, c.firstPred (mem c a (a.root v)) = some pr := by
    cases h : c.firstPred (mem c a (a.root v)) with
    | some pr => exact ⟨pr, rfl⟩
    | none =>
      exfalso
      unfold Ctx.firstPred at h
      have := List.findSome?_eq_none_iff.mp h v hvmem
      rw [hpredv] at this
      cases this
  obtain ⟨prs, hfp⟩ := hfpne
  have hcl := closed_root hA hall hv
  have hsinkB := fp_some hG hcl hfp
  have hsv := sink_node hA hG hall hv
  obtain ⟨js, xs, hjs, hfs, hbef⟩ := findSome_spec (f := c.pred) (mem c a (a.root v)) prs hfp
  have hjsj : js ≤ j := by
    refine Classical.byContradiction fun hn => ?_
    have := hbef j (by omega) v hj
    rw [hpredv] at this
    cases this
  by_cases hjj : js = j
  · subst hjj
    rw [hj] at hjs
    cases hjs
    rw [hpredv] at hfs
    cases hfs
    have hs1 : st.sink v = st.sink vL := by
      rw [hsv, hsinkB, sink_node hA hG hall hvLf]
    have hs2 := run_eq hA hG hall (ℓ := ℓ) (c.pos[vL]! - c.pos[u]!) u vL hu hvLf hru
      (by omega) (by omega)
      (fun z hzf hzr h1 h2 => hbet z hzf hzr h1 (by omega))
    rw [hs1, hs2]
    exact Nat.le_refl _
  · have hjsj' : js < j := by omega
    have hxsmem : xs ∈ mem c a (a.root v) := List.mem_of_getElem? hjs
    have hxsrank := members_rank hA c.layers.length (a.root v) hBf js xs hjs
    have hcons := hA.lay.pred_iff.mp hfs
    obtain ⟨hprf, hxsf⟩ := cons_mem hcons
    have hcr := (cons_rank hA.lay hcons).1
    have hB'f := (root_top hA _ prs hprf rfl).1
    have hB'r := root_root hA hprf
    have hB'rk : c.rank[a.root prs]! ≤ c.rank[prs]! := (root_top hA _ prs hprf rfl).2.2
    have hbg : BG c a (a.root prs) (a.root v) := bg_of_pred (wf_of_af hA) hBr hxsmem hfs
    have hX : Pres c a (a.root v) ℓ (c.pos[v]!) := by
      have := pres_node hA hv
      rw [hrv] at this
      exact this
    have H1 : ∀ n, n ∈ c.layers.flatten → c.rank[n]! = ℓ → c.pos[n]! < c.pos[v]! →
        a.up n = none := by
      intro n hn hrn hpn
      by_cases hp : c.pos[n]! = c.pos[u]!
      · have := node_unique hA.lay hn hu (by omega) hp
        rw [this]
        exact hup
      · exact hbet n hn hrn (by omega) hpn
    have hchain := hG.chain (a.root prs) (closed_root hA hall hprf)
    have hUres := chain_U hA hX H1 (a.root prs) (st.sink (a.root prs)) hchain hB'f hB'r
      (Relation.TransGen.single hbg) (by omega)
    have hrootu : a.root u = u := by
      have h := hA.root_eq u hu
      simp only [hup] at h
      exact h
    have hcu := closed_root hA hall hu
    rw [hrootu] at hcu
    have hchu := hG.chain u hcu
    have hT := chain_T hA hu hrootu hru hpos0 u (st.sink u) hchu hu hrootu (Or.inl rfl)
      (by omega)
    rw [hsv, hsinkB]
    omega

theorem gprime {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {ℓ : Nat}
    (hprev : ∀ u0 v0, u0 ∈ c.layers.flatten → v0 ∈ c.layers.flatten → c.rank[u0]! + 1 = ℓ →
      c.rank[v0]! + 1 = ℓ → c.pos[u0]! ≤ c.pos[v0]! → c.rank[st.sink v0]! ≤ c.rank[st.sink u0]!) :
    ∀ (k u v : Nat), u ∈ c.layers.flatten → v ∈ c.layers.flatten → c.rank[u]! = ℓ →
      c.rank[v]! = ℓ → c.pos[u]! = k → c.pos[u]! < c.pos[v]! → a.up v ≠ none →
      (∀ z, z ∈ c.layers.flatten → c.rank[z]! = ℓ → c.pos[u]! < c.pos[z]! →
        c.pos[z]! < c.pos[v]! → a.up z = none) →
      c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
  intro k
  induction k with
  | zero =>
    intro u v hu hv hru hrv hk hlt hupv hbet
    cases hupu : a.up u with
    | some u0 => exact cont_case hA hG hall hprev hru hrv hupu hupv hlt
    | none => exact root0_case hA hG hall hu hv hru hrv hupu hk hlt hbet
  | succ k ih =>
    intro u v hu hv hru hrv hk hlt hupv hbet
    cases hupu : a.up u with
    | some u0 => exact cont_case hA hG hall hprev hru hrv hupu hupv hlt
    | none =>
      obtain ⟨u', hpred, hu'f, hu'r, hu'p⟩ := left_exists hA.lay hu (by omega)
      have hs := new_root_sink hA hG hall hu hupu hpred
      have := ih u' v hu'f hv (by omega) hrv (by omega) (by omega) hupv (by
        intro z hzf hzr h1 h2
        by_cases hz : c.pos[z]! = c.pos[u]!
        · have := node_unique hA.lay hzf hu (by omega) hz
          rw [this]
          exact hupu
        · exact hbet z hzf hzr (by omega) h2)
      rw [hs]
      exact this

theorem adj_case {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {ℓ : Nat}
    (hprev : ∀ u0 v0, u0 ∈ c.layers.flatten → v0 ∈ c.layers.flatten → c.rank[u0]! + 1 = ℓ →
      c.rank[v0]! + 1 = ℓ → c.pos[u0]! ≤ c.pos[v0]! → c.rank[st.sink v0]! ≤ c.rank[st.sink u0]!)
    {a1 b1 : Nat} (ha : a1 ∈ c.layers.flatten) (hb : b1 ∈ c.layers.flatten)
    (hra : c.rank[a1]! = ℓ) (hrb : c.rank[b1]! = ℓ) (hp : c.pos[a1]! + 1 = c.pos[b1]!) :
    c.rank[st.sink b1]! ≤ c.rank[st.sink a1]! := by
  cases hupb : a.up b1 with
  | none =>
    obtain ⟨b', hpred, hb'f, hb'r, hb'p⟩ := left_exists hA.lay hb (by omega)
    have := node_unique hA.lay hb'f ha (by omega) (by omega)
    rw [this] at hpred
    rw [new_root_sink hA hG hall hb hupb hpred]
    exact Nat.le_refl _
  | some b0 =>
    exact gprime hA hG hall hprev (c.pos[a1]!) a1 b1 ha hb hra hrb rfl (by omega)
      (by rw [hupb]; exact Option.some_ne_none b0)
      (fun z _ _ h1 h2 => by omega)

theorem mono_all {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) :
    ∀ (ℓ u v : Nat), u ∈ c.layers.flatten → v ∈ c.layers.flatten → c.rank[u]! = ℓ →
      c.rank[v]! = ℓ → c.pos[u]! ≤ c.pos[v]! → c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
  intro ℓ
  induction ℓ with
  | zero =>
    have hprev : ∀ u0 v0, u0 ∈ c.layers.flatten → v0 ∈ c.layers.flatten →
        c.rank[u0]! + 1 = 0 → c.rank[v0]! + 1 = 0 → c.pos[u0]! ≤ c.pos[v0]! →
        c.rank[st.sink v0]! ≤ c.rank[st.sink u0]! := by
      intro u0 v0 _ _ h
      omega
    have key : ∀ (d u v : Nat), u ∈ c.layers.flatten → v ∈ c.layers.flatten → c.rank[u]! = 0 →
        c.rank[v]! = 0 → c.pos[v]! = c.pos[u]! + d → c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
      intro d
      induction d with
      | zero =>
        intro u v hu hv hru hrv hp
        have := node_unique hA.lay hv hu (by omega) (by omega)
        rw [this]
        exact Nat.le_refl _
      | succ d ih =>
        intro u v hu hv hru hrv hp
        obtain ⟨w, _, hwf, hwr, hwp⟩ := left_exists hA.lay hv (by omega)
        have h1 := adj_case hA hG hall hprev hwf hv (by omega) hrv hwp
        have h2 := ih u w hu hwf hru (by omega) (by omega)
        omega
    intro u v hu hv hru hrv hp
    exact key (c.pos[v]! - c.pos[u]!) u v hu hv hru hrv (by omega)
  | succ ℓ ih =>
    have hprev : ∀ u0 v0, u0 ∈ c.layers.flatten → v0 ∈ c.layers.flatten →
        c.rank[u0]! + 1 = ℓ + 1 → c.rank[v0]! + 1 = ℓ + 1 → c.pos[u0]! ≤ c.pos[v0]! →
        c.rank[st.sink v0]! ≤ c.rank[st.sink u0]! :=
      fun u0 v0 hu0 hv0 h1 h2 h3 => ih u0 v0 hu0 hv0 (by omega) (by omega) h3
    have key : ∀ (d u v : Nat), u ∈ c.layers.flatten → v ∈ c.layers.flatten →
        c.rank[u]! = ℓ + 1 → c.rank[v]! = ℓ + 1 → c.pos[v]! = c.pos[u]! + d →
        c.rank[st.sink v]! ≤ c.rank[st.sink u]! := by
      intro d
      induction d with
      | zero =>
        intro u v hu hv hru hrv hp
        have := node_unique hA.lay hv hu (by omega) (by omega)
        rw [this]
        exact Nat.le_refl _
      | succ d ih2 =>
        intro u v hu hv hru hrv hp
        obtain ⟨w, _, hwf, hwr, hwp⟩ := left_exists hA.lay hv (by omega)
        have h1 := adj_case hA hG hall hprev hwf hv (by omega) hrv hwp
        have h2 := ih2 u w hu hwf hru (by omega) (by omega)
        omega
    intro u v hu hv hru hrv hp
    exact key (c.pos[v]! - c.pos[u]!) u v hu hv hru hrv (by omega)

theorem chain_end {c : Ctx} {a : Al} {r s : Nat} (h : Chain c a r s) :
    c.firstPred (mem c a s) = none := by
  induction h with
  | stop h => exact h
  | step _ _ ih => exact ih

theorem sink_facts {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {n : Nat}
    (hn : n ∈ c.layers.flatten) : st.sink n ∈ c.layers.flatten ∧ c.pos[st.sink n]! = 0 := by
  have hc := closed_root hA hall hn
  have hs := hG.sinks _ hc
  have hsn : st.sink n ∈ c.layers.flatten := by
    rw [sink_node hA hG hall hn]
    exact hG.inL _ hs.1.2.1
  refine ⟨hsn, ?_⟩
  have hch := hG.chain _ hc
  have hfp := chain_end hch
  rw [sink_node hA hG hall hn]
  have hsn' : st.sink (a.root n) ∈ c.layers.flatten := by
    rw [← sink_node hA hG hall hn]
    exact hsn
  apply pos_zero_of_pred_none hA.lay hsn'
  unfold Ctx.firstPred at hfp
  exact List.findSome?_eq_none_iff.mp hfp _ (List.mem_of_getElem? (mem_head hA hsn'))

theorem x_node {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) {n : Nat}
    (hn : n ∈ c.layers.flatten) : st.x n = st.x (a.root n) := by
  have hc := closed_root hA hall hn
  rcases hG.set_ (a.root n) hc.1 hc.2.1 with hin | hdone
  · simp at hin
  · exact (hdone n (node_mem hA _ n hn rfl)).2.1

theorem same_sep {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) :
    ∀ l ∈ c.layers, ∀ ab ∈ l.zip l.tail, st.sink ab.1 = st.sink ab.2 →
      st.x ab.1 + c.sep ab.1 ab.2 ≤ st.x ab.2 := by
  intro l hl ab hz hs
  obtain ⟨p, q⟩ := ab
  have hcons : Cons c p q := ⟨l, hl, hz⟩
  obtain ⟨hpf, hqf⟩ := cons_mem hcons
  have hd2 := (hG.d2 (a.root q) (closed_root hA hall hqf) p q hcons rfl).2
  simp only [] at hs ⊢
  rw [sink_node hA hG hall hpf, sink_node hA hG hall hqf] at hs
  rw [x_node hA hG hall hpf, x_node hA hG hall hqf]
  exact hd2 hs

theorem pairs_rank {c : Ctx} {a : Al} {st : PS} (hA : AF c a) (hG : GInv c a [] st)
    (hall : ∀ v ∈ c.layers.flatten, a.root v = v → st.isSet v = true) :
    ∀ q ∈ allPairs c st, PairRank c st q := by
  intro q hq
  obtain ⟨⟨l, hl, hz⟩, hne⟩ := mem_allPairs.mp hq
  obtain ⟨p, q'⟩ := q
  simp only [] at hne
  have hcons : Cons c p q' := ⟨l, hl, hz⟩
  obtain ⟨hpf, hqf⟩ := cons_mem hcons
  obtain ⟨hr, hp⟩ := cons_rank hA.lay hcons
  have hle := mono_all hA hG hall (c.rank[p]!) p q' hpf hqf rfl hr.symm (by omega)
  obtain ⟨hsf1, hp1⟩ := sink_facts hA hG hall hpf
  obtain ⟨hsf2, hp2⟩ := sink_facts hA hG hall hqf
  have hlt : c.rank[st.sink q']! < c.rank[st.sink p]! := by
    refine Nat.lt_of_le_of_ne hle (fun heq => hne ?_)
    exact node_unique hA.lay hsf1 hsf2 heq.symm (by omega)
  refine ⟨hlt, ?_⟩
  obtain ⟨l', hl', hs'⟩ := hA.lay.loc hsf2
  cases l' with
  | nil => simp at hs'
  | cons s rest => exact ⟨s, rest, hl'⟩

def tr (r : Nat) : Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | j, v :: vs => (v, r, j) :: tr r (j + 1) vs

def trs : Nat → List (List Nat) → List (Nat × Nat × Nat)
  | _, [] => []
  | r, l :: ls => tr r 0 l ++ trs (r + 1) ls

theorem tr_map (r : Nat) : ∀ (vs : List Nat) (j : Nat), (tr r j vs).map (·.1) = vs := by
  intro vs
  induction vs with
  | nil => intro j; rfl
  | cons v vs ih => intro j; simp [tr, ih]

theorem trs_map : ∀ (ls : List (List Nat)) (r : Nat), (trs r ls).map (·.1) = ls.flatten := by
  intro ls
  induction ls with
  | nil => intro r; rfl
  | cons l ls ih => intro r; simp [trs, tr_map, ih]

theorem mem_tr (r : Nat) : ∀ (vs : List Nat) (j jj v : Nat), vs[jj]? = some v →
    (v, r, j + jj) ∈ tr r j vs := by
  intro vs
  induction vs with
  | nil => intro j jj v h; simp at h
  | cons x xs ih =>
    intro j jj v h
    cases jj with
    | zero =>
      simp at h
      subst h
      simp [tr]
    | succ jj =>
      simp only [List.getElem?_cons_succ] at h
      have := ih (j + 1) jj v h
      simp only [tr, List.mem_cons]
      right
      rw [show j + (jj + 1) = j + 1 + jj by omega]
      exact this

theorem mem_trs : ∀ (ls : List (List Nat)) (r ii : Nat) (l : List Nat) (jj v : Nat),
    ls[ii]? = some l → l[jj]? = some v → (v, r + ii, jj) ∈ trs r ls := by
  intro ls
  induction ls with
  | nil => intro r ii l jj v h; simp at h
  | cons x xs ih =>
    intro r ii l jj v h1 h2
    cases ii with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      rw [← h1] at h2
      have := mem_tr r x 0 jj v h2
      simp only [trs, List.mem_append]
      left
      simpa using this
    | succ ii =>
      simp only [List.getElem?_cons_succ] at h1
      have := ih (r + 1) ii l jj v h1 h2
      simp only [trs, List.mem_append]
      right
      rw [show r + (ii + 1) = r + 1 + ii by omega]
      exact this

structure SInv (p : Proper) (s : Array Nat × Array Bool) (T : List (Nat × Nat × Nat)) : Prop where
  size1 : s.1.size = p.nodes.length
  size2 : s.2.size = p.nodes.length
  ok : ∀ t ∈ T, t.1 < p.nodes.length ∧ rk p.rank t.1 = (t.2.1 : Int) ∧ s.2[t.1]! = true
  seen : ∀ v, s.2[v]! = true → v ∈ T.map (·.1)
  nodup : (T.map (·.1)).Nodup

theorem sinv_init (p : Proper) :
    SInv p (Array.replicate p.nodes.length 0, Array.replicate p.nodes.length false) [] := by
  refine ⟨by simp, by simp, by simp, ?_, by simp⟩
  intro v h
  by_cases hv : v < p.nodes.length
  · simp [hv] at h
  · simp [hv] at h

theorem sinv_step {p : Proper} {s : Array Nat × Array Bool} {T : List (Nat × Nat × Nat)}
    {r j v : Nat} (hs : SInv p s T) (hc : ¬ (p.nodes.length ≤ v ∨ s.2[v]! = true ∨
      rk p.rank v ≠ (r : Int))) :
    SInv p (s.1.set! v j, s.2.set! v true) (T ++ [(v, r, j)]) := by
  have hv : v < p.nodes.length := by
    simp only [not_or] at hc
    omega
  have hsv : s.2[v]! = false := by
    simp only [not_or] at hc
    simpa using hc.2.1
  have hrk : rk p.rank v = (r : Int) := by
    simp only [not_or] at hc
    exact Classical.not_not.mp hc.2.2
  have hnot : v ∉ T.map (·.1) := by
    intro hm
    obtain ⟨t, ht, e⟩ := List.mem_map.mp hm
    have := (hs.ok t ht).2.2
    rw [e, hsv] at this
    cases this
  refine ⟨by rw [Array.size_set!]; exact hs.size1, by rw [Array.size_set!]; exact hs.size2, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · have h1 := hs.ok t ht
      have hne : v ≠ t.1 := by
        intro e
        apply hnot
        exact List.mem_map.mpr ⟨t, ht, e.symm⟩
      refine ⟨h1.1, h1.2.1, ?_⟩
      show (s.2.set! v true)[t.1]! = true
      rw [Array.getElem!_set!_ne _ _ _ _ hne]
      exact h1.2.2
    · simp at ht
      subst ht
      refine ⟨hv, hrk, ?_⟩
      show (s.2.set! v true)[v]! = true
      exact Array.getElem!_set!_self _ _ _ (by rw [hs.size2]; exact hv)
  · intro u hu
    by_cases huv : u = v
    · subst huv
      simp
    · have : s.2[u]! = true := by
        have h : (s.2.set! v true)[u]! = true := hu
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm huv)] at h
        exact h
      have := hs.seen u this
      simp only [List.map_append, List.mem_append]
      exact Or.inl this
  · simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨hs.nodup, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    intro e
    subst e
    exact hnot ha

theorem layerStep_spec {p : Proper} (r : Nat) :
    ∀ (vs : List Nat) (j : Nat) (s s' : Array Nat × Array Bool) (T : List (Nat × Nat × Nat)),
      layerStep p p.nodes.length r j vs s = .ok s' → SInv p s T → SInv p s' (T ++ tr r j vs) := by
  intro vs
  induction vs with
  | nil =>
    intro j s s' T h hs
    simp only [layerStep, Except.ok.injEq] at h
    subst h
    simpa [tr] using hs
  | cons v vs ih =>
    intro j s s' T h hs
    simp only [layerStep] at h
    by_cases hc : (p.nodes.length ≤ v ∨ s.2[v]! = true ∨ rk p.rank v ≠ (r : Int))
    · rw [ite_eq_left hc] at h
      cases h
    · rw [ite_eq_right hc] at h
      have := ih (j + 1) _ s' (T ++ [(v, r, j)]) h (sinv_step hs hc)
      simpa [tr, List.append_assoc] using this

theorem layersStep_spec {p : Proper} :
    ∀ (ls : List (List Nat)) (r : Nat) (s s' : Array Nat × Array Bool)
      (T : List (Nat × Nat × Nat)),
      layersStep p p.nodes.length r ls s = .ok s' → SInv p s T → SInv p s' (T ++ trs r ls) := by
  intro ls
  induction ls with
  | nil =>
    intro r s s' T h hs
    simp only [layersStep, Except.ok.injEq] at h
    subst h
    simpa [trs] using hs
  | cons l ls ih =>
    intro r s s' T h hs
    simp only [layersStep] at h
    cases h1 : layerStep p p.nodes.length r 0 l s with
    | error e =>
      rw [h1] at h
      cases h
    | ok s1 =>
      rw [h1] at h
      have h2 := layerStep_spec r l 0 s s1 T h1 hs
      have h3 := ih (r + 1) s1 s' (T ++ tr r 0 l) h h2
      simpa [trs, List.append_assoc] using h3

theorem layerPositions_spec {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    (h : layerPositions p layers = .ok pos) :
    layers.flatten.Nodup ∧
      (∀ (i : Nat) (l : List Nat) (v : Nat), layers[i]? = some l → v ∈ l →
        rk p.rank v = (i : Int)) ∧
      (∀ v, v < p.nodes.length → v ∈ layers.flatten) := by
  unfold layerPositions at h
  cases hs : layersStep p p.nodes.length 0 layers
      (Array.replicate p.nodes.length 0, Array.replicate p.nodes.length false) with
  | error e =>
    rw [hs] at h
    cases h
  | ok s =>
    rw [hs] at h
    simp only [] at h
    by_cases hany : s.2.any (fun b => !b) = true
    · rw [ite_eq_left hany] at h
      cases h
    · have hSI := layersStep_spec layers 0 _ s [] hs (sinv_init p)
      simp only [List.nil_append] at hSI
      have hall : ∀ (i : Nat) (hi : i < s.2.size), s.2[i] = true := by
        intro i hi
        have h0 := Array.any_eq_false.mp (Bool.eq_false_iff.mpr hany) i hi
        simpa using h0
      refine ⟨?_, ?_, ?_⟩
      · have := hSI.nodup
        rwa [trs_map] at this
      · intro i l v hl hv
        obtain ⟨jj, hj⟩ := List.mem_iff_getElem?.mp hv
        have hm := mem_trs layers 0 i l jj v hl hj
        have := (hSI.ok _ hm).2.1
        simpa using this
      · intro v hv
        have h1 : s.2[v]! = true := by
          have hi : v < s.2.size := by rw [hSI.size2]; exact hv
          rw [getElem!_pos s.2 v hi]
          exact hall v hi
        have := hSI.seen v h1
        rwa [trs_map] at this

theorem checkEdges_spec {p : Proper} (h : checkEdges p = .ok ()) :
    ∀ e ∈ p.edges, e.tail < p.nodes.length ∧ e.head < p.nodes.length ∧
      rk p.rank e.head = rk p.rank e.tail + 1 := by
  unfold checkEdges at h
  by_cases hall : p.edges.all (fun e =>
      decide (e.tail < p.nodes.length) && decide (e.head < p.nodes.length) &&
        decide (rk p.rank e.head = rk p.rank e.tail + 1)) = true
  · intro e he
    have := List.all_eq_true.mp hall e he
    have h : (e.tail < p.nodes.length ∧ e.head < p.nodes.length) ∧
        rk p.rank e.head = rk p.rank e.tail + 1 := by simpa using this
    exact ⟨h.1.1, h.1.2, h.2⟩
  · rw [ite_eq_right hall] at h
    cases h

theorem flatten_map_perm {f : List Nat → List Nat} :
    ∀ (L : List (List Nat)), (∀ l ∈ L, (f l).Perm l) → (L.map f).flatten.Perm L.flatten := by
  intro L
  induction L with
  | nil => intro _; exact List.Perm.refl _
  | cons l ls ih =>
    intro h
    simp only [List.map_cons, List.flatten_cons]
    exact List.Perm.append (h l List.mem_cons_self)
      (ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')))

theorem flatten_reverse_perm : ∀ (L : List (List Nat)), L.reverse.flatten.Perm L.flatten := by
  intro L
  induction L with
  | nil => exact List.Perm.refl _
  | cons l ls ih =>
    simp only [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    exact List.perm_append_comm.trans (List.Perm.append_left l ih)

theorem passLayers_perm (layers : List (List Nat)) (k : Nat) :
    (passLayers layers k).flatten.Perm layers.flatten := by
  unfold passLayers
  have h1 : ((if 2 ≤ k then layers.reverse else layers).map
      fun l => if k % 2 = 1 then l.reverse else l).flatten.Perm
      (if 2 ≤ k then layers.reverse else layers).flatten := by
    apply flatten_map_perm
    intro l _
    split
    · exact List.reverse_perm l
    · exact List.Perm.refl _
  refine h1.trans ?_
  split
  · exact flatten_reverse_perm layers
  · exact List.Perm.refl _

theorem passLayers_length (layers : List (List Nat)) (k : Nat) :
    (passLayers layers k).length = layers.length := by
  unfold passLayers
  rw [List.length_map]
  split
  · exact List.length_reverse
  · rfl

theorem passLayers_get (layers : List (List Nat)) (k : Nat) {i : Nat} {l : List Nat}
    (hl : layers[i]? = some l) :
    ∃ l0, (passLayers layers k)[if 2 ≤ k then layers.length - 1 - i else i]? = some l0 ∧
      ∀ v, v ∈ l0 ↔ v ∈ l := by
  have hi : i < layers.length := (List.getElem?_eq_some_iff.mp hl).1
  unfold passLayers
  by_cases hk : 2 ≤ k
  · have hrev : (layers.reverse)[layers.length - 1 - i]? = some l := by
      rw [List.getElem?_reverse (by omega)]
      have : layers.length - 1 - (layers.length - 1 - i) = i := by omega
      rw [this]
      exact hl
    refine ⟨(fun l => if k % 2 = 1 then l.reverse else l) l, ?_, ?_⟩
    · simp only [hk, ite_true, List.getElem?_map, hrev]
      simp
    · intro v
      split
      · simp
      · exact Iff.rfl
  · refine ⟨(fun l => if k % 2 = 1 then l.reverse else l) l, ?_, ?_⟩
    · simp only [hk, ite_false, List.getElem?_map, hl]
      simp
    · intro v
      split
      · simp
      · exact Iff.rfl

structure RInv (n : Nat) (acc : Array Nat × Array Nat) (T : List (Nat × Nat × Nat)) : Prop where
  size1 : acc.1.size = n
  size2 : acc.2.size = n
  ok : ∀ t ∈ T, t.1 < n ∧ acc.1[t.1]! = t.2.1 ∧ acc.2[t.1]! = t.2.2
  unset : ∀ v, v ∉ T.map (·.1) → acc.2[v]! = 0

theorem rinv_init (n : Nat) : RInv n (Array.replicate n 0, Array.replicate n 0) [] := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro v _
  by_cases hv : v < n
  · simp [hv]
  · simp [hv]

theorem posStep_spec {n : Nat} (i : Nat) :
    ∀ (vs : List Nat) (j : Nat) (acc : Array Nat × Array Nat) (T : List (Nat × Nat × Nat)),
      RInv n acc T → (∀ v ∈ vs, v < n) → ((T ++ tr i j vs).map (·.1)).Nodup →
      RInv n (posStep i j vs acc) (T ++ tr i j vs) := by
  intro vs
  induction vs with
  | nil =>
    intro j acc T hs _ _
    simpa [posStep, tr] using hs
  | cons v vs ih =>
    intro j acc T hs hlt hnd
    simp only [posStep]
    have hv : v < n := hlt v List.mem_cons_self
    have hnd' : ((T ++ [(v, i, j)] ++ tr i (j + 1) vs).map (·.1)).Nodup := by
      simpa [tr, List.append_assoc] using hnd
    have hnot : v ∉ T.map (·.1) := by
      have := hnd
      simp only [tr, List.map_append, List.map_cons] at this
      rw [List.nodup_append] at this
      obtain ⟨_, h2, h3⟩ := this
      intro hm
      exact h3 v hm v (by simp) rfl
    have hS : RInv n (acc.1.set! v i, acc.2.set! v j) (T ++ [(v, i, j)]) := by
      refine ⟨by rw [Array.size_set!]; exact hs.size1, by rw [Array.size_set!]; exact hs.size2,
        ?_, ?_⟩
      · intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · have h1 := hs.ok t ht
          have hne : v ≠ t.1 := by
            intro e
            apply hnot
            exact List.mem_map.mpr ⟨t, ht, e.symm⟩
          refine ⟨h1.1, ?_, ?_⟩
          · show (acc.1.set! v i)[t.1]! = t.2.1
            rw [Array.getElem!_set!_ne _ _ _ _ hne]
            exact h1.2.1
          · show (acc.2.set! v j)[t.1]! = t.2.2
            rw [Array.getElem!_set!_ne _ _ _ _ hne]
            exact h1.2.2
        · simp at ht
          subst ht
          refine ⟨hv, ?_, ?_⟩
          · exact Array.getElem!_set!_self _ _ _ (by rw [hs.size1]; exact hv)
          · exact Array.getElem!_set!_self _ _ _ (by rw [hs.size2]; exact hv)
      · intro u hu
        have hu1 : u ≠ v ∧ u ∉ T.map (·.1) := by
          simp only [List.map_append, List.mem_append, not_or, List.map_cons, List.map_nil,
            List.mem_singleton] at hu
          exact ⟨hu.2, hu.1⟩
        show (acc.2.set! v j)[u]! = 0
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hu1.1)]
        exact hs.unset u hu1.2
    have := ih (j + 1) _ (T ++ [(v, i, j)]) hS (fun w hw => hlt w (List.mem_cons_of_mem _ hw)) hnd'
    simpa [tr, List.append_assoc] using this

theorem rankStep_spec {n : Nat} :
    ∀ (ls : List (List Nat)) (i : Nat) (acc : Array Nat × Array Nat)
      (T : List (Nat × Nat × Nat)), RInv n acc T → (∀ v ∈ ls.flatten, v < n) →
      ((T ++ trs i ls).map (·.1)).Nodup → RInv n (rankStep i ls acc) (T ++ trs i ls) := by
  intro ls
  induction ls with
  | nil =>
    intro i acc T hs _ _
    simpa [rankStep, trs] using hs
  | cons l ls ih =>
    intro i acc T hs hlt hnd
    simp only [rankStep]
    have hnd1 : ((T ++ tr i 0 l).map (·.1)).Nodup := by
      have : (T ++ tr i 0 l ++ trs (i + 1) ls) = T ++ trs i (l :: ls) := by
        simp [trs, List.append_assoc]
      have h2 : ((T ++ tr i 0 l ++ trs (i + 1) ls).map (·.1)).Nodup := by rw [this]; exact hnd
      simp only [List.map_append] at h2 ⊢
      exact h2.sublist (List.sublist_append_left _ _)
    have hS := posStep_spec i l 0 acc T hs
      (fun v hv => hlt v (by simp [hv])) (by simpa using hnd1) 
    have hnd2 : ((T ++ tr i 0 l ++ trs (i + 1) ls).map (·.1)).Nodup := by
      have : (T ++ tr i 0 l ++ trs (i + 1) ls) = T ++ trs i (l :: ls) := by
        simp [trs, List.append_assoc]
      rw [this]
      exact hnd
    have := ih (i + 1) _ (T ++ tr i 0 l) hS (fun v hv => hlt v (by simp [hv])) hnd2
    simpa [trs, List.append_assoc] using this

theorem rankPos_spec {n : Nat} {ls : List (List Nat)} (hlt : ∀ v ∈ ls.flatten, v < n)
    (hnd : ls.flatten.Nodup) :
    (∀ (i : Nat) (l : List Nat) (j v : Nat), ls[i]? = some l → l[j]? = some v →
      (rankPos n ls).1[v]! = i ∧ (rankPos n ls).2[v]! = j) ∧
    (∀ v, v ∉ ls.flatten → (rankPos n ls).2[v]! = 0) := by
  have hnd0 : ((trs 0 ls).map (·.1)).Nodup := by
    simpa [trs_map] using hnd
  have hnd' : (([] ++ trs 0 ls).map (fun t : Nat × Nat × Nat => t.1)).Nodup := by
    simpa using hnd0
  have hS := rankStep_spec ls 0 _ [] (rinv_init n) hlt hnd'
  simp only [List.nil_append] at hS
  refine ⟨?_, ?_⟩
  · intro i l j v hl hv
    have hm := mem_trs ls 0 i l j v hl hv
    have := hS.ok _ hm
    simp only [Nat.zero_add] at this
    exact this.2
  · intro v hv
    apply hS.unset
    rwa [trs_map]

def EdgeOK (c : Ctx) : Prop :=
  ∀ e, e < c.edges.size →
    c.edges[e]!.tail ∈ c.layers.flatten ∧ c.edges[e]!.head ∈ c.layers.flatten ∧
      (c.rank[c.edges[e]!.head]! = c.rank[c.edges[e]!.tail]! + 1 ∨
        c.rank[c.edges[e]!.tail]! = c.rank[c.edges[e]!.head]! + 1)

theorem mem_upperEdges {edges : Array ProperEdge} {rank pos : Array Nat} {v e : Nat}
    (h : e ∈ upperEdges edges rank pos v) :
    e < edges.size ∧
      ((edges[e]!.head = v ∧ rank[edges[e]!.tail]! < rank[v]!) ∨
        (edges[e]!.tail = v ∧ rank[edges[e]!.head]! < rank[v]!)) := by
  unfold upperEdges at h
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
  have hx' := List.mem_mergeSort.mp hx
  obtain ⟨i, hi, hix⟩ := List.mem_map.mp hx'
  have hie : i = e := by rw [← hxe, ← hix]
  subst hie
  have := List.mem_filter.mp hi
  obtain ⟨hr, hp⟩ := this
  refine ⟨List.mem_range.mp hr, ?_⟩
  simpa using hp

theorem alignPick_spec {c : Ctx} (hE : EdgeOK c) {v : Nat} {last : Int} {w : Nat}
    (h : alignPick c v last = some w) :
    c.rank[w]! + 1 = c.rank[v]! ∧ w ∈ c.layers.flatten ∧ last < (c.pos[w]! : Int) := by
  unfold alignPick at h
  obtain ⟨kk, _, hk⟩ := List.exists_of_findSome?_eq_some h
  cases hes : (upperEdges c.edges c.rank c.pos v)[kk]? with
  | none =>
    rw [hes] at hk
    cases hk
  | some e =>
    rw [hes] at hk
    simp only [Option.bind_some] at hk
    by_cases hc : (!c.marked[e]! && decide (last < (c.pos[otherEnd c.edges[e]! v]! : Int))) = true
    · rw [ite_eq_left hc] at hk
      cases hk
      have hlast : last < (c.pos[otherEnd c.edges[e]! v]! : Int) := by
        have h' : c.marked[e]! = false ∧ last < (c.pos[otherEnd c.edges[e]! v]! : Int) := by
          simpa using hc
        exact h'.2
      have hme := mem_upperEdges (List.mem_of_getElem? hes)
      obtain ⟨hesz, hcase⟩ := hme
      obtain ⟨ht, hh, hadj⟩ := hE e hesz
      refine ⟨?_, ?_, hlast⟩
      · unfold otherEnd
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hnt : (c.edges[e]!.tail == v) = false := by
            have : c.edges[e]!.tail ≠ v := by
              intro e2
              rw [e2, ← h1] at h2
              omega
            simpa using this
          rw [hnt]
          simp only [Bool.false_eq_true, ite_false]
          rw [h1] at hadj
          omega
        · have hnt : (c.edges[e]!.tail == v) = true := by simpa using h1
          rw [hnt]
          simp only [ite_true]
          rw [h1] at hadj
          omega
      · unfold otherEnd
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hnt : (c.edges[e]!.tail == v) = false := by
            have : c.edges[e]!.tail ≠ v := by
              intro e2
              rw [e2, ← h1] at h2
              omega
            simpa using this
          rw [hnt]
          simpa using ht
        · have hnt : (c.edges[e]!.tail == v) = true := by simpa using h1
          rw [hnt]
          simpa using hh
    · rw [ite_eq_right hc] at hk
      cases hk

def Pr (c : Ctx) (i : Nat) (pre : List Nat) (v : Nat) : Prop :=
  v ∈ c.layers.flatten ∧ (c.rank[v]! < i ∨ v ∈ pre)

structure AInv (c : Ctx) (i : Nat) (pre : List Nat) (a : Al) (last : Int) : Prop where
  up_rank : ∀ v w, a.up v = some w →
    c.rank[w]! + 1 = c.rank[v]! ∧ w ∈ c.layers.flatten ∧ Pr c i pre v
  unproc : ∀ v, ¬ Pr c i pre v → a.up v = none ∧ a.root v = v
  down_iff : ∀ v w, a.down w = some v ↔ a.up v = some w
  root_eq : ∀ v, Pr c i pre v → a.root v = (match a.up v with | some w => a.root w | none => v)
  mono : ∀ v1 v2 w1 w2, a.up v1 = some w1 → a.up v2 = some w2 → c.rank[v1]! = c.rank[v2]! →
    c.pos[v1]! < c.pos[v2]! → c.pos[w1]! < c.pos[w2]!
  lastb : ∀ v w, v ∈ pre → a.up v = some w → (c.pos[w]! : Int) ≤ last
  lastmin : -1 ≤ last

theorem alignNode_none {c : Ctx} {a : Al} {last : Int} {v : Nat}
    (hp : alignPick c v last = none) : alignNode c (a, last) v = (a, last) := by
  simp [alignNode, hp]

theorem alignNode_some {c : Ctx} {a : Al} {last : Int} {v w : Nat}
    (hp : alignPick c v last = some w) :
    alignNode c (a, last) v =
      ({ up := upd a.up v (some w), down := upd a.down w (some v),
         root := upd a.root v (a.root w) }, (c.pos[w]! : Int)) := by
  simp [alignNode, hp]

theorem alignNode_inv {c : Ctx} (hE : EdgeOK c) {i : Nat} {pre : List Nat} {a : Al} {last : Int}
    {v : Nat} (hI : AInv c i pre a last) (hv : v ∈ c.layers.flatten) (hrv : c.rank[v]! = i)
    (hnp : v ∉ pre)
    (hpre : ∀ v' ∈ pre, v' ∈ c.layers.flatten ∧ c.rank[v']! = i ∧ c.pos[v']! < c.pos[v]!) :
    AInv c i (pre ++ [v]) (alignNode c (a, last) v).1 (alignNode c (a, last) v).2 := by
  have hnPr : ¬ Pr c i pre v := by
    rintro ⟨_, h | h⟩
    · omega
    · exact hnp h
  have hupv := (hI.unproc v hnPr).1
  have hrootv := (hI.unproc v hnPr).2
  have prMono : ∀ u, Pr c i pre u → Pr c i (pre ++ [v]) u :=
    fun u hu => ⟨hu.1, hu.2.imp_right (fun h => List.mem_append_left _ h)⟩
  have hvPr : Pr c i (pre ++ [v]) v := ⟨hv, Or.inr (by simp)⟩
  cases hp : alignPick c v last with
  | none =>
    rw [alignNode_none hp]
    dsimp only
    refine ⟨?_, ?_, hI.down_iff, ?_, hI.mono, ?_, hI.lastmin⟩
    · intro v' w' h
      obtain ⟨h1, h2, h3⟩ := hI.up_rank v' w' h
      exact ⟨h1, h2, prMono v' h3⟩
    · intro u hu
      exact hI.unproc u (fun h => hu (prMono u h))
    · intro u hu
      by_cases huv : u = v
      · rw [huv, hupv, hrootv]
      · apply hI.root_eq
        refine ⟨hu.1, ?_⟩
        rcases hu.2 with h2 | h2
        · exact Or.inl h2
        · rcases List.mem_append.mp h2 with h2 | h2
          · exact Or.inr h2
          · simp at h2
            exact absurd h2 huv
    · intro v' w' hv' hup
      rcases List.mem_append.mp hv' with h | h
      · exact hI.lastb v' w' h hup
      · simp at h
        rw [h, hupv] at hup
        cases hup
  | some w =>
    obtain ⟨hrw, hwf, hlast⟩ := alignPick_spec hE hp
    rw [alignNode_some hp]
    dsimp only
    have hwv : w ≠ v := by
      intro h
      rw [h] at hrw
      omega
    have hno : ∀ v'', a.up v'' ≠ some w := by
      intro v'' h
      obtain ⟨h1, h2, h3⟩ := hI.up_rank v'' w h
      have hr'' : c.rank[v'']! = i := by omega
      rcases h3.2 with h4 | h4
      · omega
      · have := hI.lastb v'' w h4 h
        omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v' w' h
      by_cases hv' : v' = v
      · simp only [upd, hv', ite_true, Option.some.injEq] at h
        rw [← h, hv']
        exact ⟨hrw, hwf, hvPr⟩
      · simp only [upd, hv', ite_false] at h
        obtain ⟨h1, h2, h3⟩ := hI.up_rank v' w' h
        exact ⟨h1, h2, prMono v' h3⟩
    · intro u hu
      have huv : u ≠ v := fun h => hu (h ▸ hvPr)
      have := hI.unproc u (fun h => hu (prMono u h))
      simpa [upd, huv] using this
    · intro v' w'
      by_cases h1 : w' = w <;> by_cases h2 : v' = v
      · have e1 : (upd a.down w (some v)) w' = some v := by simp [upd, h1]
        have e2 : (upd a.up v (some w)) v' = some w := by simp [upd, h2]
        show (upd a.down w (some v)) w' = some v' ↔ (upd a.up v (some w)) v' = some w'
        rw [e1, e2, h1, h2]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
      · have e1 : (upd a.down w (some v)) w' = some v := by simp [upd, h1]
        have e2 : (upd a.up v (some w)) v' = a.up v' := by simp [upd, h2]
        show (upd a.down w (some v)) w' = some v' ↔ (upd a.up v (some w)) v' = some w'
        rw [e1, e2, h1]
        constructor
        · intro hh
          exact absurd (Option.some.inj hh).symm h2
        · intro hh
          exact absurd hh (hno v')
      · have e1 : (upd a.down w (some v)) w' = a.down w' := by simp [upd, h1]
        have e2 : (upd a.up v (some w)) v' = some w := by simp [upd, h2]
        show (upd a.down w (some v)) w' = some v' ↔ (upd a.up v (some w)) v' = some w'
        rw [e1, e2, h2]
        constructor
        · intro hh
          have := (hI.down_iff v w').mp hh
          rw [hupv] at this
          cases this
        · intro hh
          exact absurd (Option.some.inj hh).symm h1
      · have e1 : (upd a.down w (some v)) w' = a.down w' := by simp [upd, h1]
        have e2 : (upd a.up v (some w)) v' = a.up v' := by simp [upd, h2]
        show (upd a.down w (some v)) w' = some v' ↔ (upd a.up v (some w)) v' = some w'
        rw [e1, e2]
        exact hI.down_iff v' w'
    · intro u hu
      by_cases huv : u = v
      · rw [huv]
        simp [upd, hwv]
      · have hu1 : Pr c i pre u := by
          refine ⟨hu.1, ?_⟩
          rcases hu.2 with h2 | h2
          · exact Or.inl h2
          · rcases List.mem_append.mp h2 with h2 | h2
            · exact Or.inr h2
            · simp at h2
              exact absurd h2 huv
        have hr := hI.root_eq u hu1
        cases hu' : a.up u with
        | none =>
          rw [hu'] at hr
          simp only [upd, huv, ite_false, hu']
          exact hr
        | some w'' =>
          rw [hu'] at hr
          obtain ⟨hh1, hh2, hh3⟩ := hI.up_rank u w'' hu'
          have hw'' : w'' ≠ v := by
            intro e
            rw [e] at hh1
            rcases hu1.2 with h | h
            · omega
            · have := (hpre u h).2.1
              omega
          simp only [upd, huv, hw'', ite_false, hu']
          exact hr
    · intro v1 v2 w1 w2 h1 h2 hr hp'
      by_cases e1 : v1 = v <;> by_cases e2 : v2 = v
      · rw [e1, e2] at hp'
        omega
      · simp only [upd, e2, ite_false] at h2
        obtain ⟨_, _, h3⟩ := hI.up_rank v2 w2 h2
        rcases h3.2 with h4 | h4
        · rw [e1] at hr
          omega
        · have := (hpre v2 h4).2.2
          rw [e1] at hp'
          omega
      · simp only [upd, e1, ite_false] at h1
        simp only [upd, e2, ite_true, Option.some.injEq] at h2
        subst h2
        obtain ⟨_, _, h3⟩ := hI.up_rank v1 w1 h1
        rcases h3.2 with h4 | h4
        · rw [e2] at hr
          omega
        · have := hI.lastb v1 w1 h4 h1
          omega
      · simp only [upd, e1, e2, ite_false] at h1 h2
        exact hI.mono v1 v2 w1 w2 h1 h2 hr hp'
    · intro v' w' hv' hup
      rcases List.mem_append.mp hv' with h | h
      · have hv'v : v' ≠ v := fun e => hnp (e ▸ h)
        simp only [upd, hv'v, ite_false] at hup
        have := hI.lastb v' w' h hup
        omega
      · simp at h
        simp only [upd, h, ite_true, Option.some.injEq] at hup
        rw [← hup]
        exact Int.le_refl _
    · omega

theorem pre_facts {c : Ctx} (hL : Lay c) {i : Nat} {l : List Nat} (hl : c.layers[i]? = some l)
    {pre rest : List Nat} {v : Nat} (h : pre ++ v :: rest = l) :
    v ∈ c.layers.flatten ∧ c.rank[v]! = i ∧ c.pos[v]! = pre.length ∧
      ∀ v' ∈ pre, v' ∈ c.layers.flatten ∧ c.rank[v']! = i ∧ c.pos[v']! < c.pos[v]! := by
  have hlmem : l ∈ c.layers := List.mem_of_getElem? hl
  have hvl : l[pre.length]? = some v := by
    rw [← h]
    simp
  have hv := hL.idx i l pre.length v hl hvl
  refine ⟨List.mem_flatten.mpr ⟨l, hlmem, by rw [← h]; simp⟩, hv.1, hv.2, ?_⟩
  intro v' hv'
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv'
  have hjlt : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjl : l[j]? = some v' := by
    rw [← h, List.getElem?_append_left hjlt]
    exact hj
  have hv' := hL.idx i l j v' hl hjl
  refine ⟨List.mem_flatten.mpr ⟨l, hlmem, List.mem_of_getElem? hjl⟩, hv'.1, ?_⟩
  omega

theorem alignNodes_inv {c : Ctx} (hL : Lay c) (hE : EdgeOK c) {i : Nat} {l : List Nat}
    (hl : c.layers[i]? = some l) :
    ∀ (rest pre : List Nat) (a : Al) (last : Int), pre ++ rest = l → AInv c i pre a last →
      AInv c i l (rest.foldl (alignNode c) (a, last)).1 (rest.foldl (alignNode c) (a, last)).2 := by
  intro rest
  induction rest with
  | nil =>
    intro pre a last h hI
    simp only [List.append_nil] at h
    subst h
    exact hI
  | cons v rest ih =>
    intro pre a last h hI
    obtain ⟨hv, hrv, hpv, hpre⟩ := pre_facts hL hl h
    have hnp : v ∉ pre := by
      intro hm
      have := (hpre v hm).2.2
      omega
    have hI' := alignNode_inv hE hI hv hrv hnp hpre
    simp only [List.foldl_cons]
    exact ih (pre ++ [v]) _ _ (by rw [← h]; simp) hI'

theorem pr_equiv {c : Ctx} (hL : Lay c) {i : Nat} {l : List Nat} (hl : c.layers[i]? = some l)
    {u : Nat} : Pr c (i + 1) [] u ↔ Pr c i l u := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    rcases h with h | h
    · by_cases hlt : c.rank[u]! < i
      · exact Or.inl hlt
      · right
        obtain ⟨l', hl', hul⟩ := hL.loc hu
        have : c.rank[u]! = i := by omega
        rw [this, hl] at hl'
        cases hl'
        exact List.mem_of_getElem? hul
    · simp at h
  · rintro ⟨hu, h⟩
    refine ⟨hu, ?_⟩
    rcases h with h | h
    · exact Or.inl (by omega)
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
      have := hL.idx i l j u hl hj
      exact Or.inl (by omega)

theorem alignLayer_inv {c : Ctx} (hL : Lay c) (hE : EdgeOK c) {i : Nat} {l : List Nat}
    (hl : c.layers[i]? = some l) {a : Al} (hI : AInv c i [] a (-1)) :
    AInv c (i + 1) [] (alignLayer c a l) (-1) := by
  have h := alignNodes_inv hL hE hl l [] a (-1) (by simp) hI
  unfold alignLayer
  have he := fun u => pr_equiv hL hl (u := u)
  refine ⟨?_, ?_, h.down_iff, ?_, h.mono, ?_, Int.le_refl _⟩
  · intro v w hvw
    obtain ⟨h1, h2, h3⟩ := h.up_rank v w hvw
    exact ⟨h1, h2, (he v).mpr h3⟩
  · intro u hu
    exact h.unproc u (fun hh => hu ((he u).mpr hh))
  · intro u hu
    exact h.root_eq u ((he u).mp hu)
  · intro v w hv
    simp at hv

theorem alignLayers_inv {c : Ctx} (hL : Lay c) (hE : EdgeOK c) :
    ∀ (rest done : List (List Nat)) (a : Al), c.layers = done ++ rest →
      AInv c done.length [] a (-1) →
      AInv c c.layers.length [] (rest.foldl (alignLayer c) a) (-1) := by
  intro rest
  induction rest with
  | nil =>
    intro done a h hI
    simp only [List.append_nil] at h
    rw [h]
    exact hI
  | cons l rest ih =>
    intro done a h hI
    have hl : c.layers[done.length]? = some l := by
      rw [h]
      simp
    have hI' := alignLayer_inv hL hE hl hI
    simp only [List.foldl_cons]
    refine ih (done ++ [l]) _ (by rw [h]; simp) ?_
    simpa using hI'

theorem af_of_layout {c : Ctx} (hL : Lay c) (hE : EdgeOK c) : AF c (alignAll c) := by
  have hinit : AInv c ([] : List (List Nat)).length [] Al.init (-1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Int.le_refl _⟩
    · intro v w h
      simp [Al.init] at h
    · intro v _
      simp [Al.init]
    · intro v w
      simp [Al.init]
    · intro v hv
      obtain ⟨_, h⟩ := hv
      simp at h
    · intro v1 v2 w1 w2 h
      simp [Al.init] at h
    · intro v w hv
      simp at hv
  have hI := alignLayers_inv hL hE c.layers [] Al.init (by simp) hinit
  refine ⟨hL, ?_, hI.mono, hI.down_iff, ?_⟩
  · intro v w h
    obtain ⟨h1, h2, h3⟩ := hI.up_rank v w h
    exact ⟨h1, h2, h3.1⟩
  · intro v hv
    exact hI.root_eq v ⟨hv, Or.inl (hL.rank_lt hv)⟩

theorem checkLayers_parts {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    (h : checkLayers p layers = .ok pos) :
    layersInRange p layers = true ∧ (∃ pos', layerPositions p layers = .ok pos') ∧
      checkEdges p = .ok () := by
  unfold checkLayers at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next hs =>
      split at h
      · simp at h
      · next hr =>
        split at h
        · simp at h
        · next pos' hpos =>
          split at h
          · simp at h
          · next hed =>
            exact ⟨by simpa using hr, ⟨pos', hpos⟩, hed⟩

theorem rank_orient {gap : Int} {p : Proper} {layers : List (List Nat)} {marked : Array Bool}
    {k : Nat} (hL : Lay (mkCtx gap p layers marked k)) {i : Nat} {l : List Nat} {v : Nat}
    (hl : layers[i]? = some l) (hv : v ∈ l) :
    (mkCtx gap p layers marked k).rank[v]! =
      (if 2 ≤ k then layers.length - 1 - i else i) := by
  obtain ⟨l0, hl0, hiff⟩ := passLayers_get layers k hl
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ((hiff v).mpr hv)
  exact (hL.idx _ l0 j v hl0 hj).1

theorem ginv_init {c : Ctx} {a : Al} : GInv c a [] PS.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j h
    simp [PS.init] at h
  · intro r _ h
    simp [PS.init] at h
  · intro r _ _
    exact ⟨rfl, rfl⟩
  · intro r hr
    have := hr.2.1
    simp [PS.init] at this
  · intro r hr
    have := hr.2.1
    simp [PS.init] at this
  · intro r hr
    have := hr.2.1
    simp [PS.init] at this
  · intro r hr
    have := hr.2.1
    simp [PS.init] at this

theorem layout_facts {gap : Int} {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    (marked : Array Bool) (k : Nat) (h : checkLayers p layers = .ok pos) :
    Lay (mkCtx gap p layers marked k) ∧ EdgeOK (mkCtx gap p layers marked k) := by
  obtain ⟨hr, ⟨pos', hlp⟩, hce⟩ := checkLayers_parts h
  obtain ⟨hnd, hrk, hcov⟩ := layerPositions_spec hlp
  have hedges := checkEdges_spec hce
  have hperm := passLayers_perm layers k
  have hlt : ∀ v ∈ (passLayers layers k).flatten, v < p.nodes.length := by
    intro v hv
    obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp (hperm.mem_iff.mp hv)
    exact layer_node_lt hr hl hvl
  have hndls : (passLayers layers k).flatten.Nodup := hperm.nodup_iff.mpr hnd
  have hrp := rankPos_spec hlt hndls
  have hL : Lay (mkCtx gap p layers marked k) := by
    refine ⟨?_, ?_⟩
    · intro i l j v hl hv
      exact hrp.1 i l j v hl hv
    · intro v hv
      exact hrp.2 v hv
  refine ⟨hL, ?_⟩
  intro e he
  have he' : e < p.edges.length := by simpa [mkCtx] using he
  have hmem : (mkCtx gap p layers marked k).edges[e]! ∈ p.edges := by
    show p.edges.toArray[e]! ∈ p.edges
    rw [getElem!_pos p.edges.toArray e (by simpa using he')]
    exact List.getElem_mem _
  obtain ⟨h1, h2, h3⟩ := hedges _ hmem
  have hmem1 := hcov _ h1
  have hmem2 := hcov _ h2
  obtain ⟨lt, hlt1, htl⟩ := List.mem_flatten.mp hmem1
  obtain ⟨lh, hlh1, hhl⟩ := List.mem_flatten.mp hmem2
  obtain ⟨it, hit⟩ := List.mem_iff_getElem?.mp hlt1
  obtain ⟨ih, hih⟩ := List.mem_iff_getElem?.mp hlh1
  have hrt := hrk it lt _ hit htl
  have hrh := hrk ih lh _ hih hhl
  have hih' : ih < layers.length := (List.getElem?_eq_some_iff.mp hih).1
  have hit' : it < layers.length := (List.getElem?_eq_some_iff.mp hit).1
  have hrel : ih = it + 1 := by
    rw [hrt, hrh] at h3
    omega
  have hmemflat : ∀ x, x ∈ layers.flatten → x ∈ (mkCtx gap p layers marked k).layers.flatten := by
    intro x hx
    exact hperm.mem_iff.mpr hx
  refine ⟨hmemflat _ hmem1, hmemflat _ hmem2, ?_⟩
  rw [rank_orient hL hit htl, rank_orient hL hih hhl]
  by_cases hk : 2 ≤ k
  · simp only [hk, ite_true]
    right
    omega
  · simp only [hk, ite_false]
    left
    omega

theorem rawPass_separated {gap : Int} {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    {k : Nat} {x : Array Int} (_hg : 1 ≤ gap) (hc : checkLayers p layers = .ok pos)
    (hr : rawPass gap p layers (typeOneConflicts p pos) k = .ok x) (_hk : k < 4) :
    passSeparated gap p layers x = true := by
  obtain ⟨hL, hE⟩ := layout_facts (gap := gap) (typeOneConflicts p pos) k hc
  have hA := af_of_layout hL hE
  have hW := wf_of_af hA
  exact rawPass_separated_of_facts (checkLayers_parts hc).1 hr (by
    intro st hst
    obtain ⟨hG, hall, _⟩ := placeRoots_spec hW _ _ PS.init st (fun v hv => hv) ginv_init hst
    exact ⟨same_sep hA hG hall, pairs_rank hA hG hall⟩)

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
      match rawPass gap p layers marked 0 with
      | .error e => .error e
      | .ok x0 =>
        match rawPass gap p layers marked 1 with
        | .error e => .error e
        | .ok x1 =>
          match rawPass gap p layers marked 2 with
          | .error e => .error e
          | .ok x2 =>
            match rawPass gap p layers marked 3 with
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

def borderMember (p : Proper) (a b : Nat) : Bool :=
  match p.nodes[a]?, p.nodes[b]? with
  | some na, some nb =>
    let pa := na.node.clusterPath
    let pb := nb.node.clusterPath
    let ba := na.node.border == -1 || na.node.border == 1
    let bb := nb.node.border == -1 || nb.node.border == 1
    (ba && (pa.getLast?.any fun c => pb.contains c)) ||
      (bb && (pb.getLast?.any fun c => pa.contains c))
  | _, _ => false

def ownTitleAnchor (p : Proper) (a b : Nat) : Bool :=
  match p.nodes[a]?, p.nodes[b]? with
  | some na, some nb =>
    !na.node.clusterPath.isEmpty && na.node.clusterPath == nb.node.clusterPath &&
      (((na.node.border == -2 || na.node.border == 2) && na.node.w == 0 && nb.node.border == 3) ||
       ((nb.node.border == -2 || nb.node.border == 2) && nb.node.w == 0 && na.node.border == 3))
  | _, _ => false

def clusterGap (nodeGap clusterPad : Int) (p : Proper) (a b : Nat) : Int :=
  if borderMember p a b then clusterPad else if ownTitleAnchor p a b then 0 else nodeGap

def clusterSep (nodeGap clusterPad : Int) (p : Proper) (a b : Nat) : Int :=
  coordSep (clusterGap nodeGap clusterPad p a b) p a b

def borderAlignment (p : Proper) (layers : List (List Nat)) : Proper :=
  let pairs := (layers.zip layers.tail).flatMap fun ls =>
    ls.1.flatMap fun a => ls.2.filterMap fun b =>
      let na := (p.nodes.getD a default).node
      let nb := (p.nodes.getD b default).node
      if (na.border == -1 || na.border == 1) && na.border == nb.border &&
          na.clusterPath == nb.clusterPath then
        some ({ tail := a, head := b, decl := na.decl, original := 0 } : ProperEdge)
      else none
  { p with edges := p.edges ++ pairs }

def clusterCtx (nodeGap clusterPad : Int) (p : Proper) (layers : List (List Nat))
    (marked : Array Bool) (k : Nat) : Ctx :=
  { mkCtx nodeGap p layers marked k with
    pairGap := some (clusterGap nodeGap clusterPad p) }

def clusterPass (nodeGap clusterPad : Int) (p : Proper) (layers : List (List Nat))
    (marked : Array Bool) (k : Nat) : Except LayoutError (Array Int) :=
  runPass (clusterCtx nodeGap clusterPad p layers marked k) (k % 2 == 1)

def crossClusterPasses (nodeGap clusterPad : Int) (p : Proper) (layers : List (List Nat)) :
    Except LayoutError (Array Int × Array Int × Array Int × Array Int) :=
  match checkLayers p layers with
  | .error e => .error e
  | .ok pos =>
    if nodeGap < 1 ∨ clusterPad < 1 then .error .domain
    else
      let marked := typeOneConflicts p pos
      match clusterPass nodeGap clusterPad p layers marked 0 with
      | .error e => .error e
      | .ok x0 =>
        match clusterPass nodeGap clusterPad p layers marked 1 with
        | .error e => .error e
        | .ok x1 =>
          match clusterPass nodeGap clusterPad p layers marked 2 with
          | .error e => .error e
          | .ok x2 =>
            match clusterPass nodeGap clusterPad p layers marked 3 with
            | .error e => .error e
            | .ok x3 => .ok (x0, x1, x2, x3)

def crossCoordsClusterWith (nodeGap clusterPad : Int) (p : Proper)
    (layers : List (List Nat)) : Except LayoutError (List Int) :=
  let aligned := borderAlignment p layers
  if p.nodes.length = 0 then
    match checkLayers aligned layers with
    | .error e => .error e
    | .ok _ => if nodeGap < 1 ∨ clusterPad < 1 then .error .domain else .ok []
  else
    match crossClusterPasses nodeGap clusterPad aligned layers with
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
              exact ⟨by omega, hc.1, hc.2, rawPass_separated (by omega) hpos h0 (by omega),
                rawPass_separated (by omega) hpos h1 (by omega),
                rawPass_separated (by omega) hpos h2 (by omega),
                rawPass_separated (by omega) hpos h3 (by omega)⟩

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
    exact Int.add_nonneg this.1 (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
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



theorem borderMember_symm (p : Proper) (a b : Nat) : borderMember p a b = borderMember p b a := by
  unfold borderMember
  cases p.nodes[a]? <;> cases p.nodes[b]? <;> simp [Bool.or_comm]

theorem ownTitleAnchor_symm (p : Proper) (a b : Nat) :
    ownTitleAnchor p a b = ownTitleAnchor p b a := by
  unfold ownTitleAnchor
  cases p.nodes[a]? <;> cases p.nodes[b]? <;> try rfl
  rename_i na nb
  by_cases he : na.node.clusterPath = nb.node.clusterPath
  · simp [he, Bool.or_comm]
  · apply Bool.eq_iff_iff.mpr
    simp [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, he, Ne.symm he]

theorem clusterSep_symm (ng cp : Int) (p : Proper) (a b : Nat) :
    clusterSep ng cp p a b = clusterSep ng cp p b a := by
  unfold clusterSep coordSep clusterGap
  rw [borderMember_symm p a b, ownTitleAnchor_symm p a b]
  omega

theorem clusterCtx_sep {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {marked : Array Bool} {k a b : Nat} (ha : a < p.nodes.length) (hb : b < p.nodes.length) :
    (clusterCtx ng cp p layers marked k).sep a b = clusterSep ng cp p a b := by
  unfold Ctx.sep clusterSep coordSep clusterCtx mkCtx
  simp only []
  rw [array_map_range_get (nodeW p) ha, array_map_range_get (nodeW p) hb]

theorem clusterPass_separated {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {pos : Array Nat} {k : Nat} {x : Array Int}
    (hc : checkLayers p layers = .ok pos)
    (h : clusterPass ng cp p layers (typeOneConflicts p pos) k = .ok x) :
    ∀ l ∈ layers, ∀ ab ∈ l.zip l.tail,
      clusterSep ng cp p ab.1 ab.2 ≤ x[ab.2]! - x[ab.1]! := by
  let c := clusterCtx ng cp p layers (typeOneConflicts p pos) k
  obtain ⟨hL, hE⟩ := layout_facts (gap := ng) (typeOneConflicts p pos) k hc
  have hLc : Lay c := ⟨hL.idx, hL.unset⟩
  have hEc : EdgeOK c := hE
  have hA := af_of_layout hLc hEc
  have hW := wf_of_af hA
  obtain ⟨st, hst, hx⟩ := runPass_ok h
  obtain ⟨hG, hall, _⟩ := placeRoots_spec hW _ _ PS.init st (fun v hv => hv) ginv_init hst
  have hO := xo_separated (PassFacts.mk (same_sep hA hG hall) (pairs_rank hA hG hall))
  intro l hl ab hab
  obtain ⟨a, b⟩ := ab
  obtain ⟨i, hia, hib⟩ := mem_zip_tail_iff.mp hab
  have hr := (checkLayers_parts hc).1
  have ha : a < p.nodes.length := layer_node_lt hr hl (List.mem_of_getElem? hia)
  have hb : b < p.nodes.length := layer_node_lt hr hl (List.mem_of_getElem? hib)
  have hxa : x[a]! = finalX st (offsetsOf c st) (k % 2 == 1) a - lowest c st (offsetsOf c st) (k % 2 == 1) := by
    rw [hx]
    exact array_map_range_get _ ha
  have hxb : x[b]! = finalX st (offsetsOf c st) (k % 2 == 1) b - lowest c st (offsetsOf c st) (k % 2 == 1) := by
    rw [hx]
    exact array_map_range_get _ hb
  have hmem : l ∈ (if 2 ≤ k then layers.reverse else layers) := by
    split
    · exact List.mem_reverse.mpr hl
    · exact hl
  by_cases hk : k % 2 = 1
  · have hl' : l.reverse ∈ c.layers := by
      show l.reverse ∈ passLayers layers k
      unfold passLayers
      exact List.mem_map.mpr ⟨l, hmem, by simp [hk]⟩
    have hz : (b, a) ∈ l.reverse.zip l.reverse.tail := mem_zip_tail_reverse.mpr hab
    have h1 := hO l.reverse hl' (b, a) hz
    change (clusterCtx ng cp p layers (typeOneConflicts p pos) k).sep b a ≤ _ at h1
    rw [clusterCtx_sep hb ha, clusterSep_symm ng cp p b a] at h1
    rw [hxa, hxb]
    simp only [finalX, hk, beq_self_eq_true, ite_true]
    dsimp only at h1
    omega
  · have hk0 : k % 2 = 0 := by omega
    have hl' : l ∈ c.layers := by
      show l ∈ passLayers layers k
      unfold passLayers
      exact List.mem_map.mpr ⟨l, hmem, by simp [hk0]⟩
    have h1 := hO l hl' (a, b) hab
    change (clusterCtx ng cp p layers (typeOneConflicts p pos) k).sep a b ≤ _ at h1
    rw [clusterCtx_sep ha hb] at h1
    rw [hxa, hxb]
    simp [finalX, hk0]
    dsimp only at h1
    omega

def clusterPassSeparated (ng cp : Int) (p : Proper) (layers : List (List Nat)) (x : Array Int) : Prop :=
  ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
    clusterSep ng cp p a b ≤ x[b]! - x[a]!

theorem crossClusterPasses_spec {ng cp : Int} {p : Proper} {layers : List (List Nat)}
    {x0 x1 x2 x3 : Array Int} (h : crossClusterPasses ng cp p layers = .ok (x0, x1, x2, x3)) :
    1 ≤ ng ∧ 1 ≤ cp ∧ layersInRange p layers = true ∧ sizesNonneg p = true ∧
      clusterPassSeparated ng cp p layers x0 ∧ clusterPassSeparated ng cp p layers x1 ∧
      clusterPassSeparated ng cp p layers x2 ∧ clusterPassSeparated ng cp p layers x3 := by
  unfold crossClusterPasses at h
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
              refine ⟨by omega, by omega, hc.1, hc.2, ?_, ?_, ?_, ?_⟩
              all_goals
                intro l hl i a b ha hb
                first
                | exact clusterPass_separated hpos h0 l hl (a,b) (mem_zip_tail l i a b ha hb)
                | exact clusterPass_separated hpos h1 l hl (a,b) (mem_zip_tail l i a b ha hb)
                | exact clusterPass_separated hpos h2 l hl (a,b) (mem_zip_tail l i a b ha hb)
                | exact clusterPass_separated hpos h3 l hl (a,b) (mem_zip_tail l i a b ha hb)

theorem crossCoordsClusterWith_spec {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    1 ≤ ng ∧ 1 ≤ cp ∧ layersInRange p layers = true ∧ sizesNonneg p = true ∧
      ((p.nodes.length = 0 ∧ xs = []) ∨
        ∃ x0 x1 x2 x3, crossClusterPasses ng cp (borderAlignment p layers) layers = .ok (x0,x1,x2,x3) ∧
          xs = balanceValues p.nodes.length x0 x1 x2 x3) := by
  unfold crossCoordsClusterWith at h
  dsimp only at h
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
        exact ⟨by omega, by omega, hc.1, hc.2, Or.inl ⟨h0, h.symm⟩⟩
  · next h0 =>
    split at h
    · simp at h
    · next x0 x1 x2 x3 hp =>
      have hs := crossClusterPasses_spec hp
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
        Or.inr ⟨x0, x1, x2, x3, hp, balance_ok h⟩⟩

theorem cluster_balance_separated {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      clusterSep ng cp p a b ≤ xs.getD b 0 - xs.getD a 0 := by
  intro layer hl i a b ha hb
  obtain ⟨_, _, hr, _, hcase⟩ := crossCoordsClusterWith_spec h
  have ha' := layers_mem_lt hr hl ha
  have hb' := layers_mem_lt hr hl hb
  rcases hcase with ⟨h0, _⟩ | ⟨x0, x1, x2, x3, hp, hx⟩
  · omega
  · obtain ⟨_, _, _, _, s0, s1, s2, s3⟩ := crossClusterPasses_spec hp
    subst hx
    rw [balanceValues_getD _ _ _ _ _ ha', balanceValues_getD _ _ _ _ _ hb']
    have d0 := s0 layer hl i a b ha hb
    have d1 := s1 layer hl i a b ha hb
    have d2 := s2 layer hl i a b ha hb
    have d3 := s3 layer hl i a b ha hb
    change clusterSep ng cp p a b ≤ _ at d0 d1 d2 d3
    have key := bal4_mono (clusterSep ng cp p a b)
      (x0[a]! + (balanceOffsets x0 x1 x2 x3).o0) (x1[a]! + (balanceOffsets x0 x1 x2 x3).o1)
      (x2[a]! + (balanceOffsets x0 x1 x2 x3).o2) (x3[a]! + (balanceOffsets x0 x1 x2 x3).o3)
      (x0[b]! + (balanceOffsets x0 x1 x2 x3).o0) (x1[b]! + (balanceOffsets x0 x1 x2 x3).o1)
      (x2[b]! + (balanceOffsets x0 x1 x2 x3).o2) (x3[b]! + (balanceOffsets x0 x1 x2 x3).o3)
      (by omega) (by omega) (by omega) (by omega)
    omega

theorem crossCoordsClusterWith_length {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) : xs.length = p.nodes.length := by
  obtain ⟨_, _, _, _, hcase⟩ := crossCoordsClusterWith_spec h
  rcases hcase with ⟨h0, hx⟩ | ⟨x0, x1, x2, x3, _, hx⟩
  · subst hx
    simp [h0]
  · subst hx
    simp [balanceValues]

theorem clusterSep_pos {ng cp : Int} {p : Proper} (hn : 1 ≤ ng) (hp : 1 ≤ cp)
    (hs : sizesNonneg p = true) (a b : Nat) (ht : ownTitleAnchor p a b = false) :
    1 ≤ clusterSep ng cp p a b := by
  apply coordSep_pos (p := p) (gap := clusterGap ng cp p a b) _ hs
  simp only [clusterGap, ht, Bool.false_eq_true, ite_false]
  split <;> assumption

theorem clusterSep_nonneg {ng cp : Int} {p : Proper} (hn : 1 ≤ ng) (hp : 1 ≤ cp)
    (hs : sizesNonneg p = true) (a b : Nat) : 0 ≤ clusterSep ng cp p a b := by
  have ha := nodeW_nonneg hs a
  have hb := nodeW_nonneg hs b
  have hg : 0 ≤ clusterGap ng cp p a b := by
    unfold clusterGap
    split
    · omega
    · split <;> omega
  unfold clusterSep coordSep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide), Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem cluster_coords_order_preserved {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ i a b, layer[i]? = some a → layer[i + 1]? = some b →
      xs.getD a 0 ≤ xs.getD b 0 := by
  intro layer hl i a b ha hb
  have h1 := cluster_balance_separated h layer hl i a b ha hb
  obtain ⟨hn, hp, _, hs, _⟩ := crossCoordsClusterWith_spec h
  have h2 := clusterSep_nonneg hn hp hs a b
  omega

theorem clusterSep_real_real {ng cp : Int} {p : Proper} {a b : Nat} {na nb : ProperNode}
    (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hba : na.node.border = 0) (hbb : nb.node.border = 0) :
    clusterSep ng cp p a b = coordSep ng p a b := by
  simp [clusterSep, clusterGap, borderMember, ownTitleAnchor, ha, hb, hba, hbb]

theorem clusterGap_nonneg {ng cp : Int} (hn : 1 ≤ ng) (hp : 1 ≤ cp) (p : Proper) (a b : Nat) :
    0 ≤ clusterGap ng cp p a b := by
  unfold clusterGap
  split
  · omega
  · split <;> omega

theorem clusterGap_ge_min {ng cp : Int} (p : Proper) (a b : Nat)
    (ht : ownTitleAnchor p a b = false) : min ng cp ≤ clusterGap ng cp p a b := by
  simp only [clusterGap, ht, Bool.false_eq_true, ite_false]
  split <;> omega

theorem cluster_zero_pairs_separated {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    ∀ layer ∈ layers, ∀ (i j a b : Nat), i < j → layer[i]? = some a → layer[j]? = some b →
      Int.fdiv (nodeW p a) 2 + Int.fdiv (nodeW p b) 2 ≤ xs.getD b 0 - xs.getD a 0 := by
  obtain ⟨hn,hp,_,hs,_⟩ := crossCoordsClusterWith_spec h
  intro layer hl i j
  induction j with
  | zero => intro a b hij; omega
  | succ j ih =>
    intro a b hij ha hb
    by_cases he : i = j
    · subst i
      have hd := cluster_balance_separated h layer hl j a b ha hb
      have hg := clusterGap_nonneg hn hp p a b
      unfold clusterSep coordSep at hd
      omega
    · have hj : j < layer.length := by
        have hb_len : j+1 < layer.length := (List.getElem?_eq_some_iff.mp hb).1
        omega
      have hex : ∃ c, layer[j]? = some c := by
        cases hc : layer[j]? with
        | none => have := List.getElem?_eq_none_iff.mp hc; omega
        | some c => exact ⟨c,rfl⟩
      obtain ⟨c,hc⟩ := hex
      have hd := cluster_balance_separated h layer hl j c b hc hb
      have hi := ih a c (by omega) ha hc
      have hg := clusterGap_nonneg hn hp p c b
      unfold clusterSep coordSep at hd
      have hh : 0 ≤ Int.fdiv (nodeW p c) 2 := by
        rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
        exact Int.ediv_nonneg (nodeW_nonneg hs c) (by decide)
      omega

theorem ownTitleAnchor_left_nonanchor {p : Proper} {a b : Nat} {na nb : ProperNode}
    (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hna : na.node.border ≠ -2) (hpa : na.node.border ≠ 2)
    (ht : ownTitleAnchor p a b = true) :
    na.node.border = 3 ∧ na.node.clusterPath = nb.node.clusterPath ∧
      (nb.node.border = -2 ∨ nb.node.border = 2) := by
  simp only [ownTitleAnchor, ha, hb, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with ⟨⟨_, heq⟩, hfirst | hsecond⟩
  · rcases hfirst with ⟨⟨hborder, _⟩, _⟩
    rcases hborder with he | he
    · exact False.elim (hna he)
    · exact False.elim (hpa he)
  · exact ⟨hsecond.2, heq, hsecond.1.1⟩

theorem layer_nodup_of_flatten {layers : List (List Nat)} (h : layers.flatten.Nodup) :
    ∀ l ∈ layers, l.Nodup := by
  induction layers with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatten_cons, List.nodup_append] at h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact ih h.2.1 q hq

theorem cluster_layer_nodup {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs) :
    ∀ l ∈ layers, l.Nodup := by
  obtain ⟨_,_,hr,_,he⟩ := crossCoordsClusterWith_spec h
  rcases he with ⟨he,_⟩ | ⟨x0,x1,x2,x3,hp,_⟩
  · intro l hl
    have hempty : l = [] := by
      cases l with
      | nil => rfl
      | cons a as =>
        have hm := layer_node_lt hr hl (List.mem_cons_self)
        omega
    rw [hempty]
    exact List.nodup_nil
  · unfold crossClusterPasses at hp
    split at hp
    · simp at hp
    · next pos hpos =>
      obtain ⟨_,⟨pos',hlp⟩,_⟩ := checkLayers_parts hpos
      exact layer_nodup_of_flatten (layerPositions_spec hlp).1

theorem ownTitleAnchor_after_anchor {p : Proper} {a b : Nat} {na nb : ProperNode}
    (ha : p.nodes[a]? = some na) (hb : p.nodes[b]? = some nb)
    (hna : na.node.border = -2 ∨ na.node.border = 2)
    (ht : ownTitleAnchor p a b = true) :
    nb.node.border = 3 ∧ na.node.clusterPath = nb.node.clusterPath := by
  simp only [ownTitleAnchor, ha, hb, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with ⟨⟨_, heq⟩, hfirst | hsecond⟩
  · exact ⟨hfirst.2, heq⟩
  · have hbad := hsecond.2
    rcases hna with he | he <;> omega

theorem cluster_all_pairs_separated {ng cp : Int} {p : Proper} {layers : List (List Nat)} {xs : List Int}
    (h : crossCoordsClusterWith ng cp p layers = .ok xs)
    (huniq : ∀ (a b : Nat) (na nb : ProperNode), p.nodes[a]? = some na → p.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 → na.node.clusterPath = nb.node.clusterPath → a = b) :
    ∀ layer ∈ layers, ∀ (i j a b : Nat) na nb, i < j → layer[i]? = some a → layer[j]? = some b →
      p.nodes[a]? = some na → p.nodes[b]? = some nb →
      na.node.border ≠ -2 → na.node.border ≠ 2 → nb.node.border ≠ -2 → nb.node.border ≠ 2 →
      coordSep (min ng cp) p a b ≤ xs.getD b 0 - xs.getD a 0 := by
  intro layer hl i j a b na nb hij ha hb hna hnb hna1 hna2 hnb1 hnb2
  obtain ⟨hn,hp,hr,hs,_⟩ := crossCoordsClusterWith_spec h
  have halfnonneg : ∀ v, 0 ≤ Int.fdiv (nodeW p v) 2 := by
    intro v
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
    exact Int.ediv_nonneg (nodeW_nonneg hs v) (by decide)
  have hnd := cluster_layer_nodup h layer hl
  have middle : ∀ k, k ≤ j → ∃ c, layer[k]? = some c := by
    intro k hkj
    have hj : j < layer.length := (List.getElem?_eq_some_iff.mp hb).1
    cases hc : layer[k]? with
    | none => have := List.getElem?_eq_none_iff.mp hc; omega
    | some c => exact ⟨c,rfl⟩
  obtain ⟨c,hc⟩ := middle (i+1) (by omega)
  have hc_lt := layers_mem_lt hr hl hc
  have hcn : ∃ nc, p.nodes[c]? = some nc := by
    cases he : p.nodes[c]? with
    | none => have := List.getElem?_eq_none_iff.mp he; omega
    | some nc => exact ⟨nc,rfl⟩
  obtain ⟨nc,hnc⟩ := hcn
  have hadj := cluster_balance_separated h layer hl i a c ha hc
  by_cases ht : ownTitleAnchor p a c = true
  · obtain ⟨hatitle,hpath,hcanchor⟩ := ownTitleAnchor_left_nonanchor hna hnc hna1 hna2 ht
    have hic : i+1 < j := by
      by_cases he : i+1 < j
      · exact he
      have heq : i+1 = j := by omega
      have hcb : c = b := by rw [heq,hb] at hc; exact Option.some.inj hc.symm
      subst c
      rw [hnb] at hnc
      have hrec : nc = nb := Option.some.inj hnc.symm
      subst nc
      rcases hcanchor with he | he <;> contradiction
    obtain ⟨d,hd⟩ := middle (i+2) (by omega)
    have hd_lt := layers_mem_lt hr hl hd
    have hdn : ∃ nd, p.nodes[d]? = some nd := by
      cases he : p.nodes[d]? with
      | none => have := List.getElem?_eq_none_iff.mp he; omega
      | some nd => exact ⟨nd,rfl⟩
    obtain ⟨nd,hndnode⟩ := hdn
    have ht2 : ownTitleAnchor p c d = false := by
      cases ht2 : ownTitleAnchor p c d with
      | false => rfl
      | true =>
        obtain ⟨hdtitle,hpath2⟩ := ownTitleAnchor_after_anchor hnc hndnode hcanchor ht2
        have had : a = d := huniq a d na nd hna hndnode hatitle hdtitle (hpath.trans hpath2)
        subst d
        have hi_len : i < layer.length := (List.getElem?_eq_some_iff.mp ha).1
        have heq : i = i+2 := (List.Nodup.getElem?_inj hi_len hnd).mp (ha.trans hd.symm)
        omega
    have hadj2 := cluster_balance_separated h layer hl (i+1) c d hc hd
    have hg := clusterGap_ge_min (ng := ng) (cp := cp) p c d ht2
    have hz := clusterGap_nonneg hn hp p a c
    have hw := halfnonneg c
    unfold clusterSep coordSep at hadj hadj2
    unfold coordSep
    by_cases heq : i+2 = j
    · have hdb : d = b := by rw [heq,hb] at hd; exact Option.some.inj hd.symm
      subst d
      omega
    · have htail := cluster_zero_pairs_separated h layer hl (i+2) j d b (by omega) hd hb
      have hwd := halfnonneg d
      omega
  · have htf : ownTitleAnchor p a c = false := Bool.eq_false_iff.mpr ht
    have hg := clusterGap_ge_min (ng := ng) (cp := cp) p a c htf
    unfold clusterSep coordSep at hadj
    unfold coordSep
    by_cases heq : i+1 = j
    · have hcb : c = b := by rw [heq,hb] at hc; exact Option.some.inj hc.symm
      subst c
      omega
    · have htail := cluster_zero_pairs_separated h layer hl (i+1) j c b (by omega) hc hb
      have hw := halfnonneg c
      omega
end CoordsImpl

export CoordsImpl (crossCoords crossCoordsWith crossCoordsClusterWith clusterSep clusterGap
  cluster_balance_separated cluster_coords_order_preserved crossCoordsClusterWith_spec
  crossCoordsClusterWith_length clusterSep_real_real clusterSep_pos clusterSep_nonneg ownTitleAnchor
  cluster_all_pairs_separated
  crossPasses rankCoords rankCoordsWith coordSep
  layerHeight crossCoords_eq rankCoords_eq crossCoordsWith_length rankCoordsWith_length
  rankAxis_node_in_band)

theorem rawPass_separated {gap : Int} {p : Proper} {layers : List (List Nat)} {pos : Array Nat}
    {k : Nat} {x : Array Int} (hg : 1 ≤ gap)
    (hc : CoordsImpl.checkLayers p layers = .ok pos)
    (hr : CoordsImpl.rawPass gap p layers (CoordsImpl.typeOneConflicts p pos) k = .ok x)
    (hk : k < 4) : CoordsImpl.passSeparated gap p layers x = true :=
  CoordsImpl.rawPass_separated hg hc hr hk

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
