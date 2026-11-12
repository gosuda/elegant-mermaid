import ElegantGeometry.Crossings
import Elegant.Gen.Layoutconst
import Elegant.Layered.Normalize

set_option autoImplicit false

/-! Ordering phase (spec/layout/layered.md, "Order") for flat graphs: the initial order by
declaration index, alternating barycentre sweeps starting downward, transpose passes under the
fuel `crossings + 1`, and the best order kept on strictly fewer crossings, stopping after
`sweep_stall` sweeps without improvement or `sweep_max` sweeps.

`crossCount` is the inversion count of the bottom positions of the edges sorted by (top position,
bottom position), summed over the layers; it is exact in `Nat`, and the Go accumulator tree counts
the same number. `crossCount_eq_naive` proves it equals the naive count of edge pairs with
`(pos a - pos c) * (pos b - pos d) < 0`, `transpose_crossings_le` that the local swap delta is
exact so a transpose never raises it, `order_perm` that every layer stays a permutation of the
initial layer, and `order_crossings_le_init` that the kept order is no worse than the initial one.
The transpose theorem assumes `OrderImpl.Valid p` (the checks `order` makes) and
`OrderImpl.Layering p L` (each layer permutes the nodes of that rank). -/

namespace Elegant
namespace Layered

open RankImpl (rk_of_lt)

inductive OrderStart where
  | declaration
deriving DecidableEq, Repr

inductive OrderKey where
  | barycentre
deriving DecidableEq, Repr

structure OrderOptions where
  start : OrderStart := .declaration
  key : OrderKey := .barycentre
deriving DecidableEq, Repr

structure OrderResult where
  layers : List (List Nat)
  budgetExhausted : Bool
deriving DecidableEq, Repr

namespace OrderImpl

def lay (p : Proper) (v : Nat) : Nat := (rk p.rank v).toNat

def layerCount (p : Proper) : Nat := p.rank.foldl (fun m r => max m (r.toNat + 1)) 0

def declOf (p : Proper) (v : Nat) : Nat := (p.nodes.getD v default).node.decl

def declLe (p : Proper) (a b : Nat) : Bool :=
  decide (declOf p a < declOf p b ∨ (declOf p a = declOf p b ∧ a ≤ b))

def layerNodes (p : Proper) (r : Nat) : List Nat :=
  ((List.range p.rank.length).filter (fun v => lay p v == r)).mergeSort (declLe p)

def initOrder (p : Proper) : List (List Nat) :=
  (List.range (layerCount p)).map (layerNodes p)

def posOf (p : Proper) (L : List (List Nat)) (v : Nat) : Int :=
  ((L.getD (lay p v) []).idxOf v : Nat)

def aboveOf (p : Proper) (v : Nat) : List Nat :=
  (p.edges.filter (fun e => e.head == v)).map (·.tail)

def belowOf (p : Proper) (v : Nat) : List Nat :=
  (p.edges.filter (fun e => e.tail == v)).map (·.head)

def layerKeys (p : Proper) (L : List (List Nat)) (r : Nat) : List (Int × Int) :=
  (p.edges.filter (fun e => lay p e.tail == r)).map
    (fun e => (posOf p L e.tail, posOf p L e.head))

def crossLayer (p : Proper) (L : List (List Nat)) (r : Nat) : Nat :=
  countInversionsNat ((sortKeys (layerKeys p L r)).map (fun k => k.2))

def crossCount (p : Proper) (L : List (List Nat)) : Nat :=
  ((List.range L.length).map (crossLayer p L)).sum

def crossesPair (p : Proper) (n : Nat) (pos : Nat → Int) (e f : ProperEdge) : Bool :=
  lay p e.tail == lay p f.tail && decide (lay p e.tail < n) &&
    decide ((pos e.tail - pos f.tail) * (pos e.head - pos f.head) < 0)

def naiveCountAux (c : ProperEdge → ProperEdge → Bool) : List ProperEdge → Nat
  | [] => 0
  | e :: rest => rest.countP (c e) + naiveCountAux c rest

def naiveCrossCount (p : Proper) (L : List (List Nat)) : Nat :=
  naiveCountAux (crossesPair p L.length (posOf p L)) p.edges

def fracKey (nb : Nat → List Nat) (pos : Nat → Int) (v : Nat) : Int × Int :=
  match nb v with
  | [] => (pos v, 1)
  | ns => ((ns.map pos).sum, (ns.length : Int))

def fracLe (a b : Int × Int) : Bool := decide (a.1 * b.2 ≤ b.1 * a.2)

def sortLayer (nb : Nat → List Nat) (pos : Nat → Int) (layer : List Nat) : List Nat :=
  layer.mergeSort (fun a b => fracLe (fracKey nb pos a) (fracKey nb pos b))

def sweepStep (p : Proper) (nb : Nat → List Nat) (L : List (List Nat)) (r : Nat) :
    List (List Nat) :=
  L.set r (sortLayer nb (posOf p L) (L.getD r []))

def sweepLayers (p : Proper) (s : Nat) (L : List (List Nat)) : List (List Nat) :=
  if s % 2 = 0 then
    (List.range (L.length - 1)).foldl (fun M k => sweepStep p (aboveOf p) M (k + 1)) L
  else
    (List.range (L.length - 1)).foldl
      (fun M k => sweepStep p (belowOf p) M (L.length - 2 - k)) L

def cmpSign (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

def swapDelta (pos : Nat → Int) (a b : List Nat) : Int :=
  (a.map fun u => (b.map fun v => cmpSign (pos v) (pos u)).sum).sum

def delta (p : Proper) (pos : Nat → Int) (a b : Nat) : Int :=
  swapDelta pos (aboveOf p a) (aboveOf p b) + swapDelta pos (belowOf p a) (belowOf p b)

def scanGo (p : Proper) (pos : Nat → Int) : Nat → List Nat → List Nat
  | c, [] => [c]
  | c, x :: rest =>
    if delta p pos c x < 0 then x :: scanGo p pos c rest else c :: scanGo p pos x rest

def scanLayer (p : Proper) (pos : Nat → Int) : List Nat → List Nat
  | [] => []
  | c :: rest => scanGo p pos c rest

def transposeStep (p : Proper) (L : List (List Nat)) (r : Nat) : List (List Nat) :=
  L.set r (scanLayer p (posOf p L) (L.getD r []))

def transposePass (p : Proper) (L : List (List Nat)) : List (List Nat) :=
  (List.range L.length).foldl (transposeStep p) L

def transposeLoop (p : Proper) : Nat → List (List Nat) → List (List Nat)
  | 0, L => L
  | f + 1, L =>
    let L' := transposePass p L
    if L' = L then L' else transposeLoop p f L'

def transpose (p : Proper) (L : List (List Nat)) : List (List Nat) :=
  transposeLoop p (crossCount p L + 1) L

opaque sweepMax : Nat :=
  match layoutconst.find? (fun c => c.name == "vector.sweep_max") with
  | some c => if 0 < c.value then c.value.toNat else 0
  | none => 0

opaque sweepStall : Nat :=
  match layoutconst.find? (fun c => c.name == "vector.sweep_stall") with
  | some c => if 0 < c.value then c.value.toNat else 0
  | none => 0

def runFrom (p : Proper) (limit stallLimit : Nat) :
    Nat → Nat → List (List Nat) → Nat → Nat → OrderResult
  | 0, _, best, _, _ => ⟨best, false⟩
  | fuel + 1, sweep, best, score, stall =>
    let trial := transpose p (sweepLayers p sweep best)
    let next := crossCount p trial
    let improved := decide (next < score)
    let best' := if improved then trial else best
    let score' := if improved then next else score
    let stall' := if improved then 0 else stall + 1
    if sweep + 1 = limit then ⟨best', true⟩
    else if stallLimit ≤ stall' then ⟨best', false⟩
    else runFrom p limit stallLimit fuel (sweep + 1) best' score' stall'

def Valid (p : Proper) : Prop :=
  p.nodes.length = p.rank.length ∧
    (p.nodes.length : Int) ≤ I32_MAX ∧ (p.edges.length : Int) ≤ I32_MAX ∧
    (∀ r ∈ p.rank, 0 ≤ r ∧ r ≤ (p.nodes.length : Int)) ∧
    ∀ e ∈ p.edges, e.tail < p.rank.length ∧ e.head < p.rank.length ∧
      rk p.rank e.head - rk p.rank e.tail = 1

instance (p : Proper) : Decidable (Valid p) := by
  unfold Valid
  infer_instance

def orderWithBudget (p : Proper) (opts : OrderOptions) : Except LayoutError OrderResult :=
  match opts.start, opts.key with
  | .declaration, .barycentre =>
    if Valid p then
      if 0 < sweepMax ∧ 0 < sweepStall then
        .ok (runFrom p sweepMax sweepStall sweepMax 0 (initOrder p) (crossCount p (initOrder p)) 0)
      else .error .domain
    else .error .domain

def order (p : Proper) (opts : OrderOptions) : Except LayoutError (List (List Nat)) :=
  match orderWithBudget p opts with
  | .ok res => .ok res.layers
  | .error e => .error e

theorem foldl_inv {α β : Type} (P : α → Prop) (f : α → β → α) (l : List β) (a : α)
    (h0 : P a) (hs : ∀ a, P a → ∀ x ∈ l, P (f a x)) : P (l.foldl f a) := by
  induction l generalizing a with
  | nil => exact h0
  | cons x xs ih =>
    exact ih (f a x) (hs a h0 x (List.mem_cons_self ..)) (fun a' ha' y hy => hs a' ha' y (List.mem_cons_of_mem _ hy))

def Layering (p : Proper) (L : List (List Nat)) : Prop :=
  L.length = layerCount p ∧ ∀ r, r < L.length → (L.getD r []).Perm (layerNodes p r)

theorem getD_set_self {L : List (List Nat)} {r : Nat} (h : r < L.length) (x : List Nat) :
    (L.set r x).getD r [] = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne {L : List (List Nat)} {r i : Nat} (h : i ≠ r) (x : List Nat) :
    (L.set r x).getD i [] = L.getD i [] := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem layering_init (p : Proper) : Layering p (initOrder p) := by
  refine ⟨by simp [initOrder], ?_⟩
  intro r hr
  have hr' : r < layerCount p := by simpa [initOrder] using hr
  simp [initOrder, List.getD_eq_getElem?_getD, hr']

theorem layering_set {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    {x : List Nat} (hx : x.Perm (L.getD r [])) : Layering p (L.set r x) := by
  refine ⟨by rw [List.length_set]; exact hL.1, ?_⟩
  intro i hi
  rw [List.length_set] at hi
  by_cases hir : i = r
  · subst hir
    rw [getD_set_self hi]
    exact hx.trans (hL.2 i hi)
  · rw [getD_set_ne hir]
    exact hL.2 i hi

theorem sweepStep_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L)
    (nb : Nat → List Nat) (r : Nat) : Layering p (sweepStep p nb L r) :=
  layering_set hL (List.mergeSort_perm _ _)

theorem sweepLayers_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L) (s : Nat) :
    Layering p (sweepLayers p s L) := by
  unfold sweepLayers
  split
  · exact foldl_inv (Layering p) _ _ L hL (fun a ha k _ => sweepStep_layering ha _ _)
  · exact foldl_inv (Layering p) _ _ L hL (fun a ha k _ => sweepStep_layering ha _ _)

theorem scanGo_perm (p : Proper) (pos : Nat → Int) :
    ∀ (rest : List Nat) (c : Nat), (scanGo p pos c rest).Perm (c :: rest) := by
  intro rest
  induction rest with
  | nil => intro c; exact List.Perm.refl _
  | cons x xs ih =>
    intro c
    unfold scanGo
    split
    · exact ((ih c).cons x).trans (List.Perm.swap c x xs)
    · exact (ih x).cons c

theorem scanLayer_perm (p : Proper) (pos : Nat → Int) (l : List Nat) :
    (scanLayer p pos l).Perm l := by
  cases l with
  | nil => exact List.Perm.refl _
  | cons c rest => exact scanGo_perm p pos rest c

theorem transposeStep_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L)
    (r : Nat) : Layering p (transposeStep p L r) :=
  layering_set hL (scanLayer_perm _ _ _)

theorem transposePass_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L) :
    Layering p (transposePass p L) :=
  foldl_inv (Layering p) _ _ L hL (fun _ ha r _ => transposeStep_layering ha r)

theorem transposeLoop_layering (p : Proper) :
    ∀ (f : Nat) (L : List (List Nat)), Layering p L → Layering p (transposeLoop p f L) := by
  intro f
  induction f with
  | zero => intro L hL; exact hL
  | succ f ih =>
    intro L hL
    unfold transposeLoop
    simp only
    split
    · exact transposePass_layering hL
    · exact ih _ (transposePass_layering hL)

theorem transpose_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L) :
    Layering p (transpose p L) :=
  transposeLoop_layering p _ L hL

theorem runFrom_spec (p : Proper) (limit stallLimit : Nat) :
    ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      Layering p best → score = crossCount p best →
      Layering p (runFrom p limit stallLimit fuel sweep best score stall).layers ∧
      crossCount p (runFrom p limit stallLimit fuel sweep best score stall).layers
        ≤ crossCount p best := by
  intro fuel
  induction fuel with
  | zero =>
    intro sweep best score stall hb hs
    exact ⟨hb, Nat.le_refl _⟩
  | succ f ih =>
    intro sweep best score stall hb hs
    have htrial : Layering p (transpose p (sweepLayers p sweep best)) :=
      transpose_layering (sweepLayers_layering hb sweep)
    unfold runFrom
    simp only
    by_cases himp : crossCount p (transpose p (sweepLayers p sweep best)) < score
    · simp only [himp, decide_true, ite_true]
      split
      · exact ⟨htrial, by dsimp only; omega⟩
      · split
        · exact ⟨htrial, by dsimp only; omega⟩
        · obtain ⟨h1, h2⟩ := ih (sweep + 1) _ _ 0 htrial rfl
          exact ⟨h1, by omega⟩
    · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
      split
      · exact ⟨hb, Nat.le_refl _⟩
      · split
        · exact ⟨hb, Nat.le_refl _⟩
        · obtain ⟨h1, h2⟩ := ih (sweep + 1) best score (stall + 1) hb hs
          exact ⟨h1, h2⟩

theorem orderWithBudget_spec (p : Proper) (opts : OrderOptions) (r : OrderResult)
    (h : orderWithBudget p opts = .ok r) :
    Layering p r.layers ∧ crossCount p r.layers ≤ crossCount p (initOrder p) := by
  obtain ⟨start, key⟩ := opts
  cases start
  cases key
  unfold orderWithBudget at h
  simp only at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact runFrom_spec p _ _ _ _ _ _ _ (layering_init p) rfl
    · simp at h
  · simp at h

theorem crossLayer_eq (p : Proper) (L : List (List Nat)) (r : Nat) :
    crossLayer p L r = crossCountN (layerKeys p L r) := by
  unfold crossLayer
  rw [inversions_sorted _ (sortKeys_pairwise _)]
  exact crossCountN_perm (sortKeys_perm _)

theorem sum_range_ite (c n : Nat) (f : Nat → Nat) :
    ((List.range n).map (fun r => if c == r then f r else 0)).sum = if c < n then f c else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases h1 : c < n
    · have h2 : ¬ c = n := by omega
      simp [h1, h2, show c < n + 1 by omega]
    · by_cases h3 : c = n
      · subst h3
        simp
      · have h4 : ¬ c < n + 1 := by omega
        simp [h1, h3, h4]

theorem sum_map_add {β : Type} (l : List β) (f g : β → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem sum_map_zero {β : Type} (l : List β) : (l.map (fun _ => (0 : Nat))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]

theorem layers_sum_eq (n : Nat) (lay' : ProperEdge → Nat) (key : ProperEdge → Int × Int) :
    ∀ E : List ProperEdge,
      ((List.range n).map
        (fun r => crossCountN ((E.filter (fun e => lay' e == r)).map key))).sum =
      naiveCountAux
        (fun e f => lay' e == lay' f && decide (lay' e < n) && crossesKeyB (key e) (key f)) E := by
  intro E
  induction E with
  | nil =>
    have h0 : ∀ r, crossCountN (([] : List ProperEdge).filter (fun e => lay' e == r)|>.map key) = 0 :=
      fun _ => rfl
    simp only [h0, naiveCountAux]
    exact sum_map_zero _
  | cons e rest ih =>
    have hterm : ∀ r, crossCountN (((e :: rest).filter (fun x => lay' x == r)).map key) =
        (if lay' e == r then
          List.countP (crossesKeyB (key e)) ((rest.filter (fun x => lay' x == r)).map key)
        else 0) + crossCountN ((rest.filter (fun x => lay' x == r)).map key) := by
      intro r
      rw [List.filter_cons]
      by_cases h : lay' e == r
      · simp only [h, ite_true, List.map_cons]
        rfl
      · simp only [h, Bool.false_eq_true, ite_false, Nat.zero_add]
    simp only [hterm]
    rw [sum_map_add, ih, sum_range_ite]
    have hcount : (if lay' e < n then
          List.countP (crossesKeyB (key e)) ((rest.filter (fun x => lay' x == lay' e)).map key)
        else 0) =
        List.countP (fun f => lay' e == lay' f && decide (lay' e < n) && crossesKeyB (key e) (key f))
          rest := by
      by_cases hn : lay' e < n
      · simp only [hn, ite_true]
        rw [List.countP_map, List.countP_filter]
        refine List.countP_congr (fun f _ => ?_)
        simp only [Function.comp, decide_true, Bool.and_true]
        cases h1 : lay' f == lay' e <;> cases h2 : lay' e == lay' f <;> cases h3 : crossesKeyB (key e) (key f) <;> simp_all [beq_iff_eq] <;> omega
      · simp only [hn, decide_false, Bool.and_false, Bool.false_and, ite_false]
        simp
    rw [hcount]
    rfl

theorem crossCount_eq_naive (p : Proper) (L : List (List Nat)) :
    crossCount p L = naiveCrossCount p L := by
  unfold crossCount naiveCrossCount
  have h := layers_sum_eq L.length (fun e => lay p e.tail)
    (fun e => (posOf p L e.tail, posOf p L e.head)) p.edges
  have hfun : crossLayer p L = fun r => crossCountN (layerKeys p L r) :=
    funext (crossLayer_eq p L)
  rw [hfun]
  exact h

def bi (b : Bool) : Int := if b then 1 else 0

def swapPos (pos : Nat → Int) (a b : Nat) : Nat → Int :=
  fun v => if v = a then pos b else if v = b then pos a else pos v

def fterm (a b xe xf : Nat) (u v : Int) : Int :=
  (if xe = a ∧ xf = b then cmpSign v u else 0) +
    (if xf = a ∧ xe = b then cmpSign u v else 0)

def pairG (pos : Nat → Int) (a b : Nat) (e f : ProperEdge) : Int :=
  fterm a b e.head f.head (pos e.tail) (pos f.tail) +
    fterm a b e.tail f.tail (pos e.head) (pos f.head)

theorem mul_neg_iff' (x y : Int) : x * y < 0 ↔ (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) := by
  constructor
  · intro h
    rcases Int.lt_trichotomy x 0 with hx | hx | hx
    · refine Or.inl ⟨hx, ?_⟩
      by_cases hy : 0 < y
      · exact hy
      · have h1 : 0 ≤ -x * -y := Int.mul_nonneg (by omega) (by omega)
        rw [Int.neg_mul_neg] at h1
        omega
    · subst hx
      rw [Int.zero_mul] at h
      exact absurd h (Int.lt_irrefl 0)
    · refine Or.inr ⟨hx, ?_⟩
      by_cases hy : y < 0
      · exact hy
      · have h1 : 0 ≤ x * y := Int.mul_nonneg (by omega) (by omega)
        omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Int.mul_neg_of_neg_of_pos h1 h2
    · exact Int.mul_neg_of_pos_of_neg h1 h2

theorem bi_same_sign {x x' y : Int} (h : (0 < x ∧ 0 < x') ∨ (x < 0 ∧ x' < 0)) :
    bi (decide (x' * y < 0)) = bi (decide (x * y < 0)) := by
  have h1 := mul_neg_iff' x y
  have h2 := mul_neg_iff' x' y
  unfold bi
  by_cases p1 : x' * y < 0 <;> by_cases p2 : x * y < 0 <;>
    simp only [p1, p2, decide_true, decide_false, ite_true, ite_false, Bool.false_eq_true] <;>
    omega

theorem bi_flip_pos (u v : Int) :
    bi (decide (1 * (u - v) < 0)) = bi (decide ((-1) * (u - v) < 0)) + cmpSign v u := by
  unfold bi cmpSign
  simp only [Int.one_mul, Int.neg_mul]
  by_cases h1 : u - v < 0 <;> by_cases h2 : -(u - v) < 0 <;> by_cases h3 : v < u <;>
    by_cases h4 : u < v <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false, ite_true, ite_false,
      Bool.false_eq_true] <;>
    omega

theorem bi_flip_neg (u v : Int) :
    bi (decide ((-1) * (u - v) < 0)) = bi (decide (1 * (u - v) < 0)) + cmpSign u v := by
  unfold bi cmpSign
  simp only [Int.one_mul, Int.neg_mul]
  by_cases h1 : u - v < 0 <;> by_cases h2 : -(u - v) < 0 <;> by_cases h3 : v < u <;>
    by_cases h4 : u < v <;>
    simp only [h1, h2, h3, h4, decide_true, decide_false, ite_true, ite_false,
      Bool.false_eq_true] <;>
    omega

theorem factor_exact (pos : Nat → Int) (a b xe xf : Nat) (u v : Int) (hab : a ≠ b)
    (hadj : pos b = pos a + 1)
    (hxe : (xf = a ∨ xf = b) → xe ≠ a → xe ≠ b → pos xe < pos a ∨ pos b < pos xe)
    (hxf : (xe = a ∨ xe = b) → xf ≠ a → xf ≠ b → pos xf < pos a ∨ pos b < pos xf) :
    bi (decide ((swapPos pos a b xe - swapPos pos a b xf) * (u - v) < 0)) =
      bi (decide ((pos xe - pos xf) * (u - v) < 0)) + fterm a b xe xf u v := by
  have hba : b ≠ a := fun h => hab h.symm
  have e1 : pos b - pos a = 1 := by omega
  have e2 : pos a - pos b = -1 := by omega
  by_cases he : xe = a
  · by_cases hf : xf = a
    · simp [swapPos, fterm, he, hf, hab, bi]
    · by_cases hf' : xf = b
      · simp only [swapPos, fterm, he, hf', hab, hba, ↓reduceIte, and_self, Int.add_zero]
        rw [e1, e2]
        exact bi_flip_pos u v
      · have h := hxf (Or.inl he) hf hf'
        simp only [swapPos, fterm, he, hf, hf', hab, ↓reduceIte, and_false, Int.add_zero]
        exact bi_same_sign (by omega)
  · by_cases he' : xe = b
    · by_cases hf : xf = a
      · simp only [swapPos, fterm, he', hf, hab, hba, ↓reduceIte, and_self, Int.zero_add]
        rw [e1, e2]
        exact bi_flip_neg u v
      · by_cases hf' : xf = b
        · simp [swapPos, fterm, he', hf', hba, bi]
        · have h := hxf (Or.inr he') hf hf'
          simp only [swapPos, fterm, he', hf, hf', hba, ↓reduceIte, and_false, false_and,
            Int.add_zero]
          exact bi_same_sign (by omega)
    · by_cases hf : xf = a
      · have h := hxe (Or.inl hf) he he'
        simp only [swapPos, fterm, he, he', hf, hab, ↓reduceIte, and_false, Int.add_zero]
        exact bi_same_sign (by omega)
      · by_cases hf' : xf = b
        · have h := hxe (Or.inr hf') he he'
          simp only [swapPos, fterm, he, he', hf', hba, ↓reduceIte, and_false, false_and,
            Int.add_zero]
          exact bi_same_sign (by omega)
        · simp [swapPos, fterm, he, he', hf, hf']

theorem swapPos_of_ne {pos : Nat → Int} {a b x : Nat} (h1 : x ≠ a) (h2 : x ≠ b) :
    swapPos pos a b x = pos x := by
  simp [swapPos, h1, h2]

theorem fterm_zero_left {a b xe xf : Nat} {u v : Int} (h1 : xe ≠ a) (h2 : xe ≠ b) :
    fterm a b xe xf u v = 0 := by
  simp [fterm, h1, h2]

theorem fterm_zero_layers (p : Proper) {a b r xe xf : Nat} {u v : Int} (hla : lay p a = r)
    (hlb : lay p b = r) (h : lay p xe ≠ lay p xf) : fterm a b xe xf u v = 0 := by
  unfold fterm
  have c1 : ¬ (xe = a ∧ xf = b) := by
    rintro ⟨h1, h2⟩
    apply h
    rw [h1, h2, hla, hlb]
  have c2 : ¬ (xf = a ∧ xe = b) := by
    rintro ⟨h1, h2⟩
    apply h
    rw [h1, h2, hla, hlb]
  simp only [c1, c2, ↓reduceIte, Int.add_zero]

theorem ne_ab_of_layer (p : Proper) {a b r x : Nat} (hla : lay p a = r) (hlb : lay p b = r)
    (h : lay p x ≠ r) : x ≠ a ∧ x ≠ b := by
  constructor
  · intro h'
    apply h
    rw [h']
    exact hla
  · intro h'
    apply h
    rw [h']
    exact hlb

structure SwapHyp (p : Proper) (n : Nat) (pos : Nat → Int) (a b r : Nat) : Prop where
  hab : a ≠ b
  hla : lay p a = r
  hlb : lay p b = r
  hr : r < n
  hadj : pos b = pos a + 1
  hx : ∀ x, x ≠ a → x ≠ b → lay p x = r → pos x < pos a ∨ pos b < pos x

theorem pair_exact {p : Proper} {n : Nat} {pos : Nat → Int} {a b r : Nat}
    (H : SwapHyp p n pos a b r) (e f : ProperEdge)
    (he : lay p e.head = lay p e.tail + 1) (hf : lay p f.head = lay p f.tail + 1) :
    bi (crossesPair p n (swapPos pos a b) e f) =
      bi (crossesPair p n pos e f) + pairG pos a b e f := by
  by_cases hl : lay p e.tail = lay p f.tail
  · by_cases hA : lay p e.tail = r
    · have hn : lay p e.tail < n := by have := H.hr; omega
      have hcp : ∀ q : Nat → Int, crossesPair p n q e f =
          decide ((q e.tail - q f.tail) * (q e.head - q f.head) < 0) := by
        intro q
        have hn' : lay p f.tail < n := hl ▸ hn
        simp [crossesPair, hl, hn']
      rw [hcp, hcp]
      have hhe := ne_ab_of_layer p H.hla H.hlb (x := e.head) (by omega)
      have hhf := ne_ab_of_layer p H.hla H.hlb (x := f.head) (by omega)
      rw [swapPos_of_ne hhe.1 hhe.2, swapPos_of_ne hhf.1 hhf.2]
      have key := factor_exact pos a b e.tail f.tail (pos e.head) (pos f.head) H.hab H.hadj
        (fun _ h1 h2 => H.hx _ h1 h2 hA) (fun _ h1 h2 => H.hx _ h1 h2 (by omega))
      unfold pairG
      rw [fterm_zero_left hhe.1 hhe.2, Int.zero_add]
      exact key
    · by_cases hB : lay p e.tail + 1 = r
      · have hn : lay p e.tail < n := by have := H.hr; omega
        have hcp : ∀ q : Nat → Int, crossesPair p n q e f =
            decide ((q e.tail - q f.tail) * (q e.head - q f.head) < 0) := by
          intro q
          have hn' : lay p f.tail < n := hl ▸ hn
          simp [crossesPair, hl, hn']
        rw [hcp, hcp]
        have hte := ne_ab_of_layer p H.hla H.hlb (x := e.tail) (by omega)
        have htf := ne_ab_of_layer p H.hla H.hlb (x := f.tail) (by omega)
        rw [swapPos_of_ne hte.1 hte.2, swapPos_of_ne htf.1 htf.2]
        have key := factor_exact pos a b e.head f.head (pos e.tail) (pos f.tail) H.hab H.hadj
          (fun _ h1 h2 => H.hx _ h1 h2 (by omega)) (fun _ h1 h2 => H.hx _ h1 h2 (by omega))
        rw [Int.mul_comm (pos e.tail - pos f.tail), Int.mul_comm (pos e.tail - pos f.tail)]
        unfold pairG
        rw [fterm_zero_left hte.1 hte.2, Int.add_zero]
        exact key
      · have hte := ne_ab_of_layer p H.hla H.hlb (x := e.tail) hA
        have htf := ne_ab_of_layer p H.hla H.hlb (x := f.tail) (by omega)
        have hhe := ne_ab_of_layer p H.hla H.hlb (x := e.head) (by omega)
        have hhf := ne_ab_of_layer p H.hla H.hlb (x := f.head) (by omega)
        have hcp : crossesPair p n (swapPos pos a b) e f = crossesPair p n pos e f := by
          simp only [crossesPair, swapPos_of_ne hte.1 hte.2, swapPos_of_ne htf.1 htf.2,
            swapPos_of_ne hhe.1 hhe.2, swapPos_of_ne hhf.1 hhf.2]
        rw [hcp]
        unfold pairG
        rw [fterm_zero_left hhe.1 hhe.2, fterm_zero_left hte.1 hte.2, Int.add_zero, Int.add_zero]
  · have hcp : ∀ q : Nat → Int, crossesPair p n q e f = false := by
      intro q
      simp [crossesPair, hl]
    rw [hcp, hcp]
    unfold pairG
    rw [fterm_zero_layers p H.hla H.hlb (by omega), fterm_zero_layers p H.hla H.hlb hl]
    rfl

theorem isum_map_add {β : Type} (l : List β) (f g : β → Int) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem isum_map_zero {β : Type} (l : List β) : (l.map (fun _ => (0 : Int))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; rfl

theorem countP_eq_sum {β : Type} (c : β → Bool) (l : List β) :
    (l.countP c : Int) = (l.map (fun x => bi (c x))).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ← ih]
    cases h : c x
    · simp [bi]
    · simp [bi]
      omega

def gSum {α : Type} (g : α → α → Int) : List α → Int
  | [] => 0
  | e :: rest => (rest.map (g e)).sum + gSum g rest

theorem naive_exact {p : Proper} {n : Nat} {pos : Nat → Int} {a b r : Nat}
    (H : SwapHyp p n pos a b r) :
    ∀ E : List ProperEdge, (∀ e ∈ E, lay p e.head = lay p e.tail + 1) →
      (naiveCountAux (crossesPair p n (swapPos pos a b)) E : Int) =
        (naiveCountAux (crossesPair p n pos) E : Int) + gSum (pairG pos a b) E := by
  intro E
  induction E with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro hE
    have hrest : ∀ x ∈ rest, lay p x.head = lay p x.tail + 1 :=
      fun x hx => hE x (List.mem_cons_of_mem _ hx)
    have he := hE e (List.mem_cons_self ..)
    have h1 := ih hrest
    have h2 : (rest.countP (crossesPair p n (swapPos pos a b) e) : Int) =
        (rest.countP (crossesPair p n pos e) : Int) + (rest.map (pairG pos a b e)).sum := by
      rw [countP_eq_sum, countP_eq_sum, ← isum_map_add]
      congr 1
      exact List.map_congr_left (fun f hf => pair_exact H e f he (hrest f hf))
    simp only [naiveCountAux, gSum, Int.natCast_add]
    omega

theorem ordered_sum {α : Type} (G : α → α → Int) (l : List α) :
    (l.map (fun e => (l.map (G e)).sum)).sum =
      gSum (fun e f => G e f + G f e) l + (l.map (fun e => G e e)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hin : ∀ e, ((x :: xs).map (G e)).sum = G e x + (xs.map (G e)).sum := by
      intro e
      simp only [List.map_cons, List.sum_cons]
    have hout : (xs.map (fun e => ((x :: xs).map (G e)).sum)).sum =
        (xs.map (fun e => G e x)).sum + (xs.map (fun e => (xs.map (G e)).sum)).sum := by
      rw [← isum_map_add]
      exact congrArg List.sum (List.map_congr_left (fun e _ => hin e))
    have hsym : (xs.map (fun f => G x f + G f x)).sum =
        (xs.map (G x)).sum + (xs.map (fun f => G f x)).sum := isum_map_add xs _ _
    have lhs : ((x :: xs).map (fun e => ((x :: xs).map (G e)).sum)).sum =
        (G x x + (xs.map (G x)).sum) +
          ((xs.map (fun e => G e x)).sum + (xs.map (fun e => (xs.map (G e)).sum)).sum) := by
      rw [List.map_cons, List.sum_cons, hout, hin x]
    have rhs : gSum (fun e f => G e f + G f e) (x :: xs) + ((x :: xs).map (fun e => G e e)).sum =
        ((xs.map (G x)).sum + (xs.map (fun f => G f x)).sum +
          gSum (fun e f => G e f + G f e) xs) + (G x x + (xs.map (fun e => G e e)).sum) := by
      rw [List.map_cons, List.sum_cons]
      simp only [gSum]
      rw [hsym]
    rw [lhs, rhs]
    omega

theorem sum_filter_map {α : Type} (l : List α) (P : α → Bool) (f : α → Int) :
    ((l.filter P).map f).sum = (l.map (fun x => if P x then f x else 0)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons]
    by_cases h : P x
    · simp [h, ih]
    · simp [h, ih]

theorem swapDelta_eq (E : List ProperEdge) (pos : Nat → Int) (a b : Nat)
    (key vr : ProperEdge → Nat) :
    swapDelta pos ((E.filter (fun e => key e == a)).map vr)
        ((E.filter (fun e => key e == b)).map vr) =
      (E.map (fun e => (E.map (fun f =>
        if key e = a ∧ key f = b then cmpSign (pos (vr f)) (pos (vr e)) else 0)).sum)).sum := by
  unfold swapDelta
  simp only [List.map_map]
  rw [sum_filter_map]
  refine congrArg List.sum (List.map_congr_left (fun e _ => ?_))
  by_cases h : key e = a
  · simp only [Function.comp, h, beq_self_eq_true, ite_true, true_and]
    rw [sum_filter_map]
    simp only [beq_iff_eq]
    rfl
  · simp only [Function.comp, h, beq_iff_eq, ite_false, false_and]
    exact (isum_map_zero E).symm

def gHead (pos : Nat → Int) (a b : Nat) (e f : ProperEdge) : Int :=
  if e.head = a ∧ f.head = b then cmpSign (pos f.tail) (pos e.tail) else 0

def gTail (pos : Nat → Int) (a b : Nat) (e f : ProperEdge) : Int :=
  if e.tail = a ∧ f.tail = b then cmpSign (pos f.head) (pos e.head) else 0

theorem pairG_eq (pos : Nat → Int) (a b : Nat) (e f : ProperEdge) :
    pairG pos a b e f =
      (gHead pos a b e f + gTail pos a b e f) + (gHead pos a b f e + gTail pos a b f e) := by
  unfold pairG fterm gHead gTail
  omega

theorem gSum_eq_delta (p : Proper) (pos : Nat → Int) (a b : Nat) (hab : a ≠ b) :
    gSum (pairG pos a b) p.edges = delta p pos a b := by
  have hfun : pairG pos a b = fun e f =>
      (fun e f => gHead pos a b e f + gTail pos a b e f) e f +
        (fun e f => gHead pos a b e f + gTail pos a b e f) f e := by
    funext e f
    exact pairG_eq pos a b e f
  have hdiag : ∀ e : ProperEdge, gHead pos a b e e + gTail pos a b e e = 0 := by
    intro e
    unfold gHead gTail
    have c1 : ¬ (e.head = a ∧ e.head = b) := fun h => hab (h.1.symm.trans h.2)
    have c2 : ¬ (e.tail = a ∧ e.tail = b) := fun h => hab (h.1.symm.trans h.2)
    simp only [c1, c2, ↓reduceIte, Int.add_zero]
  have hos := ordered_sum (fun e f => gHead pos a b e f + gTail pos a b e f) p.edges
  have hd0 : (p.edges.map (fun e => gHead pos a b e e + gTail pos a b e e)).sum = 0 := by
    rw [show (fun e : ProperEdge => gHead pos a b e e + gTail pos a b e e) = fun _ => (0 : Int) from
      funext hdiag]
    exact isum_map_zero _
  have hsplit : (p.edges.map (fun e => (p.edges.map
        (fun f => gHead pos a b e f + gTail pos a b e f)).sum)).sum =
      (p.edges.map (fun e => (p.edges.map (gHead pos a b e)).sum)).sum +
        (p.edges.map (fun e => (p.edges.map (gTail pos a b e)).sum)).sum := by
    rw [← isum_map_add]
    refine congrArg List.sum (List.map_congr_left (fun e _ => ?_))
    exact isum_map_add p.edges _ _
  have hA := swapDelta_eq p.edges pos a b (fun e => e.head) (fun e => e.tail)
  have hB := swapDelta_eq p.edges pos a b (fun e => e.tail) (fun e => e.head)
  rw [hfun]
  rw [hd0, Int.add_zero] at hos
  rw [← hos, hsplit]
  unfold delta aboveOf belowOf
  rw [hA, hB]
  rfl

theorem layerNodes_nodup (p : Proper) (r : Nat) : (layerNodes p r).Nodup := by
  unfold layerNodes
  exact ((List.mergeSort_perm _ _).nodup_iff).mpr
    (List.Pairwise.sublist List.filter_sublist List.nodup_range)

theorem mem_layerNodes {p : Proper} {r v : Nat} :
    v ∈ layerNodes p r ↔ v < p.rank.length ∧ lay p v = r := by
  unfold layerNodes
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter, List.mem_range]
  simp

theorem layer_mem {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    (hr : r < L.length) {v : Nat} :
    v ∈ L.getD r [] ↔ v < p.rank.length ∧ lay p v = r :=
  ((hL.2 r hr).mem_iff).trans mem_layerNodes

theorem layer_nodup {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    (hr : r < L.length) : (L.getD r []).Nodup :=
  (hL.2 r hr).nodup_iff.mpr (layerNodes_nodup p r)

theorem idxOf_first {pre post : List Nat} {a b : Nat} (ha : a ∉ pre) :
    (pre ++ a :: b :: post).idxOf a = pre.length := by
  rw [List.idxOf_append]
  simp [ha]

theorem idxOf_second {pre post : List Nat} {a b : Nat} (hab : a ≠ b) (hb : b ∉ pre) :
    (pre ++ a :: b :: post).idxOf b = pre.length + 1 := by
  rw [List.idxOf_append]
  simp [hb, List.idxOf_cons, hab]
  omega

theorem idxOf_other {pre post : List Nat} {a b x : Nat} (hxa : x ≠ a) (hxb : x ≠ b) :
    (pre ++ a :: b :: post).idxOf x =
      if x ∈ pre then pre.idxOf x else post.idxOf x + 2 + pre.length := by
  rw [List.idxOf_append]
  by_cases h : x ∈ pre
  · simp [h]
  · simp only [h, ite_false, List.idxOf_cons, beq_iff_eq, Ne.symm hxa, Ne.symm hxb]

theorem idxOf_other_swap {pre post : List Nat} {a b x : Nat} (hxa : x ≠ a) (hxb : x ≠ b) :
    (pre ++ b :: a :: post).idxOf x = (pre ++ a :: b :: post).idxOf x := by
  rw [idxOf_other hxb hxa, idxOf_other hxa hxb]

theorem idxOf_other_cases {pre post : List Nat} {a b x : Nat} (hxa : x ≠ a) (hxb : x ≠ b) :
    (pre ++ a :: b :: post).idxOf x < pre.length ∨
      pre.length + 2 ≤ (pre ++ a :: b :: post).idxOf x := by
  rw [idxOf_other hxa hxb]
  by_cases h : x ∈ pre
  · simp only [h, ite_true]
    exact Or.inl (List.idxOf_lt_length_of_mem h)
  · simp only [h, ite_false]
    omega

theorem valid_edge_layers {p : Proper} (hV : Valid p) :
    ∀ e ∈ p.edges, lay p e.head = lay p e.tail + 1 := by
  obtain ⟨_, _, _, hr, he⟩ := hV
  intro e hmem
  obtain ⟨ht, _, hs⟩ := he e hmem
  have h1 : 0 ≤ rk p.rank e.tail := by
    rw [rk_of_lt ht]
    exact (hr _ (List.getElem_mem ht)).1
  unfold lay
  omega

theorem swap_facts {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    (hr : r < L.length) {pre post : List Nat} {a b : Nat}
    (hl : L.getD r [] = pre ++ a :: b :: post) :
    a ≠ b ∧ a ∉ pre ∧ b ∉ pre ∧ lay p a = r ∧ lay p b = r := by
  have hnd := layer_nodup hL hr
  have hmem : ∀ v, v ∈ L.getD r [] ↔ v < p.rank.length ∧ lay p v = r :=
    fun v => layer_mem hL hr
  rw [hl] at hnd hmem
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, not_or] at hnd
  obtain ⟨_, ⟨⟨hab, _⟩, _, _⟩, hdisj⟩ := hnd
  refine ⟨hab, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (hdisj a h a (Or.inl rfl)) rfl
  · intro h
    exact (hdisj b h b (Or.inr (Or.inl rfl))) rfl
  · exact ((hmem a).mp (by simp)).2
  · exact ((hmem b).mp (by simp)).2

theorem posOf_swap {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    (hr : r < L.length) {pre post : List Nat} {a b : Nat}
    (hl : L.getD r [] = pre ++ a :: b :: post) :
    posOf p (L.set r (pre ++ b :: a :: post)) = swapPos (posOf p L) a b := by
  obtain ⟨hab, hapre, hbpre, hla, hlb⟩ := swap_facts hL hr hl
  have hba : b ≠ a := fun h => hab h.symm
  funext v
  by_cases hv : lay p v = r
  · have e1 : posOf p (L.set r (pre ++ b :: a :: post)) v =
        ((pre ++ b :: a :: post).idxOf v : Nat) := by
      unfold posOf
      rw [hv, getD_set_self hr]
    have e2 : ∀ w, lay p w = r → posOf p L w = ((pre ++ a :: b :: post).idxOf w : Nat) := by
      intro w hw
      unfold posOf
      rw [hw, hl]
    rw [e1]
    by_cases hva : v = a
    · rw [hva]
      simp only [swapPos, ite_true]
      rw [e2 b hlb, idxOf_second hba hapre, idxOf_second hab hbpre]
    · by_cases hvb : v = b
      · rw [hvb]
        simp only [swapPos, hba, ite_false, ite_true]
        rw [e2 a hla, idxOf_first hbpre, idxOf_first hapre]
      · simp only [swapPos, hva, hvb, ite_false]
        rw [e2 v hv, idxOf_other_swap hva hvb]
  · have hva : v ≠ a := fun h => hv (h ▸ hla)
    have hvb : v ≠ b := fun h => hv (h ▸ hlb)
    rw [swapPos_of_ne hva hvb]
    unfold posOf
    rw [getD_set_ne hv]

theorem swapHyp {p : Proper} {L : List (List Nat)} (hL : Layering p L) {r : Nat}
    (hr : r < L.length) {pre post : List Nat} {a b : Nat}
    (hl : L.getD r [] = pre ++ a :: b :: post) :
    SwapHyp p L.length (posOf p L) a b r := by
  obtain ⟨hab, hapre, hbpre, hla, hlb⟩ := swap_facts hL hr hl
  have e2 : ∀ w, lay p w = r → posOf p L w = ((pre ++ a :: b :: post).idxOf w : Nat) := by
    intro w hw
    unfold posOf
    rw [hw, hl]
  refine ⟨hab, hla, hlb, hr, ?_, ?_⟩
  · rw [e2 b hlb, e2 a hla, idxOf_second hab hbpre, idxOf_first hapre]
    omega
  · intro x hxa hxb hx
    rw [e2 x hx, e2 a hla, e2 b hlb, idxOf_first hapre, idxOf_second hab hbpre]
    rcases idxOf_other_cases (pre := pre) (post := post) hxa hxb with h | h
    · omega
    · omega

theorem crossCount_swap {p : Proper} (hV : Valid p) {L : List (List Nat)} (hL : Layering p L)
    {r : Nat} (hr : r < L.length) {pre post : List Nat} {a b : Nat}
    (hl : L.getD r [] = pre ++ a :: b :: post) :
    (crossCount p (L.set r (pre ++ b :: a :: post)) : Int) =
      (crossCount p L : Int) + delta p (posOf p L) a b := by
  have hH := swapHyp hL hr hl
  rw [crossCount_eq_naive, crossCount_eq_naive]
  unfold naiveCrossCount
  rw [List.length_set, posOf_swap hL hr hl,
    naive_exact hH p.edges (valid_edge_layers hV), gSum_eq_delta p (posOf p L) a b hH.hab]

theorem swapDelta_congr {pos pos' : Nat → Int} {A B : List Nat}
    (hA : ∀ u ∈ A, pos u = pos' u) (hB : ∀ v ∈ B, pos v = pos' v) :
    swapDelta pos A B = swapDelta pos' A B := by
  unfold swapDelta
  refine congrArg List.sum (List.map_congr_left (fun u hu => ?_))
  refine congrArg List.sum (List.map_congr_left (fun v hv => ?_))
  rw [hA u hu, hB v hv]

theorem delta_congr {p : Proper} (hE : ∀ e ∈ p.edges, lay p e.head = lay p e.tail + 1)
    {pos pos' : Nat → Int} {r : Nat} (h : ∀ v, lay p v ≠ r → pos v = pos' v) {a b : Nat}
    (hla : lay p a = r) (hlb : lay p b = r) : delta p pos a b = delta p pos' a b := by
  have up : ∀ c, lay p c = r → ∀ u ∈ aboveOf p c, pos u = pos' u := by
    intro c hc u hu
    simp only [aboveOf, List.mem_map, List.mem_filter, beq_iff_eq] at hu
    obtain ⟨e, ⟨hemem, hhead⟩, rfl⟩ := hu
    have := hE e hemem
    rw [hhead, hc] at this
    exact h _ (by omega)
  have down : ∀ c, lay p c = r → ∀ v ∈ belowOf p c, pos v = pos' v := by
    intro c hc v hv
    simp only [belowOf, List.mem_map, List.mem_filter, beq_iff_eq] at hv
    obtain ⟨e, ⟨hemem, htail⟩, rfl⟩ := hv
    have := hE e hemem
    rw [htail, hc] at this
    exact h _ (by omega)
  unfold delta
  rw [swapDelta_congr (up a hla) (up b hlb), swapDelta_congr (down a hla) (down b hlb)]

theorem set_getD_self {L : List (List Nat)} {r : Nat} (hr : r < L.length) :
    L.set r (L.getD r []) = L := by
  have h : L.getD r [] = L[r] := by simp [List.getD_eq_getElem?_getD, hr]
  rw [h, List.set_getElem_self]

theorem scanGo_le {p : Proper} (hV : Valid p) {r : Nat} (pos₀ : Nat → Int) :
    ∀ (rest pre : List Nat) (c : Nat) (M : List (List Nat)),
      Layering p M → r < M.length → M.getD r [] = pre ++ c :: rest →
      (∀ v, lay p v ≠ r → posOf p M v = pos₀ v) →
      crossCount p (M.set r (pre ++ scanGo p pos₀ c rest)) ≤ crossCount p M := by
  intro rest
  induction rest with
  | nil =>
    intro pre c M _ hr hl _
    simp only [scanGo]
    have h := set_getD_self hr
    rw [hl] at h
    rw [show pre ++ [c] = pre ++ c :: [] from rfl, h]
    exact Nat.le_refl _
  | cons x rest' ih =>
    intro pre c M hM hr hl hpos
    obtain ⟨_, _, _, hlc, hlx⟩ := swap_facts hM hr (a := c) (b := x) (post := rest') hl
    have hd : delta p pos₀ c x = delta p (posOf p M) c x :=
      delta_congr (valid_edge_layers hV) (fun v hv => (hpos v hv).symm) hlc hlx
    unfold scanGo
    by_cases hneg : delta p pos₀ c x < 0
    · simp only [hneg, ite_true]
      have hswap := crossCount_swap hV hM hr hl
      have hperm : (pre ++ x :: c :: rest').Perm (M.getD r []) := by
        rw [hl]
        exact List.Perm.append_left pre (List.Perm.swap c x rest')
      have hM1 : Layering p (M.set r (pre ++ x :: c :: rest')) := layering_set hM hperm
      have hr1 : r < (M.set r (pre ++ x :: c :: rest')).length := by
        rw [List.length_set]
        exact hr
      have hget1 : (M.set r (pre ++ x :: c :: rest')).getD r [] = (pre ++ [x]) ++ c :: rest' := by
        rw [getD_set_self hr]
        simp
      have hpos1 : ∀ v, lay p v ≠ r →
          posOf p (M.set r (pre ++ x :: c :: rest')) v = pos₀ v := by
        intro v hv
        unfold posOf
        rw [getD_set_ne hv]
        exact hpos v hv
      have h2 := ih (pre ++ [x]) c _ hM1 hr1 hget1 hpos1
      rw [List.set_set] at h2
      have e : (pre ++ [x]) ++ scanGo p pos₀ c rest' = pre ++ x :: scanGo p pos₀ c rest' := by
        simp
      rw [e] at h2
      omega
    · simp only [hneg, ite_false]
      have h2 := ih (pre ++ [c]) x M hM hr (by rw [hl]; simp) hpos
      have e : (pre ++ [c]) ++ scanGo p pos₀ x rest' = pre ++ c :: scanGo p pos₀ x rest' := by
        simp
      rw [e] at h2
      exact h2

theorem transposeStep_le {p : Proper} (hV : Valid p) {L : List (List Nat)} (hL : Layering p L)
    (r : Nat) : crossCount p (transposeStep p L r) ≤ crossCount p L := by
  unfold transposeStep
  by_cases hr : r < L.length
  · cases hl : L.getD r [] with
    | nil =>
      have h := set_getD_self hr
      rw [hl] at h
      simp only [scanLayer]
      rw [h]
      exact Nat.le_refl _
    | cons c rest =>
      exact scanGo_le hV (posOf p L) rest [] c L hL hr (by rw [hl]; rfl) (fun v _ => rfl)
  · rw [List.set_eq_of_length_le (by omega)]
    exact Nat.le_refl _

theorem transposePass_le {p : Proper} (hV : Valid p) {L : List (List Nat)}
    (hL : Layering p L) :
    Layering p (transposePass p L) ∧ crossCount p (transposePass p L) ≤ crossCount p L :=
  foldl_inv (fun M => Layering p M ∧ crossCount p M ≤ crossCount p L) (transposeStep p)
    (List.range L.length) L ⟨hL, Nat.le_refl _⟩
    (fun _ hM r _ =>
      ⟨transposeStep_layering hM.1 r, Nat.le_trans (transposeStep_le hV hM.1 r) hM.2⟩)

theorem transposeLoop_le {p : Proper} (hV : Valid p) :
    ∀ (f : Nat) (L : List (List Nat)), Layering p L →
      crossCount p (transposeLoop p f L) ≤ crossCount p L := by
  intro f
  induction f with
  | zero =>
    intro L _
    exact Nat.le_refl _
  | succ f ih =>
    intro L hL
    obtain ⟨h1, h2⟩ := transposePass_le hV hL
    unfold transposeLoop
    simp only
    split
    · exact h2
    · exact Nat.le_trans (ih _ h1) h2

theorem transpose_crossings_le {p : Proper} (hV : Valid p) {L : List (List Nat)}
    (hL : Layering p L) : crossCount p (transpose p L) ≤ crossCount p L :=
  transposeLoop_le hV _ L hL

theorem ok_layers {p : Proper} {opts : OrderOptions} {L : List (List Nat)}
    (h : order p opts = .ok L) : ∃ r, orderWithBudget p opts = .ok r ∧ r.layers = L := by
  unfold order at h
  cases hr : orderWithBudget p opts with
  | error e =>
    rw [hr] at h
    exact absurd h (by simp)
  | ok r =>
    rw [hr] at h
    simp only [Except.ok.injEq] at h
    exact ⟨r, rfl, h⟩

theorem getD_nil_of_le {L : List (List Nat)} {i : Nat} (h : L.length ≤ i) : L.getD i [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem order_perm (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) :
    L.length = (initOrder p).length ∧
      ∀ i, (L.getD i []).Perm ((initOrder p).getD i []) := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  have hL := (orderWithBudget_spec p opts r hr).1
  have hlen : r.layers.length = (initOrder p).length := by
    rw [hL.1]
    simp [initOrder]
  refine ⟨hlen, fun i => ?_⟩
  by_cases hi : i < r.layers.length
  · have hi' : i < layerCount p := by rw [← hL.1]; exact hi
    have hinit : (initOrder p).getD i [] = layerNodes p i := by
      simp [initOrder, List.getD_eq_getElem?_getD, hi']
    rw [hinit]
    exact hL.2 i hi
  · rw [getD_nil_of_le (by omega), getD_nil_of_le (by omega)]

theorem order_crossings_le_init (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : crossCount p L ≤ crossCount p (initOrder p) := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  exact (orderWithBudget_spec p opts r hr).2

theorem order_valid_layering (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : Valid p ∧ Layering p L := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  refine ⟨?_, (orderWithBudget_spec p opts r hr).1⟩
  obtain ⟨start, key⟩ := opts
  cases start
  cases key
  unfold orderWithBudget at hr
  by_cases hv : Valid p
  · exact hv
  · simp [hv] at hr

end OrderImpl

export OrderImpl (order orderWithBudget initOrder crossCount naiveCrossCount transpose)

theorem order_perm (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) :
    L.length = (initOrder p).length ∧
      ∀ i, (L.getD i []).Perm ((initOrder p).getD i []) :=
  OrderImpl.order_perm p opts L h

theorem order_crossings_le_init (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : crossCount p L ≤ crossCount p (initOrder p) :=
  OrderImpl.order_crossings_le_init p opts L h

theorem transpose_crossings_le (p : Proper) (hV : OrderImpl.Valid p) (L : List (List Nat))
    (hL : OrderImpl.Layering p L) : crossCount p (transpose p L) ≤ crossCount p L :=
  OrderImpl.transpose_crossings_le hV hL

theorem crossCount_eq_naive (p : Proper) (L : List (List Nat)) :
    crossCount p L = naiveCrossCount p L :=
  OrderImpl.crossCount_eq_naive p L

theorem order_valid_layering (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : OrderImpl.Valid p ∧ OrderImpl.Layering p L :=
  OrderImpl.order_valid_layering p opts L h

private def refCase (decls : List Nat) (ranks : List Int) (edges : List (Nat × Nat)) :
    Proper :=
  { nodes := decls.map fun d => ⟨⟨d, 0, 0⟩, false, none⟩
    edges := edges.map fun (t, h) => ⟨t, h, 0, 0⟩
    rank := ranks
    chains := [] }

private def refOrder (p : Proper) : Option (List (List Nat) × Nat × Nat) :=
  match order p {} with
  | .ok L => some (L, naiveCrossCount p (initOrder p), naiveCrossCount p L)
  | .error _ => none

#guard refOrder (refCase [0, 1, 2, 3] [0, 0, 1, 0] [(1, 2)]) ==
  some ([[0, 1, 3], [2]], 0, 0)

#guard refOrder (refCase [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] [0, 1, 0, 0, 0, 0, 1, 1, 1, 2]
    [(5, 6), (6, 9), (0, 7), (8, 9), (8, 9), (3, 6), (0, 1)]) ==
  some ([[0, 2, 3, 4, 5], [1, 7, 6, 8], [9]], 2, 0)

#guard refOrder (refCase [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 2, 1, 2, 1]
    [(11, 15), (13, 14), (9, 12), (11, 13), (10, 14), (11, 13), (7, 15), (3, 9), (2, 9),
      (7, 8), (8, 14)]) ==
  some ([[0, 1, 2, 3, 4, 5, 6, 7, 11], [9, 10, 8, 15, 13], [12, 14]], 5, 0)

#guard refOrder (refCase [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 1]
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 2, 0, 0, 1, 2, 2, 3, 2]
    [(4, 14), (14, 18), (18, 17), (10, 15), (8, 10), (9, 15), (10, 11), (14, 16), (7, 11),
      (16, 17), (2, 10)]) ==
  some ([[0, 1, 2, 3, 4, 5, 6, 8, 12, 13], [7, 10, 9, 14], [11, 15, 18, 16], [17]], 6, 1)

#guard refOrder (refCase
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 12, 12, 18]
    [0, 0, 0, 1, 2, 0, 0, 1, 1, 1, 2, 0, 2, 2, 0, 1, 0, 3, 3, 4, 5, 6, 1, 4, 5, 1]
    [(6, 22), (22, 13), (3, 10), (8, 12), (18, 19), (8, 10), (5, 7), (0, 8), (10, 18),
      (0, 3), (19, 20), (2, 8), (4, 17), (18, 23), (23, 24), (24, 21), (9, 13), (6, 9),
      (12, 17), (20, 21), (14, 15), (2, 25), (25, 12)]) ==
  some ([[2, 1, 0, 5, 6, 11, 14, 16], [25, 8, 3, 7, 22, 9, 15], [4, 12, 10, 13], [17, 18],
      [23, 19], [24, 20], [21]], 16, 0)

#guard refOrder (refCase [0, 1, 2, 3] [0, 0, 1, 1] [(0, 3), (1, 2)]) ==
  some ([[0, 1], [3, 2]], 1, 0)

#guard (orderWithBudget (refCase [] [] []) {}).toOption.map (·.budgetExhausted) == some false

#guard (OrderImpl.runFrom (refCase [] [] []) 1 4 1 0 [] 0 0).budgetExhausted == true

#guard (order (refCase [0] [0, 0] []) {}).toOption == none

#guard (order (refCase [0, 1] [0, 2] [(0, 1)]) {}).toOption == none

end Layered
end Elegant
