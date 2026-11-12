import ElegantGeometry.Route
import Elegant.Layered.Cycles
import Elegant.Layered.Rank
import Elegant.Layered.Normalize

set_option autoImplicit false

namespace Elegant
namespace Layered

structure RoutingSegment where
  tail : Nat
  head : Nat
  decl : Nat
  slot : Int
  sourceX : Int
  targetX : Int
  edges : List Nat
deriving DecidableEq, Repr, Inhabited

structure RoutingGap where
  segments : List RoutingSegment
  slots : Int
deriving DecidableEq, Repr, Inhabited

structure Routing where
  gaps : List RoutingGap
  sourceX : List Int
  targetX : List Int
  segment : List Nat
deriving DecidableEq, Repr, Inhabited

structure EdgeRoute where
  original : Nat
  points : List Point
deriving DecidableEq, Repr, Inhabited

namespace RouteImpl

def edgeAt (p : Proper) (i : Nat) : ProperEdge := p.edges.getD i default

def nodeW (p : Proper) (v : Nat) : Int :=
  match p.nodes[v]? with
  | some n => n.node.w
  | none => 0

def nodeH (p : Proper) (v : Nat) : Int :=
  match p.nodes[v]? with
  | some n => n.node.h
  | none => 0

def nodeDecl (p : Proper) (v : Nat) : Nat :=
  match p.nodes[v]? with
  | some n => n.node.decl
  | none => 0

def xAt (x : List Int) (v : Nat) : Int := x.getD v 0

def layerHeight (p : Proper) (layer : List Nat) : Int :=
  layer.foldl (fun m v => max m (nodeH p v)) 0

def mapOk {α β : Type} (f : α → Except LayoutError β) : List α → Except LayoutError (List β)
  | [] => .ok []
  | a :: as =>
    match f a with
    | .error e => .error e
    | .ok b =>
      match mapOk f as with
      | .error e => .error e
      | .ok bs => .ok (b :: bs)

def sizesOk (p : Proper) : Bool :=
  p.nodes.all fun n =>
    decide (0 ≤ n.node.w ∧ n.node.w ≤ I32_MAX ∧ 0 ≤ n.node.h ∧ n.node.h ≤ I32_MAX)

def layersOk (p : Proper) (layers : List (List Nat)) : Bool :=
  decide (p.rank.length = p.nodes.length) && sizesOk p &&
    (List.range layers.length).all (fun k =>
      (layers.getD k []).all fun v => decide (v < p.nodes.length ∧ rk p.rank v = (k : Int))) &&
    decide layers.flatten.Nodup &&
    (List.range p.nodes.length).all (fun v => layers.flatten.contains v) &&
    p.edges.all fun e =>
      decide (e.tail < p.nodes.length ∧ e.head < p.nodes.length ∧
        rk p.rank e.head = rk p.rank e.tail + 1)

def otherEnd (e : ProperEdge) (v : Nat) : Nat := if e.tail = v then e.head else e.tail

def neighbourLE (p : Proper) (x : List Int) (a b : Nat) : Bool :=
  decide (xAt x a < xAt x b ∨ (xAt x a = xAt x b ∧
    (nodeDecl p a < nodeDecl p b ∨ (nodeDecl p a = nodeDecl p b ∧ a ≤ b))))

def portNeighbours (p : Proper) (x : List Int) (v : Nat) (es : List Nat) : List Nat :=
  ((es.map fun i => otherEnd (edgeAt p i) v).eraseDups).mergeSort (neighbourLE p x)

def outgoingOf (p : Proper) (v : Nat) : List Nat :=
  (List.range p.edges.length).filter fun i => (edgeAt p i).tail == v

def incomingOf (p : Proper) (v : Nat) : List Nat :=
  (List.range p.edges.length).filter fun i => (edgeAt p i).head == v

def portCoord (p : Proper) (x : List Int) (v : Nat) (es : List Nat) (i : Nat) : Int :=
  let ns := portNeighbours p x v es
  let w := nodeW p v
  let j := ns.idxOf (otherEnd (edgeAt p i) v)
  xAt x v - Int.fdiv w 2 + Int.fdiv (((j : Int) + 1) * w) ((ns.length : Int) + 1)

def portAt (p : Proper) (x : List Int) (v : Nat) (es : List Nat) (i : Nat) :
    Except LayoutError Int :=
  if portCoord p x v es i < I32_MIN ∨ I32_MAX < portCoord p x v es i then .error .overflow
  else .ok (portCoord p x v es i)

def sourcePort (p : Proper) (x : List Int) (i : Nat) : Except LayoutError Int :=
  portAt p x (edgeAt p i).tail (outgoingOf p (edgeAt p i).tail) i

def targetPort (p : Proper) (x : List Int) (i : Nat) : Except LayoutError Int :=
  portAt p x (edgeAt p i).head (incomingOf p (edgeAt p i).head) i

def gapOf (p : Proper) (i : Nat) : Nat := (rk p.rank (edgeAt p i).tail).toNat

def gapEdges (p : Proper) (g : Nat) : List Nat :=
  (List.range p.edges.length).filter fun i => gapOf p i == g

def segKey (p : Proper) (i : Nat) : Nat × Nat := ((edgeAt p i).tail, (edgeAt p i).head)

def gapKeys (p : Proper) (g : Nat) : List (Nat × Nat) :=
  ((gapEdges p g).map (segKey p)).eraseDups

def minDecl : List Nat → Nat
  | [] => 0
  | d :: ds => ds.foldl min d

def buildSegment (p : Proper) (sx tx : List Int) (g : Nat) (k : Nat × Nat) : RoutingSegment :=
  let es := (gapEdges p g).filter fun i => segKey p i == k
  { tail := k.1, head := k.2, decl := minDecl (es.map fun i => (edgeAt p i).decl), slot := -1,
    sourceX := sx.getD (es.headD 0) 0, targetX := tx.getD (es.headD 0) 0, edges := es }

def gapSegments (p : Proper) (sx tx : List Int) (g : Nat) : List RoutingSegment :=
  (gapKeys p g).map (buildSegment p sx tx g)

def segStraight (a : RoutingSegment) : Bool := decide (a.sourceX = a.targetX)

def segConflict (a b : RoutingSegment) : Bool :=
  !segStraight a && !segStraight b &&
    decide (max (min a.sourceX a.targetX) (min b.sourceX b.targetX) ≤
      min (max a.sourceX a.targetX) (max b.sourceX b.targetX))

def segBefore (a b : RoutingSegment) : Bool :=
  decide (a.sourceX < b.sourceX ∨ (a.sourceX = b.sourceX ∧ a.decl < b.decl))

def segArc (a b : RoutingSegment) : Bool := segBefore a b && segConflict a b

def kahnReady (n : Nat) (arc : Nat → Nat → Bool) (done : List Nat) (j : Nat) : Bool :=
  !done.contains j && (List.range n).all fun i => !arc i j || done.contains i

def kahnStep (n : Nat) (arc : Nat → Nat → Bool) (decl : Nat → Nat) (done : List Nat)
    (acc : Option Nat) (j : Nat) : Option Nat :=
  if kahnReady n arc done j then
    match acc with
    | none => some j
    | some v => if decl j < decl v then some j else acc
  else acc

def kahnPick (n : Nat) (arc : Nat → Nat → Bool) (decl : Nat → Nat) (done : List Nat) :
    Option Nat :=
  (List.range n).foldl (kahnStep n arc decl done) none

def kahnValue (n : Nat) (arc : Nat → Nat → Bool) (straight : Nat → Bool) (sl : Nat → Int)
    (v : Nat) : Int :=
  if straight v then -1
  else (List.range n).foldl (fun m i => if arc i v then max m (sl i + 1) else m) 0

def kahn (n : Nat) (arc : Nat → Nat → Bool) (decl : Nat → Nat) (straight : Nat → Bool) :
    Nat → List Nat → (Nat → Int) → (Nat → Int)
  | 0, _, sl => sl
  | fuel + 1, done, sl =>
    match kahnPick n arc decl done with
    | none => sl
    | some v =>
      kahn n arc decl straight fuel (v :: done)
        (fun j => if j = v then kahnValue n arc straight sl v else sl j)

def numberSlots (segs : List RoutingSegment) : Nat → Int :=
  kahn segs.length (fun i j => segArc (segs.getD i default) (segs.getD j default))
    (fun j => (segs.getD j default).decl) (fun j => segStraight (segs.getD j default))
    segs.length [] (fun _ => -1)

def numberGap (segs : List RoutingSegment) : RoutingGap :=
  let sl := numberSlots segs
  { segments := (List.range segs.length).map fun i => { segs.getD i default with slot := sl i }
    slots := (List.range segs.length).foldl
      (fun m i => if !segStraight (segs.getD i default) then max m (sl i + 1) else m) 0 }

def route (p : Proper) (layers : List (List Nat)) (x : List Int) : Except LayoutError Routing :=
  if I32_MAX < (p.nodes.length : Int) ∨ I32_MAX < (p.edges.length : Int) then .error .overflow
  else if !layersOk p layers ∨ x.length ≠ p.nodes.length then .error .domain
  else
    match mapOk (sourcePort p x) (List.range p.edges.length) with
    | .error e => .error e
    | .ok sx =>
      match mapOk (targetPort p x) (List.range p.edges.length) with
      | .error e => .error e
      | .ok tx =>
        .ok { gaps := (List.range (layers.length - 1)).map fun g =>
                numberGap (gapSegments p sx tx g)
              sourceX := sx
              targetX := tx
              segment := (List.range p.edges.length).map fun i =>
                (gapKeys p (gapOf p i)).idxOf (segKey p i) }

def edgesOf (p : Proper) (o : Nat) : List Nat :=
  (List.range p.edges.length).filter fun i => (edgeAt p i).original == o

def yAt (y : List Int) (v : Nat) : Int := y.getD v 0

def pieceStart (p : Proper) (y : List Int) (r : Routing) (i : Nat) : Point :=
  ⟨r.sourceX.getD i 0, yAt y (edgeAt p i).tail + nodeH p (edgeAt p i).tail⟩

def pieceEnd (p : Proper) (y : List Int) (r : Routing) (i : Nat) : Point :=
  ⟨r.targetX.getD i 0, yAt y (edgeAt p i).head⟩

def midOf (p : Proper) (slot : Int) (top heights : List Int) (r : Routing) (i : Nat) : Int :=
  top.getD (gapOf p i) 0 + heights.getD (gapOf p i) 0 +
    slot * (((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).slot + 1) +
    Int.fdiv slot 2

def pieceOf (p : Proper) (slot : Int) (y top heights : List Int) (r : Routing) (i : Nat) :
    Except LayoutError (List Point) :=
  if I32_MAX < (pieceStart p y r i).y then .error .overflow
  else if (pieceStart p y r i).x = (pieceEnd p y r i).x then
    .ok [pieceStart p y r i, pieceEnd p y r i]
  else if I32_MAX < midOf p slot top heights r i then .error .overflow
  else
    .ok [pieceStart p y r i, ⟨(pieceStart p y r i).x, midOf p slot top heights r i⟩,
      ⟨(pieceEnd p y r i).x, midOf p slot top heights r i⟩, pieceEnd p y r i]

def dedupFrom (last : Point) : List Point → List Point
  | [] => []
  | q :: qs => if q = last then dedupFrom last qs else q :: dedupFrom q qs

def dedup : List Point → List Point
  | [] => []
  | q :: qs => q :: dedupFrom q qs

def routeOf (p : Proper) (slot : Int) (y top heights : List Int) (r : Routing) (o : Nat) :
    Except LayoutError EdgeRoute :=
  match mapOk (pieceOf p slot y top heights r) (edgesOf p o) with
  | .error e => .error e
  | .ok pcs => .ok ⟨o, dedup pcs.flatten⟩

def routePointsWith (slot : Int) (p : Proper) (layers : List (List Nat)) (x y top : List Int)
    (r : Routing) : Except LayoutError (List EdgeRoute) :=
  if I32_MAX < (p.nodes.length : Int) ∨ I32_MAX < (p.edges.length : Int) then .error .overflow
  else if !layersOk p layers ∨ x.length ≠ p.nodes.length ∨ y.length ≠ p.nodes.length ∨
      top.length ≠ layers.length ∨ slot < 1 then .error .domain
  else
    mapOk (routeOf p slot y top (layers.map (layerHeight p)) r) (List.range p.chains.length)

def pairsAll (P : Point → Point → Prop) : List Point → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => P p q ∧ pairsAll P (q :: rest)

theorem isOrthogonal_iff :
    ∀ l : List Point, Polyline.isOrthogonal l = true ↔
      pairsAll (fun p q => p.x = q.x ∨ p.y = q.y) l
  | [] => by simp [Polyline.isOrthogonal, pairsAll]
  | [_] => by simp [Polyline.isOrthogonal, pairsAll]
  | p :: q :: rest => by
    rw [Polyline.isOrthogonal_cons]
    simp only [pairsAll, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    rw [isOrthogonal_iff (q :: rest)]

theorem allSegsMiss_iff (R : Rect) :
    ∀ l : List Point, Polyline.allSegsMiss l R ↔
      pairsAll (fun p q => Polyline.segMisses p q R) l
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | p :: q :: rest => by
    simp only [Polyline.allSegsMiss, pairsAll]
    rw [allSegsMiss_iff R (q :: rest)]

theorem pairsAll_dedupFrom (P : Point → Point → Prop) :
    ∀ (qs : List Point) (last : Point), pairsAll P (last :: qs) →
      pairsAll P (last :: dedupFrom last qs)
  | [], last, _ => by simp [dedupFrom, pairsAll]
  | q :: qs, last, h => by
    by_cases hq : q = last
    · subst hq
      simp only [dedupFrom, ite_true]
      exact pairsAll_dedupFrom P qs q h.2
    · simp only [dedupFrom, hq, ite_false]
      exact ⟨h.1, pairsAll_dedupFrom P qs q h.2⟩

theorem pairsAll_dedup (P : Point → Point → Prop) :
    ∀ l : List Point, pairsAll P l → pairsAll P (dedup l)
  | [], _ => by simp [dedup, pairsAll]
  | q :: qs, h => by
    simp only [dedup]
    exact pairsAll_dedupFrom P qs q h

theorem dedup_head (l : List Point) : (dedup l).head? = l.head? := by
  cases l <;> simp [dedup]

theorem dedupFrom_getLast (last : Point) :
    ∀ qs : List Point, (last :: dedupFrom last qs).getLast? = (last :: qs).getLast?
  | [] => by simp [dedupFrom]
  | q :: qs => by
    by_cases hq : q = last
    · subst hq
      simp only [dedupFrom, ite_true]
      rw [dedupFrom_getLast q qs]
      cases qs <;> simp
    · simp only [dedupFrom, hq, ite_false]
      have := dedupFrom_getLast q qs
      rw [List.getLast?_cons_cons, this]
      cases qs <;> simp

theorem dedup_getLast (l : List Point) : (dedup l).getLast? = l.getLast? := by
  cases l with
  | nil => simp [dedup]
  | cons q qs => simp only [dedup]; exact dedupFrom_getLast q qs

def Zipped {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Zipped R as bs
  | _, _ => False

theorem mapOk_zipped {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (ys : List β), mapOk f l = .ok ys → Zipped (fun a b => f a = .ok b) l ys
  | [], ys, h => by
    simp only [mapOk, Except.ok.injEq] at h
    subst h
    trivial
  | a :: as, ys, h => by
    simp only [mapOk] at h
    split at h
    · simp at h
    · next b hb =>
      split at h
      · simp at h
      · next bs hbs =>
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hb, mapOk_zipped f as bs hbs⟩

theorem mapOk_length {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (ys : List β), mapOk f l = .ok ys → ys.length = l.length
  | [], ys, h => by
    simp only [mapOk, Except.ok.injEq] at h
    subst h
    rfl
  | a :: as, ys, h => by
    simp only [mapOk] at h
    split at h
    · simp at h
    · next b hb =>
      split at h
      · simp at h
      · next bs hbs =>
        simp only [Except.ok.injEq] at h
        subst h
        simp [mapOk_length f as bs hbs]

theorem mapOk_mem {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (ys : List β), mapOk f l = .ok ys → ∀ y ∈ ys, ∃ a ∈ l, f a = .ok y
  | [], ys, h => by
    simp only [mapOk, Except.ok.injEq] at h
    subst h
    simp
  | a :: as, ys, h => by
    simp only [mapOk] at h
    split at h
    · simp at h
    · next b hb =>
      split at h
      · simp at h
      · next bs hbs =>
        simp only [Except.ok.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, by simp, hb⟩
        · obtain ⟨a', ha', hf⟩ := mapOk_mem f as bs hbs y hy
          exact ⟨a', by simp [ha'], hf⟩

theorem mapOk_getElem {α β : Type} (f : α → Except LayoutError β) :
    ∀ (l : List α) (ys : List β), mapOk f l = .ok ys →
      ∀ (i : Nat) (hi : i < l.length), ∃ b, ys[i]? = some b ∧ f l[i] = .ok b
  | [], ys, h, i, hi => by simp at hi
  | a :: as, ys, h, i, hi => by
    simp only [mapOk] at h
    split at h
    · simp at h
    · next b hb =>
      split at h
      · simp at h
      · next bs hbs =>
        simp only [Except.ok.injEq] at h
        subst h
        cases i with
        | zero => exact ⟨b, by simp, by simpa using hb⟩
        | succ i =>
          obtain ⟨b', h1, h2⟩ := mapOk_getElem f as bs hbs i (by simpa using hi)
          exact ⟨b', by simpa using h1, by simpa using h2⟩

def chainRel (R : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | i :: j :: rest => R i j ∧ chainRel R (j :: rest)

theorem pairsAll_append_of (P : Point → Point → Prop) :
    ∀ (A B : List Point) (a b : Point), A.getLast? = some a → B.head? = some b →
      pairsAll P A → P a b → pairsAll P B → pairsAll P (A ++ B)
  | [], B, a, b, hA, _, _, _, _ => by simp at hA
  | [c], B, a, b, hA, hB, _, hab, hPB => by
    simp at hA
    subst hA
    cases B with
    | nil => simp at hB
    | cons b' B' =>
      simp at hB
      subst hB
      exact ⟨hab, hPB⟩
  | c :: d :: A'', B, a, b, hA, hB, hPA, hab, hPB => by
    have hA' : (d :: A'').getLast? = some a := by
      rw [List.getLast?_cons_cons] at hA
      exact hA
    have := pairsAll_append_of P (d :: A'') B a b hA' hB hPA.2 hab hPB
    exact ⟨hPA.1, this⟩

theorem pairsAll_flatten_of (P : Point → Point → Prop) (S E : Nat → Point)
    (R : Nat → Nat → Prop) (hR : ∀ i j, R i j → P (E i) (S j)) :
    ∀ (es : List Nat) (pcs : List (List Point)),
      Zipped (fun i pc => pc.head? = some (S i) ∧ pc.getLast? = some (E i) ∧ pairsAll P pc) es pcs →
      chainRel R es → pairsAll P pcs.flatten
  | [], pcs, hz, _ => by
    cases pcs with
    | nil => simp [pairsAll]
    | cons _ _ => exact hz.elim
  | [i], pcs, hz, _ => by
    cases pcs with
    | nil => exact hz.elim
    | cons pc pcs' =>
      cases pcs' with
      | nil => simpa using hz.1.2.2
      | cons _ _ => exact hz.2.elim
  | i :: j :: rest, pcs, hz, hc => by
    cases pcs with
    | nil => exact hz.elim
    | cons pc pcs' =>
      cases pcs' with
      | nil => exact hz.2.elim
      | cons pc2 pcs'' =>
        have ih := pairsAll_flatten_of P S E R hR (j :: rest) (pc2 :: pcs'') hz.2 hc.2
        have hhead : (pc2 :: pcs'').flatten.head? = some (S j) := by
          have := hz.2.1.1
          cases hpc2 : pc2 with
          | nil => rw [hpc2] at this; simp at this
          | cons q qs =>
            rw [hpc2] at this
            simp at this
            simp [this]
        show pairsAll P (pc ++ (pc2 :: pcs'').flatten)
        exact pairsAll_append_of P pc _ (E i) (S j) hz.1.2.1 hhead hz.1.2.2 (hR i j hc.1) ih
theorem foldl_cmax_ge (g : Nat → Int) (P : Nat → Bool) :
    ∀ (l : List Nat) (m : Int), m ≤ l.foldl (fun m i => if P i then max m (g i) else m) m
  | [], m => Int.le_refl m
  | a :: l, m => by
    simp only [List.foldl_cons]
    have h1 := foldl_cmax_ge g P l (if P a then max m (g a) else m)
    have h2 : m ≤ (if P a then max m (g a) else m) := by
      split <;> omega
    exact Int.le_trans h2 h1

theorem foldl_cmax_ge_mem (g : Nat → Int) (P : Nat → Bool) :
    ∀ (l : List Nat) (m : Int) (i : Nat), i ∈ l → P i = true →
      g i ≤ l.foldl (fun m i => if P i then max m (g i) else m) m
  | [], m, i, h, _ => by simp at h
  | a :: l, m, i, h, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with hia | hil
    · have h1 := foldl_cmax_ge g P l (if P a then max m (g a) else m)
      have h2 : g i ≤ (if P a then max m (g a) else m) := by
        rw [hia]
        rw [hia] at hp
        simp only [hp, ↓reduceIte]
        omega
      exact Int.le_trans h2 h1
    · exact foldl_cmax_ge_mem g P l _ i hil hp

theorem kahnReady_iff {n : Nat} {arc : Nat → Nat → Bool} {done : List Nat} {j : Nat} :
    kahnReady n arc done j = true ↔ j ∉ done ∧ ∀ i, i < n → arc i j = true → i ∈ done := by
  simp only [kahnReady, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun i hi hij => ?_⟩
    rcases h2 i hi with h | h
    · rw [h] at hij; exact absurd hij (by decide)
    · simpa using h
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun i hi => ?_⟩
    by_cases hij : arc i j = true
    · exact Or.inr (by simpa using h2 i hi hij)
    · exact Or.inl (by simpa using hij)

theorem kahnPick_fold (n : Nat) (arc : Nat → Nat → Bool) (decl : Nat → Nat) (done : List Nat) :
    ∀ (l : List Nat) (acc : Option Nat),
      (∀ v, l.foldl (kahnStep n arc decl done) acc = some v →
        acc = some v ∨ (v ∈ l ∧ kahnReady n arc done v = true)) ∧
      (l.foldl (kahnStep n arc decl done) acc = none →
        acc = none ∧ ∀ j ∈ l, kahnReady n arc done j = false)
  | [], acc => by simp
  | a :: l, acc => by
    simp only [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := kahnPick_fold n arc decl done l (kahnStep n arc decl done acc a)
    constructor
    · intro v hv
      rcases ih1 v hv with h | h
      · unfold kahnStep at h
        by_cases hr : kahnReady n arc done a = true
        · simp only [hr, ↓reduceIte] at h
          cases acc with
          | none =>
            simp only [Option.some.injEq] at h
            exact Or.inr ⟨by simp [h], by rw [← h]; exact hr⟩
          | some w =>
            simp only at h
            by_cases hd : decl a < decl w
            · simp only [hd, ↓reduceIte] at h
              simp only [Option.some.injEq] at h
              exact Or.inr ⟨by simp [h], by rw [← h]; exact hr⟩
            · simp only [hd, ↓reduceIte] at h
              exact Or.inl h
        · simp only [hr] at h
          exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩
    · intro hv
      obtain ⟨h1, h2⟩ := ih2 hv
      unfold kahnStep at h1
      by_cases hr : kahnReady n arc done a = true
      · simp only [hr, ↓reduceIte] at h1
        cases acc with
        | none => simp at h1
        | some w =>
          simp only at h1
          by_cases hd : decl a < decl w
          · simp [hd] at h1
          · simp [hd] at h1
      · simp only [hr] at h1
        refine ⟨h1, fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · simpa using hr
        · exact h2 j hj

theorem kahnPick_some {n : Nat} {arc : Nat → Nat → Bool} {decl : Nat → Nat} {done : List Nat}
    {v : Nat} (h : kahnPick n arc decl done = some v) :
    v < n ∧ kahnReady n arc done v = true := by
  have := (kahnPick_fold n arc decl done (List.range n) none).1 v h
  rcases this with h | h
  · simp at h
  · exact ⟨List.mem_range.mp h.1, h.2⟩

theorem kahnPick_none {n : Nat} {arc : Nat → Nat → Bool} {decl : Nat → Nat} {done : List Nat}
    (h : kahnPick n arc decl done = none) : ∀ j, j < n → kahnReady n arc done j = false := by
  intro j hj
  exact ((kahnPick_fold n arc decl done (List.range n) none).2 h).2 j (List.mem_range.mpr hj)

theorem exists_min_mem (lt : Nat → Nat → Prop) (hirr : ∀ i, ¬ lt i i)
    (htrans : ∀ i j k, lt i j → lt j k → lt i k) :
    ∀ (L : List Nat), L ≠ [] → ∃ m ∈ L, ∀ x ∈ L, ¬ lt x m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun x hx => by
      have : x = a := by simpa using hx
      subst this
      exact hirr x⟩
  | a :: b :: L, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_mem lt hirr htrans (b :: L) (by simp)
    by_cases hlt : lt a m
    · refine ⟨a, by simp, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hirr x
      · intro hxa
        exact hmin x hx (htrans x a m hxa hlt)
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hlt
      · exact hmin x hx

theorem exists_ready {n : Nat} {arc : Nat → Nat → Bool} (lt : Nat → Nat → Prop)
    (hirr : ∀ i, ¬ lt i i) (htrans : ∀ i j k, lt i j → lt j k → lt i k)
    (harc : ∀ i j, arc i j = true → lt i j) (done : List Nat) {j0 : Nat} (hj0 : j0 < n)
    (hnd : j0 ∉ done) : ∃ j, j < n ∧ kahnReady n arc done j = true := by
  have hne : (List.range n).filter (fun j => !done.contains j) ≠ [] := by
    intro h
    have : j0 ∈ (List.range n).filter (fun j => !done.contains j) := by
      simp [List.mem_filter, List.mem_range, hj0, hnd]
    rw [h] at this
    simp at this
  obtain ⟨m, hm, hmin⟩ := exists_min_mem lt hirr htrans _ hne
  simp only [List.mem_filter, List.mem_range, Bool.not_eq_true'] at hm hmin
  have hmd : m ∉ done := fun h => by
    have h2 := List.contains_iff_mem.mpr h
    have h3 := hm.2
    rw [h2] at h3
    exact absurd h3 (by decide)
  refine ⟨m, hm.1, kahnReady_iff.mpr ⟨hmd, fun i hi hij => ?_⟩⟩
  refine Classical.byContradiction fun hnot => ?_
  exact hmin i ⟨hi, Bool.eq_false_iff.mpr (fun h => hnot (List.contains_iff_mem.mp h))⟩
    (harc i m hij)

structure KInv (n : Nat) (arc : Nat → Nat → Bool) (straight : Nat → Bool) (done : List Nat)
    (sl : Nat → Int) : Prop where
  nodup : done.Nodup
  lt_n : ∀ j ∈ done, j < n
  arcs : ∀ j ∈ done, ∀ i, i < n → arc i j = true → i ∈ done ∧ sl i + 1 ≤ sl j
  nonneg : ∀ j ∈ done, straight j = false → 0 ≤ sl j

theorem kinv_step {n : Nat} {arc : Nat → Nat → Bool} {straight : Nat → Bool}
    (harc : ∀ i j, arc i j = true → straight i = false ∧ straight j = false)
    {done : List Nat} {sl : Nat → Int} {v : Nat} (hI : KInv n arc straight done sl)
    (hr : kahnReady n arc done v = true) (hv : v < n) :
    KInv n arc straight (v :: done)
      (fun j => if j = v then kahnValue n arc straight sl v else sl j) := by
  obtain ⟨hvn, hpre⟩ := kahnReady_iff.mp hr
  have hne : ∀ k ∈ done, k ≠ v := fun k hk h => hvn (h ▸ hk)
  refine ⟨List.nodup_cons.mpr ⟨hvn, hI.nodup⟩, ?_, ?_, ?_⟩
  · intro j hj
    rcases List.mem_cons.mp hj with hj | hj
    · rw [hj]; exact hv
    · exact hI.lt_n j hj
  · intro j hj i hi hij
    by_cases hjv : j = v
    · have hij' : arc i v = true := by rw [← hjv]; exact hij
      have hid := hpre i hi hij'
      have hiv : i ≠ v := hne i hid
      have hs : straight v = false := (harc i v hij').2
      refine ⟨List.mem_cons_of_mem _ hid, ?_⟩
      have hval : sl i + 1 ≤ kahnValue n arc straight sl v := by
        unfold kahnValue
        rw [hs]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact foldl_cmax_ge_mem (fun i => sl i + 1) (fun i => arc i v) (List.range n) 0 i
          (List.mem_range.mpr hi) hij'
      simp [hjv, hiv, hval]
    · have hjd : j ∈ done := (List.mem_cons.mp hj).resolve_left hjv
      obtain ⟨hid, hle⟩ := hI.arcs j hjd i hi hij
      refine ⟨List.mem_cons_of_mem _ hid, ?_⟩
      have hiv := hne i hid
      simp only [hiv, hjv, ↓reduceIte]
      exact hle
  · intro j hj hsj
    by_cases hjv : j = v
    · have hs : straight v = false := by rw [← hjv]; exact hsj
      have h0 : 0 ≤ kahnValue n arc straight sl v := by
        unfold kahnValue
        rw [hs]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact foldl_cmax_ge (fun i => sl i + 1) (fun i => arc i v) (List.range n) 0
      simpa [hjv] using h0
    · have hjd : j ∈ done := (List.mem_cons.mp hj).resolve_left hjv
      simp only [hjv, ↓reduceIte]
      exact hI.nonneg j hjd hsj

theorem kinv_conclude {n : Nat} {arc : Nat → Nat → Bool} {straight : Nat → Bool}
    {done : List Nat} {sl : Nat → Int} (hI : KInv n arc straight done sl)
    (hall : ∀ j, j < n → j ∈ done) :
    (∀ j, j < n → ∀ i, i < n → arc i j = true → sl i + 1 ≤ sl j) ∧
      (∀ j, j < n → straight j = false → 0 ≤ sl j) :=
  ⟨fun j hj i hi h => (hI.arcs j (hall j hj) i hi h).2,
   fun j hj hs => hI.nonneg j (hall j hj) hs⟩

theorem kahn_spec {n : Nat} {arc : Nat → Nat → Bool} {decl : Nat → Nat}
    {straight : Nat → Bool} (lt : Nat → Nat → Prop) (hirr : ∀ i, ¬ lt i i)
    (htrans : ∀ i j k, lt i j → lt j k → lt i k) (harc_lt : ∀ i j, arc i j = true → lt i j)
    (harc : ∀ i j, arc i j = true → straight i = false ∧ straight j = false) :
    ∀ (fuel : Nat) (done : List Nat) (sl : Nat → Int), KInv n arc straight done sl →
      n ≤ done.length + fuel →
      (∀ j, j < n → ∀ i, i < n → arc i j = true →
        kahn n arc decl straight fuel done sl i + 1 ≤ kahn n arc decl straight fuel done sl j) ∧
      (∀ j, j < n → straight j = false →
        0 ≤ kahn n arc decl straight fuel done sl j)
  | 0, done, sl, hI, hlen => by
    have hall : ∀ j, j < n → j ∈ done := by
      intro j hj
      refine Classical.byContradiction fun hnot => ?_
      have hnd : (j :: done).Nodup := List.nodup_cons.mpr ⟨hnot, hI.nodup⟩
      have hsub : (j :: done) ⊆ List.range n := by
        intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · rw [hk]; exact List.mem_range.mpr hj
        · exact List.mem_range.mpr (hI.lt_n k hk)
      have := hnd.length_le_of_subset hsub
      simp at this
      omega
    simpa [kahn] using kinv_conclude hI hall
  | fuel + 1, done, sl, hI, hlen => by
    simp only [kahn]
    cases hp : kahnPick n arc decl done with
    | none =>
      have hall : ∀ j, j < n → j ∈ done := by
        intro j hj
        refine Classical.byContradiction fun hnot => ?_
        obtain ⟨k, hk, hrk⟩ := exists_ready lt hirr htrans harc_lt done hj hnot
        have := kahnPick_none hp k hk
        rw [hrk] at this
        exact absurd this (by decide)
      exact kinv_conclude hI hall
    | some v =>
      obtain ⟨hvn, hrv⟩ := kahnPick_some hp
      have hI' := kinv_step harc hI hrv hvn
      exact kahn_spec lt hirr htrans harc_lt harc fuel (v :: done) _ hI' (by
        simp only [List.length_cons]; omega)

theorem segStraight_false {a : RoutingSegment} :
    segStraight a = false ↔ a.sourceX ≠ a.targetX := by
  simp [segStraight]

theorem segBefore_irrefl (a : RoutingSegment) : segBefore a a = false := by
  simp [segBefore]

theorem segBefore_trans {a b c : RoutingSegment} (h1 : segBefore a b = true)
    (h2 : segBefore b c = true) : segBefore a c = true := by
  simp only [segBefore, decide_eq_true_eq] at h1 h2 ⊢
  omega

theorem segArc_before {a b : RoutingSegment} (h : segArc a b = true) : segBefore a b = true := by
  simp only [segArc, Bool.and_eq_true] at h
  exact h.1

theorem segArc_straight {a b : RoutingSegment} (h : segArc a b = true) :
    segStraight a = false ∧ segStraight b = false := by
  simp only [segArc, segConflict, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.2.1.1, h.2.1.2⟩

theorem segConflict_comm {a b : RoutingSegment} (h : segConflict a b = true) :
    segConflict b a = true := by
  simp only [segConflict, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨⟨h2, h1⟩, by omega⟩

theorem numberSlots_spec (segs : List RoutingSegment) :
    (∀ i j, i < segs.length → j < segs.length →
      segArc (segs.getD i default) (segs.getD j default) = true →
      numberSlots segs i + 1 ≤ numberSlots segs j) ∧
    (∀ j, j < segs.length → segStraight (segs.getD j default) = false →
      0 ≤ numberSlots segs j) := by
  have key := kahn_spec (n := segs.length)
    (arc := fun i j => segArc (segs.getD i default) (segs.getD j default))
    (decl := fun j => (segs.getD j default).decl)
    (straight := fun j => segStraight (segs.getD j default))
    (fun i j => segBefore (segs.getD i default) (segs.getD j default) = true)
    (fun i h => by simp [segBefore_irrefl] at h)
    (fun i j k h1 h2 => segBefore_trans h1 h2)
    (fun i j h => segArc_before h)
    (fun i j h => segArc_straight h) segs.length [] (fun _ => -1)
    ⟨List.nodup_nil, fun j hj => by simp at hj, fun j hj => by simp at hj,
      fun j hj => by simp at hj⟩
    (by simp)
  exact ⟨fun i j hi hj h => key.1 j hj i hi h, key.2⟩

theorem mem_numberGap_segments {segs : List RoutingSegment} {s : RoutingSegment}
    (h : s ∈ (numberGap segs).segments) :
    ∃ i, i < segs.length ∧ s = { segs.getD i default with slot := numberSlots segs i } := by
  simp only [numberGap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, hi, rfl⟩

theorem numberGap_slots_nonneg (segs : List RoutingSegment) : 0 ≤ (numberGap segs).slots :=
  foldl_cmax_ge (fun i => numberSlots segs i + 1)
    (fun i => !segStraight (segs.getD i default)) (List.range segs.length) 0

theorem numberGap_slots_ge {segs : List RoutingSegment} {i : Nat} (hi : i < segs.length)
    (hs : segStraight (segs.getD i default) = false) :
    numberSlots segs i + 1 ≤ (numberGap segs).slots :=
  foldl_cmax_ge_mem (fun i => numberSlots segs i + 1)
    (fun i => !segStraight (segs.getD i default)) (List.range segs.length) 0 i
    (List.mem_range.mpr hi) (by rw [hs]; rfl)

theorem numberGap_separates (segs : List RoutingSegment)
    (hkeys : ∀ i j, i < segs.length → j < segs.length →
      ((segs.getD i default).tail ≠ (segs.getD j default).tail ∨
        (segs.getD i default).head ≠ (segs.getD j default).head) →
      (segs.getD i default).sourceX ≠ (segs.getD j default).sourceX ∨
        (segs.getD i default).decl ≠ (segs.getD j default).decl) :
    ∀ i j, i < segs.length → j < segs.length →
      ((segs.getD i default).tail ≠ (segs.getD j default).tail ∨
        (segs.getD i default).head ≠ (segs.getD j default).head) →
      segConflict (segs.getD i default) (segs.getD j default) = true →
      numberSlots segs i ≠ numberSlots segs j := by
  intro i j hi hj htr hc
  have hcj := segConflict_comm hc
  have hk := hkeys i j hi hj htr
  obtain ⟨hs1, hs2⟩ := numberSlots_spec segs
  have hbefore : segBefore (segs.getD i default) (segs.getD j default) = true ∨
      segBefore (segs.getD j default) (segs.getD i default) = true := by
    simp only [segBefore, decide_eq_true_eq]
    omega
  rcases hbefore with hb | hb
  · have harc : segArc (segs.getD i default) (segs.getD j default) = true := by
      simp only [segArc, Bool.and_eq_true]; exact ⟨hb, hc⟩
    have := hs1 i j hi hj harc
    omega
  · have harc : segArc (segs.getD j default) (segs.getD i default) = true := by
      simp only [segArc, Bool.and_eq_true]; exact ⟨hb, hcj⟩
    have := hs1 j i hj hi harc
    omega


theorem layersOk_spec {p : Proper} {layers : List (List Nat)} (h : layersOk p layers = true) :
    p.rank.length = p.nodes.length ∧
    (∀ v, v < p.nodes.length → 0 ≤ nodeW p v ∧ 0 ≤ nodeH p v) ∧
    (∀ (k : Nat) (l : List Nat), layers[k]? = some l → ∀ v ∈ l,
      v < p.nodes.length ∧ rk p.rank v = (k : Int)) ∧
    (∀ v, v < p.nodes.length →
      ∃ l, layers[(rk p.rank v).toNat]? = some l ∧ v ∈ l ∧ 0 ≤ rk p.rank v) ∧
    (∀ i, i < p.edges.length → (edgeAt p i).tail < p.nodes.length ∧
      (edgeAt p i).head < p.nodes.length ∧
      rk p.rank (edgeAt p i).head = rk p.rank (edgeAt p i).tail + 1) := by
  unfold layersOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨hlen, hsz⟩, hlay⟩, _⟩, hcov⟩, hedge⟩ := h
  have hsz' : ∀ nd ∈ p.nodes,
      0 ≤ nd.node.w ∧ nd.node.w ≤ I32_MAX ∧ 0 ≤ nd.node.h ∧ nd.node.h ≤ I32_MAX := by
    simpa [sizesOk, List.all_eq_true] using hsz
  have hlay' : ∀ (k : Nat) (l : List Nat), layers[k]? = some l → ∀ v ∈ l,
      v < p.nodes.length ∧ rk p.rank v = (k : Int) := by
    intro k l hkl v hv
    have hk : k < layers.length := (List.getElem?_eq_some_iff.mp hkl).1
    have hg : layers.getD k [] = l := by simp [List.getD_eq_getElem?_getD, hkl]
    exact hlay k hk v (by rw [hg]; exact hv)
  refine ⟨hlen, ?_, hlay', ?_, ?_⟩
  · intro v hv
    have hm := hsz' (p.nodes[v]) (List.getElem_mem hv)
    have hn : p.nodes[v]? = some p.nodes[v] := List.getElem?_eq_getElem hv
    simp only [nodeW, nodeH, hn]
    exact ⟨hm.1, hm.2.2.1⟩
  · intro v hv
    obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp (hcov v hv)
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
    have := hlay' k l hk v hvl
    have hk' : (rk p.rank v).toNat = k := by omega
    exact ⟨l, by rw [hk']; exact hk, hvl, by omega⟩
  · intro i hi
    have hmem : edgeAt p i ∈ p.edges := by
      have : edgeAt p i = p.edges[i] := by
        simp [edgeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [this]
      exact List.getElem_mem hi
    exact hedge _ hmem

theorem mapOk_range_getD {f : Nat → Except LayoutError Int} {m : Nat} {ys : List Int}
    (h : mapOk f (List.range m) = .ok ys) :
    ys.length = m ∧ ∀ i, i < m → f i = .ok (ys.getD i 0) := by
  refine ⟨by simpa using mapOk_length f _ ys h, fun i hi => ?_⟩
  obtain ⟨b, hb, hf⟩ := mapOk_getElem f (List.range m) ys h i (by simpa using hi)
  have hb' : ys.getD i 0 = b := by simp [List.getD_eq_getElem?_getD, hb]
  rw [hb']
  simpa using hf

theorem route_spec {p : Proper} {layers : List (List Nat)} {x : List Int} {r : Routing}
    (h : route p layers x = .ok r) :
    layersOk p layers = true ∧ x.length = p.nodes.length ∧
    r.sourceX.length = p.edges.length ∧ r.targetX.length = p.edges.length ∧
    (∀ i, i < p.edges.length → sourcePort p x i = .ok (r.sourceX.getD i 0) ∧
        targetPort p x i = .ok (r.targetX.getD i 0)) ∧
    r.gaps = (List.range (layers.length - 1)).map
      (fun g => numberGap (gapSegments p r.sourceX r.targetX g)) ∧
    r.segment = (List.range p.edges.length).map
      (fun i => (gapKeys p (gapOf p i)).idxOf (segKey p i)) := by
  unfold route at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next h2 =>
      split at h
      · simp at h
      · next sx hsx =>
        split at h
        · simp at h
        · next tx htx =>
          simp only [Except.ok.injEq] at h
          subst h
          have hl : layersOk p layers = true := by
            refine Classical.byContradiction fun hc => ?_
            exact h2 (Or.inl (by simpa using hc))
          have hx : x.length = p.nodes.length := by
            refine Classical.byContradiction fun hc => ?_
            exact h2 (Or.inr hc)
          obtain ⟨hsl, hs⟩ := mapOk_range_getD hsx
          obtain ⟨htl, ht⟩ := mapOk_range_getD htx
          exact ⟨hl, hx, hsl, htl, fun i hi => ⟨hs i hi, ht i hi⟩, rfl, rfl⟩

theorem portAt_eq {p : Proper} {x : List Int} {v : Nat} {es : List Nat} {i : Nat} {a : Int}
    (h : portAt p x v es i = .ok a) : a = portCoord p x v es i := by
  unfold portAt at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h
    exact h.symm

theorem portCoord_bounds {p : Proper} {x : List Int} {v : Nat} {es : List Nat} {i : Nat}
    (hi : i ∈ es) (hw : 0 ≤ nodeW p v) :
    xAt x v - Int.fdiv (nodeW p v) 2 ≤ portCoord p x v es i ∧
      portCoord p x v es i ≤ xAt x v - Int.fdiv (nodeW p v) 2 + nodeW p v := by
  have hmem : otherEnd (edgeAt p i) v ∈ portNeighbours p x v es := by
    unfold portNeighbours
    rw [List.mem_mergeSort, List.mem_eraseDups]
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  have hj := List.idxOf_lt_length_of_mem hmem
  unfold portCoord
  simp only
  generalize (portNeighbours p x v es).idxOf (otherEnd (edgeAt p i) v) = j at hj ⊢
  generalize (portNeighbours p x v es).length = len at hj ⊢
  have h1 : 0 ≤ Int.fdiv (((j : Int) + 1) * nodeW p v) ((len : Int) + 1) :=
    Int.fdiv_nonneg (Int.mul_nonneg (by omega) hw) (by omega)
  have h2 : Int.fdiv (((j : Int) + 1) * nodeW p v) ((len : Int) + 1) ≤ nodeW p v := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
    apply Int.ediv_le_of_le_mul (by omega)
    have : ((j : Int) + 1) * nodeW p v ≤ ((len : Int) + 1) * nodeW p v :=
      Int.mul_le_mul_of_nonneg_right (by omega) hw
    rw [Int.mul_comm (nodeW p v)]
    exact this
  omega

theorem sourcePort_congr {p : Proper} {x : List Int} {i i' : Nat}
    (ht : (edgeAt p i).tail = (edgeAt p i').tail) (hh : (edgeAt p i).head = (edgeAt p i').head) :
    sourcePort p x i = sourcePort p x i' := by
  unfold sourcePort portAt portCoord otherEnd
  simp only [ht, hh]

theorem targetPort_congr {p : Proper} {x : List Int} {i i' : Nat}
    (ht : (edgeAt p i).tail = (edgeAt p i').tail) (hh : (edgeAt p i).head = (edgeAt p i').head) :
    targetPort p x i = targetPort p x i' := by
  unfold targetPort portAt portCoord otherEnd
  simp only [ht, hh]

theorem mem_outgoingOf {p : Proper} {i : Nat} (hi : i < p.edges.length) :
    i ∈ outgoingOf p (edgeAt p i).tail := by
  simp [outgoingOf, hi]

theorem mem_incomingOf {p : Proper} {i : Nat} (hi : i < p.edges.length) :
    i ∈ incomingOf p (edgeAt p i).head := by
  simp [incomingOf, hi]

theorem port_ranges {p : Proper} {layers : List (List Nat)} {x : List Int} {r : Routing}
    (h : route p layers x = .ok r) {i : Nat} (hi : i < p.edges.length) :
    xAt x (edgeAt p i).tail - Int.fdiv (nodeW p (edgeAt p i).tail) 2 ≤ r.sourceX.getD i 0 ∧
      r.sourceX.getD i 0 ≤ xAt x (edgeAt p i).tail - Int.fdiv (nodeW p (edgeAt p i).tail) 2 +
        nodeW p (edgeAt p i).tail ∧
    xAt x (edgeAt p i).head - Int.fdiv (nodeW p (edgeAt p i).head) 2 ≤ r.targetX.getD i 0 ∧
      r.targetX.getD i 0 ≤ xAt x (edgeAt p i).head - Int.fdiv (nodeW p (edgeAt p i).head) 2 +
        nodeW p (edgeAt p i).head := by
  obtain ⟨hl, _, _, _, hp, _⟩ := route_spec h
  obtain ⟨_, hsz, _, _, hedge⟩ := layersOk_spec hl
  obtain ⟨h1, h2, _⟩ := hedge i hi
  have hs := portAt_eq (hp i hi).1
  have ht := portAt_eq (hp i hi).2
  have b1 := portCoord_bounds (x := x) (mem_outgoingOf hi) (hsz _ h1).1
  have b2 := portCoord_bounds (x := x) (mem_incomingOf hi) (hsz _ h2).1
  rw [hs]
  rw [ht]
  exact ⟨b1.1, b1.2, b2.1, b2.2⟩

theorem getD_map_range {α : Type} (f : Nat → α) (n i : Nat) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem buildSegment_ports {p : Proper} {x sx tx : List Int}
    (hs : ∀ i, i < p.edges.length → sourcePort p x i = .ok (sx.getD i 0))
    (ht : ∀ i, i < p.edges.length → targetPort p x i = .ok (tx.getD i 0))
    {i : Nat} (hi : i < p.edges.length) :
    (buildSegment p sx tx (gapOf p i) (segKey p i)).sourceX = sx.getD i 0 ∧
    (buildSegment p sx tx (gapOf p i) (segKey p i)).targetX = tx.getD i 0 := by
  have hes : i ∈ (gapEdges p (gapOf p i)).filter (fun i' => segKey p i' == segKey p i) := by
    simp [gapEdges, hi]
  unfold buildSegment
  simp only
  generalize hE : (gapEdges p (gapOf p i)).filter (fun i' => segKey p i' == segKey p i) = es
    at hes ⊢
  cases es with
  | nil => simp at hes
  | cons a es' =>
    have ha : a ∈ (gapEdges p (gapOf p i)).filter (fun i' => segKey p i' == segKey p i) := by
      rw [hE]; simp
    obtain ⟨hga, hka⟩ := List.mem_filter.mp ha
    have ham : a < p.edges.length := by
      simp only [gapEdges, List.mem_filter, List.mem_range] at hga
      exact hga.1
    have hk : segKey p a = segKey p i := by simpa using hka
    have hk1 : (edgeAt p a).tail = (edgeAt p i).tail := by
      have := congrArg Prod.fst hk
      simpa [segKey] using this
    have hk2 : (edgeAt p a).head = (edgeAt p i).head := by
      have := congrArg Prod.snd hk
      simpa [segKey] using this
    have e1 : sourcePort p x a = sourcePort p x i := sourcePort_congr hk1 hk2
    have e2 : targetPort p x a = targetPort p x i := targetPort_congr hk1 hk2
    rw [hs a ham, hs i hi] at e1
    rw [ht a ham, ht i hi] at e2
    simp only [Except.ok.injEq] at e1 e2
    simp only [List.headD_cons]
    exact ⟨e1, e2⟩

theorem route_segment_facts {p : Proper} {layers : List (List Nat)} {x : List Int} {r : Routing}
    (h : route p layers x = .ok r) {i : Nat} (hi : i < p.edges.length) :
    gapOf p i + 1 < layers.length ∧
    0 ≤ (r.gaps.getD (gapOf p i) default).slots ∧
    ((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).sourceX =
      r.sourceX.getD i 0 ∧
    ((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).targetX =
      r.targetX.getD i 0 ∧
    (r.sourceX.getD i 0 ≠ r.targetX.getD i 0 →
      0 ≤ ((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).slot ∧
      ((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).slot + 1 ≤
        (r.gaps.getD (gapOf p i) default).slots) := by
  obtain ⟨hl, _, _, _, hp, hgaps, hseg⟩ := route_spec h
  obtain ⟨_, _, _, hcov, hedge⟩ := layersOk_spec hl
  obtain ⟨ht1, hh1, hrk⟩ := hedge i hi
  obtain ⟨lt, hlt, _, hlt0⟩ := hcov _ ht1
  obtain ⟨lh, hlh, _, hlh0⟩ := hcov _ hh1
  have hg : gapOf p i + 1 < layers.length := by
    have : (rk p.rank (edgeAt p i).head).toNat < layers.length :=
      (List.getElem?_eq_some_iff.mp hlh).1
    have e : (rk p.rank (edgeAt p i).head).toNat = gapOf p i + 1 := by
      simp only [gapOf]; omega
    omega
  have hgap : r.gaps.getD (gapOf p i) default =
      numberGap (gapSegments p r.sourceX r.targetX (gapOf p i)) := by
    rw [hgaps]
    exact getD_map_range _ _ _ (by omega) _
  have hsegi : r.segment.getD i 0 = (gapKeys p (gapOf p i)).idxOf (segKey p i) := by
    rw [hseg]
    exact getD_map_range _ _ _ hi _
  have hkey : segKey p i ∈ gapKeys p (gapOf p i) := by
    simp only [gapKeys, List.mem_eraseDups, List.mem_map]
    exact ⟨i, by simp [gapEdges, hi], rfl⟩
  have hk : (gapKeys p (gapOf p i)).idxOf (segKey p i) < (gapKeys p (gapOf p i)).length :=
    List.idxOf_lt_length_of_mem hkey
  have hsl : (gapSegments p r.sourceX r.targetX (gapOf p i)).length =
      (gapKeys p (gapOf p i)).length := by
    simp [gapSegments]
  have hseg' : (gapSegments p r.sourceX r.targetX (gapOf p i)).getD
      ((gapKeys p (gapOf p i)).idxOf (segKey p i)) default =
      buildSegment p r.sourceX r.targetX (gapOf p i) (segKey p i) := by
    have := List.getElem_idxOf hk
    simp only [gapSegments, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hk, this]
    rfl
  obtain ⟨hs, ht⟩ := buildSegment_ports (fun i hi => (hp i hi).1) (fun i hi => (hp i hi).2) hi
  rw [hgap, hsegi]
  generalize hidx : (gapKeys p (gapOf p i)).idxOf (segKey p i) = idx at hk hseg' ⊢
  generalize hsegs : gapSegments p r.sourceX r.targetX (gapOf p i) = segs at hsl hseg' ⊢
  have hidxl : idx < segs.length := by rw [hsl]; exact hk
  have hG : (numberGap segs).segments.getD idx default =
      { segs.getD idx default with slot := numberSlots segs idx } := by
    simp only [numberGap]
    exact getD_map_range _ _ _ hidxl _
  have hstr : segStraight (segs.getD idx default) = false ↔
      r.sourceX.getD i 0 ≠ r.targetX.getD i 0 := by
    rw [hseg', segStraight_false]
    simp only [hs, ht]
  rw [hG, hseg']
  refine ⟨hg, numberGap_slots_nonneg segs, hs, ht, fun hne => ?_⟩
  have hf := hstr.mpr hne
  exact ⟨(numberSlots_spec segs).2 idx hidxl hf, numberGap_slots_ge hidxl hf⟩

structure Geo where
  rk : Nat → Nat
  left : Nat → Int
  wid : Nat → Int
  yv : Nat → Int
  hv : Nat → Int
  T : Nat → Int
  H : Nat → Int

def Geo.rect (G : Geo) (v : Nat) : Rect := ⟨G.left v, G.yv v, G.wid v, G.hv v⟩

structure Geo.Ok (G : Geo) (n K : Nat) : Prop where
  wid_nn : ∀ v, v < n → 0 ≤ G.wid v
  hv_nn : ∀ v, v < n → 0 ≤ G.hv v
  H_nn : ∀ k, k < K → 0 ≤ G.H k
  rk_lt : ∀ v, v < n → G.rk v < K
  band : ∀ v, v < n → G.T (G.rk v) ≤ G.yv v ∧ G.yv v + G.hv v ≤ G.T (G.rk v) + G.H (G.rk v)
  mono : ∀ k k', k < k' → k' < K → G.T k + G.H k ≤ G.T k'
  apart : ∀ u v, u < n → v < n → G.rk u = G.rk v → u ≠ v →
    G.left u + G.wid u ≤ G.left v ∨ G.left v + G.wid v ≤ G.left u

theorem miss_left {P Q : Point} {R : Rect} (h : max P.x Q.x ≤ R.x) :
    Polyline.segMisses P Q R := Or.inl h

theorem miss_right {P Q : Point} {R : Rect} (h : R.x + R.w ≤ min P.x Q.x) :
    Polyline.segMisses P Q R := Or.inr (Or.inl h)

theorem miss_above {P Q : Point} {R : Rect} (h : max P.y Q.y ≤ R.y) :
    Polyline.segMisses P Q R := Or.inr (Or.inr (Or.inl h))

theorem miss_below {P Q : Point} {R : Rect} (h : R.y + R.h ≤ min P.y Q.y) :
    Polyline.segMisses P Q R := Or.inr (Or.inr (Or.inr (Or.inl h)))

local macro "geo_omega" : tactic => `(tactic| (dsimp only [Geo.rect]; omega))

theorem range_miss {G : Geo} {u v : Nat} {P Q : Point}
    (hap : G.left u + G.wid u ≤ G.left v ∨ G.left v + G.wid v ≤ G.left u)
    (hP : G.left u ≤ P.x ∧ P.x ≤ G.left u + G.wid u)
    (hQ : G.left u ≤ Q.x ∧ Q.x ≤ G.left u + G.wid u) :
    Polyline.segMisses P Q (G.rect v) := by
  rcases hap with h | h
  · apply miss_left
    geo_omega
  · apply miss_right
    geo_omega

theorem junction_miss {G : Geo} {n K : Nat} (hG : G.Ok n K) {d v : Nat} (hd : d < n)
    (hv : v < n) (hvd : v ≠ d) {tx sx : Int}
    (h1 : G.left d ≤ tx ∧ tx ≤ G.left d + G.wid d)
    (h2 : G.left d ≤ sx ∧ sx ≤ G.left d + G.wid d) :
    Polyline.segMisses ⟨tx, G.yv d⟩ ⟨sx, G.yv d + G.hv d⟩ (G.rect v) := by
  have bd := hG.band d hd
  have bv := hG.band v hv
  have hvn := hG.hv_nn v hv
  have hdn := hG.hv_nn d hd
  have hKv := hG.rk_lt v hv
  have hKd := hG.rk_lt d hd
  rcases Nat.lt_trichotomy (G.rk v) (G.rk d) with hlt | heq | hgt
  · have hm := hG.mono _ _ hlt hKd
    apply miss_below
    geo_omega
  · exact range_miss (hG.apart d v hd hv heq.symm (Ne.symm hvd)) h1 h2
  · have hm := hG.mono _ _ hgt hKv
    apply miss_above
    geo_omega

theorem piece_miss {G : Geo} {n K : Nat} (hG : G.Ok n K) {t h v : Nat} (ht : t < n)
    (hh : h < n) (hv : v < n) (hrk : G.rk h = G.rk t + 1) (hvt : v ≠ t) (hvh : v ≠ h)
    {sx tx : Int} (hsx : G.left t ≤ sx ∧ sx ≤ G.left t + G.wid t)
    (htx : G.left h ≤ tx ∧ tx ≤ G.left h + G.wid h) {pc : List Point}
    (hpc : (pc = [⟨sx, G.yv t + G.hv t⟩, ⟨tx, G.yv h⟩] ∧ sx = tx) ∨
      ∃ mid, G.T (G.rk t) + G.H (G.rk t) ≤ mid ∧ mid ≤ G.T (G.rk t + 1) ∧
        pc = [⟨sx, G.yv t + G.hv t⟩, ⟨sx, mid⟩, ⟨tx, mid⟩, ⟨tx, G.yv h⟩]) :
    pairsAll (fun P Q => Polyline.segMisses P Q (G.rect v)) pc := by
  have bt := hG.band t ht
  have bh := hG.band h hh
  have bv := hG.band v hv
  have hvn := hG.hv_nn v hv
  have htn := hG.hv_nn t ht
  have hhn := hG.hv_nn h hh
  have hKh := hG.rk_lt h hh
  have hKt := hG.rk_lt t ht
  have hKv := hG.rk_lt v hv
  have hH0 := hG.H_nn (G.rk t) hKt
  have hH1 := hG.H_nn (G.rk h) hKh
  have hstep := hG.mono (G.rk t) (G.rk h) (by omega) hKh
  rw [hrk] at bh hH1 hstep
  rcases (by omega : G.rk v < G.rk t ∨ G.rk v = G.rk t ∨ G.rk v = G.rk t + 1 ∨
      G.rk t + 2 ≤ G.rk v) with c | c | c | c
  · have hm := hG.mono _ _ c hKt
    rcases hpc with ⟨rfl, hs⟩ | ⟨mid, hm1, hm2, rfl⟩
    · exact ⟨miss_below (by geo_omega), trivial⟩
    · exact ⟨miss_below (by geo_omega), miss_below (by geo_omega), miss_below (by geo_omega),
        trivial⟩
  · have hap := hG.apart t v ht hv c.symm (Ne.symm hvt)
    rw [c] at bv
    rcases hpc with ⟨rfl, hs⟩ | ⟨mid, hm1, hm2, rfl⟩
    · subst hs
      exact ⟨range_miss hap hsx hsx, trivial⟩
    · exact ⟨range_miss hap hsx hsx, miss_below (by geo_omega), miss_below (by geo_omega),
        trivial⟩
  · have hap := hG.apart h v hh hv (by omega) (Ne.symm hvh)
    rw [c] at bv
    rcases hpc with ⟨rfl, hs⟩ | ⟨mid, hm1, hm2, rfl⟩
    · subst hs
      exact ⟨range_miss hap htx htx, trivial⟩
    · exact ⟨miss_above (by geo_omega), miss_above (by geo_omega), range_miss hap htx htx,
        trivial⟩
  · have hm := hG.mono (G.rk t + 1) (G.rk v) (by omega) hKv
    rcases hpc with ⟨rfl, hs⟩ | ⟨mid, hm1, hm2, rfl⟩
    · exact ⟨miss_above (by geo_omega), trivial⟩
    · exact ⟨miss_above (by geo_omega), miss_above (by geo_omega), miss_above (by geo_omega),
        trivial⟩

def coordSep (gap : Int) (p : Proper) (a b : Nat) : Int :=
  Int.fdiv (nodeW p a) 2 + Int.fdiv (nodeW p b) 2 + gap

structure CoordFacts (p : Proper) (layers : List (List Nat)) (x y top : List Int) (r : Routing)
    (gap rankGap slot : Int) : Prop where
  gap_pos : 1 ≤ gap
  rank_gap_nonneg : 0 ≤ rankGap
  slot_pos : 1 ≤ slot
  half_slot_le : Int.fdiv slot 2 ≤ rankGap
  separated : ∀ layer ∈ layers, ∀ (i a b : Nat), layer[i]? = some a → layer[i + 1]? = some b →
    coordSep gap p a b ≤ xAt x b - xAt x a
  node_in_band : ∀ (k : Nat) (l : List Nat) (v : Nat), layers[k]? = some l → v ∈ l →
    v < p.nodes.length → rk p.rank v = (k : Int) →
    top.getD k 0 ≤ yAt y v ∧ yAt y v + nodeH p v ≤ top.getD k 0 + layerHeight p l
  band_step : ∀ (k : Nat) (l : List Nat), layers[k]? = some l → k + 1 < layers.length →
    top.getD (k + 1) 0 =
      top.getD k 0 + layerHeight p l + rankGap + slot * (r.gaps.getD k default).slots

def routeGeo (p : Proper) (layers : List (List Nat)) (x y top : List Int) : Geo where
  rk v := (Elegant.Layered.rk p.rank v).toNat
  left v := xAt x v - Int.fdiv (nodeW p v) 2
  wid v := nodeW p v
  yv v := yAt y v
  hv v := nodeH p v
  T k := top.getD k 0
  H k := (layers.map (layerHeight p)).getD k 0

theorem heights_getD {p : Proper} {layers : List (List Nat)} {k : Nat} {l : List Nat}
    (hk : layers[k]? = some l) : (layers.map (layerHeight p)).getD k 0 = layerHeight p l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hk]

theorem foldl_max_ge (f : Nat → Int) :
    ∀ (l : List Nat) (m : Int), m ≤ l.foldl (fun m v => max m (f v)) m
  | [], m => Int.le_refl m
  | a :: l, m => by
    simp only [List.foldl_cons]
    exact Int.le_trans (by omega) (foldl_max_ge f l (max m (f a)))

theorem layerHeight_nonneg (p : Proper) (l : List Nat) : 0 ≤ layerHeight p l :=
  foldl_max_ge (nodeH p) l 0

theorem top_mono {p : Proper} {layers : List (List Nat)} {top : List Int} {r : Routing}
    {rankGap slot : Int} (hrg : 0 ≤ rankGap) (hsl : 0 ≤ slot)
    (hnn : ∀ k, k + 1 < layers.length → 0 ≤ (r.gaps.getD k default).slots)
    (hstep : ∀ (k : Nat) (l : List Nat), layers[k]? = some l → k + 1 < layers.length →
      top.getD (k + 1) 0 =
        top.getD k 0 + layerHeight p l + rankGap + slot * (r.gaps.getD k default).slots) :
    ∀ (d k : Nat), k + d + 1 < layers.length →
      top.getD k 0 + (layers.map (layerHeight p)).getD k 0 ≤ top.getD (k + d + 1) 0
  | 0, k, hk => by
    obtain ⟨l, hl⟩ : ∃ l, layers[k]? = some l := ⟨layers[k]'(by omega), List.getElem?_eq_getElem _⟩
    rw [heights_getD hl]
    have := hstep k l hl (by omega)
    have h2 := Int.mul_nonneg hsl (hnn k (by omega))
    have e0 : k + 0 + 1 = k + 1 := by omega
    rw [e0]
    omega
  | d + 1, k, hk => by
    have ih := top_mono hrg hsl hnn hstep d k (by omega)
    obtain ⟨l, hl⟩ : ∃ l, layers[k + d + 1]? = some l :=
      ⟨layers[k + d + 1]'(by omega), List.getElem?_eq_getElem _⟩
    have h1 := hstep (k + d + 1) l hl (by omega)
    have h2 := Int.mul_nonneg hsl (hnn (k + d + 1) (by omega))
    have h3 := layerHeight_nonneg p l
    have e : k + (d + 1) + 1 = k + d + 1 + 1 := by omega
    rw [e, h1]
    omega

theorem pairwise_of_separated {gap : Int} (hgap : 1 ≤ gap) {p : Proper} {x : List Int} :
    ∀ (L : List Nat), (∀ v ∈ L, 0 ≤ nodeW p v) →
      (∀ (i a b : Nat), L[i]? = some a → L[i + 1]? = some b →
        coordSep gap p a b ≤ xAt x b - xAt x a) →
      List.Pairwise (fun a b => xAt x a - Int.fdiv (nodeW p a) 2 + nodeW p a ≤
        xAt x b - Int.fdiv (nodeW p b) 2) L
  | [], _, _ => List.Pairwise.nil
  | [a], _, _ => List.pairwise_singleton _ _
  | a :: b :: L, hw, hs => by
    have ih := pairwise_of_separated hgap (b :: L) (fun v hv => hw v (List.mem_cons_of_mem _ hv))
      (fun i a' b' h1 h2 => hs (i + 1) a' b' (by simpa using h1) (by simpa using h2))
    have hab := hs 0 a b (by simp) (by simp)
    have hwa := hw a (by simp)
    have hwb := hw b (by simp)
    have e : ∀ w : Int, Int.fdiv w 2 = w / 2 := fun w => Int.fdiv_eq_ediv_of_nonneg w (by decide)
    unfold coordSep at hab
    have rab : xAt x a - Int.fdiv (nodeW p a) 2 + nodeW p a ≤
        xAt x b - Int.fdiv (nodeW p b) 2 := by
      simp only [e] at hab ⊢
      omega
    refine List.pairwise_cons.mpr ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.mp hc with hcb | hc
    · rw [hcb]; exact rab
    · have hbc := (List.pairwise_cons.mp ih).1 c hc
      have hbc' : xAt x b - Int.fdiv (nodeW p b) 2 + nodeW p b ≤ xAt x c - Int.fdiv (nodeW p c) 2 := hbc
      omega

theorem apart_of_pairwise {R : Nat → Nat → Prop} :
    ∀ (L : List Nat), L.Pairwise R → ∀ u ∈ L, ∀ v ∈ L, u ≠ v → R u v ∨ R v u
  | [], _, u, hu, _, _, _ => by simp at hu
  | a :: L, hp, u, hu, v, hv, hne => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hu with hua | hu'
    · rcases List.mem_cons.mp hv with hva | hv'
      · exact absurd (hua.trans hva.symm) hne
      · rw [hua]; exact Or.inl (h1 v hv')
    · rcases List.mem_cons.mp hv with hva | hv'
      · rw [hva]; exact Or.inr (h1 u hu')
      · exact apart_of_pairwise L h2 u hu' v hv' hne

theorem geo_ok {p : Proper} {layers : List (List Nat)} {x y top : List Int} {r : Routing}
    {gap rankGap slot : Int} (hr : route p layers x = .ok r)
    (hF : CoordFacts p layers x y top r gap rankGap slot) :
    (routeGeo p layers x y top).Ok p.nodes.length layers.length := by
  obtain ⟨hl, _, _, _, _, hgaps, _⟩ := route_spec hr
  obtain ⟨_, hsz, hlay, hcov, _⟩ := layersOk_spec hl
  have hgapnn : ∀ k, k + 1 < layers.length → 0 ≤ (r.gaps.getD k default).slots := by
    intro k hk
    rw [hgaps, getD_map_range _ _ _ (by omega) _]
    exact numberGap_slots_nonneg _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (hsz v hv).1
  · intro v hv
    exact (hsz v hv).2
  · intro k hk
    obtain ⟨l, hl⟩ : ∃ l, layers[k]? = some l := ⟨layers[k], List.getElem?_eq_getElem hk⟩
    show 0 ≤ (layers.map (layerHeight p)).getD k 0
    rw [heights_getD hl]
    exact layerHeight_nonneg p l
  · intro v hv
    obtain ⟨l, hl, _, _⟩ := hcov v hv
    exact (List.getElem?_eq_some_iff.mp hl).1
  · intro v hv
    obtain ⟨l, hl, hvl, h0⟩ := hcov v hv
    have := hF.node_in_band _ l v hl hvl hv (by omega)
    show top.getD (rk p.rank v).toNat 0 ≤ yAt y v ∧ yAt y v + nodeH p v ≤
      top.getD (rk p.rank v).toNat 0 + (layers.map (layerHeight p)).getD (rk p.rank v).toNat 0
    rw [heights_getD hl]
    exact this
  · intro k k' hkk hk'
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkk
    exact top_mono hF.rank_gap_nonneg (by have := hF.slot_pos; omega) hgapnn hF.band_step d k hk'
  · intro u v hu hv h hne
    obtain ⟨lu, hlu, hul, _⟩ := hcov u hu
    obtain ⟨lv, hlv, hvl, _⟩ := hcov v hv
    have h' : (rk p.rank u).toNat = (rk p.rank v).toNat := h
    rw [h'] at hlu
    have hleq : lu = lv := Option.some.inj (hlu.symm.trans hlv)
    subst hleq
    have hpw := pairwise_of_separated hF.gap_pos lu
      (fun w hw => by
        obtain ⟨hwn, _⟩ := hlay _ lu hlv w hw
        exact (hsz w hwn).1)
      (hF.separated lu (List.mem_of_getElem? hlv))
    exact apart_of_pairwise lu hpw u hul v hvl hne

def FlatDummy (p : Proper) (v : Nat) : Prop :=
  ∃ nd, p.nodes[v]? = some nd ∧ nd.dummy = true ∧ nd.node.h = 0

def ChainLink (p : Proper) (i j : Nat) : Prop :=
  i < p.edges.length ∧ j < p.edges.length ∧ (edgeAt p i).head = (edgeAt p j).tail ∧
    FlatDummy p (edgeAt p j).tail

def ProperShape (p : Proper) : Prop := ∀ o, chainRel (ChainLink p) (edgesOf p o)

def IsReal (p : Proper) (v : Nat) : Prop := ∀ nd, p.nodes[v]? = some nd → nd.dummy = false

def boxRect (p : Proper) (x y : List Int) (v : Nat) : Rect :=
  ⟨xAt x v - Int.fdiv (nodeW p v) 2, yAt y v, nodeW p v, nodeH p v⟩

def routePoints (p : Proper) (layers : List (List Nat)) (x y top : List Int) (r : Routing) :
    Except LayoutError (List EdgeRoute) :=
  match NormalizeImpl.defaultSlot with
  | some slot => routePointsWith slot p layers x y top r
  | none => .error .domain

theorem flatDummy_h {p : Proper} {v : Nat} (h : FlatDummy p v) : nodeH p v = 0 := by
  obtain ⟨nd, hnd, _, hh⟩ := h
  simp [nodeH, hnd, hh]

theorem mem_edgesOf {p : Proper} {o i : Nat} (h : i ∈ edgesOf p o) : i < p.edges.length := by
  simp only [edgesOf, List.mem_filter, List.mem_range] at h
  exact h.1

theorem Zipped.imp {α β : Type} {R R' : α → β → Prop} :
    ∀ (l : List α) (ys : List β), (∀ a ∈ l, ∀ b, R a b → R' a b) → Zipped R l ys →
      Zipped R' l ys
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | a :: as, b :: bs, hl, h =>
    ⟨hl a (List.mem_cons_self) b h.1,
      Zipped.imp as bs (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha')) h.2⟩

theorem pieceOf_cases {p : Proper} {slot : Int} {y top heights : List Int} {r : Routing}
    {i : Nat} {pc : List Point} (h : pieceOf p slot y top heights r i = .ok pc) :
    (pc = [pieceStart p y r i, pieceEnd p y r i] ∧
      r.sourceX.getD i 0 = r.targetX.getD i 0) ∨
    (pc = [pieceStart p y r i, ⟨r.sourceX.getD i 0, midOf p slot top heights r i⟩,
        ⟨r.targetX.getD i 0, midOf p slot top heights r i⟩, pieceEnd p y r i] ∧
      r.sourceX.getD i 0 ≠ r.targetX.getD i 0) := by
  unfold pieceOf at h
  split at h
  · simp at h
  · split at h
    · next hx =>
      simp only [Except.ok.injEq] at h
      exact Or.inl ⟨h.symm, hx⟩
    · split at h
      · simp at h
      · next hx _ =>
        simp only [Except.ok.injEq] at h
        exact Or.inr ⟨h.symm, hx⟩

theorem pieceOf_basic {p : Proper} {slot : Int} {y top heights : List Int} {r : Routing}
    {i : Nat} {pc : List Point} (h : pieceOf p slot y top heights r i = .ok pc) :
    pc.head? = some (pieceStart p y r i) ∧ pc.getLast? = some (pieceEnd p y r i) ∧
      pairsAll (fun P Q => P.x = Q.x ∨ P.y = Q.y) pc := by
  rcases pieceOf_cases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · exact ⟨rfl, rfl, Or.inl hx, trivial⟩
  · exact ⟨rfl, rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl, trivial⟩

theorem routePointsWith_spec {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute}
    (h : routePointsWith slot p layers x y top r = .ok routes) :
    layersOk p layers = true ∧ 1 ≤ slot ∧ x.length = p.nodes.length ∧
    ∀ rt ∈ routes, ∃ pcs, Zipped (fun i pc =>
        pieceOf p slot y top (layers.map (layerHeight p)) r i = .ok pc)
      (edgesOf p rt.original) pcs ∧ rt.points = dedup pcs.flatten := by
  unfold routePointsWith at h
  split at h
  · simp at h
  · next h1 =>
    split at h
    · simp at h
    · next h2 =>
      have hl : layersOk p layers = true := by
        refine Classical.byContradiction fun hc => ?_
        exact h2 (Or.inl (by simpa using hc))
      have hx : x.length = p.nodes.length := by
        refine Classical.byContradiction fun hc => ?_
        exact h2 (Or.inr (Or.inl hc))
      have hs : 1 ≤ slot := by
        refine Classical.byContradiction fun hc => ?_
        exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
      refine ⟨hl, hs, hx, fun rt hrt => ?_⟩
      obtain ⟨o, _, hro⟩ := mapOk_mem _ _ routes h rt hrt
      unfold routeOf at hro
      split at hro
      · simp at hro
      · next pcs hpcs =>
        simp only [Except.ok.injEq] at hro
        subst hro
        exact ⟨pcs, mapOk_zipped _ _ _ hpcs, rfl⟩

theorem route_orthogonal_aux {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute} (hP : ProperShape p)
    (h : routePointsWith slot p layers x y top r = .ok routes) :
    ∀ rt ∈ routes, Polyline.isOrthogonal rt.points = true := by
  intro rt hrt
  obtain ⟨_, _, _, hspec⟩ := routePointsWith_spec h
  obtain ⟨pcs, hz, hpts⟩ := hspec rt hrt
  rw [hpts, isOrthogonal_iff]
  apply pairsAll_dedup
  refine pairsAll_flatten_of _ (pieceStart p y r) (pieceEnd p y r) (ChainLink p) ?_
    (edgesOf p rt.original) pcs ?_ (hP rt.original)
  · intro i j hij
    obtain ⟨_, _, hhead, hfd⟩ := hij
    have h0 := flatDummy_h hfd
    refine Or.inr ?_
    show yAt y (edgeAt p i).head = yAt y (edgeAt p j).tail + nodeH p (edgeAt p j).tail
    rw [hhead, h0]
    omega
  · exact Zipped.imp _ _ (fun i _ pc hpc => pieceOf_basic hpc) hz

theorem mem_of_head' {l : List Nat} {a : Nat} (h : l.head? = some a) : a ∈ l := by
  obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.mp h
  simp

theorem flatten_head {S E : Nat → Point} :
    ∀ (es : List Nat) (pcs : List (List Point)),
      Zipped (fun i pc => pc.head? = some (S i) ∧ pc.getLast? = some (E i)) es pcs →
      ∀ i₀, es.head? = some i₀ → pcs.flatten.head? = some (S i₀)
  | [], _, _, i₀, h => by simp at h
  | i :: es', pcs, hz, i₀, h => by
    cases pcs with
    | nil => exact hz.elim
    | cons pc pcs' =>
      have hi : i = i₀ := by simpa using h
      rw [← hi]
      have h1 := hz.1.1
      simp only [List.flatten_cons]
      cases pc with
      | nil => simp at h1
      | cons q qs =>
        simp only [List.cons_append, List.head?_cons] at h1 ⊢
        exact h1

theorem flatten_last {S E : Nat → Point} :
    ∀ (es : List Nat) (pcs : List (List Point)),
      Zipped (fun i pc => pc.head? = some (S i) ∧ pc.getLast? = some (E i)) es pcs →
      ∀ i₁, es.getLast? = some i₁ → pcs.flatten.getLast? = some (E i₁)
  | [], _, _, i₁, h => by simp at h
  | [i], pcs, hz, i₁, h => by
    cases pcs with
    | nil => exact hz.elim
    | cons pc pcs' =>
      cases pcs' with
      | nil =>
        have hi : i = i₁ := by simpa using h
        rw [← hi]
        simpa using hz.1.2
      | cons _ _ => exact hz.2.elim
  | i :: j :: rest, pcs, hz, i₁, h => by
    cases pcs with
    | nil => exact hz.elim
    | cons pc pcs' =>
      cases pcs' with
      | nil => exact hz.2.elim
      | cons pc2 pcs'' =>
        have ih := flatten_last (j :: rest) (pc2 :: pcs'') hz.2 i₁ (by simpa using h)
        simp only [List.flatten_cons] at ih ⊢
        rw [List.getLast?_append, ih]
        rfl

theorem route_endpoints_aux {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute}
    (hr : route p layers x = .ok r) (h : routePointsWith slot p layers x y top r = .ok routes) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (edgesOf p rt.original).head? = some i₀ →
      (edgesOf p rt.original).getLast? = some i₁ →
      ∃ px qx, sourcePort p x i₀ = .ok px ∧ targetPort p x i₁ = .ok qx ∧
        xAt x (edgeAt p i₀).tail - Int.fdiv (nodeW p (edgeAt p i₀).tail) 2 ≤ px ∧
        px ≤ xAt x (edgeAt p i₀).tail - Int.fdiv (nodeW p (edgeAt p i₀).tail) 2 +
          nodeW p (edgeAt p i₀).tail ∧
        xAt x (edgeAt p i₁).head - Int.fdiv (nodeW p (edgeAt p i₁).head) 2 ≤ qx ∧
        qx ≤ xAt x (edgeAt p i₁).head - Int.fdiv (nodeW p (edgeAt p i₁).head) 2 +
          nodeW p (edgeAt p i₁).head ∧
        rt.points.head? = some ⟨px, yAt y (edgeAt p i₀).tail + nodeH p (edgeAt p i₀).tail⟩ ∧
        rt.points.getLast? = some ⟨qx, yAt y (edgeAt p i₁).head⟩ := by
  intro rt hrt i₀ i₁ h0 h1
  obtain ⟨_, _, _, hspec⟩ := routePointsWith_spec h
  obtain ⟨pcs, hz, hpts⟩ := hspec rt hrt
  obtain ⟨_, _, _, _, hp, _⟩ := route_spec hr
  have hi0 := mem_edgesOf (mem_of_head' h0)
  have hi1 := mem_edgesOf (List.mem_of_getLast? h1)
  have pr0 := port_ranges hr hi0
  have pr1 := port_ranges hr hi1
  have hz' : Zipped (fun i pc => pc.head? = some (pieceStart p y r i) ∧
      pc.getLast? = some (pieceEnd p y r i)) (edgesOf p rt.original) pcs :=
    Zipped.imp _ _ (fun i _ pc hpc => ⟨(pieceOf_basic hpc).1, (pieceOf_basic hpc).2.1⟩) hz
  refine ⟨r.sourceX.getD i₀ 0, r.targetX.getD i₁ 0, (hp i₀ hi0).1, (hp i₁ hi1).2,
    pr0.1, pr0.2.1, pr1.2.2.1, pr1.2.2.2, ?_, ?_⟩
  · rw [hpts, dedup_head]
    exact flatten_head _ pcs hz' i₀ h0
  · rw [hpts, dedup_getLast]
    exact flatten_last _ pcs hz' i₁ h1

theorem chain_ne {p : Proper} {v : Nat} (hv : IsReal p v) :
    ∀ (es : List Nat), chainRel (ChainLink p) es →
      (∀ i₀, es.head? = some i₀ → (edgeAt p i₀).tail ≠ v) →
      (∀ i₁, es.getLast? = some i₁ → (edgeAt p i₁).head ≠ v) →
      ∀ i ∈ es, (edgeAt p i).tail ≠ v ∧ (edgeAt p i).head ≠ v
  | [], _, _, _, i, hi => by simp at hi
  | [i'], _, h0, h1, i, hi => by
    have hii : i = i' := by simpa using hi
    rw [hii]
    exact ⟨h0 i' rfl, h1 i' rfl⟩
  | i' :: j :: rest, hc, h0, h1, i, hi => by
    obtain ⟨_, _, hhead, nd, hnd, hdum, _⟩ := hc.1
    have hj : (edgeAt p j).tail ≠ v := by
      intro hjv
      have := hv nd (by rw [← hjv]; exact hnd)
      rw [this] at hdum
      exact absurd hdum (by decide)
    have ih := chain_ne hv (j :: rest) hc.2
      (fun i₀ h => by
        have e := Option.some.inj h
        rw [← e]
        exact hj)
      (fun i₁ h => h1 i₁ (by simpa using h))
    rcases List.mem_cons.mp hi with hii | hi'
    · rw [hii]
      exact ⟨h0 i' rfl, by rw [hhead]; exact hj⟩
    · exact ih i hi'

theorem mid_bounds {slot gap rankGap : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} (hr : route p layers x = .ok r)
    (hF : CoordFacts p layers x y top r gap rankGap slot) {i : Nat}
    (hi : i < p.edges.length) (hne : r.sourceX.getD i 0 ≠ r.targetX.getD i 0) :
    top.getD (gapOf p i) 0 + (layers.map (layerHeight p)).getD (gapOf p i) 0 ≤
      midOf p slot top (layers.map (layerHeight p)) r i ∧
    midOf p slot top (layers.map (layerHeight p)) r i ≤ top.getD (gapOf p i + 1) 0 := by
  obtain ⟨hg, _, _, _, hslot⟩ := route_segment_facts hr hi
  obtain ⟨hs0, hs1⟩ := hslot hne
  obtain ⟨l, hl⟩ : ∃ l, layers[gapOf p i]? = some l :=
    ⟨layers[gapOf p i]'(by omega), List.getElem?_eq_getElem _⟩
  have hb := hF.band_step (gapOf p i) l hl hg
  have hsl := hF.slot_pos
  have hrg := hF.half_slot_le
  have hf : 0 ≤ Int.fdiv slot 2 := Int.fdiv_nonneg (by omega) (by decide)
  unfold midOf
  rw [heights_getD hl]
  generalize ((r.gaps.getD (gapOf p i) default).segments.getD (r.segment.getD i 0) default).slot
    = s at hs0 hs1 ⊢
  generalize (r.gaps.getD (gapOf p i) default).slots = S at hs1 hb
  have m1 : 0 ≤ slot * (s + 1) := Int.mul_nonneg (by omega) (by omega)
  have m2 : slot * (s + 1) ≤ slot * S := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  omega

theorem piece_pairs {slot gap rankGap : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} (hr : route p layers x = .ok r)
    (hF : CoordFacts p layers x y top r gap rankGap slot) {v : Nat} (hv : v < p.nodes.length)
    {i : Nat} (hi : i < p.edges.length) (hvt : (edgeAt p i).tail ≠ v)
    (hvh : (edgeAt p i).head ≠ v) {pc : List Point}
    (hpc : pieceOf p slot y top (layers.map (layerHeight p)) r i = .ok pc) :
    pairsAll (fun P Q => Polyline.segMisses P Q (boxRect p x y v)) pc := by
  have hG := geo_ok hr hF
  obtain ⟨hl, _, _, _, hp, _⟩ := route_spec hr
  obtain ⟨_, _, _, hcov, hedge⟩ := layersOk_spec hl
  obtain ⟨ht, hh, hrk⟩ := hedge i hi
  obtain ⟨_, _, _, h0⟩ := hcov _ ht
  have pr := port_ranges hr hi
  have hrk' : (routeGeo p layers x y top).rk (edgeAt p i).head =
      (routeGeo p layers x y top).rk (edgeAt p i).tail + 1 := by
    show (Elegant.Layered.rk p.rank (edgeAt p i).head).toNat =
      (Elegant.Layered.rk p.rank (edgeAt p i).tail).toNat + 1
    omega
  have hc := pieceOf_cases hpc
  have key := piece_miss (G := routeGeo p layers x y top) hG ht hh hv hrk' (Ne.symm hvt)
    (Ne.symm hvh) (sx := r.sourceX.getD i 0) (tx := r.targetX.getD i 0) ⟨pr.1, pr.2.1⟩
    ⟨pr.2.2.1, pr.2.2.2⟩ (pc := pc) (by
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨midOf p slot top (layers.map (layerHeight p)) r i,
          (mid_bounds hr hF hi h2).1, (mid_bounds hr hF hi h2).2, h1⟩)
  exact key

theorem route_avoids_aux {slot gap rankGap : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute} (hP : ProperShape p)
    (hr : route p layers x = .ok r) (h : routePointsWith slot p layers x y top r = .ok routes)
    (hF : CoordFacts p layers x y top r gap rankGap slot) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (edgesOf p rt.original).head? = some i₀ →
      (edgesOf p rt.original).getLast? = some i₁ →
      ∀ v, v < p.nodes.length → IsReal p v → v ≠ (edgeAt p i₀).tail → v ≠ (edgeAt p i₁).head →
        ¬ Polyline.hitsRect rt.points (boxRect p x y v) := by
  intro rt hrt i₀ i₁ h0 h1 v hv hreal hv0 hv1
  obtain ⟨_, _, _, hspec⟩ := routePointsWith_spec h
  obtain ⟨pcs, hz, hpts⟩ := hspec rt hrt
  obtain ⟨hl, _, _, _, hp, _⟩ := route_spec hr
  obtain ⟨_, hsz, _, hcov, hedge⟩ := layersOk_spec hl
  have hG := geo_ok hr hF
  have hne := chain_ne hreal (edgesOf p rt.original) (hP _)
    (fun i' hi' => by
      rw [h0] at hi'
      have e := Option.some.inj hi'
      rw [← e]
      exact Ne.symm hv0)
    (fun i' hi' => by
      rw [h1] at hi'
      have e := Option.some.inj hi'
      rw [← e]
      exact Ne.symm hv1)
  rw [hpts]
  apply Polyline.not_hits_of_allMiss
  rw [allSegsMiss_iff]
  apply pairsAll_dedup
  refine pairsAll_flatten_of (fun P Q => Polyline.segMisses P Q (boxRect p x y v))
    (pieceStart p y r) (pieceEnd p y r) (ChainLink p) ?_ (edgesOf p rt.original) pcs ?_
    (hP rt.original)
  · intro i j hij
    obtain ⟨hi, hj, hhead, nd, hnd, hdum, _⟩ := hij
    have hd : (edgeAt p j).tail < p.nodes.length := (hedge j hj).1
    have hvd : v ≠ (edgeAt p j).tail := by
      intro hvd
      have := hreal nd (by rw [hvd]; exact hnd)
      rw [this] at hdum
      exact absurd hdum (by decide)
    have pi := port_ranges hr hi
    have pj := port_ranges hr hj
    rw [hhead] at pi
    have key := junction_miss (G := routeGeo p layers x y top) hG hd hv hvd
      (tx := r.targetX.getD i 0) (sx := r.sourceX.getD j 0) ⟨pi.2.2.1, pi.2.2.2⟩
      ⟨pj.1, pj.2.1⟩
    simp only [pieceEnd, pieceStart, hhead]
    exact key
  · exact Zipped.imp _ _ (fun i hi pc hpc =>
      ⟨(pieceOf_basic hpc).1, (pieceOf_basic hpc).2.1,
        piece_pairs hr hF hv (mem_edgesOf hi) (hne i hi).1 (hne i hi).2 hpc⟩) hz

theorem slots_separate_aux {p : Proper} {layers : List (List Nat)} {x : List Int} {r : Routing}
    (hr : route p layers x = .ok r)
    (hkeys : ∀ g ∈ r.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
      (s.tail ≠ t.tail ∨ s.head ≠ t.head) → s.sourceX ≠ t.sourceX ∨ s.decl ≠ t.decl) :
    ∀ g ∈ r.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
      (s.tail ≠ t.tail ∨ s.head ≠ t.head) → segConflict s t = true → s.slot ≠ t.slot := by
  obtain ⟨_, _, _, _, _, hgaps, _⟩ := route_spec hr
  intro g hg s hs t ht htr hc
  have hg' := hg
  rw [hgaps] at hg'
  obtain ⟨k, _, hgk⟩ := List.mem_map.mp hg'
  subst hgk
  obtain ⟨i, hi, rfl⟩ := mem_numberGap_segments hs
  obtain ⟨j, hj, rfl⟩ := mem_numberGap_segments ht
  generalize gapSegments p r.sourceX r.targetX k = segs at hg hi hj htr hc ⊢
  have hmem : ∀ i', i' < segs.length →
      { segs.getD i' default with slot := numberSlots segs i' } ∈ (numberGap segs).segments :=
    fun i' hi' => List.mem_map.mpr ⟨i', List.mem_range.mpr hi', rfl⟩
  exact numberGap_separates segs
    (fun i' j' hi' hj' htr' =>
      hkeys _ hg { segs.getD i' default with slot := numberSlots segs i' } (hmem i' hi')
        { segs.getD j' default with slot := numberSlots segs j' } (hmem j' hj') htr')
    i j hi hj htr hc

theorem edgeAt_append_left {es new : List ProperEdge} {i : Nat} (hi : i < es.length) :
    (es ++ new).getD i default = es.getD i default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem edgeAt_append_right {es new : List ProperEdge} {k : Nat} :
    (es ++ new).getD (es.length + k) default = new.getD k default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]

theorem edgesOfL_append (es new : List ProperEdge) (o : Nat) :
    (List.range (es ++ new).length).filter (fun i => ((es ++ new).getD i default).original == o) =
      (List.range es.length).filter (fun i => (es.getD i default).original == o) ++
      ((List.range new.length).filter (fun k => (new.getD k default).original == o)).map
        (fun k => es.length + k) := by
  rw [List.length_append, List.range_add, List.filter_append, List.filter_map]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [edgeAt_append_left (List.mem_range.mp hi)]
  · congr 1
    apply List.filter_congr
    intro k _
    simp only [Function.comp, edgeAt_append_right]

theorem chainRel_mono {R R' : Nat → Nat → Prop} (hR : ∀ i j, R i j → R' i j) :
    ∀ l : List Nat, chainRel R l → chainRel R' l
  | [], _ => trivial
  | [_], _ => trivial
  | i :: j :: rest, h => ⟨hR i j h.1, chainRel_mono hR (j :: rest) h.2⟩

theorem chainRel_map_range (R : Nat → Nat → Prop) :
    ∀ (s : Nat) (f : Nat → Nat), (∀ k, k + 1 < s → R (f k) (f (k + 1))) →
      chainRel R ((List.range s).map f)
  | 0, _, _ => trivial
  | s + 1, f, h => by
    cases s with
    | zero => simp [chainRel]
    | succ s' =>
      have ih := chainRel_map_range R (s' + 1) (f ∘ Nat.succ) (fun k hk => h (k + 1) (by omega))
      rw [List.range_succ_eq_map (n := s'), List.map_cons] at ih
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.range_succ_eq_map (n := s'),
        List.map_cons]
      exact ⟨h 0 (by omega), ih⟩

def NInv (q : Proper) (k : Nat) : Prop :=
  (∀ i, i < q.edges.length → (edgeAt q i).original < k) ∧
    ∀ o, chainRel (ChainLink q) (edgesOf q o)

theorem chainLink_append {q q' : Proper} {new : List ProperEdge} {extra : List ProperNode}
    (hE : q'.edges = q.edges ++ new) (hN : q'.nodes = q.nodes ++ extra) {i j : Nat}
    (h : ChainLink q i j) : ChainLink q' i j := by
  obtain ⟨hi, hj, hhead, nd, hnd, hd, hh⟩ := h
  have hi' : i < q'.edges.length := by rw [hE]; simp; omega
  have hj' : j < q'.edges.length := by rw [hE]; simp; omega
  have ei : edgeAt q' i = edgeAt q i := by
    simp only [edgeAt, hE]
    exact edgeAt_append_left hi
  have ej : edgeAt q' j = edgeAt q j := by
    simp only [edgeAt, hE]
    exact edgeAt_append_left hj
  have hv : (edgeAt q j).tail < q.nodes.length := by
    have := (List.getElem?_eq_some_iff.mp hnd).1
    exact this
  refine ⟨hi', hj', by rw [ei, ej]; exact hhead, nd, ?_, hd, hh⟩
  rw [ej, hN, List.getElem?_append_left hv]
  exact hnd

open NormalizeImpl in
theorem normalizeEdge_nInv {slot : Int} {q q' : Proper} {e : Edge} {idx : Nat}
    (h : NormalizeImpl.normalizeEdge slot q e idx = .ok q') (hI : NInv q idx) :
    NInv q' (idx + 1) := by
  unfold NormalizeImpl.normalizeEdge at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨fun i hi => Nat.lt_succ_of_lt (hI.1 i hi), hI.2⟩
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        generalize (rk q.rank e.head - rk q.rank e.tail).toNat = s
        have hE : (appendChain slot q e idx s).edges =
            q.edges ++ NormalizeImpl.chainEdges e idx q.nodes.length s := rfl
        have hN : (appendChain slot q e idx s).nodes =
            q.nodes ++ NormalizeImpl.dummyNodes e idx slot s := rfl
        have hlen : (NormalizeImpl.chainEdges e idx q.nodes.length s).length = s := by
          simp [NormalizeImpl.chainEdges]
        have hget : ∀ k, k < s → (NormalizeImpl.chainEdges e idx q.nodes.length s).getD k default =
            ⟨NormalizeImpl.chainNode e.tail e.head q.nodes.length s k,
              NormalizeImpl.chainNode e.tail e.head q.nodes.length s (k + 1), e.decl, idx⟩ := by
          intro k hk
          simp [NormalizeImpl.chainEdges, List.getD_eq_getElem?_getD, hk]
        have hnode : ∀ k, k + 1 < s →
            (appendChain slot q e idx s).nodes[q.nodes.length + k]? =
              some ⟨⟨e.decl, slot, 0⟩, true, some idx⟩ := by
          intro k hk
          rw [hN, List.getElem?_append_right (Nat.le_add_right _ _)]
          simp [NormalizeImpl.dummyNodes, List.getElem?_replicate]
          omega
        refine ⟨?_, ?_⟩
        · intro i hi
          rw [hE] at hi
          simp only [edgeAt, hE]
          by_cases hm : i < q.edges.length
          · rw [edgeAt_append_left hm]
            exact Nat.lt_succ_of_lt (hI.1 i hm)
          · obtain ⟨k, rfl⟩ : ∃ k, i = q.edges.length + k := ⟨i - q.edges.length, by omega⟩
            rw [edgeAt_append_right]
            simp only [List.length_append, hlen] at hi
            rw [hget k (by omega)]
            exact Nat.lt_succ_self idx
        · intro o
          have hEo : edgesOf (appendChain slot q e idx s) o =
              edgesOf q o ++ ((List.range s).filter (fun _ => idx == o)).map
                (fun k => q.edges.length + k) := by
            unfold edgesOf
            simp only [edgeAt, hE]
            rw [edgesOfL_append, hlen]
            congr 2
            apply List.filter_congr
            intro k hk
            rw [hget k (List.mem_range.mp hk)]
          rw [hEo]
          by_cases ho : o = idx
          · subst ho
            have hold : edgesOf q o = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro i hi
              have := hI.1 i (List.mem_range.mp hi)
              simp only [beq_iff_eq]
              omega
            rw [hold]
            have hall : (List.range s).filter (fun _ => o == o) = List.range s := by
              apply List.filter_eq_self.mpr
              intro k _
              simp
            rw [hall, List.nil_append]
            apply chainRel_map_range
            intro k hk
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [hE]; simp; omega
            · rw [hE]; simp; omega
            · simp only [edgeAt, hE]
              rw [edgeAt_append_right, edgeAt_append_right, hget k (by omega), hget (k + 1) hk]
            · simp only [edgeAt, hE]
              rw [edgeAt_append_right, hget (k + 1) hk]
              have hne1 : k + 1 ≠ 0 := by omega
              have hne2 : k + 1 ≠ s := by omega
              refine ⟨⟨⟨e.decl, slot, 0⟩, true, some o⟩, ?_, rfl, rfl⟩
              simp only [NormalizeImpl.chainNode, hne1, hne2, ↓reduceIte]
              have := hnode k hk
              rw [Nat.add_sub_cancel] 
              exact this
          · have hnil : (List.range s).filter (fun _ => idx == o) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro k _
              simp only [beq_iff_eq]
              omega
            rw [hnil, List.map_nil, List.append_nil]
            exact chainRel_mono (fun i j hij => chainLink_append hE hN hij) _ (hI.2 o)

open NormalizeImpl in
theorem normalizeLoop_nInv {slot : Int} :
    ∀ (l : List Edge) (k : Nat) (q q' : Proper),
      NormalizeImpl.normalizeLoop slot (l.zipIdx k) q = .ok q' → NInv q k →
      NInv q' (k + l.length)
  | [], k, q, q', h, hI => by
    simp only [List.zipIdx_nil, NormalizeImpl.normalizeLoop, Except.ok.injEq] at h
    subst h
    simpa using hI
  | e :: l, k, q, q', h, hI => by
    rw [List.zipIdx_cons] at h
    unfold NormalizeImpl.normalizeLoop at h
    split at h
    · simp at h
    · next q1 h1 =>
      have hI1 := normalizeEdge_nInv h1 hI
      have := normalizeLoop_nInv l (k + 1) q1 q' h hI1
      have e1 : k + (e :: l).length = k + 1 + l.length := by
        simp only [List.length_cons]
        omega
      rw [e1]
      exact this

theorem normalize_shape {g : Graph} {rank : List Int} {p : Proper}
    (h : NormalizeImpl.normalize g rank = .ok p) : ProperShape p := by
  unfold NormalizeImpl.normalize at h
  split at h
  · simp at h
  · next slot hs =>
    split at h
    · have hbase : NInv { nodes := g.nodes.map fun n => ⟨n, false, none⟩
                          edges := []
                          rank := rank
                          chains := [] } 0 :=
        ⟨fun i hi => by simp at hi, fun o => by simp [edgesOf, chainRel]⟩
      exact (normalizeLoop_nInv g.edges 0 _ p h hbase).2
    · simp at h

def DistinctSegmentKeys (r : Routing) : Prop :=
  ∀ g ∈ r.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
    (s.tail ≠ t.tail ∨ s.head ≠ t.head) → s.sourceX ≠ t.sourceX ∨ s.decl ≠ t.decl

def GapDeclsDistinct (p : Proper) : Prop :=
  ∀ i j, i < p.edges.length → j < p.edges.length → gapOf p i = gapOf p j →
    (edgeAt p i).decl = (edgeAt p j).decl → i = j

theorem foldl_min_mem (a : Nat) : ∀ l : List Nat, l.foldl min a ∈ a :: l
  | [] => by simp
  | b :: l => by
    simp only [List.foldl_cons]
    have ih := foldl_min_mem (min a b) l
    have hab : min a b = a ∨ min a b = b := by omega
    rcases List.mem_cons.mp ih with h | h
    · rw [h]
      rcases hab with e | e
      · rw [e]
        simp
      · rw [e]
        simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem minDecl_mem : ∀ l : List Nat, l ≠ [] → minDecl l ∈ l
  | [], h => absurd rfl h
  | d :: ds, _ => by
    simp only [minDecl]
    exact foldl_min_mem d ds

theorem mem_gapSegments_decl {p : Proper} {sx tx : List Int} {g : Nat} {s : RoutingSegment}
    (h : s ∈ (numberGap (gapSegments p sx tx g)).segments) :
    ∃ i, i ∈ gapEdges p g ∧ segKey p i = (s.tail, s.head) ∧ s.decl = (edgeAt p i).decl := by
  obtain ⟨k, hk, rfl⟩ := mem_numberGap_segments h
  have hk' : k < (gapKeys p g).length := by simpa [gapSegments] using hk
  have hseg : (gapSegments p sx tx g).getD k default =
      buildSegment p sx tx g ((gapKeys p g)[k]) := by
    simp [gapSegments, List.getD_eq_getElem?_getD, hk']
  have hmem : (gapKeys p g)[k] ∈ gapKeys p g := List.getElem_mem hk'
  have hex : ∃ i₁ ∈ gapEdges p g, segKey p i₁ = (gapKeys p g)[k] := by
    simp only [gapKeys, List.mem_eraseDups, List.mem_map] at hmem
    exact hmem
  obtain ⟨i₁, hi₁, hkey⟩ := hex
  rw [hseg]
  unfold buildSegment
  simp only
  generalize hE : (gapEdges p g).filter (fun i => segKey p i == (gapKeys p g)[k]) = es
  have hi₁es : i₁ ∈ es := by
    rw [← hE]
    simp [List.mem_filter, hi₁, hkey]
  have hne : es.map (fun i => (edgeAt p i).decl) ≠ [] := by
    intro h0
    have := List.mem_map_of_mem (f := fun i => (edgeAt p i).decl) hi₁es
    rw [h0] at this
    simp at this
  obtain ⟨i, hi, hdi⟩ := List.mem_map.mp (minDecl_mem _ hne)
  have hi' : i ∈ (gapEdges p g).filter (fun i => segKey p i == (gapKeys p g)[k]) := by
    rw [hE]
    exact hi
  obtain ⟨hig, hkeyi⟩ := List.mem_filter.mp hi'
  refine ⟨i, hig, ?_, hdi.symm⟩
  have := beq_iff_eq.mp hkeyi
  rw [this]

theorem distinctSegmentKeys_of_gap_decls {p : Proper} {layers : List (List Nat)} {x : List Int}
    {r : Routing} (hr : route p layers x = .ok r) (hD : GapDeclsDistinct p) :
    DistinctSegmentKeys r := by
  obtain ⟨_, _, _, _, _, hgaps, _⟩ := route_spec hr
  intro g hg s hs t ht htr
  right
  intro hdecl
  have hg' := hg
  rw [hgaps] at hg'
  obtain ⟨k, _, hgk⟩ := List.mem_map.mp hg'
  subst hgk
  obtain ⟨i, hi, hki, hdi⟩ := mem_gapSegments_decl hs
  obtain ⟨j, hj, hkj, hdj⟩ := mem_gapSegments_decl ht
  simp only [gapEdges, List.mem_filter, List.mem_range, beq_iff_eq] at hi hj
  have hij : i = j := hD i j hi.1 hj.1 (by rw [hi.2, hj.2]) (by rw [← hdi, ← hdj]; exact hdecl)
  subst hij
  rw [hki] at hkj
  have h1 := congrArg Prod.fst hkj
  have h2 := congrArg Prod.snd hkj
  simp only at h1 h2
  rcases htr with h | h
  · exact h h1
  · exact h h2

theorem routePoints_eq {p : Proper} {layers : List (List Nat)} {x y top : List Int}
    {r : Routing} {routes : List EdgeRoute} (h : routePoints p layers x y top r = .ok routes) :
    ∃ slot, NormalizeImpl.defaultSlot = some slot ∧
      routePointsWith slot p layers x y top r = .ok routes := by
  unfold routePoints at h
  split at h
  · next slot hs => exact ⟨slot, hs, h⟩
  · simp at h

end RouteImpl

export RouteImpl (route routePointsWith routePoints ProperShape CoordFacts IsReal boxRect edgesOf
  edgeAt pieceStart pieceEnd segConflict sourcePort targetPort DistinctSegmentKeys
  GapDeclsDistinct)

theorem route_orthogonal {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute} (hP : ProperShape p)
    (h : routePointsWith slot p layers x y top r = .ok routes) :
    ∀ rt ∈ routes, Polyline.isOrthogonal rt.points = true :=
  RouteImpl.route_orthogonal_aux hP h

theorem route_endpoints_on_ports {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute}
    (hr : route p layers x = .ok r) (h : routePointsWith slot p layers x y top r = .ok routes) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (edgesOf p rt.original).head? = some i₀ →
      (edgesOf p rt.original).getLast? = some i₁ →
      ∃ px qx, sourcePort p x i₀ = .ok px ∧ targetPort p x i₁ = .ok qx ∧
        (boxRect p x y (edgeAt p i₀).tail).x ≤ px ∧
        px ≤ (boxRect p x y (edgeAt p i₀).tail).x + (boxRect p x y (edgeAt p i₀).tail).w ∧
        (boxRect p x y (edgeAt p i₁).head).x ≤ qx ∧
        qx ≤ (boxRect p x y (edgeAt p i₁).head).x + (boxRect p x y (edgeAt p i₁).head).w ∧
        rt.points.head? = some ⟨px, (boxRect p x y (edgeAt p i₀).tail).y +
          (boxRect p x y (edgeAt p i₀).tail).h⟩ ∧
        rt.points.getLast? = some ⟨qx, (boxRect p x y (edgeAt p i₁).head).y⟩ :=
  RouteImpl.route_endpoints_aux hr h

theorem route_avoids_nodes {slot gap rankGap : Int} {p : Proper} {layers : List (List Nat)}
    {x y top : List Int} {r : Routing} {routes : List EdgeRoute} (hP : ProperShape p)
    (hr : route p layers x = .ok r) (h : routePointsWith slot p layers x y top r = .ok routes)
    (hF : CoordFacts p layers x y top r gap rankGap slot) :
    ∀ rt ∈ routes, ∀ i₀ i₁, (edgesOf p rt.original).head? = some i₀ →
      (edgesOf p rt.original).getLast? = some i₁ →
      ∀ v, v < p.nodes.length → IsReal p v → v ≠ (edgeAt p i₀).tail → v ≠ (edgeAt p i₁).head →
        ¬ Polyline.hitsRect rt.points (boxRect p x y v) :=
  RouteImpl.route_avoids_aux hP hr h hF

theorem slots_separate_overlapping_segments {p : Proper} {layers : List (List Nat)}
    {x : List Int} {r : Routing} (hr : route p layers x = .ok r) (hkeys : DistinctSegmentKeys r) :
    ∀ g ∈ r.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
      (s.tail ≠ t.tail ∨ s.head ≠ t.head) → segConflict s t = true → s.slot ≠ t.slot :=
  RouteImpl.slots_separate_aux hr hkeys

theorem normalize_shape {g : Graph} {rank : List Int} {p : Proper}
    (h : normalize g rank = .ok p) : ProperShape p :=
  RouteImpl.normalize_shape h

theorem slots_separate_of_gap_decls {p : Proper} {layers : List (List Nat)}
    {x : List Int} {r : Routing} (hr : route p layers x = .ok r) (hD : GapDeclsDistinct p) :
    ∀ g ∈ r.gaps, ∀ s ∈ g.segments, ∀ t ∈ g.segments,
      (s.tail ≠ t.tail ∨ s.head ≠ t.head) → segConflict s t = true → s.slot ≠ t.slot :=
  slots_separate_overlapping_segments hr (RouteImpl.distinctSegmentKeys_of_gap_decls hr hD)

end Layered
end Elegant
