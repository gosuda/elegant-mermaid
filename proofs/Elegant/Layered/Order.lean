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
  | breadthFirst
  | reversed
deriving DecidableEq, Repr

inductive OrderKey where
  | barycentre
  | median
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

def commonPath : List Nat → List Nat → List Nat
  | a :: as, b :: bs => if a = b then a :: commonPath as bs else []
  | _, _ => []

def nodePath (p : Proper) (v : Nat) : List Nat :=
  let n := (p.nodes.getD v default)
  if !n.dummy then n.node.clusterPath
  else
    match p.chains.find? (fun chain => chain.contains v) with
    | none => []
    | some chain =>
      commonPath ((p.nodes.getD (chain.headD v) default).node.clusterPath)
        ((p.nodes.getD (chain.getLastD v) default).node.clusterPath)

def borderLinks (next decl offset : Nat) : List ProperEdge :=
  if offset = 0 then [] else
    [{ tail := next - 2, head := next, decl := decl, original := 0, synthetic := true },
     { tail := next - 1, head := next + 1, decl := decl, original := 0, synthetic := true }]

def dropSynthetic (p : Proper) : Proper :=
  { p with edges := p.edges.filter (fun edge => !edge.synthetic) }

theorem dropSynthetic_nodes (p : Proper) : (dropSynthetic p).nodes = p.nodes := rfl
theorem dropSynthetic_rank (p : Proper) : (dropSynthetic p).rank = p.rank := rfl
theorem dropSynthetic_chains (p : Proper) : (dropSynthetic p).chains = p.chains := rfl

def addClusterBorders (p : Proper) (borderWidth : Int) : Proper :=
  let anchors := p.nodes.zipIdx.filter fun q => q.1.node.border == -2
  anchors.foldl (fun out q =>
    let top := q.2
    let path := q.1.node.clusterPath
    let bottom := (p.nodes.zipIdx.find? fun b =>
      b.1.node.border == 2 && b.1.node.clusterPath == path).map (·.2)
    match bottom with
    | none => out
    | some bot =>
      let lo := (rk p.rank top).toNat
      let hi := (rk p.rank bot).toNat
      (List.range (hi + 1 - lo)).foldl (fun state offset =>
        let node : Node := {
          decl := q.1.node.decl
          w := borderWidth
          h := 0
          clusterPath := path }
        { state with
          edges := state.edges ++ borderLinks state.nodes.length q.1.node.decl offset
          nodes := state.nodes ++
            [⟨{ node with border := -1 }, false, none⟩,
             ⟨{ node with border := 1, loopExtent := q.1.node.loopExtent }, false, none⟩]
          rank := state.rank ++ [((lo + offset : Nat) : Int), ((lo + offset : Nat) : Int)] }) out) p
def medianKey (nb : Nat → List Nat) (pos : Nat → Int) (v : Nat) : Int × Int :=
  match (nb v).map pos |>.mergeSort (fun a b => decide (a ≤ b)) with
  | [] => (pos v, 1)
  | ns => (ns.getD ((ns.length - 1) / 2) 0, 1)

def nodeKey (key : OrderKey) (nb : Nat → List Nat) (pos : Nat → Int) (v : Nat) :
    Int × Int :=
  match key with
  | .barycentre => fracKey nb pos v
  | .median => medianKey nb pos v

structure BlockKey where
  band : Int
  fraction : Int × Int
  decl : Nat
  index : Nat
  child : Option Nat := none
deriving Repr

def blockKeyLe (a b : BlockKey) : Bool :=
  if a.band != b.band then decide (a.band < b.band)
  else if a.fraction.1 * b.fraction.2 != b.fraction.1 * a.fraction.2 then
    decide (a.fraction.1 * b.fraction.2 < b.fraction.1 * a.fraction.2)
  else if a.decl != b.decl then decide (a.decl < b.decl)
  else if a.child.isSome != b.child.isSome then !a.child.isSome
  else if a.child != b.child then decide (a.child.getD 0 < b.child.getD 0)
  else decide (a.index ≤ b.index)

theorem blockKeyLe_loose_before_child (band : Int) (fraction : Int × Int)
    (decl i j child : Nat) :
    blockKeyLe ⟨band, fraction, decl, i, none⟩
      ⟨band, fraction, decl, j, some child⟩ = true := by
  simp [blockKeyLe]

theorem blockKeyLe_band_lt (a b : BlockKey) (h : a.band < b.band) :
    blockKeyLe a b = true := by
  simp [blockKeyLe, show a.band ≠ b.band by omega, h]

theorem blockKeyLe_band_gt (a b : BlockKey) (h : b.band < a.band) :
    blockKeyLe a b = false := by
  simp [blockKeyLe, show a.band ≠ b.band by omega, show ¬ a.band < b.band by omega]

theorem merge_border_bands {α : Type} (le : α → α → Bool) (band : α → Int)
    (htrue : ∀ a b, le a b = true → band a ≤ band b)
    (hfalse : ∀ a b, le a b = false → band b ≤ band a)
    (left right : List α)
    (hl : left.Pairwise (fun a b => band a ≤ band b))
    (hr : right.Pairwise (fun a b => band a ≤ band b)) :
    (left.merge right le).Pairwise (fun a b => band a ≤ band b) := by
  induction left generalizing right with
  | nil => simpa only [List.merge] using hr
  | cons x left ih =>
    induction right with
    | nil => simpa only [List.merge] using hl
    | cons y right ih2 =>
      simp only [List.merge]
      split <;> rename_i h
      · apply List.Pairwise.cons
        · intro z hz
          rw [List.mem_merge,List.mem_cons] at hz
          rcases hz with hz | rfl | hz
          · exact List.rel_of_pairwise_cons hl hz
          · exact htrue x z h
          · exact Int.le_trans (htrue x y h) (List.rel_of_pairwise_cons hr hz)
        · exact ih _ hl.tail hr
      · apply List.Pairwise.cons
        · intro z hz
          rw [List.mem_merge,List.mem_cons] at hz
          have hf : le x y = false := by simpa using h
          rcases hz with (rfl | hz) | hz
          · exact hfalse z y hf
          · exact Int.le_trans (hfalse x y hf) (List.rel_of_pairwise_cons hl hz)
          · exact List.rel_of_pairwise_cons hr hz
        · exact ih2 hr.tail

theorem mergeSort_border_bands {α : Type} (le : α → α → Bool) (band : α → Int)
    (htrue : ∀ a b, le a b = true → band a ≤ band b)
    (hfalse : ∀ a b, le a b = false → band b ≤ band a) :
    ∀ layer : List α, (layer.mergeSort le).Pairwise (fun a b => band a ≤ band b)
  | [] => by simp
  | [a] => by simp
  | a :: b :: rest => by
    rw [List.mergeSort]
    apply merge_border_bands le band htrue hfalse
    · exact mergeSort_border_bands le band htrue hfalse _
    · exact mergeSort_border_bands le band htrue hfalse _
termination_by layer => layer.length

theorem blockKeyLe_true_band (a b : BlockKey) (h : blockKeyLe a b = true) : a.band ≤ b.band := by
  by_cases hb : a.band = b.band
  · omega
  · simp only [blockKeyLe, show (a.band != b.band) = true by simp [hb], ite_true,
      decide_eq_true_eq] at h
    omega
theorem blockKeyLe_false_band (a b : BlockKey) (h : blockKeyLe a b = false) : b.band ≤ a.band := by
  by_cases hb : a.band = b.band
  · omega
  · simp only [blockKeyLe, show (a.band != b.band) = true by simp [hb], ite_true,
      decide_eq_false_iff_not] at h
    omega

theorem sorted_head_of_strict_min {α : Type} (band : α → Int)
    (xs : List α) (a : α) (ha : a ∈ xs)
    (hs : xs.Pairwise (fun x y => band x ≤ band y))
    (hm : ∀ b ∈ xs, a ≠ b → band a < band b) : xs.head? = some a := by
  cases xs with
  | nil => simp at ha
  | cons b rest =>
    by_cases hab : a = b
    · simp [hab]
    · have hat : a ∈ rest := (List.mem_cons.mp ha).resolve_left hab
      have hba := List.rel_of_pairwise_cons hs hat
      have hab' := hm b (List.mem_cons_self ..) hab
      omega

def clusterBlocks (key : Nat → Option Nat) : Nat → List Nat → List (List Nat)
  | 0, xs => [xs]
  | _ + 1, [] => []
  | fuel + 1, v :: vs =>
    match key v with
    | none => [v] :: clusterBlocks key fuel vs
    | some c => (v :: vs.filter (fun w => key w == some c)) ::
        clusterBlocks key fuel (vs.filter (fun w => key w != some c))

theorem clusterBlocks_perm (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat) :
    (clusterBlocks key fuel xs).flatten.Perm xs := by
  induction fuel generalizing xs with
  | zero => simp [clusterBlocks]
  | succ fuel ih =>
    cases xs with
    | nil => simp [clusterBlocks]
    | cons v vs =>
      simp only [clusterBlocks]
      split
      · simpa using (ih vs).cons v
      · rename_i c hc
        simp only [List.flatten_cons]
        have h := ((List.Perm.refl (vs.filter (fun w => key w == some c))).append
          (ih (vs.filter (fun w => key w != some c)))).trans
            (List.filter_append_perm (fun w => key w == some c) vs)
        simpa using h.cons v

theorem clusterBlocks_boundary_singleton (key : Nat → Option Nat) (fuel : Nat) (layer block : List Nat) (a : Nat)
    (hf : layer.length ≤ fuel) (hb : block ∈ clusterBlocks key fuel layer)
    (ha : a ∈ block) (hn : key a = none) : block = [a] := by
  induction fuel generalizing layer block with
  | zero =>
    have hz : layer = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hz
    simp [clusterBlocks] at hb
    subst hb
    simp at ha
  | succ fuel ih =>
    cases layer with
    | nil => simp [clusterBlocks] at hb
    | cons v rest =>
      simp only [clusterBlocks] at hb
      split at hb
      · simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · have hv : a = v := by simpa only [List.mem_singleton] using ha
          simp [hv]
        · exact ih rest block (by simp at hf; omega) hb ha
      · rename_i c hc
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp only [List.mem_cons,List.mem_filter,beq_iff_eq] at ha
          rcases ha with rfl | ha
          · simp [hn] at hc
          · simp [hn] at ha
        · exact ih _ block (by have := List.length_filter_le (fun w => key w != some c) rest; simp at hf; omega) hb ha

def ClusterUniform (key : Nat → Option Nat) (xs : List Nat) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, key a = key b

theorem clusterBlocks_uniform (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat)
    (hf : xs.length ≤ fuel) : ∀ block ∈ clusterBlocks key fuel xs, ClusterUniform key block := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx
    simp [clusterBlocks, ClusterUniform]
  | succ f ih =>
    cases xs with
    | nil => simp [clusterBlocks]
    | cons v vs =>
      simp only [clusterBlocks]
      split
      · intro block hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · simp [ClusterUniform]
        · exact ih vs (by simp at hf; omega) block hb
      · rename_i c hc
        intro block hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · intro a ha b hb
          have all : ∀ w ∈ v :: vs.filter (fun w => key w == some c), key w = some c := by
            intro w hw
            simp only [List.mem_cons, List.mem_filter, beq_iff_eq] at hw
            rcases hw with rfl | hw
            · exact hc
            · exact hw.2
          exact (all a ha).trans (all b hb).symm
        · exact ih _ (by have := List.length_filter_le (fun w => key w != some c) vs; simp at hf; omega) block hb

def ClusterSeparate (key : Nat → Option Nat) (a b : List Nat) : Prop :=
  ∀ c x, x ∈ a → key x = some c → ∀ y ∈ b, key y ≠ some c

theorem clusterBlocks_separate (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat)
    (hf : xs.length ≤ fuel) : List.Pairwise (ClusterSeparate key) (clusterBlocks key fuel xs) := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx
    simp [clusterBlocks]
  | succ f ih =>
    cases xs with
    | nil => simp [clusterBlocks]
    | cons v vs =>
      simp only [clusterBlocks]
      split
      · rename_i hv
        rw [List.pairwise_cons]
        refine ⟨?_, ih vs (by simp at hf; omega)⟩
        intro block hb c x hx hc y hy
        simp only [List.mem_singleton] at hx
        subst hx
        simp [hv] at hc
      · rename_i c hc
        rw [List.pairwise_cons]
        refine ⟨?_, ih _ (by have := List.length_filter_le (fun w => key w != some c) vs; simp at hf; omega)⟩
        intro block hb d x hx hd y hy
        have hx' : key x = some c := by
          simp only [List.mem_cons, List.mem_filter, beq_iff_eq] at hx
          rcases hx with rfl | hx
          · exact hc
          · exact hx.2
        have hdc : d = c := by simpa [hx'] using hd.symm
        cases hdc
        have hymem : y ∈ (clusterBlocks key f (vs.filter (fun w => key w != some c))).flatten :=
          List.mem_flatten.mpr ⟨block,hb,hy⟩
        have hy' := (clusterBlocks_perm key f _).mem_iff.mp hymem
        have hne : y ∈ vs ∧ key y ≠ some c := by
          simpa [List.mem_filter, bne_iff_ne] using hy'
        exact hne.2

def clusterTree (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool) :
    Nat → Nat → List Nat → List Nat
  | 0, _, layer => layer
  | fuel + 1, depth, layer =>
    let blocks := clusterBlocks (fun v => (path v).head?) layer.length layer
    let nested := blocks.map fun block =>
      if ((path (block.headD 0)).head?).isSome then
        clusterTree (fun v => (path v).tail) cmp fuel (depth + 1) block else block
    (nested.mergeSort (cmp depth)).flatten

theorem flatten_map_perm (xs : List (List Nat)) (f : List Nat → List Nat)
    (hf : ∀ x, (f x).Perm x) : (xs.map f).flatten.Perm xs.flatten := by
  induction xs with
  | nil => simp
  | cons x xs ih => exact (hf x).append ih

theorem clusterTree_perm (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (fuel depth : Nat) (layer : List Nat) :
    (clusterTree path cmp fuel depth layer).Perm layer := by
  induction fuel generalizing path depth layer with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    unfold clusterTree
    refine (List.mergeSort_perm _ _).flatten.trans ?_
    refine (flatten_map_perm _ _ (fun block => ?_)).trans (clusterBlocks_perm _ _ _)
    split
    · exact ih _ _ _
    · exact List.Perm.refl _

theorem ClusterSeparate.symm {key : Nat → Option Nat} {a b : List Nat}
    (h : ClusterSeparate key a b) : ClusterSeparate key b a := by
  intro c y hy hc x hx hx'
  exact h c x hx hx' y hy hc

theorem clusterSeparate_map (key : Nat → Option Nat) (blocks : List (List Nat))
    (f : List Nat → List Nat) (hf : ∀ b, (f b).Perm b)
    (hs : List.Pairwise (ClusterSeparate key) blocks) :
    List.Pairwise (ClusterSeparate key) (blocks.map f) := by
  rw [List.pairwise_map]
  exact hs.imp (fun h c x hx hxc y hy => h c x ((hf _).mem_iff.mp hx) hxc y ((hf _).mem_iff.mp hy))


theorem filter_infix_of_subordinate (key : Nat → Option Nat) (c : Nat)
    (pred : Nat → Bool) (blocks : List (List Nat))
    (hpred : ∀ x, pred x = true → key x = some c)
    (hs : List.Pairwise (ClusterSeparate key) blocks)
    (hu : ∀ b ∈ blocks, (b.filter pred).IsInfix b) :
    (blocks.flatten.filter pred).IsInfix blocks.flatten := by
  induction blocks with
  | nil => simp
  | cons b rest ih =>
    rw [List.pairwise_cons] at hs
    have hb := hu b (by simp)
    have hr := ih hs.2 (fun d hd => hu d (by simp [hd]))
    simp only [List.flatten_cons, List.filter_append]
    by_cases he : b.filter pred = []
    · rw [he, List.nil_append]
      exact List.infix_append_of_infix_right hr
    · have hrest : rest.flatten.filter pred = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy hyc
        obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (b.filter pred) he
        have hx' := List.mem_filter.mp hx
        obtain ⟨d,hd,hyd⟩ := List.mem_flatten.mp hy
        exact hs.1 d hd c x hx'.1 (hpred x hx'.2) y hyd (hpred y hyc)
      rw [hrest, List.append_nil]
      exact List.infix_append_of_infix_left hb


theorem prefix_head (path : Nat → List Nat) (c : Nat) (cs : List Nat) (v : Nat)
    (h : (c :: cs).isPrefixOf (path v) = true) : (path v).head? = some c := by
  cases hp : path v with
  | nil => simp [hp] at h
  | cons a rest =>
    rw [hp, List.isPrefixOf_cons_cons] at h
    have hc := (Bool.and_eq_true_iff.mp h).1
    simp only [beq_iff_eq] at hc
    simp [hc]

theorem clusterTree_contiguous (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (fuel depth : Nat) (layer pref : List Nat) (hf : pref.length ≤ fuel) :
    ((clusterTree path cmp fuel depth layer).filter (fun v => pref.isPrefixOf (path v))).IsInfix
      (clusterTree path cmp fuel depth layer) := by
  induction fuel generalizing path depth layer pref with
  | zero =>
    have hp : pref = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    change (layer.filter (fun _ => true)).IsInfix layer
    rw [List.filter_eq_self.mpr (by simp)]
    exact List.infix_refl _
  | succ fuel ih =>
    cases pref with
    | nil =>
      change ((clusterTree path cmp (fuel+1) depth layer).filter (fun _ => true)).IsInfix _
      rw [List.filter_eq_self.mpr (by simp)]
      exact List.infix_refl _
    | cons c cs =>
      let blocks := clusterBlocks (fun v => (path v).head?) layer.length layer
      let f := fun block => if ((path (block.headD 0)).head?).isSome then
        clusterTree (fun v => (path v).tail) cmp fuel (depth + 1) block else block
      have hperm : ∀ b, (f b).Perm b := by
        intro b
        dsimp [f]
        split
        · exact clusterTree_perm _ _ _ _ _
        · exact List.Perm.refl _
      have hsep := clusterBlocks_separate (fun v => (path v).head?) layer.length layer (Nat.le_refl _)
      have hsep' := clusterSeparate_map _ blocks f hperm hsep
      have hsorted := hsep'.perm (List.mergeSort_perm (blocks.map f) (cmp depth)).symm (fun h => ClusterSeparate.symm h)
      change (((blocks.map f).mergeSort (cmp depth)).flatten.filter
        (fun v => (c :: cs).isPrefixOf (path v))).IsInfix _
      apply filter_infix_of_subordinate (fun v => (path v).head?) c _ _ (prefix_head path c cs) hsorted
      intro b hb
      have hb' := (List.mergeSort_perm _ _).mem_iff.mp hb
      obtain ⟨orig,ho,rfl⟩ := List.mem_map.mp hb'
      have hu := clusterBlocks_uniform (fun v => (path v).head?) layer.length layer (Nat.le_refl _) orig ho
      by_cases hempty : orig = []
      · subst hempty
        have hz : f [] = [] := List.perm_nil.mp (hperm [])
        rw [hz]
        simp
      · have hhead : orig.headD 0 ∈ orig := by cases orig with
          | nil => contradiction
          | cons a rest => exact List.mem_cons_self
        by_cases hc : (path (orig.headD 0)).head? = some c
        · have hall : ∀ v ∈ orig, (path v).head? = some c := by
            intro v hv
            exact (hu v hv _ hhead).trans hc
          have hf' : f orig = clusterTree (fun v => (path v).tail) cmp fuel (depth + 1) orig := by
            dsimp only [f]
            rw [hc]
            rfl
          rw [hf']
          have hrec := ih (fun v => (path v).tail) (depth+1) orig cs (by simp at hf; omega)
          have heq : (clusterTree (fun v => (path v).tail) cmp fuel (depth+1) orig).filter
                (fun v => (c :: cs).isPrefixOf (path v)) =
              (clusterTree (fun v => (path v).tail) cmp fuel (depth+1) orig).filter
                (fun v => cs.isPrefixOf ((path v).tail)) := by
            apply List.filter_congr
            intro v hv
            have hv' := (clusterTree_perm _ _ _ _ _).mem_iff.mp hv
            have hh := hall v hv'
            cases hp : path v with
            | nil => simp [hp] at hh
            | cons a rest =>
              have ha : a = c := by simpa [hp] using hh
              subst ha
              simp [List.isPrefixOf]
          rw [heq]
          exact hrec
        · have hnil : (f orig).filter (fun v => (c :: cs).isPrefixOf (path v)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro v hv hp
            have hv' := (hperm orig).mem_iff.mp hv
            exact hc ((hu _ hhead v hv').trans (prefix_head path c cs v hp))
          rw [hnil]
          exact List.nil_infix


theorem fold_max_lower (f : Nat → Nat) (xs : List Nat) (start : Nat) :
    start ≤ xs.foldl (fun d v => max d (f v)) start ∧
    ∀ v ∈ xs, f v ≤ xs.foldl (fun d v => max d (f v)) start := by
  induction xs generalizing start with
  | nil => simp
  | cons a rest ih =>
    have h := ih (max start (f a))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h.1, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.le_trans (Nat.le_max_right _ _) h.1
    · exact h.2 v hv

theorem clusterTree_contiguous_all (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (layer pref : List Nat) :
    let fuel := layer.foldl (fun d v => max d (path v).length) 0 + 1
    ((clusterTree path cmp fuel 0 layer).filter (fun v => pref.isPrefixOf (path v))).IsInfix
      (clusterTree path cmp fuel 0 layer) := by
  dsimp only
  by_cases hf : pref.length ≤ layer.foldl (fun d v => max d (path v).length) 0 + 1
  · exact clusterTree_contiguous _ _ _ _ _ _ hf
  · have hz : (clusterTree path cmp (layer.foldl (fun d v => max d (path v).length) 0 + 1) 0 layer).filter
        (fun v => pref.isPrefixOf (path v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro v hv hp
      have hv' := (clusterTree_perm _ _ _ _ _).mem_iff.mp hv
      have hl := (fold_max_lower (fun v => (path v).length) layer 0).2 v hv'
      have hp' := (List.isPrefixOf_iff_prefix.mp hp).length_le
      omega
    rw [hz]
    exact List.nil_infix

def clusterBlockKey (p : Proper) (key : OrderKey) (nb : Nat → List Nat)
    (pos : Nat → Int) (layer : List Nat) (initial : Bool)
    (depth : Nat) (members : List Nat) : BlockKey :=
  let first := members.foldl (fun i v => min i (layer.idxOf v)) layer.length
  let neighbours := members.flatMap nb
  let values := if neighbours.isEmpty then members.map pos else neighbours.map pos
  let singleton := members.length == 1
  let fraction := if initial then ((first : Int), 1)
    else if key == .median && singleton then
      let sorted := values.mergeSort (fun a b => decide (a ≤ b))
      (sorted.getD ((sorted.length - 1) / 2) 0, 1)
    else (values.sum, (values.length : Int))
  let v := members.headD 0
  let border := (p.nodes.getD v default).node.border
  { band := if ((nodePath p v)[depth]?).isSome then 0
      else if border = -1 then -1 else if border = 1 then 1 else 0,
    fraction := fraction,
    decl := members.foldl (fun d w => min d (declOf p w)) (declOf p v),
    index := first,
    child := if initial then none else (nodePath p v)[depth]? }

def constrainedLayer (p : Proper) (key : OrderKey) (nb : Nat → List Nat)
    (pos : Nat → Int) (layer : List Nat) (initial : Bool := false) : List Nat :=
  if layer.all (fun v => (nodePath p v).isEmpty) then
    layer.mergeSort (fun a b => fracLe (nodeKey key nb pos a) (nodeKey key nb pos b))
  else
    let depth := layer.foldl (fun d v => max d (nodePath p v).length) 0
    clusterTree (nodePath p)
      (fun level a b => blockKeyLe
        (clusterBlockKey p key nb pos layer initial level a)
        (clusterBlockKey p key nb pos layer initial level b)) (depth + 1) 0 layer

namespace Sibling

abbrev Row := Nat × Nat × Int

def clusterRows (p : Proper) : List (Nat × Option Nat) :=
  p.nodes.filterMap fun n =>
    if n.node.border == -1 then
      n.node.clusterPath.getLast?.map fun c => (c, n.node.clusterPath.dropLast.getLast?)
    else none

def clusterIds (p : Proper) : List Nat :=
  ((clusterRows p).map Prod.fst).eraseDups.mergeSort (fun a b => decide (a ≤ b))

def parentOf (p : Proper) (c : Nat) : Option Nat :=
  (List.lookup c (clusterRows p)).getD none

def lbRows (p : Proper) (pos : Nat → Int) : List Row :=
  p.nodes.zipIdx.filterMap fun q =>
    if q.1.node.border == -1 then
      q.1.node.clusterPath.getLast?.map fun c => (c, lay p q.2, pos q.2)
    else none

def lbAt (rows : List Row) (c r : Nat) : Option Int :=
  (rows.reverse.find? fun t => t.1 == c && t.2.1 == r).map fun t => t.2.2

def lbSpan (rows : List Row) (c : Nat) : Option (Nat × Nat) :=
  match rows.filter (fun t => t.1 == c) with
  | [] => none
  | t :: ts => some (ts.foldl (fun s u => (min s.1 u.2.1, max s.2 u.2.1)) (t.2.1, t.2.1))

def meanKey (cell : Nat → Nat → Option Int) (span : Option (Nat × Nat)) (c : Nat) : Int × Int :=
  match span with
  | none => (0, 1)
  | some (f, l) =>
    (((List.range (l + 1 - f)).map fun k => (cell c (f + k)).getD 0).sum,
      ((l + 1 - f : Nat) : Int))

def votes (cell : Nat → Nat → Option Int) (spanA spanB : Option (Nat × Nat)) (a b : Nat) :
    Nat × Nat :=
  match spanA, spanB with
  | some (fa, la), some (fb, lb) =>
    (List.range (min la lb + 1 - max fa fb)).foldl (fun (acc : Nat × Nat) k =>
      match cell a (max fa fb + k), cell b (max fa fb + k) with
      | some pa, some pb => if pa < pb then (acc.1 + 1, acc.2) else (acc.1, acc.2 + 1)
      | _, _ => acc) (0, 0)
  | _, _ => (0, 0)

def precedes (v : Nat × Nat) (a b : Nat) : Bool :=
  if v.1 = v.2 then decide (a < b) && decide (0 < v.1 + v.2) else decide (v.2 < v.1)

def sibLess (key : Nat → Int × Int) (a b : Nat) : Bool :=
  if (key a).1 * (key b).2 = (key b).1 * (key a).2 then decide (a < b)
  else decide ((key a).1 * (key b).2 < (key b).1 * (key a).2)

def pickMin (less : Nat → Nat → Bool) : List Nat → Option Nat
  | [] => none
  | x :: xs => some (xs.foldl (fun y z => if less z y then z else y) x)

def kahnOrder (pre less : Nat → Nat → Bool) : Nat → List Nat → List Nat
  | 0, _ => []
  | fuel + 1, remaining =>
    let ready := remaining.filter fun c => remaining.all fun d => !pre d c
    match pickMin less (if ready.isEmpty then remaining else ready) with
    | none => []
    | some c => c :: kahnOrder pre less fuel (remaining.erase c)

def siblingOrders (p : Proper) (pos : Nat → Int) : List (Option Nat × List Nat) :=
  let rows := lbRows p pos
  let ids := clusterIds p
  let spans := ids.map fun c => (c, lbSpan rows c)
  let spanOf := fun c => (List.lookup c spans).getD none
  let keys := ids.map fun c => (c, meanKey (lbAt rows) (spanOf c) c)
  let keyOf := fun c => (List.lookup c keys).getD (0, 1)
  let pre := fun a b => precedes (votes (lbAt rows) (spanOf a) (spanOf b) a b) a b
  (ids.map (parentOf p)).eraseDups.map fun P =>
    let group := ids.filter fun c => parentOf p c == P
    (P, kahnOrder pre (sibLess keyOf) group.length group)

def siblingNumber (p : Proper) (orders : List (Option Nat × List Nat)) (c : Nat) : Nat :=
  ((List.lookup (parentOf p c) orders).getD []).idxOf c

abbrev Item := Option Nat × List Nat

def place : List Item → List Item → List Item
  | [], _ => []
  | t :: ts, sorted =>
    match t.1, sorted with
    | some _, b :: bs => b :: place ts bs
    | _, _ => t :: place ts sorted

def sibSorted (num : Nat → Nat) (items : List Item) : List Item :=
  (items.filter fun t => t.1.isSome).mergeSort
    fun a b => decide (num (a.1.getD 0) ≤ num (b.1.getD 0))

def sibMerge (num : Nat → Nat) (items : List Item) : List Nat :=
  ((place items (sibSorted num items)).map Prod.snd).flatten

def sibLevel (num : Nat → Nat) (path : Nat → List Nat) :
    Nat → List Nat → List Nat
  | 0, nodes => nodes
  | fuel + 1, nodes =>
    sibMerge num ((clusterBlocks (fun v => (path v).head?) (nodes.length + 1) nodes).map fun it =>
      ((path (it.headD 0)).head?,
        if ((path (it.headD 0)).head?).isSome then
          sibLevel num (fun v => (path v).tail) fuel it
        else it))

theorem place_perm : ∀ (items sorted : List Item),
    sorted.length = (items.filter fun t => t.1.isSome).length →
    (place items sorted).Perm ((items.filter fun t => !t.1.isSome) ++ sorted) := by
  intro items
  induction items with
  | nil =>
    intro sorted h
    have hs : sorted = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hs
    simp [place]
  | cons t ts ih =>
    intro sorted h
    rcases t with ⟨k, ns⟩
    cases k with
    | none =>
      have h' : sorted.length = (ts.filter fun t => t.1.isSome).length := by
        simpa [List.filter_cons] using h
      have := ih sorted h'
      simp only [place, List.filter_cons]
      simpa using this.cons (none, ns)
    | some c =>
      cases sorted with
      | nil => simp at h
      | cons b bs =>
        have h' : bs.length = (ts.filter fun t => t.1.isSome).length := by
          simpa [List.filter_cons] using h
        have := ih bs h'
        simp only [place, List.filter_cons]
        simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, ite_false]
        exact (this.cons b).trans List.perm_middle.symm

theorem place_perm_items (items sorted : List Item)
    (hsorted : sorted.Perm (items.filter fun t => t.1.isSome)) :
    (place items sorted).Perm items :=
  (place_perm items sorted hsorted.length_eq).trans
    (((List.Perm.append_left _ hsorted).trans List.perm_append_comm).trans
      (List.filter_append_perm (fun t => t.1.isSome) items))

theorem sibPlaced_perm (num : Nat → Nat) (items : List Item) :
    (place items (sibSorted num items)).Perm items :=
  place_perm_items _ _ (List.mergeSort_perm _ _)

theorem sibMerge_perm (num : Nat → Nat) (items : List Item) :
    (sibMerge num items).Perm (items.map Prod.snd).flatten :=
  ((sibPlaced_perm num items).map Prod.snd).flatten

theorem sublist_sibMerge (num : Nat → Nat) {items : List Item} {t : Item} (ht : t ∈ items) :
    t.2.Sublist (sibMerge num items) :=
  List.sublist_flatten_of_mem
    (List.mem_map.mpr ⟨t, (sibPlaced_perm num items).mem_iff.mpr ht, rfl⟩)

theorem sibLevel_perm (num : Nat → Nat) :
    ∀ (fuel : Nat) (path : Nat → List Nat) (nodes : List Nat),
      (sibLevel num path fuel nodes).Perm nodes := by
  intro fuel
  induction fuel with
  | zero => intro path nodes; exact List.Perm.refl _
  | succ fuel ih =>
    intro path nodes
    unfold sibLevel
    refine (sibMerge_perm num _).trans ?_
    rw [List.map_map]
    refine (flatten_map_perm _ _ (fun b => ?_)).trans (clusterBlocks_perm _ _ _)
    dsimp only [Function.comp]
    split
    · exact ih _ _
    · exact List.Perm.refl _

theorem sibLevel_contiguous (num : Nat → Nat) :
    ∀ (fuel : Nat) (path : Nat → List Nat) (nodes pref : List Nat), pref.length ≤ fuel →
      ((sibLevel num path fuel nodes).filter (fun v => pref.isPrefixOf (path v))).IsInfix
        (sibLevel num path fuel nodes) := by
  intro fuel
  induction fuel with
  | zero =>
    intro path nodes pref hf
    have hp : pref = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    change (nodes.filter (fun _ => true)).IsInfix nodes
    rw [List.filter_eq_self.mpr (by simp)]
    exact List.infix_refl _
  | succ fuel ih =>
    intro path nodes pref hf
    cases pref with
    | nil =>
      change ((sibLevel num path (fuel + 1) nodes).filter (fun _ => true)).IsInfix _
      rw [List.filter_eq_self.mpr (by simp)]
      exact List.infix_refl _
    | cons c cs =>
      let blocks := clusterBlocks (fun v => (path v).head?) (nodes.length + 1) nodes
      let f : List Nat → List Nat := fun it =>
        if ((path (it.headD 0)).head?).isSome then
          sibLevel num (fun v => (path v).tail) fuel it
        else it
      have hperm : ∀ b, (f b).Perm b := by
        intro b
        dsimp only [f]
        split
        · exact sibLevel_perm _ _ _ _
        · exact List.Perm.refl _
      have hsep := clusterBlocks_separate (fun v => (path v).head?) (nodes.length + 1) nodes
        (Nat.le_succ _)
      have hsep' := clusterSeparate_map _ blocks f hperm hsep
      unfold sibLevel
      generalize hI : (blocks.map fun it =>
          ((path (it.headD 0)).head?,
            if ((path (it.headD 0)).head?).isSome then
              sibLevel num (fun v => (path v).tail) fuel it
            else it)) = items
      have hmap : items.map Prod.snd = blocks.map f := by
        rw [← hI, List.map_map]
        rfl
      have hpl := sibPlaced_perm num items
      have hsepP : List.Pairwise (ClusterSeparate (fun v => (path v).head?))
          ((place items (sibSorted num items)).map Prod.snd) := by
        rw [← hmap] at hsep'
        exact hsep'.perm (hpl.map Prod.snd).symm (fun h => ClusterSeparate.symm h)
      change (((place items (sibSorted num items)).map Prod.snd).flatten.filter
        (fun v => (c :: cs).isPrefixOf (path v))).IsInfix _
      apply filter_infix_of_subordinate (fun v => (path v).head?) c _ _ (prefix_head path c cs)
        hsepP
      intro b hb
      have hb' : b ∈ blocks.map f := by
        rw [← hmap]
        exact (hpl.map Prod.snd).mem_iff.mp hb
      obtain ⟨orig, ho, rfl⟩ := List.mem_map.mp hb'
      have hu := clusterBlocks_uniform (fun v => (path v).head?) (nodes.length + 1) nodes
        (Nat.le_succ _) orig ho
      by_cases hempty : orig = []
      · subst hempty
        have hz : f [] = [] := List.perm_nil.mp (hperm [])
        rw [hz]
        simp
      · have hhead : orig.headD 0 ∈ orig := by
          cases orig with
          | nil => exact absurd rfl hempty
          | cons x rest => exact List.mem_cons_self
        by_cases hc : (path (orig.headD 0)).head? = some c
        · have hall : ∀ v ∈ orig, (path v).head? = some c := by
            intro v hv
            exact (hu v hv _ hhead).trans hc
          have hf' : f orig = sibLevel num (fun v => (path v).tail) fuel orig := by
            dsimp only [f]
            rw [hc]
            rfl
          rw [hf']
          have hrec := ih (fun v => (path v).tail) orig cs (by simp at hf; omega)
          have heq : (sibLevel num (fun v => (path v).tail) fuel orig).filter
                (fun v => (c :: cs).isPrefixOf (path v)) =
              (sibLevel num (fun v => (path v).tail) fuel orig).filter
                (fun v => cs.isPrefixOf ((path v).tail)) := by
            apply List.filter_congr
            intro v hv
            have hv' := (sibLevel_perm num _ _ _).mem_iff.mp hv
            have hh := hall v hv'
            cases hp : path v with
            | nil => simp [hp] at hh
            | cons a rest =>
              have ha : a = c := by simpa [hp] using hh
              subst ha
              simp [List.isPrefixOf]
          rw [heq]
          exact hrec
        · have hnil : (f orig).filter (fun v => (c :: cs).isPrefixOf (path v)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro v hv hp
            have hv' := (hperm orig).mem_iff.mp hv
            exact hc ((hu _ hhead v hv').trans (prefix_head path c cs v hp))
          rw [hnil]
          exact List.nil_infix

end Sibling

def sibFuel (p : Proper) (layer : List Nat) : Nat :=
  layer.foldl (fun d v => max d (nodePath p v).length) 0 + 1

def siblingLayer (p : Proper) (num : Nat → Nat) (layer : List Nat) : List Nat :=
  Sibling.sibLevel num (nodePath p) (sibFuel p layer) layer

def siblingNormalise (p : Proper) (L : List (List Nat)) : List (List Nat) :=
  if (Sibling.clusterIds p).isEmpty then L
  else
    let orders := Sibling.siblingOrders p (posOf p L)
    L.map (siblingLayer p (Sibling.siblingNumber p orders))

def initBase (p : Proper) : List (List Nat) :=
  (List.range (layerCount p)).map fun r =>
    let layer := layerNodes p r
    constrainedLayer p .barycentre (fun _ => []) (fun v => (layer.idxOf v : Int)) layer true

def initOrder (p : Proper) : List (List Nat) := siblingNormalise p (initBase p)

def sortLayer (p : Proper) (nb : Nat → List Nat) (pos : Nat → Int) (layer : List Nat)
    (key : OrderKey := .barycentre) : List Nat :=
  constrainedLayer p key nb pos layer

def sweepStep (p : Proper) (nb : Nat → List Nat) (L : List (List Nat)) (r : Nat)
    (key : OrderKey := .barycentre) : List (List Nat) :=
  L.set r (sortLayer p nb (posOf p L) (L.getD r []) key)

def sweepLayers (p : Proper) (s : Nat) (L : List (List Nat))
    (key : OrderKey := .barycentre) : List (List Nat) :=
  if s % 2 = 0 then
    (List.range (L.length - 1)).foldl (fun M k => sweepStep p (aboveOf p) M (k + 1) key) L
  else
    (List.range (L.length - 1)).foldl
      (fun M k => sweepStep p (belowOf p) M (L.length - 2 - k) key) L

def cmpSign (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

def swapDelta (pos : Nat → Int) (a b : List Nat) : Int :=
  (a.map fun u => (b.map fun v => cmpSign (pos v) (pos u)).sum).sum

def delta (p : Proper) (pos : Nat → Int) (a b : Nat) : Int :=
  swapDelta pos (aboveOf p a) (aboveOf p b) + swapDelta pos (belowOf p a) (belowOf p b)

def sameInnermost (p : Proper) (a b : Nat) : Prop :=
  let na := (p.nodes.getD a default).node
  let nb := (p.nodes.getD b default).node
  nodePath p a = nodePath p b ∧ na.border = 0 ∧ nb.border = 0

instance (p : Proper) (a b : Nat) : Decidable (sameInnermost p a b) := by
  unfold sameInnermost
  infer_instance

def scanGo (p : Proper) (pos : Nat → Int) : Nat → List Nat → List Nat
  | c, [] => [c]
  | c, x :: rest =>
    if delta p pos c x < 0 ∧ sameInnermost p c x then
      x :: scanGo p pos c rest else c :: scanGo p pos x rest

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
    let trial := siblingNormalise p (transpose p (sweepLayers p sweep best))
    let next := crossCount p trial
    let improved := decide (next < score)
    let best' := if improved then trial else best
    let score' := if improved then next else score
    let stall' := if improved then 0 else stall + 1
    if sweep + 1 = limit then ⟨best', true⟩
    else if stallLimit ≤ stall' then ⟨best', false⟩
    else runFrom p limit stallLimit fuel (sweep + 1) best' score' stall'
def runKey (p : Proper) (key : OrderKey) (limit stallLimit : Nat) :
    Nat → Nat → List (List Nat) → Nat → Nat → OrderResult
  | 0, _, best, _, _ => ⟨best, false⟩
  | fuel + 1, sweep, best, score, stall =>
    let trial := siblingNormalise p (transpose p (sweepLayers p sweep best key))
    let next := crossCount p trial
    let improved := decide (next < score)
    let best' := if improved then trial else best
    let score' := if improved then next else score
    let stall' := if improved then 0 else stall + 1
    if sweep + 1 = limit then ⟨best', true⟩
    else if stallLimit ≤ stall' then ⟨best', false⟩
    else runKey p key limit stallLimit fuel (sweep + 1) best' score' stall'

def breadthVisit (p : Proper) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, v :: queue, seen =>
    let children := (belowOf p v).foldl
      (fun acc w => if w ∈ seen ∨ w ∈ queue ∨ w ∈ acc then acc else acc ++ [w]) []
    breadthVisit p fuel (queue ++ children) (seen ++ [v])

def breadthDiscovery (p : Proper) : List Nat :=
  let roots := (List.range p.nodes.length).mergeSort (declLe p)
  let first := (roots.find? fun v => (aboveOf p v).isEmpty).getD (roots.headD 0)
  (first :: roots).foldl (fun seen v =>
    if v ∈ seen then seen else breadthVisit p p.nodes.length [v] seen) []

def startLayer (p : Proper) (start : OrderStart) (layer : List Nat) : List Nat :=
  match start with
  | .declaration => layer
  | .reversed => layer.reverse
  | .breadthFirst =>
    let discovery := breadthDiscovery p
    layer.mergeSort (fun a b => decide (discovery.idxOf a ≤ discovery.idxOf b))

def seedBase (p : Proper) (start : OrderStart) : List (List Nat) :=
  ((List.range (layerCount p)).map (layerNodes p)).map fun layer =>
    let started := startLayer p start layer
    constrainedLayer p .barycentre (fun _ => []) (fun v => (started.idxOf v : Int)) started true

def seedLayers (p : Proper) (start : OrderStart) : List (List Nat) :=
  siblingNormalise p (seedBase p start)

def seedBest (p : Proper) (start : OrderStart) : List (List Nat) :=
  let candidate := seedLayers p start
  if crossCount p candidate < crossCount p (initOrder p) then candidate else initOrder p


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
  if Valid p then
    if 0 < sweepMax ∧ 0 < sweepStall then
      let seed := seedBest p opts.start
      .ok (runKey p opts.key sweepMax sweepStall sweepMax 0 seed (crossCount p seed) 0)
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

def BordersWellFormed (p : Proper) : Prop :=
  (∀ (a : Nat) (na : ProperNode), p.nodes[a]? = some na →
    (na.node.border = -1 ∨ na.node.border = 1) → na.node.clusterPath ≠ []) ∧
  (∀ (a b : Nat) (na nb : ProperNode), p.nodes[a]? = some na → p.nodes[b]? = some nb →
    (na.node.border = -1 ∨ na.node.border = 1) → nb.node.border = na.node.border →
    nb.node.clusterPath = na.node.clusterPath → lay p a = lay p b → a = b) ∧
  (∀ (a : Nat) (na : ProperNode), p.nodes[a]? = some na → na.dummy = true →
    na.node.border = 0)

def BorderConstructionReady (p : Proper) : Prop :=
  (∀ n ∈ p.nodes, n.node.border ≠ -1 ∧ n.node.border ≠ 1) ∧
  (∀ n ∈ p.nodes, n.node.border = -2 → n.node.clusterPath ≠ []) ∧
  (∀ (a b : Nat) (na nb : ProperNode), p.nodes[a]? = some na → p.nodes[b]? = some nb →
    na.node.border = -2 → nb.node.border = -2 →
    na.node.clusterPath = nb.node.clusterPath → a = b) ∧
  p.nodes.length = p.rank.length ∧
  (∀ n ∈ p.nodes, n.dummy = true → n.node.border = 0)

def BorderExtension (p q : Proper) : Prop :=
  (∃ added, q.edges = p.edges ++ added ∧ ∀ e ∈ added, e.synthetic = true) ∧
    q.chains = p.chains ∧
    ∃ extra, q.nodes = p.nodes ++ extra ∧
      ∀ n ∈ extra, n.dummy = false ∧ n.edge = none

theorem borderExtension_refl (p : Proper) : BorderExtension p p := by
  exact ⟨⟨[], by simp, by simp⟩, rfl, [], by simp, by simp⟩

theorem borderExtension_append (p q : Proper) (h : BorderExtension p q)
    (extra : List ProperNode)
    (he : ∀ n ∈ extra, n.dummy = false ∧ n.edge = none) (r : List Int) :
    BorderExtension p { q with nodes := q.nodes ++ extra, rank := q.rank ++ r } := by
  obtain ⟨h1, h2, x, hx, hall⟩ := h
  refine ⟨h1, h2, x ++ extra, ?_, ?_⟩
  · simp [hx, List.append_assoc]
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hall n hn
    · exact he n hn

theorem borderExtension_append_edges (p q : Proper) (h : BorderExtension p q)
    (extra : List ProperNode)
    (he : ∀ n ∈ extra, n.dummy = false ∧ n.edge = none)
    (r : List Int) (links : List ProperEdge) (hs : ∀ e ∈ links, e.synthetic = true) :
    BorderExtension p {
      q with
      nodes := q.nodes ++ extra
      rank := q.rank ++ r
      edges := q.edges ++ links } := by
  obtain ⟨⟨old, hedges, hsynthetic⟩, hchains, nodes, hnodes, hmeta⟩ := h
  refine ⟨⟨old ++ links, ?_, ?_⟩, hchains, nodes ++ extra, ?_, ?_⟩
  · simp [hedges, List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hsynthetic e he
    · exact hs e he
  · simp [hnodes, List.append_assoc]
  · intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact hmeta n hn
    · exact he n hn

theorem borderLinks_synthetic (next decl offset : Nat) :
    ∀ e ∈ borderLinks next decl offset, e.synthetic = true := by
  unfold borderLinks
  split <;> simp_all

theorem addClusterBorders_metadata (p : Proper) (borderWidth : Int) :
    BorderExtension p (addClusterBorders p borderWidth) := by
  unfold addClusterBorders
  apply foldl_inv (BorderExtension p) _ _ p (borderExtension_refl p)
  intro out hout q _
  dsimp only
  split
  · exact hout
  · apply foldl_inv (BorderExtension p) _ _ out hout
    intro state hstate offset _
    apply borderExtension_append_edges p state hstate
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl <;> exact ⟨rfl, rfl⟩
    · exact borderLinks_synthetic _ _ _

theorem dropSynthetic_edges_of_extension {p q : Proper} (h : BorderExtension p q)
    (clean : ∀ e ∈ p.edges, e.synthetic = false) :
    (dropSynthetic q).edges = p.edges := by
  obtain ⟨added, hedges, hall⟩ := h.1
  change q.edges.filter (fun edge => !edge.synthetic) = p.edges
  rw [hedges, List.filter_append]
  have hclean : p.edges.filter (fun edge => !edge.synthetic) = p.edges :=
    List.filter_eq_self.mpr (fun e he => by simp [clean e he])
  have hextra : added.filter (fun edge => !edge.synthetic) = [] :=
    List.filter_eq_nil_iff.mpr (fun e he => by simp [hall e he])
  rw [hclean, hextra, List.append_nil]

theorem dropSynthetic_addClusterBorders_edges (p : Proper) (borderWidth : Int)
    (clean : ∀ e ∈ p.edges, e.synthetic = false) :
    (dropSynthetic (addClusterBorders p borderWidth)).edges = p.edges :=
  dropSynthetic_edges_of_extension (addClusterBorders_metadata p borderWidth) clean

theorem dropSynthetic_lay (p : Proper) (v : Nat) :
    lay (dropSynthetic p) v = lay p v := rfl

theorem dropSynthetic_layerNodes (p : Proper) (rank : Nat) :
    layerNodes (dropSynthetic p) rank = layerNodes p rank := rfl

def Layering (p : Proper) (L : List (List Nat)) : Prop :=
  L.length = layerCount p ∧ ∀ r, r < L.length → (L.getD r []).Perm (layerNodes p r)

theorem getD_set_self {L : List (List Nat)} {r : Nat} (h : r < L.length) (x : List Nat) :
    (L.set r x).getD r [] = x := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne {L : List (List Nat)} {r i : Nat} (h : i ≠ r) (x : List Nat) :
    (L.set r x).getD i [] = L.getD i [] := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem constrainedLayer_perm (p : Proper) (key : OrderKey) (nb : Nat → List Nat)
    (pos : Nat → Int) (layer : List Nat) (initial : Bool := false) :
    (constrainedLayer p key nb pos layer initial).Perm layer := by
  unfold constrainedLayer
  split
  · exact List.mergeSort_perm _ _
  · exact clusterTree_perm _ _ _ _ _

theorem initBase_layering (p : Proper) : Layering p (initBase p) := by
  refine ⟨by simp [initBase], ?_⟩
  intro r hr
  have hr' : r < layerCount p := by simpa [initBase] using hr
  simpa [initBase, List.getD_eq_getElem?_getD, hr'] using
    constrainedLayer_perm p .barycentre (fun _ => [])
      (fun v => ((layerNodes p r).idxOf v : Int)) (layerNodes p r) true

theorem layering_map (p : Proper) (L : List (List Nat)) (hL : Layering p L)
    (f : List Nat → List Nat) (hf : ∀ l, (f l).Perm l) : Layering p (L.map f) := by
  refine ⟨by simpa using hL.1, ?_⟩
  intro r hr
  have hr' : r < L.length := by simpa using hr
  have h := (hf L[r]).trans (by
    simpa [List.getD_eq_getElem?_getD, hr'] using hL.2 r hr')
  simpa [List.getD_eq_getElem?_getD, hr'] using h

theorem siblingLayer_perm (p : Proper) (num : Nat → Nat) (layer : List Nat) :
    (siblingLayer p num layer).Perm layer :=
  Sibling.sibLevel_perm _ _ _ _

theorem siblingNormalise_cases (p : Proper) (L : List (List Nat)) :
    siblingNormalise p L = L ∨
      ∃ num : Nat → Nat, siblingNormalise p L = L.map (siblingLayer p num) := by
  unfold siblingNormalise
  split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem siblingNormalise_length (p : Proper) (L : List (List Nat)) :
    (siblingNormalise p L).length = L.length := by
  rcases siblingNormalise_cases p L with h | ⟨num, h⟩
  · rw [h]
  · rw [h, List.length_map]

theorem siblingNormalise_perm (p : Proper) (L : List (List Nat)) :
    (siblingNormalise p L).length = L.length ∧
      ∀ i, ((siblingNormalise p L).getD i []).Perm (L.getD i []) := by
  refine ⟨siblingNormalise_length p L, fun i => ?_⟩
  rcases siblingNormalise_cases p L with h | ⟨num, h⟩
  · rw [h]
  · rw [h]
    by_cases hi : i < L.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some]
      exact siblingLayer_perm p num _
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]

theorem siblingNormalise_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L) :
    Layering p (siblingNormalise p L) := by
  rcases siblingNormalise_cases p L with h | ⟨num, h⟩
  · rw [h]
    exact hL
  · rw [h]
    exact layering_map p L hL _ (siblingLayer_perm p num)

theorem layering_init (p : Proper) : Layering p (initOrder p) :=
  siblingNormalise_layering (initBase_layering p)

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
    (nb : Nat → List Nat) (r : Nat) (key : OrderKey := .barycentre) :
    Layering p (sweepStep p nb L r key) :=
  layering_set hL (constrainedLayer_perm _ _ _ _ _)

theorem sweepLayers_layering {p : Proper} {L : List (List Nat)} (hL : Layering p L) (s : Nat)
    (key : OrderKey := .barycentre) : Layering p (sweepLayers p s L key) := by
  unfold sweepLayers
  split
  · exact foldl_inv (Layering p) _ _ L hL (fun a ha k _ => sweepStep_layering ha _ _ key)
  · exact foldl_inv (Layering p) _ _ L hL (fun a ha k _ => sweepStep_layering ha _ _ key)

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
    have htrial : Layering p (siblingNormalise p (transpose p (sweepLayers p sweep best))) :=
      siblingNormalise_layering (transpose_layering (sweepLayers_layering hb sweep))
    unfold runFrom
    simp only
    by_cases himp : crossCount p (siblingNormalise p (transpose p (sweepLayers p sweep best))) < score
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

theorem startLayer_perm (p : Proper) (start : OrderStart) (layer : List Nat) :
    (startLayer p start layer).Perm layer := by
  cases start with
  | declaration => exact List.Perm.refl _
  | reversed => exact List.reverse_perm _
  | breadthFirst => exact List.mergeSort_perm _ _

theorem declaration_layering (p : Proper) :
    Layering p ((List.range (layerCount p)).map (layerNodes p)) := by
  refine ⟨by simp, ?_⟩
  intro r hr
  have hr' : r < layerCount p := by simpa using hr
  simp [List.getD_eq_getElem?_getD, hr']

theorem seedBase_layering (p : Proper) (start : OrderStart) :
    Layering p (seedBase p start) :=
  layering_map p _ (declaration_layering p) _ (fun layer =>
    (constrainedLayer_perm _ _ _ _ _ true).trans (startLayer_perm p start layer))

theorem seedLayers_layering (p : Proper) (start : OrderStart) :
    Layering p (seedLayers p start) :=
  siblingNormalise_layering (seedBase_layering p start)

theorem seedBest_spec (p : Proper) (start : OrderStart) :
    Layering p (seedBest p start) ∧
      crossCount p (seedBest p start) ≤ crossCount p (initOrder p) := by
  unfold seedBest
  dsimp only
  split
  · exact ⟨seedLayers_layering p start, by omega⟩
  · exact ⟨layering_init p, Nat.le_refl _⟩

theorem runKey_spec (p : Proper) (key : OrderKey) (limit stallLimit : Nat) :
    ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      Layering p best → score = crossCount p best →
      Layering p (runKey p key limit stallLimit fuel sweep best score stall).layers ∧
      crossCount p (runKey p key limit stallLimit fuel sweep best score stall).layers
        ≤ crossCount p best := by
  intro fuel
  induction fuel with
  | zero =>
    intro sweep best score stall hb hs
    exact ⟨hb, Nat.le_refl _⟩
  | succ f ih =>
    intro sweep best score stall hb hs
    have htrial : Layering p (siblingNormalise p (transpose p (sweepLayers p sweep best key))) :=
      siblingNormalise_layering (transpose_layering (sweepLayers_layering hb sweep key))
    unfold runKey
    simp only
    by_cases himp : crossCount p (siblingNormalise p (transpose p (sweepLayers p sweep best key))) < score
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
  unfold orderWithBudget at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      have hs := seedBest_spec p opts.start
      have hr := runKey_spec p opts.key sweepMax sweepStall sweepMax 0
        (seedBest p opts.start) (crossCount p (seedBest p opts.start)) 0 hs.1 rfl
      exact ⟨hr.1, Nat.le_trans hr.2 hs.2⟩
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
    by_cases hswapAllowed : delta p pos₀ c x < 0 ∧ sameInnermost p c x
    · have hneg := hswapAllowed.1
      simp only [hswapAllowed.1, hswapAllowed.2, and_self, ite_true]
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
    · simp only [hswapAllowed, ite_false]
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
    rw [hL.1, (layering_init p).1]
  refine ⟨hlen, fun i => ?_⟩
  by_cases hi : i < r.layers.length
  · have hi' : i < layerCount p := by rw [← hL.1]; exact hi
    have hinit := (layering_init p).2 i (by rw [(layering_init p).1]; exact hi')
    exact (hL.2 i hi).trans hinit.symm
  · rw [getD_nil_of_le (by omega), getD_nil_of_le (by omega)]

theorem order_crossings_le_init (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : crossCount p L ≤ crossCount p (initOrder p) := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  exact (orderWithBudget_spec p opts r hr).2

theorem order_valid_layering (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) : Valid p ∧ Layering p L := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  refine ⟨?_, (orderWithBudget_spec p opts r hr).1⟩
  unfold orderWithBudget at hr
  by_cases hv : Valid p
  · exact hv
  · simp [hv] at hr

theorem filter_infix_map_transfer (pred : Nat → Bool) (xs ys : List Nat)
    (hm : ys.map pred = xs.map pred) (hc : (xs.filter pred).IsInfix xs) :
    (ys.filter pred).IsInfix ys := by
  obtain ⟨pre, post, h⟩ := hc
  have hlen : (pre.filter pred).length = 0 ∧ (post.filter pred).length = 0 := by
    have he := congrArg (fun l => (l.filter pred).length) h
    simp only [List.filter_append, List.length_append, List.filter_filter, Bool.and_self] at he
    change (pre.filter pred).length + (xs.filter pred).length + (post.filter pred).length =
      (xs.filter pred).length at he
    omega
  have hpre : pre.filter pred = [] := List.eq_nil_of_length_eq_zero hlen.1
  have hpost : post.filter pred = [] := List.eq_nil_of_length_eq_zero hlen.2
  have he : ys.map pred = (pre.map pred ++ (xs.filter pred).map pred) ++ post.map pred := by
    calc
      ys.map pred = xs.map pred := hm
      _ = (pre ++ xs.filter pred ++ post).map pred := congrArg (List.map pred) h.symm
      _ = _ := by simp only [List.map_append]
  obtain ⟨left, right, hy, hl, hr⟩ := List.map_eq_append_iff.mp he
  obtain ⟨p, m, hl', hp, hmid⟩ := List.map_eq_append_iff.mp hl
  have alltransfer : ∀ (a b : List Nat), a.map pred = b.map pred →
      (∀ x ∈ b, pred x = true) → ∀ x ∈ a, pred x = true := by
    intro a b hab hb x hx
    have hm : pred x ∈ b.map pred := hab ▸ List.mem_map_of_mem hx
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
    exact hzx ▸ hb z hz
  have nonetransfer : ∀ (a b : List Nat), a.map pred = b.map pred →
      b.filter pred = [] → a.filter pred = [] := by
    intro a b hab hb
    apply List.filter_eq_nil_iff.mpr
    intro x hx hpx
    have hm : pred x ∈ b.map pred := hab ▸ List.mem_map_of_mem hx
    obtain ⟨z, hz, hzx⟩ := List.mem_map.mp hm
    exact (List.filter_eq_nil_iff.mp hb z hz) (hzx ▸ hpx)
  have hp0 := nonetransfer p pre hp hpre
  have hr0 := nonetransfer right post hr hpost
  have hm0 := List.filter_eq_self.mpr
    (alltransfer m (xs.filter pred) hmid (fun x hx => (List.mem_filter.mp hx).2))
  have hy' : ys = p ++ m ++ right := by rw [hy, hl']
  have hfilter : ys.filter pred = m := by
    rw [hy', List.filter_append, List.filter_append, hp0, hr0, hm0]
    simp
  rw [hfilter, hy']
  exact List.infix_append _ _ _

def ClusterContiguous (p : Proper) (layer : List Nat) : Prop :=
  ∀ pref : List Nat, (layer.filter (fun v => pref.isPrefixOf (nodePath p v))).IsInfix layer

def LayersContiguous (p : Proper) (L : List (List Nat)) : Prop :=
  ∀ layer ∈ L, ClusterContiguous p layer

theorem constrainedLayer_contiguous (p : Proper) (key : OrderKey) (nb : Nat → List Nat)
    (pos : Nat → Int) (layer : List Nat) (initial : Bool := false) :
    ClusterContiguous p (constrainedLayer p key nb pos layer initial) := by
  intro pref
  unfold constrainedLayer
  split
  · rename_i hflat
    cases pref with
    | nil =>
      rw [List.filter_eq_self.mpr (by simp)]
      exact List.infix_refl _
    | cons c cs =>
      have hz : (layer.mergeSort (fun a b => fracLe (nodeKey key nb pos a) (nodeKey key nb pos b))).filter
          (fun v => (c :: cs).isPrefixOf (nodePath p v)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro v hv hp
        have hv' := (List.mergeSort_perm _ _).mem_iff.mp hv
        have he := List.all_eq_true.mp hflat v hv'
        have he' : nodePath p v = [] := by simpa using he
        simp [he'] at hp
      rw [hz]
      exact List.nil_infix
  · exact clusterTree_contiguous_all _ _ _ _

theorem forall_set {α : Type} (P : α → Prop) (L : List α) (r : Nat) (x : α)
    (h : ∀ v ∈ L, P v) (hx : P x) : ∀ v ∈ L.set r x, P v := by
  induction L generalizing r with
  | nil => simp
  | cons a rest ih =>
    cases r with
    | zero =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hx
      · exact h v (List.mem_cons_of_mem _ hv)
    | succ r =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact h v (List.mem_cons_self ..)
      · exact ih r (fun w hw => h w (List.mem_cons_of_mem _ hw)) v hv

theorem sweepStep_contiguous (p : Proper) (nb : Nat → List Nat) (L : List (List Nat))
    (r : Nat) (key : OrderKey) (h : LayersContiguous p L) :
    LayersContiguous p (sweepStep p nb L r key) :=
  forall_set _ _ _ _ h (constrainedLayer_contiguous _ _ _ _ _)

theorem sweepLayers_contiguous (p : Proper) (s : Nat) (L : List (List Nat))
    (key : OrderKey) (h : LayersContiguous p L) :
    LayersContiguous p (sweepLayers p s L key) := by
  unfold sweepLayers
  split <;> exact foldl_inv (LayersContiguous p) _ _ L h
    (fun a ha k _ => sweepStep_contiguous p _ a _ key ha)

theorem scanGo_path (p : Proper) (pos : Nat → Int) (rest : List Nat) (c : Nat) :
    (scanGo p pos c rest).map (nodePath p) = (c :: rest).map (nodePath p) := by
  induction rest generalizing c with
  | nil => rfl
  | cons x rest ih =>
    unfold scanGo
    split
    · rename_i h
      have hp := h.2.1
      simp only [List.map_cons, ih]
      rw [hp]
    · simp only [List.map_cons, ih]

theorem scanLayer_contiguous (p : Proper) (pos : Nat → Int) (layer : List Nat)
    (h : ClusterContiguous p layer) : ClusterContiguous p (scanLayer p pos layer) := by
  intro pref
  have hm : (scanLayer p pos layer).map (nodePath p) = layer.map (nodePath p) := by
    cases layer with
    | nil => rfl
    | cons c rest => exact scanGo_path _ _ _ _
  apply filter_infix_map_transfer _ _ _ ?_ (h pref)
  have he := congrArg (List.map (fun path : List Nat => pref.isPrefixOf path)) hm
  simpa only [List.map_map, Function.comp_def] using he

theorem transposeStep_contiguous (p : Proper) (L : List (List Nat)) (r : Nat)
    (h : LayersContiguous p L) : LayersContiguous p (transposeStep p L r) := by
  apply forall_set _ _ _ _ h
  apply scanLayer_contiguous
  by_cases hr : r < L.length
  · exact h _ (by simp [List.getD_eq_getElem?_getD, hr])
  · have hz : L.getD r [] = [] := getD_nil_of_le (by omega)
    rw [hz]
    intro pref
    simp

theorem transpose_contiguous (p : Proper) (L : List (List Nat))
    (h : LayersContiguous p L) : LayersContiguous p (transpose p L) := by
  have hpass : ∀ M, LayersContiguous p M → LayersContiguous p (transposePass p M) := by
    intro M hm
    exact foldl_inv (LayersContiguous p) _ _ M hm
      (fun a ha r _ => transposeStep_contiguous p a r ha)
  unfold transpose
  generalize crossCount p L + 1 = fuel
  induction fuel generalizing L with
  | zero => exact h
  | succ fuel ih =>
    unfold transposeLoop
    dsimp only
    split
    · exact hpass L h
    · exact ih _ (hpass L h)

theorem siblingLayer_contiguous (p : Proper) (num : Nat → Nat) (layer pref : List Nat) :
    ((siblingLayer p num layer).filter (fun v => pref.isPrefixOf (nodePath p v))).IsInfix
      (siblingLayer p num layer) := by
  unfold siblingLayer sibFuel
  by_cases hf : pref.length ≤ layer.foldl (fun d v => max d (nodePath p v).length) 0 + 1
  · exact Sibling.sibLevel_contiguous num _ _ _ _ hf
  · have hz : (Sibling.sibLevel num (nodePath p)
        (layer.foldl (fun d v => max d (nodePath p v).length) 0 + 1) layer).filter
          (fun v => pref.isPrefixOf (nodePath p v)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro v hv hp
      have hv' := (Sibling.sibLevel_perm _ _ _ _).mem_iff.mp hv
      have hl := (fold_max_lower (fun v => (nodePath p v).length) layer 0).2 v hv'
      have hp' := (List.isPrefixOf_iff_prefix.mp hp).length_le
      omega
    rw [hz]
    exact List.nil_infix

theorem siblingNormalise_contiguous {p : Proper} {L : List (List Nat)}
    (h : LayersContiguous p L) : LayersContiguous p (siblingNormalise p L) := by
  rcases siblingNormalise_cases p L with e | ⟨num, e⟩
  · rw [e]
    exact h
  · rw [e]
    intro layer hl pref
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hl
    exact siblingLayer_contiguous p num original pref

theorem initBase_contiguous (p : Proper) : LayersContiguous p (initBase p) := by
  intro layer hl
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
  exact constrainedLayer_contiguous _ _ _ _ _ true

theorem initOrder_contiguous (p : Proper) : LayersContiguous p (initOrder p) :=
  siblingNormalise_contiguous (initBase_contiguous p)

theorem seedBase_contiguous (p : Proper) (start : OrderStart) :
    LayersContiguous p (seedBase p start) := by
  intro layer hl
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hl
  exact constrainedLayer_contiguous _ _ _ _ _ true

theorem seedLayers_contiguous (p : Proper) (start : OrderStart) :
    LayersContiguous p (seedLayers p start) :=
  siblingNormalise_contiguous (seedBase_contiguous p start)

theorem seedBest_contiguous (p : Proper) (start : OrderStart) :
    LayersContiguous p (seedBest p start) := by
  unfold seedBest
  dsimp only
  split
  · exact seedLayers_contiguous p start
  · exact initOrder_contiguous p

theorem runKey_contiguous (p : Proper) (key : OrderKey) (limit stallLimit : Nat) :
    ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      LayersContiguous p best →
      LayersContiguous p (runKey p key limit stallLimit fuel sweep best score stall).layers := by
  intro fuel
  induction fuel with
  | zero => intro sweep best score stall h; exact h
  | succ fuel ih =>
    intro sweep best score stall h
    have ht := siblingNormalise_contiguous
      (transpose_contiguous p _ (sweepLayers_contiguous p sweep best key h))
    unfold runKey
    dsimp only
    by_cases himp : crossCount p (siblingNormalise p (transpose p (sweepLayers p sweep best key))) < score
    · simp only [himp, decide_true, ite_true]
      split
      · exact ht
      · split
        · exact ht
        · exact ih _ _ _ _ ht
    · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
      split
      · exact h
      · split
        · exact h
        · exact ih _ _ _ _ h

theorem order_clusters_contiguous (p : Proper) (opts : OrderOptions)
    (L : List (List Nat)) (h : order p opts = .ok L) :
    ∀ layer ∈ L, ∀ pref : List Nat,
      (layer.filter (fun v => pref.isPrefixOf (nodePath p v))).IsInfix layer := by
  obtain ⟨result, hr, rfl⟩ := ok_layers h
  unfold orderWithBudget at hr
  split at hr
  · split at hr
    · simp only [Except.ok.injEq] at hr
      subst hr
      exact runKey_contiguous p opts.key sweepMax sweepStall sweepMax 0
        (seedBest p opts.start) (crossCount p (seedBest p opts.start)) 0
        (seedBest_contiguous p opts.start)
    · simp at hr
  · simp at hr

theorem sorted_before_of_band_lt {α : Type} (band : α → Int) (xs : List α)
    (hs : xs.Pairwise (fun x y => band x ≤ band y)) (x y : α) (hx : x ∈ xs) (hy : y ∈ xs)
    (hxy : x ≠ y) (hlt : band x < band y) : [x, y].Sublist xs := by
  induction xs with
  | nil => simp at hx
  | cons z rest ih =>
    rw [List.pairwise_cons] at hs
    rcases List.mem_cons.mp hx with hxz | hx'
    · subst hxz
      have hy' : y ∈ rest := (List.mem_cons.mp hy).resolve_left (fun h => hxy h.symm)
      exact List.Sublist.cons_cons _ (List.singleton_sublist.mpr hy')
    · rcases List.mem_cons.mp hy with hyz | hy'
      · subst hyz
        exact absurd (hs.1 x hx') (by omega)
      · exact List.Sublist.cons _ (ih hs.2 hx' hy')

theorem pair_sublist_flatten {α : Type} (S : List (List α)) (X Y : List α) (a b : α)
    (h : [X, Y].Sublist S) (ha : a ∈ X) (hb : b ∈ Y) : [a, b].Sublist S.flatten := by
  induction S with
  | nil => simp at h
  | cons Z S ih =>
    rw [List.flatten_cons]
    rcases List.sublist_cons_iff.mp h with h1 | ⟨r, hr, h2⟩
    · exact List.sublist_append_of_sublist_right (ih h1)
    · have hr' : X = Z ∧ [Y] = r := by simpa using hr
      obtain ⟨rfl, rfl⟩ := hr'
      have hY : Y ∈ S := List.singleton_sublist.mp h2
      have h3 : [a].Sublist X := List.singleton_sublist.mpr ha
      have h4 : [b].Sublist S.flatten :=
        (List.singleton_sublist.mpr hb).trans (List.sublist_flatten_of_mem hY)
      exact h3.append h4

theorem index_lt_of_pair_sublist {l : List Nat} (hnd : l.Nodup) {a b i j : Nat}
    (hs : [a, b].Sublist l) (hab : a ≠ b) (hi : l[i]? = some a) (hj : l[j]? = some b) :
    i < j := by
  induction l generalizing i j with
  | nil => simp at hs
  | cons z rest ih =>
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.mp hs with h1 | ⟨r, hr, h2⟩
    · have ha : a ∈ rest := h1.subset (by simp)
      have hb : b ∈ rest := h1.subset (by simp)
      cases i with
      | zero =>
        simp at hi
        exact absurd (hi ▸ ha) hnd.1
      | succ i' =>
        cases j with
        | zero =>
          simp at hj
          exact absurd (hj ▸ hb) hnd.1
        | succ j' =>
          simp at hi hj
          exact Nat.succ_lt_succ (ih hnd.2 h1 hi hj)
    · have hr' : a = z ∧ [b] = r := by simpa using hr
      obtain ⟨rfl, rfl⟩ := hr'
      cases i with
      | zero =>
        cases j with
        | zero =>
          simp at hj
          exact absurd hj hab
        | succ j' => exact Nat.succ_pos _
      | succ i' =>
        simp at hi
        exact absurd (List.mem_of_getElem? hi) hnd.1

theorem pairwise_ne_cases {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) : R x y ∨ R y x := by
  induction l with
  | nil => simp at hx
  | cons z rest ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with hxz | hx' <;> rcases List.mem_cons.mp hy with hyz | hy'
    · exact absurd (hxz.trans hyz.symm) hxy
    · subst hxz; exact Or.inl (h.1 y hy')
    · subst hyz; exact Or.inr (h.1 x hx')
    · exact ih h.2 hx' hy'

theorem clusterBlocks_same_block (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat)
    (hf : xs.length ≤ fuel) {X Y : List Nat} (hX : X ∈ clusterBlocks key fuel xs)
    (hY : Y ∈ clusterBlocks key fuel xs) {a b c : Nat} (ha : a ∈ X) (hb : b ∈ Y)
    (hka : key a = some c) (hkb : key b = some c) : X = Y := by
  refine Classical.byContradiction (fun hne => ?_)
  rcases pairwise_ne_cases (clusterBlocks_separate key fuel xs hf) hX hY hne with h | h
  · exact h c a ha hka b hb hkb
  · exact h c b hb hkb a ha hka

theorem clusterBlocks_mem_block (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat) {v : Nat}
    (hv : v ∈ xs) : ∃ Y ∈ clusterBlocks key fuel xs, v ∈ Y := by
  have h := (clusterBlocks_perm key fuel xs).mem_iff.mpr hv
  obtain ⟨Y, hY, hvY⟩ := List.mem_flatten.mp h
  exact ⟨Y, hY, hvY⟩

theorem clusterBlocks_mem_of_block (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat)
    {Y : List Nat} {v : Nat} (hY : Y ∈ clusterBlocks key fuel xs) (hv : v ∈ Y) : v ∈ xs :=
  (clusterBlocks_perm key fuel xs).mem_iff.mp (List.mem_flatten.mpr ⟨Y, hY, hv⟩)

theorem clusterBlocks_nodup (key : Nat → Option Nat) (fuel : Nat) (xs : List Nat)
    (h : xs.Nodup) : ∀ Y ∈ clusterBlocks key fuel xs, Y.Nodup := by
  intro Y hY
  have hfl : (clusterBlocks key fuel xs).flatten.Nodup := (clusterBlocks_perm key fuel xs).nodup_iff.mpr h
  exact List.Nodup.sublist (List.sublist_flatten_of_mem hY) hfl

def ctNested (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool) (f depth : Nat)
    (block : List Nat) : List Nat :=
  if ((path (block.headD 0)).head?).isSome then
    clusterTree (fun v => (path v).tail) cmp f (depth + 1) block else block

theorem clusterTree_succ (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (f depth : Nat) (layer : List Nat) :
    clusterTree path cmp (f + 1) depth layer =
      (((clusterBlocks (fun v => (path v).head?) layer.length layer).map
        (ctNested path cmp f depth)).mergeSort (cmp depth)).flatten := rfl

theorem ctNested_perm (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (f depth : Nat) (block : List Nat) : (ctNested path cmp f depth block).Perm block := by
  unfold ctNested
  split
  · exact clusterTree_perm _ _ _ _ _
  · exact List.Perm.refl _

theorem ctNested_loose (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (f depth : Nat) (block : List Nat) (h : (path (block.headD 0)).head? = none) :
    ctNested path cmp f depth block = block := by
  simp only [ctNested, h, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem ctNested_nest (path : Nat → List Nat) (cmp : Nat → List Nat → List Nat → Bool)
    (f depth : Nat) (block : List Nat) (c : Nat) (h : (path (block.headD 0)).head? = some c) :
    ctNested path cmp f depth block = clusterTree (fun v => (path v).tail) cmp f (depth + 1) block := by
  simp only [ctNested, h, Option.isSome_some, ite_true]

theorem headD_mem_of_ne_nil {l : List Nat} (h : l ≠ []) : l.headD 0 ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x rest => exact List.mem_cons_self

def borderBand (np : Nat → List Nat) (bd : Nat → Int) (k v : Nat) : Int :=
  if ((np v)[k]?).isSome then 0 else if bd v = -1 then -1 else if bd v = 1 then 1 else 0

theorem clusterTree_base_order (np : Nat → List Nat) (bd : Nat → Int)
    (cmp : Nat → List Nat → List Nat → Bool)
    (htrue : ∀ k x y, cmp k x y = true →
      borderBand np bd k (x.headD 0) ≤ borderBand np bd k (y.headD 0))
    (hfalse : ∀ k x y, cmp k x y = false →
      borderBand np bd k (y.headD 0) ≤ borderBand np bd k (x.headD 0))
    (path : Nat → List Nat) (f depth : Nat) (layer : List Nat) (a : Nat)
    (hpath : ∀ v, path v = (np v).drop depth) (ha : a ∈ layer) (hpa : path a = [])
    (hshare : ∀ b ∈ layer, (np b).take depth = (np a).take depth)
    (huniq : ∀ b ∈ layer, b ≠ a → np b = np a → bd b ≠ bd a)
    (hbd : bd a = -1 ∨ bd a = 1) :
    ∀ b ∈ layer, b ≠ a →
      (bd a = -1 → [a, b].Sublist (clusterTree path cmp (f + 1) depth layer)) ∧
      (bd a = 1 → [b, a].Sublist (clusterTree path cmp (f + 1) depth layer)) := by
  intro b hb hba
  have hkey : ∀ v, (path v).head? = (np v)[depth]? := by
    intro v
    rw [hpath v, List.head?_drop]
  rw [clusterTree_succ]
  have hmem := fun v (hv : v ∈ layer) =>
    clusterBlocks_mem_block (fun v => (path v).head?) layer.length layer hv
  have hsing := fun (block : List Nat) (c : Nat)
      (hb : block ∈ clusterBlocks (fun v => (path v).head?) layer.length layer)
      (hc : c ∈ block) (hn : (path c).head? = none) =>
    clusterBlocks_boundary_singleton (fun v => (path v).head?) layer.length layer block c
      (Nat.le_refl _) hb hc hn
  have huni := clusterBlocks_uniform (fun v => (path v).head?) layer.length layer (Nat.le_refl _)
  generalize clusterBlocks (fun v => (path v).head?) layer.length layer = blocks at hmem hsing huni ⊢
  have hSsorted := mergeSort_border_bands (cmp depth)
    (fun m => borderBand np bd depth (m.headD 0)) (htrue depth) (hfalse depth)
    (blocks.map (ctNested path cmp f depth))
  have hSmem : ∀ Z, Z ∈ (blocks.map (ctNested path cmp f depth)).mergeSort (cmp depth) ↔
      Z ∈ blocks.map (ctNested path cmp f depth) :=
    fun Z => (List.mergeSort_perm _ _).mem_iff
  generalize (blocks.map (ctNested path cmp f depth)).mergeSort (cmp depth) = S at hSsorted hSmem ⊢
  have hkeyA : (path a).head? = none := by simp [hpa]
  obtain ⟨X, hX, haX⟩ := hmem a ha
  have hXa : X = [a] := hsing X a hX haX hkeyA
  have haS : [a] ∈ S := by
    refine (hSmem _).mpr (List.mem_map.mpr ⟨X, hX, ?_⟩)
    subst hXa
    exact ctNested_loose path cmp f depth [a] (by simpa using hkeyA)
  have hnoneA : (np a)[depth]? = none := by rw [← hkey a]; exact hkeyA
  have hbbA : borderBand np bd depth ([a].headD 0) = bd a := by
    show borderBand np bd depth a = bd a
    rcases hbd with h | h <;> simp [borderBand, hnoneA, h]
  obtain ⟨Y, hY, hbY⟩ := hmem b hb
  have hZS : ctNested path cmp f depth Y ∈ S := (hSmem _).mpr (List.mem_map.mpr ⟨Y, hY, rfl⟩)
  have hbZ : b ∈ ctNested path cmp f depth Y := (ctNested_perm path cmp f depth Y).mem_iff.mpr hbY
  have huniY := huni Y hY
  have hYh : Y.headD 0 ∈ Y := headD_mem_of_ne_nil (List.ne_nil_of_mem hbY)
  have hZband : (bd a = -1 → -1 < borderBand np bd depth ((ctNested path cmp f depth Y).headD 0)) ∧
      (bd a = 1 → borderBand np bd depth ((ctNested path cmp f depth Y).headD 0) < 1) := by
    rcases hh : (path (Y.headD 0)).head? with _ | c
    · have hZY : ctNested path cmp f depth Y = Y := ctNested_loose path cmp f depth Y hh
      have hkb : (path b).head? = none := (huniY b hbY (Y.headD 0) hYh).trans hh
      have hYb : Y = [b] := hsing Y b hY hbY hkb
      have hnb : (np b)[depth]? = none := by rw [← hkey b]; exact hkb
      have hnpb : np b = np a := by
        have h1 := hshare b hb
        have h2 : (np b).drop depth = [] := by
          rw [← hpath b]
          exact List.head?_eq_none_iff.mp hkb
        have h3 : (np a).drop depth = [] := by rw [← hpath a]; exact hpa
        calc np b = (np b).take depth ++ (np b).drop depth := (List.take_append_drop _ _).symm
          _ = (np a).take depth ++ (np a).drop depth := by rw [h1, h2, h3]
          _ = np a := List.take_append_drop _ _
      have hne := huniq b hb hba hnpb
      rw [hZY, hYb]
      constructor
      · intro h1
        have h2 : bd b ≠ -1 := fun h => hne (h.trans h1.symm)
        show -1 < borderBand np bd depth b
        simp only [borderBand, hnb, Option.isSome_none, Bool.false_eq_true, ite_false, h2]
        split <;> omega
      · intro h1
        have h2 : bd b ≠ 1 := fun h => hne (h.trans h1.symm)
        show borderBand np bd depth b < 1
        simp only [borderBand, hnb, Option.isSome_none, Bool.false_eq_true, ite_false, h2]
        split <;> omega
    · have hZ := ctNested_nest path cmp f depth Y c hh
      have hZne : ctNested path cmp f depth Y ≠ [] := List.ne_nil_of_mem hbZ
      have hZh := headD_mem_of_ne_nil hZne
      have hZY : (ctNested path cmp f depth Y).headD 0 ∈ Y :=
        (ctNested_perm path cmp f depth Y).mem_iff.mp hZh
      have hk' : (path ((ctNested path cmp f depth Y).headD 0)).head? = some c :=
        (huniY _ hZY (Y.headD 0) hYh).trans hh
      have hz : (np ((ctNested path cmp f depth Y).headD 0))[depth]? = some c := by
        rw [← hkey]; exact hk'
      have h0 : borderBand np bd depth ((ctNested path cmp f depth Y).headD 0) = 0 := by
        simp only [borderBand, hz, Option.isSome_some, ite_true]
      exact ⟨fun _ => by omega, fun _ => by omega⟩
  have hne : [a] ≠ ctNested path cmp f depth Y := by
    intro h
    rw [← h] at hbZ
    exact hba (List.mem_singleton.mp hbZ)
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hlt : borderBand np bd depth ([a].headD 0) <
        borderBand np bd depth ((ctNested path cmp f depth Y).headD 0) := by
      rw [hbbA, h1]
      exact hZband.1 h1
    exact pair_sublist_flatten S [a] _ a b
      (sorted_before_of_band_lt (fun m => borderBand np bd depth (m.headD 0)) S hSsorted
        [a] _ haS hZS hne hlt) (by simp) hbZ
  · have hlt : borderBand np bd depth ((ctNested path cmp f depth Y).headD 0) <
        borderBand np bd depth ([a].headD 0) := by
      rw [hbbA, h1]
      exact hZband.2 h1
    exact pair_sublist_flatten S _ [a] b a
      (sorted_before_of_band_lt (fun m => borderBand np bd depth (m.headD 0)) S hSsorted
        _ [a] hZS haS hne.symm hlt) hbZ (by simp)

theorem clusterTree_border_order (np : Nat → List Nat) (bd : Nat → Int)
    (cmp : Nat → List Nat → List Nat → Bool)
    (htrue : ∀ k x y, cmp k x y = true →
      borderBand np bd k (x.headD 0) ≤ borderBand np bd k (y.headD 0))
    (hfalse : ∀ k x y, cmp k x y = false →
      borderBand np bd k (y.headD 0) ≤ borderBand np bd k (x.headD 0)) :
    ∀ (n : Nat) (path : Nat → List Nat) (fuel depth : Nat) (layer : List Nat) (a : Nat),
      (∀ v, path v = (np v).drop depth) → layer.Nodup → a ∈ layer →
      (path a).length = n → n + 1 ≤ fuel →
      (∀ b ∈ layer, (np b).take depth = (np a).take depth) →
      (∀ b ∈ layer, b ≠ a → np b = np a → bd b ≠ bd a) →
      (bd a = -1 ∨ bd a = 1) →
      ∀ b ∈ layer, b ≠ a → path a <+: path b →
        (bd a = -1 → [a, b].Sublist (clusterTree path cmp fuel depth layer)) ∧
        (bd a = 1 → [b, a].Sublist (clusterTree path cmp fuel depth layer)) := by
  intro n
  induction n with
  | zero =>
    intro path fuel depth layer a hpath hnd ha hlen hfuel hshare huniq hbd b hb hba _
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    exact clusterTree_base_order np bd cmp htrue hfalse path f depth layer a hpath ha
      (List.eq_nil_of_length_eq_zero hlen) hshare huniq hbd b hb hba
  | succ n ih =>
    intro path fuel depth layer a hpath hnd ha hlen hfuel hshare huniq hbd b hb hba hpre
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hkey : ∀ v, (path v).head? = (np v)[depth]? := by
      intro v
      rw [hpath v, List.head?_drop]
    obtain ⟨c, cs, hpa⟩ : ∃ c cs, path a = c :: cs := by
      cases h : path a with
      | nil => rw [h] at hlen; simp at hlen
      | cons c cs => exact ⟨c, cs, rfl⟩
    obtain ⟨ds, hpb, hcs⟩ : ∃ ds, path b = c :: ds ∧ cs <+: ds := by
      cases h : path b with
      | nil => rw [h, hpa] at hpre; simp at hpre
      | cons d ds =>
        rw [h, hpa, List.cons_prefix_cons] at hpre
        obtain ⟨rfl, hpre'⟩ := hpre
        exact ⟨ds, rfl, hpre'⟩
    rw [clusterTree_succ]
    obtain ⟨X, hX, haX⟩ :=
      clusterBlocks_mem_block (fun v => (path v).head?) layer.length layer ha
    obtain ⟨Y, hY, hbY⟩ :=
      clusterBlocks_mem_block (fun v => (path v).head?) layer.length layer hb
    have hXY : X = Y :=
      clusterBlocks_same_block (fun v => (path v).head?) layer.length layer (Nat.le_refl _)
        hX hY haX hbY (c := c) (by simp [hpa]) (by simp [hpb])
    have hbX : b ∈ X := hXY ▸ hbY
    have huniX := clusterBlocks_uniform (fun v => (path v).head?) layer.length layer
      (Nat.le_refl _) X hX
    have hXnd := clusterBlocks_nodup (fun v => (path v).head?) layer.length layer hnd X hX
    have hXlayer : ∀ v ∈ X, v ∈ layer := fun v hv =>
      clusterBlocks_mem_of_block (fun v => (path v).head?) layer.length layer hX hv
    have hXh : X.headD 0 ∈ X := headD_mem_of_ne_nil (List.ne_nil_of_mem haX)
    have hXhead : (path (X.headD 0)).head? = some c :=
      (huniX (X.headD 0) hXh a haX).trans (by simp [hpa])
    have hnest := ctNested_nest path cmp f depth X c hXhead
    have hrec := ih (fun v => (path v).tail) f (depth + 1) X a
      (by intro v; show (path v).tail = _; rw [hpath v, List.tail_drop])
      hXnd haX
      (by show (path a).tail.length = n; rw [hpa]; simpa [hpa] using hlen)
      (by omega)
      (by
        intro v hv
        have hv1 := hshare v (hXlayer v hv)
        have hk : (np v)[depth]? = (np a)[depth]? := by
          rw [← hkey v, ← hkey a]; exact huniX v hv a haX
        rw [List.take_add_one, List.take_add_one, hv1, hk])
      (fun v hv hva hnp => huniq v (hXlayer v hv) hva hnp)
      hbd b hbX hba
      (by show (path a).tail <+: (path b).tail; rw [hpa, hpb]; exact hcs)
    have hFS : ctNested path cmp f depth X ∈
        ((clusterBlocks (fun v => (path v).head?) layer.length layer).map
          (ctNested path cmp f depth)).mergeSort (cmp depth) :=
      (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_map.mpr ⟨X, hX, rfl⟩)
    have hsub := List.sublist_flatten_of_mem hFS
    rw [hnest] at hsub
    exact ⟨fun h => (hrec.1 h).trans hsub, fun h => (hrec.2 h).trans hsub⟩

namespace Sibling

theorem clusterBlocks_sublist (key : Nat → Option Nat) :
    ∀ (fuel : Nat) (xs : List Nat), ∀ X ∈ clusterBlocks key fuel xs, X.Sublist xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs X hX
    simp only [clusterBlocks, List.mem_singleton] at hX
    subst hX
    exact List.Sublist.refl _
  | succ fuel ih =>
    intro xs X hX
    cases xs with
    | nil => simp [clusterBlocks] at hX
    | cons v vs =>
      simp only [clusterBlocks] at hX
      split at hX
      · rcases List.mem_cons.mp hX with rfl | hX
        · exact List.singleton_sublist.mpr List.mem_cons_self
        · exact (ih vs X hX).cons v
      · rcases List.mem_cons.mp hX with rfl | hX
        · exact List.Sublist.cons_cons v List.filter_sublist
        · exact ((ih _ X hX).trans List.filter_sublist).cons v

theorem sub_pair_restrict : ∀ {X l : List Nat}, X.Sublist l → l.Nodup →
    ∀ {a b : Nat}, a ∈ X → b ∈ X → [a, b].Sublist l → [a, b].Sublist X := by
  intro X l hs
  induction hs with
  | slnil => intro _ a b ha; simp at ha
  | cons y h ih =>
    intro hnd a b ha hb hab
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.mp hab with h1 | ⟨r, hr, _⟩
    · exact ih hnd.2 ha hb h1
    · have hay : a = y := by
        have := congrArg List.head? hr
        simpa using this
      exact absurd (hay ▸ h.subset ha) hnd.1
  | cons_cons y h ih =>
    intro hnd a b ha hb hab
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.mp hab with h1 | ⟨r, hr, h2⟩
    · have hal := h1.subset (by simp : a ∈ [a, b])
      have hbl := h1.subset (by simp : b ∈ [a, b])
      have ha' := (List.mem_cons.mp ha).resolve_left (fun h => hnd.1 (h ▸ hal))
      have hb' := (List.mem_cons.mp hb).resolve_left (fun h => hnd.1 (h ▸ hbl))
      exact (ih hnd.2 ha' hb' h1).cons y
    · have hr' : a = y ∧ [b] = r := by simpa using hr
      obtain ⟨rfl, rfl⟩ := hr'
      have hbl : b ∈ _ := List.singleton_sublist.mp h2
      have hb' := (List.mem_cons.mp hb).resolve_left (fun h => hnd.1 (h ▸ hbl))
      exact List.Sublist.cons_cons a (List.singleton_sublist.mpr hb')

theorem place_append_loose (t : Item) (ht : t.1 = none) :
    ∀ (ts sorted : List Item), place (ts ++ [t]) sorted = place ts sorted ++ [t] := by
  intro ts
  induction ts with
  | nil =>
    intro sorted
    obtain ⟨k, ns⟩ := t
    simp only at ht
    subst ht
    simp [place]
  | cons t' ts ih =>
    intro sorted
    obtain ⟨k', ns'⟩ := t'
    cases k' <;> cases sorted <;> simp [place, ih]

theorem clusterBlocks_snoc_loose (key : Nat → Option Nat) (a : Nat) (hka : key a = none) :
    ∀ (fuel : Nat) (xs : List Nat), a ∉ xs → xs.length + 2 ≤ fuel →
      ∃ pre, clusterBlocks key fuel (xs ++ [a]) = pre ++ [[a]] := by
  intro fuel
  induction fuel with
  | zero => intro xs _ h; omega
  | succ fuel ih =>
    intro xs hnot hlen
    cases xs with
    | nil =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hlen; omega⟩
      exact ⟨[], by simp [clusterBlocks, hka]⟩
    | cons v vs =>
      have hnot' : a ∉ vs := fun h => hnot (List.mem_cons_of_mem _ h)
      have hlen' : vs.length + 2 ≤ fuel := by simp at hlen; omega
      simp only [List.cons_append, clusterBlocks]
      split
      · obtain ⟨pre, hpre⟩ := ih vs hnot' hlen'
        exact ⟨[v] :: pre, by rw [hpre]; rfl⟩
      · rename_i c hc
        have h1 : ((vs ++ [a]).filter fun w => key w == some c) =
            vs.filter fun w => key w == some c := by
          simp [List.filter_append, hka]
        have h2 : ((vs ++ [a]).filter fun w => key w != some c) =
            (vs.filter fun w => key w != some c) ++ [a] := by
          simp [List.filter_append, hka]
        rw [h1, h2]
        have hnot'' : a ∉ vs.filter fun w => key w != some c :=
          fun h => hnot' (List.mem_filter.mp h).1
        have hlen'' : (vs.filter fun w => key w != some c).length + 2 ≤ fuel :=
          Nat.le_trans (Nat.add_le_add_right (List.length_filter_le _ _) 2) hlen'
        obtain ⟨pre, hpre⟩ := ih _ hnot'' hlen''
        exact ⟨(v :: vs.filter fun w => key w == some c) :: pre, by rw [hpre]; rfl⟩

theorem place_filter : ∀ (items sorted : List Item),
    sorted.length = (items.filter fun t => t.1.isSome).length →
    (∀ t ∈ sorted, t.1.isSome = true) →
    (place items sorted).filter (fun t => t.1.isSome) = sorted := by
  intro items
  induction items with
  | nil =>
    intro sorted h _
    have hs : sorted = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst hs
    simp [place]
  | cons t ts ih =>
    intro sorted h hs
    obtain ⟨k, ns⟩ := t
    cases k with
    | none =>
      have h' : sorted.length = (ts.filter fun t => t.1.isSome).length := by
        simpa [List.filter_cons] using h
      simp only [place, List.filter_cons, Option.isSome_none, Bool.false_eq_true, ite_false]
      exact ih sorted h' hs
    | some c =>
      cases sorted with
      | nil => simp at h
      | cons b bs =>
        have h' : bs.length = (ts.filter fun t => t.1.isSome).length := by
          simpa [List.filter_cons] using h
        have hb := hs b List.mem_cons_self
        simp only [place, List.filter_cons, hb, ite_true]
        rw [ih bs h' (fun t ht => hs t (List.mem_cons_of_mem _ ht))]

theorem head_of_pair_sublist {l : List Nat} {a : Nat} (hnd : l.Nodup) (ha : a ∈ l)
    (h : ∀ x ∈ l, x ≠ a → [a, x].Sublist l) : ∃ rest, l = a :: rest := by
  cases l with
  | nil => simp at ha
  | cons x xs =>
    by_cases hxa : x = a
    · exact ⟨xs, by rw [hxa]⟩
    · have h1 := h x List.mem_cons_self hxa
      rw [List.nodup_cons] at hnd
      rcases List.sublist_cons_iff.mp h1 with h2 | ⟨r, hr, _⟩
      · exact absurd (h2.subset (by simp)) hnd.1
      · have : a = x := by
          have := congrArg List.head? hr
          simpa using this
        exact absurd this.symm hxa

theorem last_of_pair_sublist {l : List Nat} {a : Nat} (hnd : l.Nodup) (ha : a ∈ l)
    (h : ∀ x ∈ l, x ≠ a → [x, a].Sublist l) : ∃ pre, l = pre ++ [a] := by
  have h' : ∀ x ∈ l.reverse, x ≠ a → [a, x].Sublist l.reverse := by
    intro x hx hxa
    have h2 := List.reverse_sublist.mpr (h x (List.mem_reverse.mp hx) hxa)
    simpa using h2
  obtain ⟨rest, hrest⟩ := head_of_pair_sublist ((List.reverse_perm l).nodup_iff.mpr hnd)
    (List.mem_reverse.mpr ha) h'
  refine ⟨rest.reverse, ?_⟩
  have := congrArg List.reverse hrest
  simpa using this

theorem sibMerge_cons_loose (num : Nat → Nat) (ns : List Nat) (tl : List Item) :
    sibMerge num ((none, ns) :: tl) = ns ++ sibMerge num tl := by
  simp [sibMerge, sibSorted, place]

theorem sibMerge_append_loose (num : Nat → Nat) (ns : List Nat) (X : List Item) :
    sibMerge num (X ++ [(none, ns)]) = sibMerge num X ++ ns := by
  simp [sibMerge, sibSorted, List.filter_append, place_append_loose (none, ns) rfl]

def BBp (path : Nat → List Nat) (bd : Nat → Int) (l : List Nat) : Prop :=
  ∀ a b, a ∈ l → b ∈ l → a ≠ b → path a <+: path b →
    (bd a = -1 → [a, b].Sublist l) ∧ (bd a = 1 → [b, a].Sublist l)

theorem sibLevel_bb (num : Nat → Nat) (bd : Nat → Int) :
    ∀ (fuel : Nat) (path : Nat → List Nat) (nodes : List Nat), nodes.Nodup →
      BBp path bd nodes → BBp path bd (sibLevel num path fuel nodes) := by
  intro fuel
  induction fuel with
  | zero => intro path nodes _ h; exact h
  | succ fuel ih =>
    intro path nodes hnd hbb a b ha hb hab hpre
    have hperm := sibLevel_perm num (fuel + 1) path nodes
    have ha' : a ∈ nodes := hperm.mem_iff.mp ha
    have hb' : b ∈ nodes := hperm.mem_iff.mp hb
    let key : Nat → Option Nat := fun v => (path v).head?
    let blocks := clusterBlocks key (nodes.length + 1) nodes
    let g : List Nat → Item := fun it =>
      ((path (it.headD 0)).head?,
        if ((path (it.headD 0)).head?).isSome then
          sibLevel num (fun v => (path v).tail) fuel it
        else it)
    have hdef : sibLevel num path (fuel + 1) nodes = sibMerge num (blocks.map g) := rfl
    rw [hdef] at hb ha ⊢
    rcases hk : (path a).head? with _ | q
    · have hpa : path a = [] := List.head?_eq_none_iff.mp hk
      have hall : ∀ x ∈ nodes, x ≠ a →
          (bd a = -1 → [a, x].Sublist nodes) ∧ (bd a = 1 → [x, a].Sublist nodes) :=
        fun x hx hxa => hbb a x ha' hx (Ne.symm hxa) (by rw [hpa]; exact List.nil_prefix)
      have hga : g [a] = (none, [a]) := by simp [g, hpa]
      constructor
      · intro h1
        obtain ⟨rest, hrest⟩ := head_of_pair_sublist hnd ha'
          (fun x hx hxa => (hall x hx hxa).1 h1)
        have hcb : blocks = [a] :: clusterBlocks key (rest.length + 1) rest := by
          subst hrest
          simp [blocks, clusterBlocks, key, hk]
        have hout : sibMerge num (blocks.map g) = a :: sibMerge num ((clusterBlocks key
            (rest.length + 1) rest).map g) := by
          rw [hcb, List.map_cons, hga, sibMerge_cons_loose]
          rfl
        rw [hout] at hb ⊢
        have hbT : b ∈ sibMerge num ((clusterBlocks key (rest.length + 1) rest).map g) :=
          (List.mem_cons.mp hb).resolve_left (fun h => hab h.symm)
        exact List.Sublist.cons_cons a (List.singleton_sublist.mpr hbT)
      · intro h1
        obtain ⟨pre, hpre'⟩ := last_of_pair_sublist hnd ha'
          (fun x hx hxa => (hall x hx hxa).2 h1)
        have hna : a ∉ pre := by
          have := hnd
          rw [hpre', List.nodup_append] at this
          exact fun h => this.2.2 a h a (by simp) rfl
        obtain ⟨pre', hcb⟩ := clusterBlocks_snoc_loose key a (by simp [key, hk]) (nodes.length + 1)
          pre hna (by rw [hpre']; simp)
        have hblocks : blocks = pre' ++ [[a]] := by
          simp only [blocks]
          rw [← hcb]
          congr 2 <;> rw [hpre']
        have hout : sibMerge num (blocks.map g) = sibMerge num (pre'.map g) ++ [a] := by
          rw [hblocks, List.map_append, List.map_cons, List.map_nil, hga, sibMerge_append_loose]
        rw [hout] at hb ⊢
        have hbT : b ∈ sibMerge num (pre'.map g) :=
          (List.mem_append.mp hb).resolve_right (fun h => hab (List.mem_singleton.mp h).symm)
        exact List.Sublist.append (List.singleton_sublist.mpr hbT) (List.Sublist.refl _)
    · obtain ⟨ta, hta⟩ : ∃ ta, path a = q :: ta := by
        cases h : path a with
        | nil => rw [h] at hk; simp at hk
        | cons x xs =>
          rw [h] at hk
          simp only [List.head?_cons, Option.some.injEq] at hk
          exact ⟨xs, by rw [hk]⟩
      obtain ⟨tb, htb, hpt⟩ : ∃ tb, path b = q :: tb ∧ ta <+: tb := by
        cases h : path b with
        | nil => rw [h, hta] at hpre; simp at hpre
        | cons y ys =>
          rw [h, hta, List.cons_prefix_cons] at hpre
          obtain ⟨rfl, hpre'⟩ := hpre
          exact ⟨ys, rfl, hpre'⟩
      obtain ⟨Xa, hXa, haX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes ha'
      obtain ⟨Xb, hXb, hbX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hb'
      have hXY : Xa = Xb :=
        clusterBlocks_same_block key (nodes.length + 1) nodes (Nat.le_succ _) hXa hXb haX hbX
          (c := q) (by simp [key, hta]) (by simp [key, htb])
      subst hXY
      have huni := clusterBlocks_uniform key (nodes.length + 1) nodes (Nat.le_succ _) Xa hXa
      have hXh : Xa.headD 0 ∈ Xa := headD_mem_of_ne_nil (List.ne_nil_of_mem haX)
      have hall : ∀ v ∈ Xa, (path v).head? = some q := fun v hv =>
        (huni v hv a haX).trans (by simp [key, hta])
      have hXhead : (path (Xa.headD 0)).head? = some q := hall _ hXh
      have hcons : ∀ v ∈ Xa, path v = q :: (path v).tail := by
        intro v hv
        have h := hall v hv
        cases hp : path v with
        | nil => rw [hp] at h; simp at h
        | cons x xs =>
          rw [hp] at h
          simp only [List.head?_cons, Option.some.injEq] at h
          simp [h]
      have hXnd : Xa.Nodup := clusterBlocks_nodup key (nodes.length + 1) nodes hnd Xa hXa
      have hsub : Xa.Sublist nodes := clusterBlocks_sublist key (nodes.length + 1) nodes Xa hXa
      have hBBX : BBp (fun v => (path v).tail) bd Xa := by
        intro a' b' ha'X hb'X hne hpre'
        have hpre'' : path a' <+: path b' := by
          rw [hcons a' ha'X, hcons b' hb'X]
          exact List.cons_prefix_cons.mpr ⟨rfl, hpre'⟩
        obtain ⟨h1, h2⟩ := hbb a' b' (hsub.subset ha'X) (hsub.subset hb'X) hne hpre''
        exact ⟨fun h => sub_pair_restrict hsub hnd ha'X hb'X (h1 h),
          fun h => sub_pair_restrict hsub hnd hb'X ha'X (h2 h)⟩
      have hrec := ih (fun v => (path v).tail) Xa hXnd hBBX a b
        ((sibLevel_perm _ _ _ _).mem_iff.mpr haX) ((sibLevel_perm _ _ _ _).mem_iff.mpr hbX) hab
        (by show (path a).tail <+: (path b).tail; rw [hta, htb]; exact hpt)
      have hmem : (some q, sibLevel num (fun v => (path v).tail) fuel Xa) ∈ blocks.map g := by
        refine List.mem_map.mpr ⟨Xa, hXa, ?_⟩
        simp only [g]
        rw [hXhead]
        rfl
      have hsubm := sublist_sibMerge num hmem
      exact ⟨fun h => (hrec.1 h).trans hsubm, fun h => (hrec.2 h).trans hsubm⟩

theorem sibLevel_order (num : Nat → Nat) :
    ∀ (P : List Nat) (fuel : Nat) (path : Nat → List Nat) (nodes : List Nat)
      (u v A B : Nat) (ru rv : List Nat),
      P.length < fuel → u ∈ nodes → v ∈ nodes → path u = P ++ A :: ru → path v = P ++ B :: rv →
      A ≠ B → num A < num B → [u, v].Sublist (sibLevel num path fuel nodes) := by
  intro P
  induction P with
  | nil =>
    intro fuel path nodes u v A B ru rv hf hu hv hpu hpv hAB hnum
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    let key : Nat → Option Nat := fun w => (path w).head?
    let blocks := clusterBlocks key (nodes.length + 1) nodes
    let g : List Nat → Item := fun it =>
      ((path (it.headD 0)).head?,
        if ((path (it.headD 0)).head?).isSome then
          sibLevel num (fun w => (path w).tail) f it
        else it)
    have hdef : sibLevel num path (f + 1) nodes = sibMerge num (blocks.map g) := rfl
    rw [hdef]
    have hku : key u = some A := by simp [key, hpu]
    have hkv : key v = some B := by simp [key, hpv]
    obtain ⟨Xu, hXu, huX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hu
    obtain ⟨Xv, hXv, hvX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hv
    have hUu := clusterBlocks_uniform key (nodes.length + 1) nodes (Nat.le_succ _) Xu hXu
    have hUv := clusterBlocks_uniform key (nodes.length + 1) nodes (Nat.le_succ _) Xv hXv
    have hXuh : Xu.headD 0 ∈ Xu := headD_mem_of_ne_nil (List.ne_nil_of_mem huX)
    have hXvh : Xv.headD 0 ∈ Xv := headD_mem_of_ne_nil (List.ne_nil_of_mem hvX)
    have hhu : (path (Xu.headD 0)).head? = some A := (hUu _ hXuh u huX).trans hku
    have hhv : (path (Xv.headD 0)).head? = some B := (hUv _ hXvh v hvX).trans hkv
    have htu : g Xu = (some A, sibLevel num (fun w => (path w).tail) f Xu) := by
      simp only [g]; rw [hhu]; rfl
    have htv : g Xv = (some B, sibLevel num (fun w => (path w).tail) f Xv) := by
      simp only [g]; rw [hhv]; rfl
    have hmu : g Xu ∈ blocks.map g := List.mem_map.mpr ⟨Xu, hXu, rfl⟩
    have hmv : g Xv ∈ blocks.map g := List.mem_map.mpr ⟨Xv, hXv, rfl⟩
    have hsu : g Xu ∈ sibSorted num (blocks.map g) :=
      (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_filter.mpr ⟨hmu, by simp [htu]⟩)
    have hsv : g Xv ∈ sibSorted num (blocks.map g) :=
      (List.mergeSort_perm _ _).mem_iff.mpr (List.mem_filter.mpr ⟨hmv, by simp [htv]⟩)
    have hsorted : (sibSorted num (blocks.map g)).Pairwise
        (fun x y => ((num (x.1.getD 0) : Nat) : Int) ≤ ((num (y.1.getD 0) : Nat) : Int)) :=
      mergeSort_border_bands
        (fun a b : Item => decide (num (a.1.getD 0) ≤ num (b.1.getD 0)))
        (fun a : Item => ((num (a.1.getD 0) : Nat) : Int))
        (fun a b h => by simpa using h)
        (fun a b h => by
          have := of_decide_eq_false h
          omega) _
    have hlt : ((num ((g Xu).1.getD 0) : Nat) : Int) < ((num ((g Xv).1.getD 0) : Nat) : Int) := by
      rw [htu, htv]
      simp only [Option.getD_some]
      exact_mod_cast hnum
    have hne : g Xu ≠ g Xv := by
      intro h
      rw [h] at hlt
      exact Int.lt_irrefl _ hlt
    have hpair := sorted_before_of_band_lt
      (fun a : Item => ((num (a.1.getD 0) : Nat) : Int)) _ hsorted _ _ hsu hsv hne hlt
    have hplace : (place (blocks.map g) (sibSorted num (blocks.map g))).filter
        (fun t => t.1.isSome) = sibSorted num (blocks.map g) :=
      place_filter _ _ (List.mergeSort_perm _ _).length_eq
        (fun t ht => (List.mem_filter.mp ((List.mergeSort_perm _ _).mem_iff.mp ht)).2)
    have hpair' : [g Xu, g Xv].Sublist (place (blocks.map g) (sibSorted num (blocks.map g))) := by
      refine hpair.trans ?_
      have hf := List.filter_sublist (p := fun t : Item => t.1.isSome)
        (l := place (blocks.map g) (sibSorted num (blocks.map g)))
      rw [hplace] at hf
      exact hf
    have hmap := hpair'.map Prod.snd
    have huX' : u ∈ (g Xu).2 := by
      rw [htu]
      exact (sibLevel_perm _ _ _ _).mem_iff.mpr huX
    have hvX' : v ∈ (g Xv).2 := by
      rw [htv]
      exact (sibLevel_perm _ _ _ _).mem_iff.mpr hvX
    exact pair_sublist_flatten _ _ _ u v hmap huX' hvX'
  | cons q P' ih =>
    intro fuel path nodes u v A B ru rv hf hu hv hpu hpv hAB hnum
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    let key : Nat → Option Nat := fun w => (path w).head?
    let blocks := clusterBlocks key (nodes.length + 1) nodes
    let g : List Nat → Item := fun it =>
      ((path (it.headD 0)).head?,
        if ((path (it.headD 0)).head?).isSome then
          sibLevel num (fun w => (path w).tail) f it
        else it)
    have hdef : sibLevel num path (f + 1) nodes = sibMerge num (blocks.map g) := rfl
    rw [hdef]
    have hku : key u = some q := by simp [key, hpu]
    have hkv : key v = some q := by simp [key, hpv]
    obtain ⟨Xu, hXu, huX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hu
    obtain ⟨Xv, hXv, hvX⟩ := clusterBlocks_mem_block key (nodes.length + 1) nodes hv
    have hXY : Xu = Xv :=
      clusterBlocks_same_block key (nodes.length + 1) nodes (Nat.le_succ _) hXu hXv huX hvX
        (c := q) hku hkv
    subst hXY
    have huni := clusterBlocks_uniform key (nodes.length + 1) nodes (Nat.le_succ _) Xu hXu
    have hXh : Xu.headD 0 ∈ Xu := headD_mem_of_ne_nil (List.ne_nil_of_mem huX)
    have hXhead : (path (Xu.headD 0)).head? = some q := (huni _ hXh u huX).trans hku
    have hrec := ih f (fun w => (path w).tail) Xu u v A B ru rv
      (by simp at hf; omega) huX hvX
      (by simp [hpu]) (by simp [hpv]) hAB hnum
    have hmem : (some q, sibLevel num (fun w => (path w).tail) f Xu) ∈ blocks.map g := by
      refine List.mem_map.mpr ⟨Xu, hXu, ?_⟩
      simp only [g]
      rw [hXhead]
      rfl
    exact hrec.trans (sublist_sibMerge num hmem)

end Sibling

def BorderBefore (p : Proper) (l : List Nat) : Prop :=
  Sibling.BBp (nodePath p) (fun v => (p.nodes.getD v default).node.border) l

def LayersBB (p : Proper) (L : List (List Nat)) : Prop :=
  ∀ layer ∈ L, BorderBefore p layer

theorem borderBefore_nil (p : Proper) : BorderBefore p [] := by
  intro a b ha
  simp at ha

theorem nodePath_of_nondummy {p : Proper} {a : Nat} {na : ProperNode}
    (hn : p.nodes[a]? = some na) (hd : na.dummy = false) :
    nodePath p a = na.node.clusterPath := by
  have h : p.nodes.getD a default = na := by simp [List.getD_eq_getElem?_getD, hn]
  unfold nodePath
  dsimp only
  rw [h, hd]
  rfl

theorem getD_border {p : Proper} {a : Nat} {na : ProperNode} (hn : p.nodes[a]? = some na) :
    (p.nodes.getD a default).node.border = na.node.border := by
  simp [List.getD_eq_getElem?_getD, hn]

theorem border_unique_in_layer {p : Proper} (hwf : BordersWellFormed p) {layer : List Nat}
    (hlay : ∀ u ∈ layer, ∀ v ∈ layer, lay p u = lay p v) {a : Nat} {na : ProperNode}
    (hna : p.nodes[a]? = some na) (ha : a ∈ layer) (hda : na.dummy = false)
    (hbd : na.node.border = -1 ∨ na.node.border = 1) :
    ∀ b ∈ layer, b ≠ a → nodePath p b = nodePath p a →
      (p.nodes.getD b default).node.border ≠ (p.nodes.getD a default).node.border := by
  intro b hb hne hnp hbeq
  rw [getD_border hna] at hbeq
  cases hnb : p.nodes[b]? with
  | none =>
    have h0 : p.nodes.getD b default = default := by simp [List.getD_eq_getElem?_getD, hnb]
    rw [h0] at hbeq
    have h1 : (default : ProperNode).node.border = 0 := rfl
    omega
  | some nb =>
    rw [getD_border hnb] at hbeq
    have hdb : nb.dummy = false := by
      cases hd : nb.dummy with
      | false => rfl
      | true =>
        have := hwf.2.2 b nb hnb hd
        omega
    have hpb := nodePath_of_nondummy hnb hdb
    have hpa := nodePath_of_nondummy hna hda
    have hpath : nb.node.clusterPath = na.node.clusterPath := by
      rw [← hpb, ← hpa]; exact hnp
    exact hne (hwf.2.1 a b na nb hna hnb hbd hbeq hpath (hlay a ha b hb)).symm

theorem border_node {p : Proper} (hwf : BordersWellFormed p) {a : Nat}
    (h : (p.nodes.getD a default).node.border = -1 ∨
      (p.nodes.getD a default).node.border = 1) :
    ∃ na : ProperNode, p.nodes[a]? = some na ∧ na.dummy = false ∧
      na.node.border = (p.nodes.getD a default).node.border := by
  cases hna : p.nodes[a]? with
  | none =>
    have h0 : p.nodes.getD a default = default := by simp [List.getD_eq_getElem?_getD, hna]
    rw [h0] at h
    have h1 : (default : ProperNode).node.border = 0 := rfl
    omega
  | some na =>
    refine ⟨na, rfl, ?_, (getD_border hna).symm⟩
    cases hd : na.dummy with
    | false => rfl
    | true =>
      have := hwf.2.2 a na hna hd
      have hb := getD_border hna
      omega

theorem constrainedLayer_borderBefore (p : Proper) (key : OrderKey) (nb : Nat → List Nat)
    (pos : Nat → Int) (layer : List Nat) (initial : Bool) (hwf : BordersWellFormed p)
    (hnd : layer.Nodup) (hlay : ∀ u ∈ layer, ∀ v ∈ layer, lay p u = lay p v) :
    BorderBefore p (constrainedLayer p key nb pos layer initial) := by
  intro a b ha hb hab hpre
  have hperm := constrainedLayer_perm p key nb pos layer initial
  have ha' : a ∈ layer := hperm.mem_iff.mp ha
  have hb' : b ∈ layer := hperm.mem_iff.mp hb
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩ <;> unfold constrainedLayer <;> split
  · rename_i hflat
    obtain ⟨na, hna, hda, hbdA⟩ := border_node hwf (Or.inl h1)
    have hpa := nodePath_of_nondummy hna hda
    have he := List.all_eq_true.mp hflat a ha'
    have he' : nodePath p a = [] := by simpa using he
    exact absurd (hpa ▸ he') (hwf.1 a na hna (Or.inl (hbdA.trans h1)))
  · rename_i hflat
    dsimp only
    obtain ⟨na, hna, hda, hbdA⟩ := border_node hwf (Or.inl h1)
    have hcmp := clusterTree_border_order (nodePath p)
      (fun v => (p.nodes.getD v default).node.border)
      (fun level x y => blockKeyLe (clusterBlockKey p key nb pos layer initial level x)
        (clusterBlockKey p key nb pos layer initial level y))
      (fun k x y h => blockKeyLe_true_band _ _ h)
      (fun k x y h => blockKeyLe_false_band _ _ h)
      (nodePath p a).length (nodePath p)
      (layer.foldl (fun d v => max d (nodePath p v).length) 0 + 1) 0 layer a
      (fun v => by simp) hnd ha' rfl
      (by have := (fold_max_lower (fun v => (nodePath p v).length) layer 0).2 a ha'; omega)
      (fun v _ => by simp)
      (border_unique_in_layer hwf hlay hna ha' hda (Or.inl (hbdA.trans h1)))
      (Or.inl h1) b hb' hab.symm hpre
    exact hcmp.1 h1
  · rename_i hflat
    obtain ⟨na, hna, hda, hbdA⟩ := border_node hwf (Or.inr h1)
    have hpa := nodePath_of_nondummy hna hda
    have he := List.all_eq_true.mp hflat a ha'
    have he' : nodePath p a = [] := by simpa using he
    exact absurd (hpa ▸ he') (hwf.1 a na hna (Or.inr (hbdA.trans h1)))
  · rename_i hflat
    dsimp only
    obtain ⟨na, hna, hda, hbdA⟩ := border_node hwf (Or.inr h1)
    have hcmp := clusterTree_border_order (nodePath p)
      (fun v => (p.nodes.getD v default).node.border)
      (fun level x y => blockKeyLe (clusterBlockKey p key nb pos layer initial level x)
        (clusterBlockKey p key nb pos layer initial level y))
      (fun k x y h => blockKeyLe_true_band _ _ h)
      (fun k x y h => blockKeyLe_false_band _ _ h)
      (nodePath p a).length (nodePath p)
      (layer.foldl (fun d v => max d (nodePath p v).length) 0 + 1) 0 layer a
      (fun v => by simp) hnd ha' rfl
      (by have := (fold_max_lower (fun v => (nodePath p v).length) layer 0).2 a ha'; omega)
      (fun v _ => by simp)
      (border_unique_in_layer hwf hlay hna ha' hda (Or.inr (hbdA.trans h1)))
      (Or.inr h1) b hb' hab.symm hpre
    exact hcmp.2 h1

theorem pair_sublist_swap {u v c x : Nat} (post : List Nat) (hne : ¬ (u = c ∧ v = x))
    (h : [u, v].Sublist (c :: x :: post)) : [u, v].Sublist (x :: c :: post) := by
  rcases List.sublist_cons_iff.mp h with h1 | ⟨r, hr, h2⟩
  · exact h1.trans ((List.Sublist.cons c (List.Sublist.refl post)).cons_cons x)
  · have hr' : u = c ∧ [v] = r := by simpa using hr
    obtain ⟨hu, hrv⟩ := hr'
    subst hrv
    have hv : v ∈ x :: post := List.singleton_sublist.mp h2
    rcases List.mem_cons.mp hv with hvx | hvp
    · exact absurd ⟨hu, hvx⟩ hne
    · rw [hu]
      exact List.Sublist.cons x (List.Sublist.cons_cons _ (List.singleton_sublist.mpr hvp))

theorem pair_sublist_swap_append {u v c x : Nat} (pre post : List Nat)
    (hne : ¬ (u = c ∧ v = x)) (h : [u, v].Sublist (pre ++ c :: x :: post)) :
    [u, v].Sublist (pre ++ x :: c :: post) := by
  obtain ⟨l₁, l₂, he, h1, h2⟩ := List.sublist_append_iff.mp h
  rcases l₁ with _ | ⟨y, _ | ⟨y', l₁'⟩⟩
  · have hl : l₂ = [u, v] := by simpa using he.symm
    subst hl
    exact List.sublist_append_of_sublist_right (pair_sublist_swap post hne h2)
  · have hl : u = y ∧ [v] = l₂ := by simpa using he
    obtain ⟨hu, hlv⟩ := hl
    subst hlv
    have hv : v ∈ c :: x :: post := List.singleton_sublist.mp h2
    have hv' : v ∈ x :: c :: post := (List.Perm.swap c x post).mem_iff.mpr hv
    have h1' : [u].Sublist pre := hu ▸ h1
    exact List.Sublist.append h1' (List.singleton_sublist.mpr hv')
  · have hl : u = y ∧ v = y' ∧ l₁' = [] ∧ l₂ = [] := by simpa using he
    obtain ⟨hu, hv, hl1, hl2⟩ := hl
    subst hl1
    subst hu
    subst hv
    exact List.sublist_append_of_sublist_left h1

theorem borderBefore_swap (p : Proper) (pre post : List Nat) (c x : Nat)
    (hc : (p.nodes.getD c default).node.border = 0)
    (hx : (p.nodes.getD x default).node.border = 0)
    (h : BorderBefore p (pre ++ c :: x :: post)) :
    BorderBefore p (pre ++ x :: c :: post) := by
  intro a b ha hb hab hpre
  have hperm : (pre ++ x :: c :: post).Perm (pre ++ c :: x :: post) :=
    List.Perm.append_left pre (List.Perm.swap c x post)
  obtain ⟨h1, h2⟩ := h a b (hperm.mem_iff.mp ha) (hperm.mem_iff.mp hb) hab hpre
  refine ⟨fun hb1 => ?_, fun hb1 => ?_⟩
  · refine pair_sublist_swap_append pre post (fun hh => ?_) (h1 hb1)
    have hb1' : (p.nodes.getD a default).node.border = -1 := hb1
    rw [hh.1, hc] at hb1'
    omega
  · refine pair_sublist_swap_append pre post (fun hh => ?_) (h2 hb1)
    have hb1' : (p.nodes.getD a default).node.border = 1 := hb1
    rw [hh.2, hx] at hb1'
    omega

theorem scanGo_borderBefore (p : Proper) (pos : Nat → Int) :
    ∀ (rest pre : List Nat) (c : Nat), BorderBefore p (pre ++ c :: rest) →
      BorderBefore p (pre ++ scanGo p pos c rest) := by
  intro rest
  induction rest with
  | nil =>
    intro pre c h
    simpa [scanGo] using h
  | cons x rest' ih =>
    intro pre c h
    unfold scanGo
    by_cases hs : delta p pos c x < 0 ∧ sameInnermost p c x
    · simp only [hs, and_self, ite_true]
      have hs2 : nodePath p c = nodePath p x ∧ (p.nodes.getD c default).node.border = 0 ∧
          (p.nodes.getD x default).node.border = 0 := hs.2
      have hsw := borderBefore_swap p pre rest' c x hs2.2.1 hs2.2.2 h
      have := ih (pre ++ [x]) c (by simpa using hsw)
      simpa using this
    · simp only [hs, ite_false]
      have := ih (pre ++ [c]) x (by simpa using h)
      simpa using this

theorem scanLayer_borderBefore (p : Proper) (pos : Nat → Int) (l : List Nat)
    (h : BorderBefore p l) : BorderBefore p (scanLayer p pos l) := by
  cases l with
  | nil => exact h
  | cons c rest => exact scanGo_borderBefore p pos rest [] c (by simpa using h)

theorem transposeStep_bb (p : Proper) (L : List (List Nat)) (r : Nat) (h : LayersBB p L) :
    LayersBB p (transposeStep p L r) := by
  apply forall_set _ _ _ _ h
  apply scanLayer_borderBefore
  by_cases hr : r < L.length
  · exact h _ (by simp [List.getD_eq_getElem?_getD, hr])
  · rw [getD_nil_of_le (by omega)]
    exact borderBefore_nil p

theorem transpose_bb (p : Proper) (L : List (List Nat)) (h : LayersBB p L) :
    LayersBB p (transpose p L) := by
  have hpass : ∀ M, LayersBB p M → LayersBB p (transposePass p M) := by
    intro M hm
    exact foldl_inv (LayersBB p) _ _ M hm (fun a ha r _ => transposeStep_bb p a r ha)
  unfold transpose
  generalize crossCount p L + 1 = fuel
  induction fuel generalizing L with
  | zero => exact h
  | succ fuel ih =>
    unfold transposeLoop
    dsimp only
    split
    · exact hpass L h
    · exact ih _ (hpass L h)

theorem layering_getD_props {p : Proper} {L : List (List Nat)} (hL : Layering p L) (r : Nat) :
    (L.getD r []).Nodup ∧ ∀ u ∈ L.getD r [], ∀ v ∈ L.getD r [], lay p u = lay p v := by
  by_cases hr : r < L.length
  · refine ⟨layer_nodup hL hr, fun u hu v hv => ?_⟩
    have h1 := ((layer_mem hL hr).mp hu).2
    have h2 := ((layer_mem hL hr).mp hv).2
    exact h1.trans h2.symm
  · rw [getD_nil_of_le (by omega)]
    exact ⟨List.nodup_nil, by simp⟩

theorem sweepStep_bb {p : Proper} (hwf : BordersWellFormed p) (nb : Nat → List Nat)
    {L : List (List Nat)}
    (hL : Layering p L) (r : Nat) (key : OrderKey) (h : LayersBB p L) :
    LayersBB p (sweepStep p nb L r key) :=
  forall_set _ _ _ _ h
    (constrainedLayer_borderBefore p key nb _ _ false hwf (layering_getD_props hL r).1
      (layering_getD_props hL r).2)

theorem sweepLayers_bb {p : Proper} (hwf : BordersWellFormed p) {L : List (List Nat)}
    (hL : Layering p L)
    (s : Nat) (key : OrderKey) (h : LayersBB p L) : LayersBB p (sweepLayers p s L key) := by
  unfold sweepLayers
  split
  · exact (foldl_inv (fun M => Layering p M ∧ LayersBB p M) _ _ L ⟨hL, h⟩
      (fun a ha k _ => ⟨sweepStep_layering ha.1 _ _ key, sweepStep_bb hwf _ ha.1 _ key ha.2⟩)).2
  · exact (foldl_inv (fun M => Layering p M ∧ LayersBB p M) _ _ L ⟨hL, h⟩
      (fun a ha k _ => ⟨sweepStep_layering ha.1 _ _ key, sweepStep_bb hwf _ ha.1 _ key ha.2⟩)).2

theorem layering_mem_nodup {p : Proper} {L : List (List Nat)} (hL : Layering p L)
    {layer : List Nat} (hl : layer ∈ L) : layer.Nodup := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hl
  have h1 := layer_nodup hL hk
  have h2 : L.getD k [] = L[k] := by simp [List.getD_eq_getElem?_getD, hk]
  rw [h2] at h1
  exact h1

theorem siblingNormalise_bb {p : Proper} {L : List (List Nat)} (hL : Layering p L)
    (h : LayersBB p L) : LayersBB p (siblingNormalise p L) := by
  rcases siblingNormalise_cases p L with e | ⟨num, e⟩
  · rw [e]
    exact h
  · rw [e]
    intro layer hl
    obtain ⟨original, horig, rfl⟩ := List.mem_map.mp hl
    exact Sibling.sibLevel_bb num _ _ _ _ (layering_mem_nodup hL horig) (h original horig)

theorem runKey_bb {p : Proper} (hwf : BordersWellFormed p) (key : OrderKey)
    (limit stallLimit : Nat) :
    ∀ (fuel sweep : Nat) (best : List (List Nat)) (score stall : Nat),
      Layering p best → LayersBB p best →
      LayersBB p (runKey p key limit stallLimit fuel sweep best score stall).layers := by
  intro fuel
  induction fuel with
  | zero =>
    intro sweep best score stall _ h
    exact h
  | succ fuel ih =>
    intro sweep best score stall hb h
    have htl : Layering p (transpose p (sweepLayers p sweep best key)) :=
      transpose_layering (sweepLayers_layering hb sweep key)
    have htrial := siblingNormalise_layering htl
    have ht := siblingNormalise_bb htl (transpose_bb p _ (sweepLayers_bb hwf hb sweep key h))
    unfold runKey
    dsimp only
    by_cases himp : crossCount p (siblingNormalise p (transpose p (sweepLayers p sweep best key))) < score
    · simp only [himp, decide_true, ite_true]
      split
      · exact ht
      · split
        · exact ht
        · exact ih _ _ _ _ htrial ht
    · simp only [himp, decide_false, Bool.false_eq_true, ite_false]
      split
      · exact h
      · split
        · exact h
        · exact ih _ _ _ _ hb h

theorem initBase_bb {p : Proper} (hwf : BordersWellFormed p) :
    LayersBB p (initBase p) := by
  intro layer hl
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hl
  exact constrainedLayer_borderBefore p _ _ _ _ true hwf (layerNodes_nodup p r)
    (fun u hu v hv => (mem_layerNodes.mp hu).2.trans (mem_layerNodes.mp hv).2.symm)

theorem initOrder_bb {p : Proper} (hwf : BordersWellFormed p) :
    LayersBB p (initOrder p) :=
  siblingNormalise_bb (initBase_layering p) (initBase_bb hwf)

theorem seedBase_bb {p : Proper} (hwf : BordersWellFormed p) (start : OrderStart) :
    LayersBB p (seedBase p start) := by
  intro layer hl
  obtain ⟨original, horig, rfl⟩ := List.mem_map.mp hl
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp horig
  have hperm := startLayer_perm p start (layerNodes p r)
  exact constrainedLayer_borderBefore p _ _ _ _ true hwf
    (hperm.nodup_iff.mpr (layerNodes_nodup p r))
    (fun u hu v hv => (mem_layerNodes.mp (hperm.mem_iff.mp hu)).2.trans
      (mem_layerNodes.mp (hperm.mem_iff.mp hv)).2.symm)

theorem seedLayers_bb {p : Proper} (hwf : BordersWellFormed p) (start : OrderStart) :
    LayersBB p (seedLayers p start) :=
  siblingNormalise_bb (seedBase_layering p start) (seedBase_bb hwf start)

theorem seedBest_bb {p : Proper} (hwf : BordersWellFormed p) (start : OrderStart) :
    LayersBB p (seedBest p start) := by
  unfold seedBest
  dsimp only
  split
  · exact seedLayers_bb hwf start
  · exact initOrder_bb hwf

theorem order_border_ends (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : order p opts = .ok L) (hwf : BordersWellFormed p) :
    ∀ layer ∈ L, ∀ (i j a b : Nat) (na nb : ProperNode),
      layer[i]? = some a →
      layer[j]? = some b →
      p.nodes[a]? = some na →
      p.nodes[b]? = some nb →
      a ≠ b →
      na.dummy = false →
      nb.dummy = false →
      na.node.clusterPath <+: nb.node.clusterPath →
      (na.node.border = -1 → i < j) ∧
      (na.node.border = 1 → j < i) := by
  obtain ⟨r, hr, rfl⟩ := ok_layers h
  have hspec := orderWithBudget_spec p opts r hr
  have hbb : LayersBB p r.layers := by
    unfold orderWithBudget at hr
    split at hr
    · split at hr
      · simp only [Except.ok.injEq] at hr
        subst hr
        exact runKey_bb hwf opts.key sweepMax sweepStall sweepMax 0 (seedBest p opts.start)
          (crossCount p (seedBest p opts.start)) 0 (seedBest_spec p opts.start).1
          (seedBest_bb hwf opts.start)
      · simp at hr
    · simp at hr
  intro layer hl i j a b na nb hi hj hna hnb hab hda hdb hpre
  have hnd : layer.Nodup := layering_mem_nodup hspec.1 hl
  have hbb' := hbb layer hl a b (List.mem_of_getElem? hi) (List.mem_of_getElem? hj) hab
    (by rw [nodePath_of_nondummy hna hda, nodePath_of_nondummy hnb hdb]; exact hpre)
  have hbdA : (p.nodes.getD a default).node.border = na.node.border := getD_border hna
  exact ⟨fun h1 => index_lt_of_pair_sublist hnd (hbb'.1 (hbdA.trans h1)) hab hi hj,
    fun h1 => index_lt_of_pair_sublist hnd (hbb'.2 (hbdA.trans h1)) hab.symm hj hi⟩

def extraKey (e : ProperNode × Int) : Int × List Nat × Int :=
  (e.1.node.border, e.1.node.clusterPath, e.2)

structure BInv (p out : Proper) (es : List (ProperNode × Int)) : Prop where
  nodes : out.nodes = p.nodes ++ es.map Prod.fst
  rank : out.rank = p.rank ++ es.map Prod.snd
  good : ∀ e ∈ es, e.1.dummy = false ∧ (e.1.node.border = -1 ∨ e.1.node.border = 1) ∧
    e.1.node.clusterPath ≠ [] ∧ 0 ≤ e.2
  keys : (es.map extraKey).Nodup

theorem binv_base (p : Proper) : BInv p p [] :=
  ⟨by simp, by simp, by simp, by simp⟩

theorem binv_append {p out out' : Proper} {es : List (ProperNode × Int)} (h : BInv p out es)
    (ns : List (ProperNode × Int))
    (hn : out'.nodes = out.nodes ++ ns.map Prod.fst)
    (hr : out'.rank = out.rank ++ ns.map Prod.snd)
    (hgood : ∀ e ∈ ns, e.1.dummy = false ∧ (e.1.node.border = -1 ∨ e.1.node.border = 1) ∧
      e.1.node.clusterPath ≠ [] ∧ 0 ≤ e.2)
    (hkeys : (ns.map extraKey).Nodup)
    (hdisj : ∀ e ∈ es, ∀ e' ∈ ns, extraKey e ≠ extraKey e') :
    BInv p out' (es ++ ns) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hn, h.nodes]
    simp [List.append_assoc]
  · rw [hr, h.rank]
    simp [List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.good e he
    · exact hgood e he
  · rw [List.map_append, List.nodup_append]
    refine ⟨h.keys, hkeys, ?_⟩
    intro k hk k' hk'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hk'
    exact hdisj e he e' he'

theorem inner_fold_binv {p : Proper} (g : Proper → Nat → Proper) (nl nr : ProperNode) (lo : Nat)
    (hg1 : ∀ s k, (g s k).nodes = s.nodes ++ [nl, nr])
    (hg2 : ∀ s k, (g s k).rank =
      s.rank ++ [((lo + k : Nat) : Int), ((lo + k : Nat) : Int)])
    (hnl : nl.dummy = false ∧ nl.node.border = -1 ∧ nl.node.clusterPath ≠ [])
    (hnr : nr.dummy = false ∧ nr.node.border = 1 ∧ nr.node.clusterPath = nl.node.clusterPath) :
    ∀ (m : Nat) (out : Proper) (es : List (ProperNode × Int)), BInv p out es →
      (∀ e ∈ es, e.1.node.clusterPath ≠ nl.node.clusterPath) →
      ∃ es', BInv p ((List.range m).foldl g out) es' ∧
        ∀ e ∈ es', e ∈ es ∨ (e.1.node.clusterPath = nl.node.clusterPath ∧
          e.2 < ((lo + m : Nat) : Int)) := by
  intro m
  induction m with
  | zero =>
    intro out es h _
    exact ⟨es, h, fun e he => Or.inl he⟩
  | succ m ih =>
    intro out es h hfresh
    obtain ⟨es', h', hes'⟩ := ih out es h hfresh
    refine ⟨es' ++ [(nl, ((lo + m : Nat) : Int)), (nr, ((lo + m : Nat) : Int))], ?_, ?_⟩
    · rw [List.range_succ, List.foldl_append]
      refine binv_append h' _ (hg1 _ _) (hg2 _ _) ?_ ?_ ?_
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨hnl.1, Or.inl hnl.2.1, hnl.2.2, by omega⟩
        · exact ⟨hnr.1, Or.inr hnr.2.1, hnr.2.2 ▸ hnl.2.2, by omega⟩
      · simp only [List.map_cons, List.map_nil, extraKey, hnl.2.1, hnr.2.1, hnr.2.2]
        simp
      · intro e he e' he'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        intro hk
        simp only [extraKey, Prod.mk.injEq] at hk
        rcases hes' e he with hold | ⟨hpath, hrank⟩
        · rcases he' with rfl | rfl
          · exact hfresh e hold hk.2.1
          · exact hfresh e hold (hk.2.1.trans hnr.2.2)
        · rcases he' with rfl | rfl
          · have := hk.2.2
            omega
          · have := hk.2.2
            omega
    · intro e he
      rcases List.mem_append.mp he with he | he
      · rcases hes' e he with hold | ⟨hp, hr⟩
        · exact Or.inl hold
        · exact Or.inr ⟨hp, by omega⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact Or.inr ⟨rfl, by omega⟩
        · exact Or.inr ⟨hnr.2.2, by omega⟩


def borderLeft (q : ProperNode × Nat) (w : Int) : ProperNode :=
  ⟨{ decl := q.1.node.decl, w := w, h := 0, clusterPath := q.1.node.clusterPath, border := -1 },
    false, none⟩

def borderRight (q : ProperNode × Nat) (w : Int) : ProperNode :=
  ⟨{ decl := q.1.node.decl, w := w, h := 0, clusterPath := q.1.node.clusterPath, border := 1,
     loopExtent := q.1.node.loopExtent }, false, none⟩

def borderInner (q : ProperNode × Nat) (w : Int) (lo : Nat) (state : Proper) (offset : Nat) :
    Proper :=
  { state with
    edges := state.edges ++ borderLinks state.nodes.length q.1.node.decl offset
    nodes := state.nodes ++ [borderLeft q w, borderRight q w]
    rank := state.rank ++ [((lo + offset : Nat) : Int), ((lo + offset : Nat) : Int)] }

def borderStep (p : Proper) (w : Int) (out : Proper) (q : ProperNode × Nat) : Proper :=
  match (p.nodes.zipIdx.find? fun b =>
      b.1.node.border == 2 && b.1.node.clusterPath == q.1.node.clusterPath).map (·.2) with
  | none => out
  | some bot =>
    (List.range ((rk p.rank bot).toNat + 1 - (rk p.rank q.2).toNat)).foldl
      (borderInner q w (rk p.rank q.2).toNat) out

theorem addClusterBorders_eq (p : Proper) (w : Int) :
    addClusterBorders p w =
      (p.nodes.zipIdx.filter fun q => q.1.node.border == -2).foldl (borderStep p w) p := rfl

theorem borderStep_binv (p : Proper) (w : Int) (q : ProperNode × Nat)
    (hq : q.1.node.clusterPath ≠ []) (out : Proper) (es : List (ProperNode × Int))
    (h : BInv p out es) (hfresh : ∀ e ∈ es, e.1.node.clusterPath ≠ q.1.node.clusterPath) :
    ∃ es', BInv p (borderStep p w out q) es' ∧
      ∀ e ∈ es', e ∈ es ∨ e.1.node.clusterPath = q.1.node.clusterPath := by
  unfold borderStep
  split
  · exact ⟨es, h, fun e he => Or.inl he⟩
  · obtain ⟨es', h', hes'⟩ := inner_fold_binv (p := p) (borderInner q w (rk p.rank q.2).toNat)
      (borderLeft q w) (borderRight q w) (rk p.rank q.2).toNat (fun s k => rfl) (fun s k => rfl)
      ⟨rfl, rfl, hq⟩ ⟨rfl, rfl, rfl⟩ ((rk p.rank _).toNat + 1 - (rk p.rank q.2).toNat) out es h
      hfresh
    exact ⟨es', h', fun e he => (hes' e he).imp id (fun hh => hh.1)⟩

theorem borders_fold_binv (p : Proper) (w : Int) :
    ∀ (as : List (ProperNode × Nat)), (∀ q ∈ as, q.1.node.clusterPath ≠ []) →
      as.Pairwise (fun q q' => q.1.node.clusterPath ≠ q'.1.node.clusterPath) →
      ∀ (out : Proper) (es : List (ProperNode × Int)), BInv p out es →
        (∀ q ∈ as, ∀ e ∈ es, e.1.node.clusterPath ≠ q.1.node.clusterPath) →
        ∃ es', BInv p (as.foldl (borderStep p w) out) es' := by
  intro as
  induction as with
  | nil =>
    intro _ _ out es h _
    exact ⟨es, h⟩
  | cons q rest ih =>
    intro hne hpw out es h hfresh
    obtain ⟨es', h', hes'⟩ := borderStep_binv p w q (hne q (List.mem_cons_self)) out es h
      (hfresh q (List.mem_cons_self))
    have hpw' := List.pairwise_cons.mp hpw
    refine ih (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq')) hpw'.2 _ es' h' ?_
    intro q' hq' e he
    rcases hes' e he with he | he
    · exact hfresh q' (List.mem_cons_of_mem _ hq') e he
    · rw [he]
      exact hpw'.1 q' hq'

theorem binv_lookup {p out : Proper} {es : List (ProperNode × Int)} (h : BInv p out es)
    {a : Nat} {na : ProperNode} (hn : out.nodes[a]? = some na) :
    (a < p.nodes.length ∧ p.nodes[a]? = some na) ∨
    (p.nodes.length ≤ a ∧ ∃ e, es[a - p.nodes.length]? = some e ∧ e.1 = na) := by
  rw [h.nodes, List.getElem?_append] at hn
  by_cases ha : a < p.nodes.length
  · left
    simp only [ha, ite_true] at hn
    exact ⟨ha, hn⟩
  · right
    refine ⟨by omega, ?_⟩
    simp only [ha, ite_false, List.getElem?_map] at hn
    obtain ⟨e, he, hen⟩ := Option.map_eq_some_iff.mp hn
    exact ⟨e, he, hen⟩

theorem binv_rank_lookup {p out : Proper} {es : List (ProperNode × Int)} (h : BInv p out es)
    (hlen : p.nodes.length = p.rank.length) {a : Nat} {e : ProperNode × Int}
    (ha : p.nodes.length ≤ a) (he : es[a - p.nodes.length]? = some e) :
    rk out.rank a = e.2 := by
  rw [h.rank, NormalizeImpl.rk_append_right (by omega), ← hlen]
  simp [rk, List.getD_eq_getElem?_getD, List.getElem?_map, he]

theorem addClusterBorders_bordersWellFormed (p : Proper) (borderWidth : Int)
    (hready : BorderConstructionReady p) :
    BordersWellFormed (addClusterBorders p borderWidth) := by
  obtain ⟨hno, hanch, huniq, hlen, hdum⟩ := hready
  have hmem : ∀ q ∈ p.nodes.zipIdx.filter (fun q => q.1.node.border == -2),
      p.nodes[q.2]? = some q.1 ∧ q.1.node.border = -2 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := List.mem_filter.mp hq
    exact ⟨List.mem_zipIdx_iff_getElem?.mp hq1, by simpa using hq2⟩
  have hnd : ((p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).map Prod.snd).Nodup := by
    have h0 : (p.nodes.zipIdx.map Prod.snd).Nodup := by
      rw [List.zipIdx_map_snd]
      exact List.nodup_range' 1 (by omega)
    exact List.Nodup.sublist ((List.filter_sublist).map Prod.snd) h0
  have hpw : (p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).Pairwise
      (fun q q' => q.1.node.clusterPath ≠ q'.1.node.clusterPath) := by
    have h1 : (p.nodes.zipIdx.filter (fun q => q.1.node.border == -2)).Pairwise
        (fun q q' => q.2 ≠ q'.2) := by
      have := List.nodup_iff_pairwise_ne.mp hnd
      rwa [List.pairwise_map] at this
    refine List.Pairwise.imp_of_mem ?_ h1
    intro q q' hq hq' hne hpath
    have hq1 := hmem q hq
    have hq2 := hmem q' hq'
    exact hne (huniq q.2 q'.2 q.1 q'.1 hq1.1 hq2.1 hq1.2 hq2.2 hpath)
  obtain ⟨es, hinv⟩ := borders_fold_binv p borderWidth _
    (fun q hq => by
      have := hmem q hq
      exact hanch q.1 (List.mem_of_getElem? this.1) this.2)
    hpw p [] (binv_base p) (fun q _ e he => by simp at he)
  rw [← addClusterBorders_eq] at hinv
  refine ⟨?_, ?_, ?_⟩
  · intro a na hna hbd
    rcases binv_lookup hinv hna with ⟨_, hna'⟩ | ⟨_, e, he, rfl⟩
    · have := hno na (List.mem_of_getElem? hna')
      omega
    · exact (hinv.good e (List.mem_of_getElem? he)).2.2.1
  · intro a b na nb hna hnb hbd hbb hpb hlay
    rcases binv_lookup hinv hna with ⟨_, hna'⟩ | ⟨ha, ea, hea, rfl⟩
    · have := hno na (List.mem_of_getElem? hna')
      omega
    · rcases binv_lookup hinv hnb with ⟨_, hnb'⟩ | ⟨hb, eb, heb, rfl⟩
      · have := hno nb (List.mem_of_getElem? hnb')
        omega
      · have hra := binv_rank_lookup hinv hlen ha hea
        have hrb := binv_rank_lookup hinv hlen hb heb
        have hga := (hinv.good ea (List.mem_of_getElem? hea)).2.2.2
        have hgb := (hinv.good eb (List.mem_of_getElem? heb)).2.2.2
        have hl : (rk (addClusterBorders p borderWidth).rank a).toNat =
            (rk (addClusterBorders p borderWidth).rank b).toNat := hlay
        rw [hra, hrb] at hl
        have hrk : ea.2 = eb.2 := by omega
        have hkey : extraKey ea = extraKey eb := by
          simp only [extraKey, Prod.mk.injEq]
          exact ⟨hbb.symm, hpb.symm, hrk⟩
        have hia : (es.map extraKey)[a - p.nodes.length]? = some (extraKey ea) := by
          simp [List.getElem?_map, hea]
        have hib : (es.map extraKey)[b - p.nodes.length]? = some (extraKey eb) := by
          simp [List.getElem?_map, heb]
        have hlt : a - p.nodes.length < (es.map extraKey).length := by
          have := (List.getElem?_eq_some_iff.mp hia).1
          exact this
        have heq : a - p.nodes.length = b - p.nodes.length :=
          (List.Nodup.getElem?_inj hlt hinv.keys).mp (hia.trans (hkey ▸ hib.symm))
        omega
  · intro a na hna hd
    rcases binv_lookup hinv hna with ⟨_, hna'⟩ | ⟨_, e, he, rfl⟩
    · exact hdum na (List.mem_of_getElem? hna') hd
    · have := (hinv.good e (List.mem_of_getElem? he)).1
      rw [this] at hd
      exact absurd hd (by simp)

theorem idxOf_pair_lt : ∀ {l : List Nat} {x y : Nat}, l.Nodup → [x, y].Sublist l →
    l.idxOf x < l.idxOf y := by
  intro l
  induction l with
  | nil => intro x y _ h; simp at h
  | cons a l ih =>
    intro x y hnd h
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.mp h with h1 | ⟨r, hr, h2⟩
    · have hx : x ∈ l := h1.subset (by simp)
      have hy : y ∈ l := h1.subset (by simp)
      have hxa : x ≠ a := fun e => hnd.1 (e ▸ hx)
      have hya : y ≠ a := fun e => hnd.1 (e ▸ hy)
      rw [List.idxOf_cons, List.idxOf_cons]
      simp only [beq_iff_eq, Ne.symm hxa, Ne.symm hya, ite_false]
      have := ih hnd.2 h1
      omega
    · obtain ⟨rfl, rfl⟩ : x = a ∧ [y] = r := by simpa using hr
      have hy : y ∈ l := h2.subset (by simp)
      have hya : y ≠ x := fun e => hnd.1 (e ▸ hy)
      rw [List.idxOf_cons, List.idxOf_cons]
      simp only [beq_iff_eq, Ne.symm hya, ite_false, ite_true]
      omega

theorem lookup_map_pair {α β : Type} [BEq α] [LawfulBEq α] (g : α → β) :
    ∀ (l : List α) (k : α), k ∈ l → (l.map fun P => (P, g P)).lookup k = some (g k)
  | [], k, h => by simp at h
  | P :: ps, k, h => by
    by_cases hk : k = P
    · subst hk
      simp
    · have hps : k ∈ ps := by simpa [hk] using h
      have hb : (k == P) = false := by simpa using hk
      rw [List.map_cons, List.lookup_cons, hb]
      exact lookup_map_pair g ps k hps

theorem foldl_pick_mem (less : Nat → Nat → Bool) :
    ∀ (xs : List Nat) (x : Nat), xs.foldl (fun y z => if less z y then z else y) x ∈ x :: xs := by
  intro xs
  induction xs with
  | nil => intro x; simp
  | cons z zs ih =>
    intro x
    simp only [List.foldl]
    have h := ih (if less z x then z else x)
    by_cases hl : less z x = true
    · simp only [hl, ite_true, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · have hl' : less z x = false := by simpa using hl
      simp only [hl', Bool.false_eq_true, ite_false, List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem pickMin_mem (less : Nat → Nat → Bool) {l : List Nat} {c : Nat}
    (h : Sibling.pickMin less l = some c) : c ∈ l := by
  cases l with
  | nil => simp [Sibling.pickMin] at h
  | cons x xs =>
    simp only [Sibling.pickMin, Option.some.injEq] at h
    rw [← h]
    exact foldl_pick_mem less xs x

theorem kahnOrder_perm (pre less : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (remaining : List Nat), remaining.length ≤ fuel →
      (Sibling.kahnOrder pre less fuel remaining).Perm remaining := by
  intro fuel
  induction fuel with
  | zero =>
    intro remaining h
    have : remaining = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [Sibling.kahnOrder]
  | succ n ih =>
    intro remaining h
    simp only [Sibling.kahnOrder]
    generalize hq : (if (List.filter (fun c => remaining.all fun d => !pre d c) remaining).isEmpty = true
      then remaining else List.filter (fun c => remaining.all fun d => !pre d c) remaining) = q
    have hqsub : ∀ c ∈ q, c ∈ remaining := by
      intro c hc
      rw [← hq] at hc
      split at hc
      · exact hc
      · exact (List.mem_filter.mp hc).1
    cases hpm : Sibling.pickMin less q with
    | none =>
      have hq0 : q = [] := by
        cases q with
        | nil => rfl
        | cons x xs => simp [Sibling.pickMin] at hpm
      subst hq0
      have hr0 : remaining = [] := by
        split at hq
        · exact hq
        · rename_i hne
          exact absurd (by rw [hq]; rfl) hne
      subst hr0
      simp
    | some c =>
      have hc : c ∈ remaining := hqsub c (pickMin_mem less hpm)
      have hlen : (remaining.erase c).length ≤ n := by
        rw [List.length_erase_of_mem hc]
        omega
      exact ((ih _ hlen).cons c).trans (List.perm_cons_erase hc).symm

theorem le_foldl_layerCount (xs : List Int) :
    ∀ s : Nat, s ≤ xs.foldl (fun m r => max m (r.toNat + 1)) s := by
  induction xs with
  | nil => intro s; exact Nat.le_refl s
  | cons x xs ih =>
    intro s
    simp only [List.foldl]
    exact Nat.le_trans (Nat.le_max_left s (x.toNat + 1)) (ih _)

theorem mem_foldl_layerCount (xs : List Int) :
    ∀ (s : Nat), ∀ r ∈ xs, r.toNat + 1 ≤ xs.foldl (fun m r => max m (r.toNat + 1)) s := by
  induction xs with
  | nil => intro s r hr; simp at hr
  | cons x xs ih =>
    intro s r hr
    simp only [List.foldl]
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Nat.le_trans (Nat.le_max_right s (r.toNat + 1)) (le_foldl_layerCount xs _)
    · exact ih _ r hr

theorem lay_lt_layerCount (p : Proper) {v : Nat} (hv : v < p.rank.length) :
    lay p v < layerCount p := by
  have hm : p.rank[v] ∈ p.rank := List.getElem_mem hv
  have := mem_foldl_layerCount p.rank 0 _ hm
  have h : lay p v = p.rank[v].toNat := by
    simp [lay, rk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
  unfold layerCount
  omega

theorem idxOf_inj_of_mem {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a = l.idxOf b) : a = b := by
  have h1 := List.idxOf_lt_length_of_mem ha
  have h2 := List.idxOf_lt_length_of_mem hb
  calc a = l[l.idxOf a] := (List.getElem_idxOf h1).symm
    _ = l[l.idxOf b] := by simp only [h]
    _ = b := List.getElem_idxOf h2

theorem siblingNumber_ne (p : Proper) (pos : Nat → Int) {A B : Nat}
    (hA : A ∈ Sibling.clusterIds p) (hB : B ∈ Sibling.clusterIds p) (hAB : A ≠ B)
    (hpar : Sibling.parentOf p A = Sibling.parentOf p B) :
    Sibling.siblingNumber p (Sibling.siblingOrders p pos) A ≠
      Sibling.siblingNumber p (Sibling.siblingOrders p pos) B := by
  have hmem : Sibling.parentOf p B ∈
      ((Sibling.clusterIds p).map (Sibling.parentOf p)).eraseDups :=
    List.mem_eraseDups.mpr (List.mem_map.mpr ⟨B, hB, rfl⟩)
  obtain ⟨K, hK, hKperm⟩ : ∃ K, List.lookup (Sibling.parentOf p B) (Sibling.siblingOrders p pos) = some K ∧
      K.Perm ((Sibling.clusterIds p).filter fun c => Sibling.parentOf p c == Sibling.parentOf p B) :=
    ⟨_, lookup_map_pair _ _ _ hmem, kahnOrder_perm _ _ _ _ (Nat.le_refl _)⟩
  have hAK : A ∈ K := hKperm.mem_iff.mpr (List.mem_filter.mpr ⟨hA, by simp [hpar]⟩)
  have hBK : B ∈ K := hKperm.mem_iff.mpr (List.mem_filter.mpr ⟨hB, by simp⟩)
  unfold Sibling.siblingNumber
  rw [hpar, hK]
  intro h
  exact hAB (idxOf_inj_of_mem hAK hBK h)

def ClusterPathsFunctional (p : Proper) : Prop :=
  ∀ (a b : Nat) (na nb : ProperNode), p.nodes[a]? = some na → p.nodes[b]? = some nb →
    na.node.border = -1 → nb.node.border = -1 →
    na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
    na.node.clusterPath = nb.node.clusterPath

theorem mem_clusterRows {p : Proper} {a : Nat} {na : ProperNode} {P : List Nat} {A : Nat}
    (hna : p.nodes[a]? = some na) (hb : na.node.border = -1)
    (hp : na.node.clusterPath = P ++ [A]) :
    (A, P.getLast?) ∈ Sibling.clusterRows p := by
  unfold Sibling.clusterRows
  refine List.mem_filterMap.mpr ⟨na, List.mem_of_getElem? hna, ?_⟩
  simp [hb, hp]

theorem clusterIds_mem {p : Proper} {a : Nat} {na : ProperNode} {P : List Nat} {A : Nat}
    (hna : p.nodes[a]? = some na) (hb : na.node.border = -1)
    (hp : na.node.clusterPath = P ++ [A]) : A ∈ Sibling.clusterIds p := by
  have h := mem_clusterRows hna hb hp
  unfold Sibling.clusterIds
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨_, h, rfl⟩

theorem parentOf_eq {p : Proper} (hfun : ClusterPathsFunctional p) {a : Nat} {na : ProperNode}
    {P : List Nat} {A : Nat} (hna : p.nodes[a]? = some na) (hb : na.node.border = -1)
    (hp : na.node.clusterPath = P ++ [A]) : Sibling.parentOf p A = P.getLast? := by
  have h := mem_clusterRows hna hb hp
  unfold Sibling.parentOf
  cases hl : List.lookup A (Sibling.clusterRows p) with
  | none =>
    have := List.lookup_eq_none_iff.mp hl _ h
    simp at this
  | some par =>
    obtain ⟨l₁, l₂, he, _⟩ := List.lookup_eq_some_iff.mp hl
    have hmem : (A, par) ∈ Sibling.clusterRows p := by
      rw [he]
      simp
    obtain ⟨n', hn', hf⟩ := List.mem_filterMap.mp (by unfold Sibling.clusterRows at hmem; exact hmem)
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn'
    have hb' : n'.node.border = -1 := by
      by_cases hne : n'.node.border = -1
      · exact hne
      · exfalso
        simp [hne] at hf
    have hf' : n'.node.clusterPath.getLast? = some A ∧
        par = n'.node.clusterPath.dropLast.getLast? := by
      simp only [hb', beq_self_eq_true, ite_true] at hf
      cases hc : n'.node.clusterPath.getLast? with
      | none => simp [hc] at hf
      | some c =>
        simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        exact ⟨by rw [hf.1], hf.2.symm⟩
    have hpath := hfun i a n' na hi hna hb' hb (by rw [hf'.1, hp]; simp)
    simp only [Option.getD_some]
    rw [hf'.2, hpath, hp]
    simp

def LeftBorderOf (p : Proper) (v : Nat) (path : List Nat) : Prop :=
  ∃ n : ProperNode, p.nodes[v]? = some n ∧ n.node.border = -1 ∧ n.node.clusterPath = path

theorem siblingNormalise_getD {p : Proper} {L : List (List Nat)}
    (h : (Sibling.clusterIds p).isEmpty = false) {r : Nat} (hr : r < L.length) :
    (siblingNormalise p L).getD r [] =
      siblingLayer p (Sibling.siblingNumber p (Sibling.siblingOrders p (posOf p L)))
        (L.getD r []) := by
  unfold siblingNormalise
  simp [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]

theorem siblingLayer_pair {p : Proper} {num : Nat → Nat} {layer : List Nat} {P : List Nat}
    {A B u v : Nat} (hu : u ∈ layer) (hv : v ∈ layer) (hpu : nodePath p u = P ++ [A])
    (hpv : nodePath p v = P ++ [B]) (hAB : A ≠ B) (hnum : num A < num B) :
    [u, v].Sublist (siblingLayer p num layer) := by
  have hfuel : P.length < sibFuel p layer := by
    have := (fold_max_lower (fun v => (nodePath p v).length) layer 0).2 u hu
    simp only [hpu, List.length_append, List.length_singleton] at this
    unfold sibFuel
    omega
  exact Sibling.sibLevel_order num P (sibFuel p layer) (nodePath p) layer u v A B [] []
    hfuel hu hv hpu hpv hAB hnum

theorem nodePath_of_node {p : Proper} {v : Nat} {n : ProperNode} (hv : p.nodes[v]? = some n)
    (hd : n.dummy = false) : nodePath p v = n.node.clusterPath := by
  simp [nodePath, List.getD_eq_getElem?_getD, hv, hd]

theorem order_siblings_consistent {p : Proper} {L : List (List Nat)} (hL : Layering p L)
    (hn : p.nodes.length = p.rank.length) (hwf : BordersWellFormed p)
    (hfun : ClusterPathsFunctional p) {P : List Nat} {A B a b a' b' : Nat} (hAB : A ≠ B)
    (ha : LeftBorderOf p a (P ++ [A])) (hb : LeftBorderOf p b (P ++ [B]))
    (ha' : LeftBorderOf p a' (P ++ [A])) (hb' : LeftBorderOf p b' (P ++ [B]))
    (hr : lay p a = lay p b) (hr' : lay p a' = lay p b')
    (hlt : posOf p (siblingNormalise p L) a < posOf p (siblingNormalise p L) b) :
    posOf p (siblingNormalise p L) a' < posOf p (siblingNormalise p L) b' := by
  obtain ⟨na, hna, hba, hpa⟩ := ha
  obtain ⟨nb, hnb, hbb, hpb⟩ := hb
  obtain ⟨na', hna', hba', hpa'⟩ := ha'
  obtain ⟨nb', hnb', hbb', hpb'⟩ := hb'
  have hdum : ∀ {v : Nat} {n : ProperNode}, p.nodes[v]? = some n → n.node.border = -1 →
      n.dummy = false := by
    intro v n hv hbv
    cases hd : n.dummy with
    | false => rfl
    | true =>
      have := hwf.2.2 v n hv hd
      omega
  have hAid := clusterIds_mem hna hba hpa
  have hBid := clusterIds_mem hnb hbb hpb
  have hne : (Sibling.clusterIds p).isEmpty = false := by
    cases hl : Sibling.clusterIds p with
    | nil => simp [hl] at hAid
    | cons => rfl
  have hpar : Sibling.parentOf p A = Sibling.parentOf p B := by
    rw [parentOf_eq hfun hna hba hpa, parentOf_eq hfun hnb hbb hpb]
  have hnum := siblingNumber_ne p (posOf p L) hAid hBid hAB hpar
  have hvr : ∀ {v : Nat} {n : ProperNode}, p.nodes[v]? = some n → v < p.rank.length := by
    intro v n hv
    rw [← hn]
    exact (List.getElem?_eq_some_iff.mp hv).1
  have hlay : ∀ {v : Nat}, v < p.rank.length → lay p v < L.length := by
    intro v hv
    rw [hL.1]
    exact lay_lt_layerCount p hv
  have hmem : ∀ {v : Nat} {n : ProperNode}, p.nodes[v]? = some n →
      v ∈ L.getD (lay p v) [] := by
    intro v n hv
    exact (layer_mem hL (hlay (hvr hv))).mpr ⟨hvr hv, rfl⟩
  have hpath : ∀ {v : Nat} {n : ProperNode}, p.nodes[v]? = some n → n.node.border = -1 →
      nodePath p v = n.node.clusterPath := fun hv hbv => nodePath_of_node hv (hdum hv hbv)
  have hnd : ∀ {v : Nat}, v < p.rank.length →
      (siblingLayer p (Sibling.siblingNumber p (Sibling.siblingOrders p (posOf p L)))
        (L.getD (lay p v) [])).Nodup := by
    intro v hv
    exact (siblingLayer_perm _ _ _).nodup_iff.mpr (layer_nodup hL (hlay hv))
  have hpos : ∀ v : Nat, v < p.rank.length → posOf p (siblingNormalise p L) v =
      ((siblingLayer p (Sibling.siblingNumber p (Sibling.siblingOrders p (posOf p L)))
        (L.getD (lay p v) [])).idxOf v : Nat) := by
    intro v hv
    have hdef : posOf p (siblingNormalise p L) v =
        (((siblingNormalise p L).getD (lay p v) []).idxOf v : Nat) := rfl
    rw [hdef, siblingNormalise_getD hne (hlay hv)]
  have hava := hvr hna
  have hbvb := hvr hnb
  have hava' := hvr hna'
  have hbvb' := hvr hnb'
  rw [hpos _ hava, hpos _ hbvb] at hlt
  rw [hpos _ hava', hpos _ hbvb']
  rcases Nat.lt_or_gt_of_ne hnum with hlt2 | hgt2
  · have ha'mem : a' ∈ L.getD (lay p a') [] := hmem hna'
    have hb'mem : b' ∈ L.getD (lay p a') [] := by
      rw [hr']
      exact hmem hnb'
    have hsub := siblingLayer_pair ha'mem hb'mem ((hpath hna' hba').trans hpa')
      ((hpath hnb' hbb').trans hpb') hAB hlt2
    have hlt3 := idxOf_pair_lt (hnd hava') hsub
    rw [← hr']
    exact Int.ofNat_lt.mpr hlt3
  · exfalso
    have hamem : a ∈ L.getD (lay p a) [] := hmem hna
    have hbmem : b ∈ L.getD (lay p a) [] := by
      rw [hr]
      exact hmem hnb
    have hsub := siblingLayer_pair hbmem hamem ((hpath hnb hbb).trans hpb)
      ((hpath hna hba).trans hpa) (Ne.symm hAB) hgt2
    have hlt3 := idxOf_pair_lt (hnd hava) hsub
    rw [← hr] at hlt
    have := Int.ofNat_lt.mp hlt
    omega

end OrderImpl

theorem order_clusters_contiguous (p : Proper) (opts : OrderOptions)
    (L : List (List Nat)) (h : OrderImpl.order p opts = .ok L) :
    ∀ layer ∈ L, ∀ pref : List Nat,
      (layer.filter (fun v => pref.isPrefixOf (OrderImpl.nodePath p v))).IsInfix layer :=
  OrderImpl.order_clusters_contiguous p opts L h

theorem order_border_ends
    (p : Proper) (opts : OrderOptions) (L : List (List Nat))
    (h : OrderImpl.order p opts = .ok L)
    (hwf : OrderImpl.BordersWellFormed p) :
    ∀ layer ∈ L, ∀ (i j a b : Nat) (na nb : ProperNode),
      layer[i]? = some a →
      layer[j]? = some b →
      p.nodes[a]? = some na →
      p.nodes[b]? = some nb →
      a ≠ b →
      na.dummy = false →
      nb.dummy = false →
      na.node.clusterPath <+: nb.node.clusterPath →
      (na.node.border = -1 → i < j) ∧
      (na.node.border = 1 → j < i) :=
  OrderImpl.order_border_ends p opts L h hwf


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

theorem siblingNormalise_perm (p : Proper) (L : List (List Nat)) :
    (OrderImpl.siblingNormalise p L).length = L.length ∧
      ∀ i, ((OrderImpl.siblingNormalise p L).getD i []).Perm (L.getD i []) :=
  OrderImpl.siblingNormalise_perm p L

theorem siblingNormalise_layering {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) : OrderImpl.Layering p (OrderImpl.siblingNormalise p L) :=
  OrderImpl.siblingNormalise_layering hL

theorem siblingNormalise_contiguous {p : Proper} {L : List (List Nat)}
    (h : OrderImpl.LayersContiguous p L) :
    OrderImpl.LayersContiguous p (OrderImpl.siblingNormalise p L) :=
  OrderImpl.siblingNormalise_contiguous h

theorem order_siblings_consistent {p : Proper} {L : List (List Nat)}
    (hL : OrderImpl.Layering p L) (hn : p.nodes.length = p.rank.length)
    (hwf : OrderImpl.BordersWellFormed p) (hfun : OrderImpl.ClusterPathsFunctional p)
    {P : List Nat} {A B a b a' b' : Nat} (hAB : A ≠ B)
    (ha : OrderImpl.LeftBorderOf p a (P ++ [A])) (hb : OrderImpl.LeftBorderOf p b (P ++ [B]))
    (ha' : OrderImpl.LeftBorderOf p a' (P ++ [A]))
    (hb' : OrderImpl.LeftBorderOf p b' (P ++ [B]))
    (hr : OrderImpl.lay p a = OrderImpl.lay p b) (hr' : OrderImpl.lay p a' = OrderImpl.lay p b')
    (hlt : OrderImpl.posOf p (OrderImpl.siblingNormalise p L) a <
      OrderImpl.posOf p (OrderImpl.siblingNormalise p L) b) :
    OrderImpl.posOf p (OrderImpl.siblingNormalise p L) a' <
      OrderImpl.posOf p (OrderImpl.siblingNormalise p L) b' :=
  OrderImpl.order_siblings_consistent hL hn hwf hfun hAB ha hb ha' hb' hr hr' hlt

theorem transpose_crossings_le_of_order (p : Proper) (opts : OrderOptions)
    (L : List (List Nat)) (h : order p opts = .ok L) :
    crossCount p (transpose p L) ≤ crossCount p L := by
  obtain ⟨hV, hL⟩ := order_valid_layering p opts L h
  exact transpose_crossings_le p hV L hL

private def refCase (decls : List Nat) (ranks : List Int) (edges : List (Nat × Nat)) :
    Proper :=
  { nodes := decls.map fun d => ⟨{ decl := d, w := 0, h := 0 }, false, none⟩
    edges := edges.map fun (t, h) => { tail := t, head := h, decl := 0, original := 0 }
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
