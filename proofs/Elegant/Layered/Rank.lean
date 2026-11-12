import ElegantGeometry.Basic
import Elegant.Gen.Layoutconst
import Elegant.Layered.Cycles

set_option autoImplicit false

/-! Rank phase (spec/layout/layered.md, "Ranking") for one connected component with no
self-loops: longest-path start (`initRank`), feasible tree (`feasibleRank`), network simplex
pivots under the fuel `pivot_factor * nodes`, and normalisation to a minimum rank of 0.
`rank_feasible` and `simplex_cost_le_init` prove feasibility and that no pivot raises the cost
above the feasible tree the simplex starts from. -/

namespace Elegant
namespace Layered

def rk (r : List Int) (v : Nat) : Int := r.getD v 0

def slack (r : List Int) (e : Edge) : Int := rk r e.head - rk r e.tail - e.minLen

def cost (g : Graph) (r : List Int) : Int :=
  (g.edges.map fun e => rk r e.head - rk r e.tail).sum

def Feasible (g : Graph) (r : List Int) : Prop :=
  ∀ e ∈ g.edges, e.minLen ≤ rk r e.head - rk r e.tail

def Graph.wellformed (g : Graph) : Bool :=
  g.edges.all fun e =>
    decide (e.tail < g.nodes.length ∧ e.head < g.nodes.length ∧ 1 ≤ e.minLen)

def Graph.rankable (g : Graph) : Bool :=
  g.wellformed && g.edges.all fun e => decide (e.tail ≠ e.head)

def Graph.withoutSelfLoops (g : Graph) : Graph :=
  { g with edges := g.edges.filter fun e => decide (e.tail ≠ e.head) }

namespace RankImpl

def readyNode (g : Graph) (done : List Nat) (v : Nat) : Bool :=
  !done.contains v &&
    g.edges.all fun e => e.head != v || e.tail == e.head || done.contains e.tail

def relaxEdge (e : Edge) (r : Nat → Int) : Nat → Int :=
  fun x => if x = e.head then max (r x) (r e.tail + e.minLen) else r x

def relaxStep (v : Nat) (r : Nat → Int) (e : Edge) : Nat → Int :=
  if e.tail = v ∧ e.tail ≠ e.head then relaxEdge e r else r

def relaxOut (g : Graph) (v : Nat) (r : Nat → Int) : Nat → Int :=
  g.edges.foldl (relaxStep v) r

def longestAux (g : Graph) : Nat → List Nat → (Nat → Int) → Except LayoutError (Nat → Int)
  | 0, _, r => .ok r
  | k + 1, done, r =>
    match (List.range g.nodes.length).find? (readyNode g done) with
    | none => .error .domain
    | some v => longestAux g k (done ++ [v]) (relaxOut g v r)

def initRank (g : Graph) : Except LayoutError (List Int) :=
  match longestAux g g.nodes.length [] (fun _ => 0) with
  | .error e => .error e
  | .ok r =>
    if ((List.range g.nodes.length).map r).all (fun x => decide (x ≤ I32_MAX)) then
      .ok ((List.range g.nodes.length).map r)
    else .error .overflow

def inS (side : List Bool) (v : Nat) : Bool := side.getD v false

def crossing (side : List Bool) (e : Edge) : Bool := inS side e.tail != inS side e.head

def entering (side : List Bool) (e : Edge) : Bool := inS side e.tail && !inS side e.head

def incident (g : Graph) (v : Nat) : List Nat :=
  g.edges.zipIdx.filterMap fun p => if p.1.tail = v ∨ p.1.head = v then some p.2 else none

def tightAt (g : Graph) (r : List Int) (side : List Bool) (i : Nat) : Bool :=
  match g.edges[i]? with
  | some e => crossing side e && slack r e == 0
  | none => false

def firstTight (g : Graph) (r : List Int) (side : List Bool) : Option Nat :=
  (List.range g.nodes.length).findSome? fun v =>
    if inS side v then (incident g v).find? (tightAt g r side) else none

def msStep (c : Edge → Bool) (r : List Int) (acc : Option (Nat × Int)) (p : Edge × Nat) :
    Option (Nat × Int) :=
  if c p.1 then
    match acc with
    | none => some (p.2, slack r p.1)
    | some (_, gap) => if slack r p.1 < gap then some (p.2, slack r p.1) else acc
  else acc

def minSlack (c : Edge → Bool) (r : List Int) (l : List (Edge × Nat)) : Option (Nat × Int) :=
  l.foldl (msStep c r) none

def closestDelta (g : Graph) (r : List Int) (side : List Bool) : Option Int :=
  match minSlack (crossing side) r g.edges.zipIdx with
  | none => none
  | some (j, s) =>
    match g.edges[j]? with
    | some e => some (if inS side e.head then -s else s)
    | none => none

def shiftBy (side : List Bool) (δ : Int) (r : List Int) : List Int :=
  r.mapIdx fun i x => if inS side i then x + δ else x

structure TT where
  side : List Bool
  tree : List Bool
  r : List Int

def TT.extend (g : Graph) (st : TT) (i : Nat) : Except LayoutError TT :=
  match g.edges[i]? with
  | some e =>
    .ok { st with
      tree := st.tree.set i true
      side := (st.side.set e.tail true).set e.head true }
  | none => .error .domain

def growStep (g : Graph) (st : TT) : Except LayoutError TT :=
  match firstTight g st.r st.side with
  | some i => st.extend g i
  | none =>
    match closestDelta g st.r st.side with
    | none => .error .domain
    | some δ =>
      match firstTight g (shiftBy st.side δ st.r) st.side with
      | some i => TT.extend g { st with r := shiftBy st.side δ st.r } i
      | none => .error .domain

def grow (g : Graph) : Nat → TT → Except LayoutError TT
  | 0, st => .ok st
  | k + 1, st =>
    match growStep g st with
    | .error e => .error e
    | .ok st' => grow g k st'

def tightTree (g : Graph) (r : List Int) : Except LayoutError TT :=
  if g.nodes.length = 0 then
    .ok { side := [], tree := List.replicate g.edges.length false, r := r }
  else
    grow g (g.nodes.length - 1)
      { side := (List.replicate g.nodes.length false).set 0 true
        tree := List.replicate g.edges.length false
        r := r }

def cutContrib (side : List Bool) (e : Edge) : Int :=
  if inS side e.tail == inS side e.head then 0 else if inS side e.head then 1 else -1

def cutValue (g : Graph) (side : List Bool) : Int := (g.edges.map (cutContrib side)).sum

def treeSideStep (g : Graph) (tree : List Bool) (removed : Nat) (side : List Bool) : List Bool :=
  g.edges.zipIdx.foldl
    (fun s p =>
      if p.2 = removed ∨ !(tree.getD p.2 false) then s
      else if inS s p.1.tail || inS s p.1.head then (s.set p.1.tail true).set p.1.head true
      else s)
    side

def treeSide (g : Graph) (tree : List Bool) (removed : Nat) : List Bool :=
  match g.edges[removed]? with
  | none => List.replicate g.nodes.length false
  | some e =>
    (List.range g.nodes.length).foldl (fun s _ => treeSideStep g tree removed s)
      ((List.replicate g.nodes.length false).set e.head true)

def leavingEdge (g : Graph) (tree : List Bool) : Option (Nat × List Bool) :=
  tree.zipIdx.findSome? fun p =>
    if p.1 then
      if cutValue g (treeSide g tree p.2) < 0 then some (p.2, treeSide g tree p.2) else none
    else none

def simplex (g : Graph) : Nat → List Bool → List Int → Except LayoutError (List Int × Bool)
  | 0, _, r => .ok (r, true)
  | fuel + 1, tree, r =>
    match leavingEdge g tree with
    | none => .ok (r, false)
    | some (leave, side) =>
      match minSlack (entering side) r g.edges.zipIdx with
      | none => .error .domain
      | some (enter, delta) =>
        simplex g fuel ((tree.set leave false).set enter true) (shiftBy side delta r)

opaque pivotFactor : Option Nat :=
  match layoutconst.find? (fun c => c.name == "vector.pivot_factor") with
  | some c => if 0 < c.value then some c.value.toNat else none
  | none => none

def startRanks (g : Graph) : Except LayoutError TT :=
  if g.rankable = true then
    match initRank g with
    | .error e => .error e
    | .ok r => tightTree g r
  else .error .domain

def feasibleRank (g : Graph) : List Int :=
  match startRanks g with
  | .ok st => st.r
  | .error _ => []

def minRank : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def normalizedRanks (r : List Int) : Except LayoutError (List Int) :=
  if (r.map (· - minRank r)).all (fun v => decide (v ≤ I32_MAX)) then
    .ok (r.map (· - minRank r))
  else .error .overflow

structure RankResult where
  ranks : List Int
  budgetExhausted : Bool
deriving Repr

def rankWithBudget (g : Graph) : Except LayoutError RankResult :=
  match startRanks g with
  | .error e => .error e
  | .ok st =>
    match pivotFactor with
    | none => .error .domain
    | some factor =>
      match simplex g (factor * g.nodes.length) st.tree st.r with
      | .error e => .error e
      | .ok (r, exhausted) =>
        match normalizedRanks r with
        | .error e => .error e
        | .ok out =>
          .ok { ranks := out, budgetExhausted := exhausted && decide (0 < g.nodes.length) }

def rank (g : Graph) : Except LayoutError (List Int) :=
  match rankWithBudget g with
  | .ok res => .ok res.ranks
  | .error e => .error e

theorem rk_of_lt {r : List Int} {v : Nat} (h : v < r.length) : rk r v = r[v] := by
  simp [rk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem shiftBy_length (side : List Bool) (δ : Int) (r : List Int) :
    (shiftBy side δ r).length = r.length := by
  simp [shiftBy]

theorem shiftBy_rk (side : List Bool) (δ : Int) (r : List Int) {v : Nat} (h : v < r.length) :
    rk (shiftBy side δ r) v = rk r v + (if inS side v then δ else 0) := by
  have h' : v < (shiftBy side δ r).length := by rw [shiftBy_length]; exact h
  rw [rk_of_lt h', rk_of_lt h]
  simp only [shiftBy, List.getElem_mapIdx]
  cases inS side v <;> simp

theorem map_sub_rk (r : List Int) (lo : Int) {v : Nat} (h : v < r.length) :
    rk (r.map (· - lo)) v = rk r v - lo := by
  have h' : v < (r.map (· - lo)).length := by simpa using h
  rw [rk_of_lt h', rk_of_lt h]
  simp

theorem slack_nonneg {g : Graph} {r : List Int} (hf : Feasible g r) {e : Edge} (he : e ∈ g.edges) :
    0 ≤ slack r e := by
  have := hf e he
  unfold slack
  omega

theorem msStep_fold (c : Edge → Bool) (r : List Int) (l : List (Edge × Nat))
    (acc : Option (Nat × Int)) (seen : List (Edge × Nat))
    (hacc : ∀ x, acc = some x →
      (∃ e, (e, x.1) ∈ seen ∧ c e = true ∧ x.2 = slack r e) ∧
      ∀ p ∈ seen, c p.1 = true → x.2 ≤ slack r p.1)
    (hnone : acc = none → ∀ p ∈ seen, c p.1 = false) :
    (∀ x, l.foldl (msStep c r) acc = some x →
      (∃ e, (e, x.1) ∈ seen ++ l ∧ c e = true ∧ x.2 = slack r e) ∧
      ∀ p ∈ seen ++ l, c p.1 = true → x.2 ≤ slack r p.1) ∧
    (l.foldl (msStep c r) acc = none → ∀ p ∈ seen ++ l, c p.1 = false) := by
  induction l generalizing acc seen with
  | nil => simpa using And.intro hacc hnone
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hstep := ih (msStep c r acc p) (seen ++ [p]) ?_ ?_
    · simpa [List.append_assoc] using hstep
    · intro x hx
      unfold msStep at hx
      by_cases hc : c p.1 = true
      · simp only [hc, ↓reduceIte] at hx
        cases hacc' : acc with
        | none =>
          rw [hacc'] at hx
          simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨⟨p.1, by simp, hc, rfl⟩, ?_⟩
          intro q hq hcq
          rcases List.mem_append.mp hq with hq | hq
          · have := hnone hacc' q hq
            rw [this] at hcq
            exact absurd hcq (by simp)
          · simp at hq; subst hq; exact Int.le_refl _
        | some y =>
          rw [hacc'] at hx
          obtain ⟨y1, y2⟩ := y
          simp only at hx
          obtain ⟨⟨e0, he0, hce0, hs0⟩, hmin⟩ := hacc _ hacc'
          by_cases hlt : slack r p.1 < y2
          · simp only [hlt, ↓reduceIte, Option.some.injEq] at hx
            subst hx
            refine ⟨⟨p.1, by simp, hc, rfl⟩, ?_⟩
            intro q hq hcq
            rcases List.mem_append.mp hq with hq | hq
            · have := hmin q hq hcq
              simp only at this
              omega
            · simp at hq; subst hq; exact Int.le_refl _
          · simp only [hlt, ↓reduceIte, Option.some.injEq] at hx
            subst hx
            refine ⟨⟨e0, by simpa using Or.inl he0, hce0, hs0⟩, ?_⟩
            intro q hq hcq
            rcases List.mem_append.mp hq with hq | hq
            · exact hmin q hq hcq
            · simp at hq; subst hq
              simp only
              omega
      · have hc' : c p.1 = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte] at hx
        obtain ⟨⟨e0, he0, hce0, hs0⟩, hmin⟩ := hacc x hx
        refine ⟨⟨e0, by simpa using Or.inl he0, hce0, hs0⟩, ?_⟩
        intro q hq hcq
        rcases List.mem_append.mp hq with hq | hq
        · exact hmin q hq hcq
        · simp at hq; subst hq
          rw [hc'] at hcq
          exact absurd hcq (by simp)
    · intro hn q hq
      unfold msStep at hn
      by_cases hc : c p.1 = true
      · simp only [hc, ↓reduceIte] at hn
        cases hacc' : acc with
        | none => rw [hacc'] at hn; simp at hn
        | some y =>
          rw [hacc'] at hn
          obtain ⟨y1, y2⟩ := y
          simp only at hn
          by_cases hlt : slack r p.1 < y2
          · simp [hlt] at hn
          · simp [hlt] at hn
      · have hc' : c p.1 = false := by simpa using hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte] at hn
        rcases List.mem_append.mp hq with hq | hq
        · exact hnone hn q hq
        · simp at hq; subst hq; exact hc'

theorem minSlack_spec (c : Edge → Bool) (r : List Int) (l : List (Edge × Nat)) {j : Nat} {s : Int}
    (h : minSlack c r l = some (j, s)) :
    (∃ e, (e, j) ∈ l ∧ c e = true ∧ s = slack r e) ∧
    ∀ p ∈ l, c p.1 = true → s ≤ slack r p.1 := by
  have := (msStep_fold c r l none [] (by simp) (by simp)).1 (j, s) h
  simpa using this

theorem mem_zipIdx_of_mem {l : List Edge} {e : Edge} (h : e ∈ l) : ∃ i, (e, i) ∈ l.zipIdx := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  exact ⟨i, List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi, he])⟩

theorem mem_of_mem_zipIdx {l : List Edge} {e : Edge} {i : Nat} (h : (e, i) ∈ l.zipIdx) :
    e ∈ l :=
  List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp h)

theorem closestDelta_spec {g : Graph} {r : List Int} (hf : Feasible g r) (side : List Bool)
    {δ : Int} (h : closestDelta g r side = some δ) :
    ∃ s, 0 ≤ s ∧ (δ = s ∨ δ = -s) ∧ ∀ e ∈ g.edges, crossing side e = true → s ≤ slack r e := by
  unfold closestDelta at h
  split at h
  · simp at h
  next j s hms =>
    split at h
    next e he =>
      simp only [Option.some.injEq] at h
      obtain ⟨⟨e0, he0, hce0, hs0⟩, hmin⟩ := minSlack_spec _ _ _ hms
      have he0g : e0 ∈ g.edges := mem_of_mem_zipIdx he0
      refine ⟨s, by rw [hs0]; exact slack_nonneg hf he0g, ?_, ?_⟩
      · rw [← h]
        cases inS side e.head <;> simp
      · intro e' he' hc'
        obtain ⟨i, hi⟩ := mem_zipIdx_of_mem he'
        exact hmin (e', i) hi hc'
    · simp at h

theorem shiftBy_feasible {g : Graph} {r : List Int} (hf : Feasible g r)
    (hlen : ∀ e ∈ g.edges, e.tail < r.length ∧ e.head < r.length) (side : List Bool) (δ : Int)
    (h1 : ∀ e ∈ g.edges, inS side e.tail = true → inS side e.head = false → δ ≤ slack r e)
    (h2 : ∀ e ∈ g.edges, inS side e.tail = false → inS side e.head = true → -δ ≤ slack r e) :
    Feasible g (shiftBy side δ r) := by
  intro e he
  obtain ⟨ht, hh⟩ := hlen e he
  rw [shiftBy_rk side δ r ht, shiftBy_rk side δ r hh]
  have hfe := hf e he
  cases hts : inS side e.tail <;> cases hhs : inS side e.head <;> simp
  · omega
  · have := h2 e he hts hhs
    unfold slack at this
    omega
  · have := h1 e he hts hhs
    unfold slack at this
    omega
  · omega

theorem sum_shift (l : List Edge) (side : List Bool) (δ : Int) (r : List Int)
    (hlen : ∀ e ∈ l, e.tail < r.length ∧ e.head < r.length) :
    (l.map fun e => rk (shiftBy side δ r) e.head - rk (shiftBy side δ r) e.tail).sum =
      (l.map fun e => rk r e.head - rk r e.tail).sum + δ * (l.map (cutContrib side)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := hlen x (by simp)
    have ih' := ih (fun e he => hlen e (by simp [he]))
    simp only [List.map_cons, List.sum_cons]
    rw [ih', shiftBy_rk side δ r hx.1, shiftBy_rk side δ r hx.2]
    unfold cutContrib
    cases hts : inS side x.tail <;> cases hhs : inS side x.head <;> simp [Int.mul_add] <;> omega

theorem cost_shift (g : Graph) (side : List Bool) (δ : Int) (r : List Int)
    (hlen : ∀ e ∈ g.edges, e.tail < r.length ∧ e.head < r.length) :
    cost g (shiftBy side δ r) = cost g r + δ * cutValue g side :=
  sum_shift g.edges side δ r hlen

theorem leavingEdge_spec {g : Graph} {tree : List Bool} {i : Nat} {side : List Bool}
    (h : leavingEdge g tree = some (i, side)) : cutValue g side < 0 := by
  unfold leavingEdge at h
  obtain ⟨l₁, a, l₂, _, hf, _⟩ := List.findSome?_eq_some_iff.mp h
  by_cases ha : a.1 = true
  · by_cases hc : cutValue g (treeSide g tree a.2) < 0
    · simp only [ha, hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨_, rfl⟩ := hf
      exact hc
    · simp [ha, hc] at hf
  · simp [ha] at hf

def GInv (g : Graph) (r : List Int) : Prop := r.length = g.nodes.length ∧ Feasible g r

theorem wellformed_spec {g : Graph} (h : g.wellformed = true) :
    ∀ e ∈ g.edges, e.tail < g.nodes.length ∧ e.head < g.nodes.length ∧ 1 ≤ e.minLen := by
  intro e he
  have := List.all_eq_true.mp h e he
  simpa using this

theorem simplex_inv (g : Graph) (hwf : g.wellformed = true) :
    ∀ fuel tree r r' cap, simplex g fuel tree r = .ok (r', cap) → GInv g r →
      GInv g r' ∧ cost g r' ≤ cost g r := by
  intro fuel
  induction fuel with
  | zero =>
    intro tree r r' cap h hg
    simp only [simplex, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨hg, Int.le_refl _⟩
  | succ fuel ih =>
    intro tree r r' cap h hg
    unfold simplex at h
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact ⟨hg, Int.le_refl _⟩
    next leave side hle =>
      split at h
      · simp at h
      next enter delta hms =>
        have hcut := leavingEdge_spec hle
        obtain ⟨⟨e0, he0, hce0, hs0⟩, hmin⟩ := minSlack_spec _ _ _ hms
        have he0g : e0 ∈ g.edges := mem_of_mem_zipIdx he0
        have hdelta : 0 ≤ delta := by rw [hs0]; exact slack_nonneg hg.2 he0g
        have hlen : ∀ e ∈ g.edges, e.tail < r.length ∧ e.head < r.length := by
          intro e he
          have := wellformed_spec hwf e he
          rw [hg.1]
          exact ⟨this.1, this.2.1⟩
        have hfeas : Feasible g (shiftBy side delta r) := by
          apply shiftBy_feasible hg.2 hlen
          · intro e he ht hh
            obtain ⟨i, hi⟩ := mem_zipIdx_of_mem he
            exact hmin (e, i) hi (by simp [entering, ht, hh])
          · intro e he ht hh
            have := slack_nonneg hg.2 he
            omega
        have hg' : GInv g (shiftBy side delta r) := ⟨by rw [shiftBy_length]; exact hg.1, hfeas⟩
        obtain ⟨hg'', hc''⟩ := ih _ _ r' cap h hg'
        refine ⟨hg'', ?_⟩
        have hshift := cost_shift g side delta r hlen
        have : delta * cutValue g side ≤ 0 :=
          Int.mul_nonpos_of_nonneg_of_nonpos hdelta (Int.le_of_lt hcut)
        omega

theorem extend_r {g : Graph} {st st' : TT} {i : Nat} (h : st.extend g i = .ok st') :
    st'.r = st.r := by
  unfold TT.extend at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    rfl
  · simp at h

theorem growStep_inv {g : Graph} (hwf : g.wellformed = true) {st st' : TT}
    (h : growStep g st = .ok st') (hg : GInv g st.r) : GInv g st'.r := by
  unfold growStep at h
  split at h
  · next i hi =>
    rw [extend_r h]
    exact hg
  · split at h
    · simp at h
    · next δ hδ =>
      have hlen : ∀ e ∈ g.edges, e.tail < st.r.length ∧ e.head < st.r.length := by
        intro e he
        have := wellformed_spec hwf e he
        rw [hg.1]
        exact ⟨this.1, this.2.1⟩
      obtain ⟨s, hs0, hδ', hmin⟩ := closestDelta_spec hg.2 st.side hδ
      have hfeas : Feasible g (shiftBy st.side δ st.r) := by
        apply shiftBy_feasible hg.2 hlen
        · intro e he ht hh
          have := hmin e he (by simp [crossing, ht, hh])
          omega
        · intro e he ht hh
          have := hmin e he (by simp [crossing, ht, hh])
          omega
      split at h
      · next i hi =>
        have := extend_r h
        simp only at this
        rw [this]
        exact ⟨by rw [shiftBy_length]; exact hg.1, hfeas⟩
      · simp at h

theorem grow_inv {g : Graph} (hwf : g.wellformed = true) :
    ∀ k (st st' : TT), grow g k st = .ok st' → GInv g st.r → GInv g st'.r := by
  intro k
  induction k with
  | zero =>
    intro st st' h hg
    simp only [grow, Except.ok.injEq] at h
    subst h
    exact hg
  | succ k ih =>
    intro st st' h hg
    unfold grow at h
    split at h
    · simp at h
    · next st1 h1 =>
      exact ih st1 st' h (growStep_inv hwf h1 hg)

theorem tightTree_inv {g : Graph} (hwf : g.wellformed = true) {r : List Int} {st : TT}
    (h : tightTree g r = .ok st) (hg : GInv g r) : GInv g st.r := by
  unfold tightTree at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact hg
  · exact grow_inv hwf _ _ _ h hg

theorem relaxStep_mono (v : Nat) (r : Nat → Int) (e : Edge) (x : Nat) :
    r x ≤ relaxStep v r e x := by
  unfold relaxStep
  split
  · unfold relaxEdge
    split
    · exact Int.le_max_left _ _
    · exact Int.le_refl _
  · exact Int.le_refl _

theorem relaxFold_mono (v : Nat) (l : List Edge) :
    ∀ (r : Nat → Int) (x : Nat), r x ≤ l.foldl (relaxStep v) r x := by
  induction l with
  | nil => intro r x; exact Int.le_refl _
  | cons f fs ih =>
    intro r x
    simp only [List.foldl_cons]
    exact Int.le_trans (relaxStep_mono v r f x) (ih _ x)

theorem relaxStep_frame (v : Nat) (r : Nat → Int) (e : Edge) (x : Nat)
    (h : ¬(e.tail = v ∧ e.tail ≠ e.head ∧ e.head = x)) : relaxStep v r e x = r x := by
  unfold relaxStep
  split
  · next hc =>
    unfold relaxEdge
    split
    · next hx => exact absurd ⟨hc.1, hc.2, hx.symm⟩ h
    · rfl
  · rfl

theorem relaxFold_frame (v : Nat) (x : Nat) (l : List Edge) :
    ∀ (r : Nat → Int), (∀ e ∈ l, ¬(e.tail = v ∧ e.tail ≠ e.head ∧ e.head = x)) →
      l.foldl (relaxStep v) r x = r x := by
  induction l with
  | nil => intro r _; rfl
  | cons f fs ih =>
    intro r h
    simp only [List.foldl_cons]
    rw [ih _ (fun e he => h e (by simp [he])), relaxStep_frame v r f x (h f (by simp))]

theorem relaxFold_edge (v : Nat) (l : List Edge) :
    ∀ (r : Nat → Int) (e : Edge), e ∈ l → e.tail = v → e.tail ≠ e.head →
      r v + e.minLen ≤ l.foldl (relaxStep v) r e.head := by
  induction l with
  | nil => intro r e he; simp at he
  | cons f fs ih =>
    intro r e he ht hne
    simp only [List.foldl_cons]
    have hv : relaxStep v r f v = r v := by
      apply relaxStep_frame
      intro h
      exact h.2.1 (h.1.trans h.2.2.symm)
    rcases List.mem_cons.mp he with rfl | he
    · have hne' : v ≠ e.head := ht ▸ hne
      have h1 : r v + e.minLen ≤ relaxStep v r e e.head := by
        have : relaxStep v r e e.head = max (r e.head) (r v + e.minLen) := by
          simp [relaxStep, relaxEdge, ht, hne']
        rw [this]
        exact Int.le_max_right _ _
      exact Int.le_trans h1 (relaxFold_mono v fs _ e.head)
    · have := ih (relaxStep v r f) e he ht hne
      rw [hv] at this
      exact this

structure LongInv (g : Graph) (done : List Nat) (r : Nat → Int) : Prop where
  nodup : done.Nodup
  bound : ∀ x ∈ done, x < g.nodes.length
  closed : ∀ e ∈ g.edges, e.tail ≠ e.head → e.head ∈ done → e.tail ∈ done
  relaxed : ∀ e ∈ g.edges, e.tail ≠ e.head → e.tail ∈ done → r e.tail + e.minLen ≤ r e.head

theorem longInv_step {g : Graph} {done : List Nat} {r : Nat → Int} {v : Nat}
    (hI : LongInv g done r) (hv : v < g.nodes.length) (hnot : v ∉ done)
    (hready : ∀ e ∈ g.edges, e.head = v → e.tail ≠ e.head → e.tail ∈ done) :
    LongInv g (done ++ [v]) (relaxOut g v r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hI.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    simp at hb
    subst hb
    exact hnot (hab ▸ ha)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hI.bound x hx
    · simp at hx; subst hx; exact hv
  · intro e he hne hh
    rcases List.mem_append.mp hh with hh | hh
    · exact List.mem_append_left _ (hI.closed e he hne hh)
    · simp at hh
      exact List.mem_append_left _ (hready e he hh hne)
  · intro e he hne ht
    unfold relaxOut
    rcases List.mem_append.mp ht with ht | ht
    · have hframe : g.edges.foldl (relaxStep v) r e.tail = r e.tail := by
        apply relaxFold_frame
        intro f hf hcon
        have := hI.closed f hf hcon.2.1 (hcon.2.2 ▸ ht)
        exact hnot (hcon.1 ▸ this)
      rw [hframe]
      exact Int.le_trans (hI.relaxed e he hne ht) (relaxFold_mono v g.edges r e.head)
    · simp at ht
      have hframe : g.edges.foldl (relaxStep v) r e.tail = r e.tail := by
        apply relaxFold_frame
        intro f hf hcon
        exact hcon.2.1 (hcon.1.trans (ht ▸ hcon.2.2).symm)
      rw [hframe]
      have := relaxFold_edge v g.edges r e he ht hne
      rw [ht]
      exact this

theorem readyNode_spec {g : Graph} {done : List Nat} {v : Nat} (h : readyNode g done v = true) :
    v ∉ done ∧ ∀ e ∈ g.edges, e.head = v → e.tail ≠ e.head → e.tail ∈ done := by
  unfold readyNode at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  refine ⟨?_, ?_⟩
  · intro hm
    have := h.1
    simp at this
    exact this hm
  · intro e he hh hne
    have := h.2 e he
    rcases this with (h1 | h1) | h1
    · exact absurd hh h1
    · exact absurd h1 hne
    · simpa using h1

theorem all_mem_of_length {n : Nat} {done : List Nat} (hnd : done.Nodup) (hb : ∀ x ∈ done, x < n)
    (hl : done.length = n) : ∀ x, x < n → x ∈ done := by
  intro x hx
  by_cases hm : x ∈ done
  · exact hm
  · exfalso
    have hnd' : (x :: done).Nodup := List.nodup_cons.mpr ⟨hm, hnd⟩
    have hsub : (x :: done) ⊆ List.range n := by
      intro y hy
      rw [List.mem_range]
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hb y hy
    have := hnd'.length_le_of_subset hsub
    simp at this
    omega

theorem longestAux_inv (g : Graph) (hwf : g.wellformed = true) :
    ∀ k (done : List Nat) (r r' : Nat → Int), k + done.length = g.nodes.length →
      LongInv g done r → longestAux g k done r = .ok r' →
      ∀ e ∈ g.edges, e.tail ≠ e.head → r' e.tail + e.minLen ≤ r' e.head := by
  intro k
  induction k with
  | zero =>
    intro done r r' hk hI h
    simp only [longestAux, Except.ok.injEq] at h
    subst h
    intro e he hne
    have hall := all_mem_of_length hI.nodup hI.bound (by omega)
    exact hI.relaxed e he hne (hall e.tail (wellformed_spec hwf e he).1)
  | succ k ih =>
    intro done r r' hk hI h
    unfold longestAux at h
    split at h
    · simp at h
    · next v hv =>
      have hready := readyNode_spec (List.find?_some hv)
      have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hv)
      have hstep := longInv_step hI hmem hready.1 hready.2
      exact ih (done ++ [v]) _ r' (by simp; omega) hstep h

theorem rankable_spec {g : Graph} (h : g.rankable = true) :
    g.wellformed = true ∧ ∀ e ∈ g.edges, e.tail ≠ e.head := by
  unfold Graph.rankable at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

theorem rk_range_map (n : Nat) (r : Nat → Int) {v : Nat} (h : v < n) :
    rk ((List.range n).map r) v = r v := by
  have h' : v < ((List.range n).map r).length := by simpa using h
  rw [rk_of_lt h']
  simp

theorem initRank_inv {g : Graph} (hr : g.rankable = true) {out : List Int}
    (h : initRank g = .ok out) : GInv g out := by
  obtain ⟨hwf, hloop⟩ := rankable_spec hr
  unfold initRank at h
  split at h
  · simp at h
  · next r hr' =>
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨by simp, ?_⟩
      intro e he
      have hbd := wellformed_spec hwf e he
      rw [rk_range_map _ r hbd.2.1, rk_range_map _ r hbd.1]
      have hI : LongInv g [] (fun _ => 0) :=
        ⟨List.nodup_nil, by simp, by simp, by simp⟩
      have := longestAux_inv g hwf g.nodes.length [] (fun _ => 0) r (by simp) hI hr' e he
        (hloop e he)
      omega
    · simp at h

theorem startRanks_inv {g : Graph} {st : TT} (h : startRanks g = .ok st) :
    g.rankable = true ∧ GInv g st.r := by
  unfold startRanks at h
  split at h
  · next hr =>
    split at h
    · simp at h
    · next r hr' =>
      exact ⟨hr, tightTree_inv (rankable_spec hr).1 h (initRank_inv hr hr')⟩
  · simp at h

theorem mapSub_inv {g : Graph} (hwf : g.wellformed = true) {r : List Int} (hg : GInv g r)
    (lo : Int) : GInv g (r.map (· - lo)) ∧ cost g (r.map (· - lo)) = cost g r := by
  have hlen : ∀ e ∈ g.edges, e.tail < r.length ∧ e.head < r.length := by
    intro e he
    have := wellformed_spec hwf e he
    rw [hg.1]
    exact ⟨this.1, this.2.1⟩
  have hdiff : ∀ e ∈ g.edges, rk (r.map (· - lo)) e.head - rk (r.map (· - lo)) e.tail =
      rk r e.head - rk r e.tail := by
    intro e he
    obtain ⟨ht, hh⟩ := hlen e he
    rw [map_sub_rk r lo ht, map_sub_rk r lo hh]
    omega
  refine ⟨⟨by simp [hg.1], ?_⟩, ?_⟩
  · intro e he
    rw [hdiff e he]
    exact hg.2 e he
  · unfold cost
    exact congrArg List.sum (List.map_congr_left hdiff)

theorem normalizedRanks_inv {g : Graph} (hwf : g.wellformed = true) {r r' : List Int}
    (h : normalizedRanks r = .ok r') (hg : GInv g r) : GInv g r' ∧ cost g r' = cost g r := by
  unfold normalizedRanks at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact mapSub_inv hwf hg _
  · simp at h

theorem rank_spec {g : Graph} {r : List Int} (h : rank g = .ok r) :
    ∃ st, startRanks g = .ok st ∧ GInv g r ∧ cost g r ≤ cost g st.r := by
  unfold rank at h
  split at h
  · next res hres =>
    simp only [Except.ok.injEq] at h
    subst h
    unfold rankWithBudget at hres
    split at hres
    · simp at hres
    · next st hst =>
      split at hres
      · simp at hres
      · next factor hf =>
        split at hres
        · simp at hres
        · next r2 ex hsim =>
          split at hres
          · simp at hres
          · next out hout =>
            simp only [Except.ok.injEq] at hres
            subst hres
            obtain ⟨hrk, hg0⟩ := startRanks_inv hst
            have hwf := (rankable_spec hrk).1
            obtain ⟨hg1, hc1⟩ := simplex_inv g hwf _ _ _ _ _ hsim hg0
            obtain ⟨hg2, hc2⟩ := normalizedRanks_inv hwf hout hg1
            have hcost : cost g out ≤ cost g st.r := by omega
            exact ⟨st, hst, hg2, hcost⟩
  · simp at h

theorem rank_feasible (g : Graph) (r : List Int) (h : rank g = .ok r) :
    ∀ e ∈ g.edges, e.minLen ≤ rk r e.head - rk r e.tail := by
  obtain ⟨_, _, hg, _⟩ := rank_spec h
  exact hg.2

theorem simplex_cost_le_init (g : Graph) (r : List Int) (h : rank g = .ok r) :
    cost g r ≤ cost g (feasibleRank g) := by
  obtain ⟨st, hst, _, hc⟩ := rank_spec h
  unfold feasibleRank
  rw [hst]
  exact hc

end RankImpl

export RankImpl (RankResult initRank feasibleRank rankWithBudget rank)

theorem rank_feasible (g : Graph) (r : List Int) (h : rank g = .ok r) :
    ∀ e ∈ g.edges, e.minLen ≤ rk r e.head - rk r e.tail :=
  RankImpl.rank_feasible g r h

theorem simplex_cost_le_init (g : Graph) (r : List Int) (h : rank g = .ok r) :
    cost g r ≤ cost g (feasibleRank g) :=
  RankImpl.simplex_cost_le_init g r h

end Layered
end Elegant
