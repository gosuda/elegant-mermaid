import Elegant.Layered.VisibilityClearance

set_option autoImplicit false

namespace Elegant.Layered.Visibility

local instance : LawfulBEq Cost where
  rfl := by deriving_ReflEq_tactic
  eq_of_beq := by deriving_LawfulEq_tactic

def DistancesNonnegative (s : Search) : Prop :=
  ∀ (v : Vertex) (cost : Cost), s.dist[v]? = some cost → 0 ≤ cost.dist

private theorem lookup_insert_nonnegative {s : Search} {key : Vertex} {candidate : Cost}
    (hs : DistancesNonnegative s) (hc : 0 ≤ candidate.dist)
    (v : Vertex) (cost : Cost) (h : (s.dist.insert key candidate)[v]? = some cost) :
    0 ≤ cost.dist := by
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · exact (Option.some.inj h) ▸ hc
  · exact hs v cost h

theorem Grid.seed_distances_nonnegative {g : Grid} {starts : List Point} {s : Search}
    (hseed : g.seed starts = some s) : DistancesNonnegative s := by
  let seedStep (acc : Search) (p : Point) : Option Search :=
    if !g.inside p then some acc
    else (g.vertexAt p).map fun v =>
      { acc with frontier := acc.frontier.push ⟨⟨0, 0⟩, v⟩,
                 dist := acc.dist.insert v ⟨0, 0⟩ }
  change starts.foldlM seedStep ⟨#[], {}, {}⟩ = some s at hseed
  suffices fold_nonnegative : ∀ (pending : List Point) (acc out : Search),
      DistancesNonnegative acc → pending.foldlM seedStep acc = some out →
      DistancesNonnegative out by
    refine fold_nonnegative starts ⟨#[], {}, {}⟩ s ?_ hseed
    intro v cost h
    change (∅ : Std.HashMap Vertex Cost)[v]? = some cost at h
    simp at h
  intro pending
  induction pending with
  | nil =>
      intro acc out ha h
      change some acc = some out at h
      rw [← Option.some.inj h]
      exact ha
  | cons p pending ih =>
      intro acc out ha h
      rw [List.foldlM_cons] at h
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
      refine ih next out ?_ hrest
      dsimp only [seedStep] at hstep
      split at hstep
      · rw [← Option.some.inj hstep]
        exact ha
      · obtain ⟨v, _, hout⟩ := Option.map_eq_some_iff.mp hstep
        rw [← hout]
        exact lookup_insert_nonnegative (key := v) (candidate := ⟨0, 0⟩) ha (by decide)

theorem Grid.relax_distances_nonnegative {g : Grid} {entry : Entry} {s : Search}
    (hs : DistancesNonnegative s) (hentry : s.dist[entry.vertex]? = some entry.cost) :
    DistancesNonnegative (g.relax entry s) := by
  have hcost := hs entry.vertex entry.cost hentry
  have step_nonnegative (acc : Search) (next : Vertex) (ha : DistancesNonnegative acc) :
      DistancesNonnegative (relaxStep g entry acc next) := by
    have hcandidate : 0 ≤ (g.step entry.vertex next entry.cost).dist := by
      change 0 ≤ entry.cost.dist + (((g.point entry.vertex).x - (g.point next).x).natAbs : Int) +
        (((g.point entry.vertex).y - (g.point next).y).natAbs : Int)
      omega
    have hinsert : DistancesNonnegative
        { frontier := acc.frontier.push ⟨g.step entry.vertex next entry.cost, next⟩
          dist := acc.dist.insert next (g.step entry.vertex next entry.cost)
          prev := acc.prev.insert next entry.vertex } :=
      lookup_insert_nonnegative (key := next) ha hcandidate
    unfold relaxStep
    split
    · exact ha
    · dsimp only
      cases hdist : acc.dist[next]? with
      | none => exact hinsert
      | some old =>
          by_cases hbetter : (g.step entry.vertex next entry.cost).lt old = true
          · simpa only [ite_eq_left hbetter] using hinsert
          · simpa only [ite_eq_right hbetter] using ha
  change DistancesNonnegative ((g.neighbours entry.vertex).foldl (relaxStep g entry) s)
  suffices fold_nonnegative : ∀ (pending : List Vertex) (acc : Search),
      DistancesNonnegative acc →
      DistancesNonnegative (pending.foldl (relaxStep g entry) acc) by
    exact fold_nonnegative _ s hs
  intro pending
  induction pending with
  | nil =>
      intro acc ha
      exact ha
  | cons next pending ih =>
      intro acc ha
      exact ih (relaxStep g entry acc next) (step_nonnegative acc next ha)

theorem Grid.run_distances {g : Grid} {ends : List Point} {fuel : Nat}
    {s out : Search} {last : Vertex} (hrun : g.run ends fuel s = some (last, out)) :
    (DistancesNonnegative s → DistancesNonnegative out) ∧
      (∃ cost : Cost, out.dist[last]? = some cost) := by
  induction fuel generalizing s with
  | zero => simp [Grid.run] at hrun
  | succ fuel ih =>
      unfold Grid.run at hrun
      split at hrun
      · simp at hrun
      · rename_i entry rest _
        dsimp only at hrun
        split at hrun
        · exact @ih { s with frontier := rest } hrun
        · rename_i current hdist
          split at hrun
          · exact @ih { s with frontier := rest } hrun
          · rename_i hmatching
            split at hrun
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              rw [← hrun.1, ← hrun.2]
              exact ⟨fun hs => hs, ⟨current, hdist⟩⟩
            · have hcost : current = entry.cost :=
                bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hmatching)
              have hentry : ({ s with frontier := rest } : Search).dist[entry.vertex]? =
                  some entry.cost := hcost ▸ hdist
              obtain ⟨hnonnegative, hlast⟩ := ih hrun
              exact ⟨fun hs => hnonnegative (Grid.relax_distances_nonnegative hs hentry), hlast⟩

theorem Grid.seed_run_distances {g : Grid} {starts ends : List Point} {fuel : Nat}
    {seeded out : Search} {last : Vertex} (hseed : g.seed starts = some seeded)
    (hrun : g.run ends fuel seeded = some (last, out)) :
    DistancesNonnegative out ∧ (∃ cost : Cost, out.dist[last]? = some cost) := by
  obtain ⟨hnonnegative, hlast⟩ := Grid.run_distances hrun
  exact ⟨hnonnegative (Grid.seed_distances_nonnegative hseed), hlast⟩

theorem DistancesNonnegative.rank_lt {s : Search} {v parent : Vertex}
    (hs : DistancesNonnegative s)
    (hedge : ∃ (parentCost vertexCost : Cost),
      s.dist[parent]? = some parentCost ∧ s.dist[v]? = some vertexCost ∧
      parentCost.dist < vertexCost.dist) :
    (s.dist[parent]?.getD default).dist.toNat < (s.dist[v]?.getD default).dist.toNat := by
  obtain ⟨parentCost, vertexCost, hp, hv, hlt⟩ := hedge
  simp only [hp, hv, Option.getD_some]
  apply Int.ofNat_lt.mp
  rw [Int.toNat_of_nonneg (hs parent parentCost hp), Int.toNat_of_nonneg (hs v vertexCost hv)]
  exact hlt

end Elegant.Layered.Visibility
