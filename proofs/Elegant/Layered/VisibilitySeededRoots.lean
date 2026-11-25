import Elegant.Layered.VisibilityClearance

set_option autoImplicit false

namespace Elegant.Layered.Visibility

def SeededRoots (g : Grid) (starts : List Point) (s : Search) : Prop :=
  ∀ (v : Vertex) (c : Cost), s.dist[v]? = some c → s.prev[v]? = none →
    ∃ p ∈ starts, g.vertexAt p = some v

theorem seed_roots {g : Grid} {starts : List Point} {s : Search}
    (hseed : g.seed starts = some s) : SeededRoots g starts s := by
  let seedStep (acc : Search) (p : Point) : Option Search :=
    if !g.inside p then some acc
    else (g.vertexAt p).map fun v =>
      { acc with frontier := acc.frontier.push ⟨⟨0, 0⟩, v⟩,
                 dist := acc.dist.insert v ⟨0, 0⟩ }
  change starts.foldlM seedStep ⟨#[], {}, {}⟩ = some s at hseed
  have step_roots (acc out : Search) (p : Point) (hmem : p ∈ starts)
      (ha : SeededRoots g starts acc) (h : seedStep acc p = some out) :
      SeededRoots g starts out := by
    dsimp only [seedStep] at h
    split at h
    · rw [← Option.some.inj h]
      exact ha
    · obtain ⟨v, hv, hout⟩ := Option.map_eq_some_iff.mp h
      rw [← hout]
      intro w c hd hp
      by_cases heq : (v == w) = true
      · have hvw : v = w := beq_iff_eq.mp heq
        exact ⟨p, hmem, hvw ▸ hv⟩
      · change (acc.dist.insert v ⟨0, 0⟩)[w]? = some c at hd
        rw [Std.HashMap.getElem?_insert, ite_eq_right heq] at hd
        exact ha w c hd hp
  suffices fold_roots : ∀ (pending : List Point) (acc out : Search),
      (∀ p ∈ pending, p ∈ starts) → SeededRoots g starts acc →
      pending.foldlM seedStep acc = some out → SeededRoots g starts out by
    refine fold_roots starts ⟨#[], {}, {}⟩ s (fun _ hp => hp) ?_ hseed
    intro v c hd _
    change (∅ : Std.HashMap Vertex Cost)[v]? = some c at hd
    simp at hd
  intro pending
  induction pending with
  | nil =>
      intro acc out _ ha h
      change some acc = some out at h
      rw [← Option.some.inj h]
      exact ha
  | cons p pending ih =>
      intro acc out hm ha h
      rw [List.foldlM_cons] at h
      obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp h
      exact ih next out (fun q hq => hm q (List.mem_cons_of_mem p hq))
        (step_roots acc next p (hm p List.mem_cons_self) ha hstep) hrest

theorem relax_roots {g : Grid} {starts : List Point} {s : Search} {entry : Entry}
    (hs : SeededRoots g starts s) : SeededRoots g starts (g.relax entry s) := by
  have step_roots (acc : Search) (next : Vertex) (ha : SeededRoots g starts acc) :
      SeededRoots g starts (relaxStep g entry acc next) := by
    have hinsert : SeededRoots g starts
        { frontier := acc.frontier.push ⟨g.step entry.vertex next entry.cost, next⟩
          dist := acc.dist.insert next (g.step entry.vertex next entry.cost)
          prev := acc.prev.insert next entry.vertex } := by
      intro v c hd hp
      change (acc.prev.insert next entry.vertex)[v]? = none at hp
      by_cases heq : (next == v) = true
      · rw [Std.HashMap.getElem?_insert, ite_eq_left heq] at hp
        exact (Option.some_ne_none _ hp).elim
      · change (acc.dist.insert next (g.step entry.vertex next entry.cost))[v]? = some c at hd
        rw [Std.HashMap.getElem?_insert, ite_eq_right heq] at hd hp
        exact ha v c hd hp
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
  suffices fold_roots : ∀ (neighbours : List Vertex) (acc : Search),
      SeededRoots g starts acc → SeededRoots g starts (neighbours.foldl (relaxStep g entry) acc) by
    exact fold_roots (g.neighbours entry.vertex) s hs
  intro neighbours
  induction neighbours with
  | nil =>
      intro acc ha
      exact ha
  | cons next rest ih =>
      intro acc ha
      exact ih (relaxStep g entry acc next) (step_roots acc next ha)

theorem run_roots {g : Grid} {starts ends : List Point} {fuel : Nat}
    {s out : Search} {last : Vertex} (hs : SeededRoots g starts s)
    (hrun : g.run ends fuel s = some (last, out)) : SeededRoots g starts out := by
  induction fuel generalizing s with
  | zero => simp [Grid.run] at hrun
  | succ fuel ih =>
      unfold Grid.run at hrun
      split at hrun
      · simp at hrun
      · rename_i entry rest _
        have hrest : SeededRoots g starts ({ s with frontier := rest } : Search) :=
          fun v c hd hp => hs v c hd hp
        dsimp only at hrun
        split at hrun
        · exact ih hrest hrun
        · split at hrun
          · exact ih hrest hrun
          · split at hrun
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              rw [← hrun.2]
              exact hrest
            · exact ih (relax_roots hrest) hrun

theorem seed_run_roots {g : Grid} {starts ends : List Point} {fuel : Nat}
    {seeded out : Search} {last : Vertex} (hseed : g.seed starts = some seeded)
    (hrun : g.run ends fuel seeded = some (last, out)) : SeededRoots g starts out :=
  run_roots (seed_roots hseed) hrun

theorem Grid.point_vertexAt {g : Grid} {p : Point} {v : Vertex}
    (h : g.vertexAt p = some v) : g.point v = p := by
  unfold Grid.vertexAt at h
  cases hx : g.xs.findIdx? (· == p.x) with
  | none => simp [hx] at h
  | some x =>
      cases hy : g.ys.findIdx? (· == p.y) with
      | none => simp [hx, hy] at h
      | some y =>
          have hv : (⟨x, y, 2⟩ : Vertex) = v :=
            Option.some.inj (by simpa only [hx, hy] using h)
          obtain ⟨hxlt, hxeq, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hx
          obtain ⟨hylt, hyeq, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hy
          subst v
          apply (point_ext_iff _ _).mpr
          constructor
          · change g.xs[x]! = p.x
            rw [getElem!_pos g.xs x hxlt]
            exact beq_iff_eq.mp hxeq
          · change g.ys[y]! = p.y
            rw [getElem!_pos g.ys y hylt]
            exact beq_iff_eq.mp hyeq

end Elegant.Layered.Visibility
