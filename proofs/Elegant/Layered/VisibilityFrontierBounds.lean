import Elegant.Layered.VisibilityPositiveStep
import Elegant.Layered.VisibilityClearance

set_option autoImplicit false

namespace Elegant.Layered.Visibility

def Grid.InBounds (g : Grid) (v : Vertex) : Prop :=
  v.x < g.xs.size ∧ v.y < g.ys.size

def FrontierBounds (g : Grid) (frontier : Array Entry) : Prop :=
  ∀ entry ∈ frontier, g.InBounds entry.vertex

private theorem frontier_push_bounds {g : Grid} {frontier : Array Entry} {entry : Entry}
    (hf : FrontierBounds g frontier) (he : g.InBounds entry.vertex) :
    FrontierBounds g (frontier.push entry) := by
  intro e hm
  rcases Array.mem_push.mp hm with hm | rfl
  · exact hf e hm
  · exact he

theorem Grid.vertexAt_bounds {g : Grid} {p : Point} {v : Vertex}
    (h : g.vertexAt p = some v) : g.InBounds v := by
  unfold Grid.vertexAt at h
  cases hx : g.xs.findIdx? (· == p.x) with
  | none => simp [hx] at h
  | some x =>
      cases hy : g.ys.findIdx? (· == p.y) with
      | none => simp [hx, hy] at h
      | some y =>
          have hv : (⟨x, y, 2⟩ : Vertex) = v :=
            Option.some.inj (by simpa only [hx, hy] using h)
          subst v
          exact ⟨(Array.findIdx?_eq_some_iff_findIdx_eq.mp hx).1,
            (Array.findIdx?_eq_some_iff_findIdx_eq.mp hy).1⟩

theorem seed_bounds {g : Grid} {starts : List Point} {s : Search}
    (hseed : g.seed starts = some s) : FrontierBounds g s.frontier := by
  let seedStep (acc : Search) (p : Point) : Option Search :=
    if !g.inside p then some acc
    else (g.vertexAt p).map fun v =>
      { acc with frontier := acc.frontier.push ⟨⟨0, 0⟩, v⟩,
                 dist := acc.dist.insert v ⟨0, 0⟩ }
  change starts.foldlM seedStep ⟨#[], {}, {}⟩ = some s at hseed
  have step_bounds (acc out : Search) (p : Point) (ha : FrontierBounds g acc.frontier)
      (h : seedStep acc p = some out) : FrontierBounds g out.frontier := by
    dsimp only [seedStep] at h
    split at h
    · rw [← Option.some.inj h]
      exact ha
    · obtain ⟨v, hv, hout⟩ := Option.map_eq_some_iff.mp h
      rw [← hout]
      exact frontier_push_bounds ha (Grid.vertexAt_bounds hv)
  suffices fold_bounds : ∀ (pending : List Point) (acc out : Search),
      FrontierBounds g acc.frontier → pending.foldlM seedStep acc = some out →
      FrontierBounds g out.frontier by
    refine fold_bounds starts ⟨#[], {}, {}⟩ s ?_ hseed
    intro e hm
    exact (Array.not_mem_empty e hm).elim
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
      exact ih next out (step_bounds acc next p ha hstep) hrest

theorem relax_bounds {g : Grid} {entry : Entry} {s : Search}
    (hentry : g.InBounds entry.vertex) (hs : FrontierBounds g s.frontier) :
    FrontierBounds g (g.relax entry s).frontier := by
  change FrontierBounds g
    ((g.neighbours entry.vertex).foldl (relaxStep g entry) s).frontier
  have step_bounds (acc : Search) (next : Vertex) (ha : FrontierBounds g acc.frontier)
      (hnext : next ∈ g.neighbours entry.vertex) :
      FrontierBounds g (relaxStep g entry acc next).frontier := by
    have hpush : FrontierBounds g
        (acc.frontier.push ⟨g.step entry.vertex next entry.cost, next⟩) :=
      frontier_push_bounds ha (Grid.neighbour_bounds hentry.1 hentry.2 hnext)
    unfold relaxStep
    split
    · exact ha
    · dsimp only
      cases hdist : acc.dist[next]? with
      | none => exact hpush
      | some old =>
          by_cases hbetter : (g.step entry.vertex next entry.cost).lt old = true
          · simpa only [ite_eq_left hbetter] using hpush
          · simpa only [ite_eq_right hbetter] using ha
  suffices fold_bounds : ∀ (ns : List Vertex) (acc : Search),
      FrontierBounds g acc.frontier → (∀ v ∈ ns, v ∈ g.neighbours entry.vertex) →
      FrontierBounds g (ns.foldl (relaxStep g entry) acc).frontier from
    fold_bounds (g.neighbours entry.vertex) s hs (fun _ h => h)
  intro ns
  induction ns with
  | nil =>
      intro acc ha _
      exact ha
  | cons next ns ih =>
      intro acc ha hm
      exact ih (relaxStep g entry acc next) (step_bounds acc next ha (hm next List.mem_cons_self))
        (fun v hv => hm v (List.mem_cons_of_mem next hv))

private theorem range_forIn_index_lt (r : Std.Legacy.Range) (init : Nat)
    (step : Nat → Nat → Id (ForInStep Nat)) (hinit : init < r.stop)
    (hstep : ∀ i, i < r.stop → ∀ index, index < r.stop →
      (step i index).value < r.stop) :
    Id.run (ForIn.forIn (m := Id) r init step) < r.stop := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have loop_lt : ∀ (indices : List Nat) (index : Nat), index < r.stop →
      (∀ i ∈ indices, i < r.stop) →
      Id.run (ForIn.forIn (m := Id) indices index step) < r.stop := by
    intro indices
    induction indices with
    | nil =>
        intro index hindex _
        exact hindex
    | cons i indices ih =>
        intro index hindex hm
        rw [List.forIn_cons]
        dsimp only [Bind.bind, Id.instMonad, Pure.pure]
        have hnext := hstep i (hm i List.mem_cons_self) index hindex
        cases hs : step i index with
        | done next => simpa only [hs, ForInStep.value, Id.run] using hnext
        | yield next =>
            refine ih next ?_ (fun j hj => hm j (List.mem_cons_of_mem i hj))
            simpa only [hs, ForInStep.value] using hnext
  exact loop_lt _ init hinit (fun _ hi =>
    Membership.mem.upper (Std.Legacy.Range.mem_of_mem_range' (r := r) hi))

theorem popMin_members {frontier rest : Array Entry} {entry : Entry}
    (hpop : popMin frontier = some (entry, rest)) :
    entry ∈ frontier ∧ ∀ e ∈ rest, e ∈ frontier := by
  unfold popMin at hpop
  split at hpop
  · simp at hpop
  · rename_i hnonempty
    have hsize : 0 < frontier.size :=
      Nat.pos_of_ne_zero (fun hz => hnonempty (Array.isEmpty_iff_size_eq_zero.mpr hz))
    let best : Nat := Id.run do
      let mut index := 0
      for i in [1:frontier.size] do
        if (frontier[i]!).lt (frontier[index]!) then index := i
      pure index
    change some (frontier[best]!, (frontier.set! best frontier.back!).pop) =
      some (entry, rest) at hpop
    have hbest : best < frontier.size := by
      dsimp only [best, Bind.bind, Id.instMonad, Pure.pure]
      apply range_forIn_index_lt (r := [1:frontier.size])
      · exact hsize
      · intro i hi index hindex
        by_cases hlt : (frontier[i]!).lt (frontier[index]!) = true
        · simpa [hlt] using hi
        · simpa [hlt] using hindex
    have hback : frontier.back! ∈ frontier := by
      unfold Array.back!
      have hlast : frontier.size - 1 < frontier.size := by omega
      rw [getElem!_pos frontier _ hlast]
      exact Array.getElem_mem hlast
    obtain ⟨he, hr⟩ := Prod.mk.inj (Option.some.inj hpop)
    rw [← he, ← hr]
    constructor
    · rw [getElem!_pos frontier best hbest]
      exact Array.getElem_mem hbest
    · intro e hm
      obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
      rw [Array.getElem_pop] at heq
      have hi' : i < (frontier.set! best frontier.back!).size := by
        rw [Array.size_pop] at hi
        omega
      have hm' := Array.getElem_mem hi'
      rw [heq, Array.set!_eq_setIfInBounds] at hm'
      rcases Array.mem_or_eq_of_mem_setIfInBounds hm' with hm' | rfl
      · exact hm'
      · exact hback

theorem popMin_bounds {g : Grid} {frontier rest : Array Entry} {entry : Entry}
    (hf : FrontierBounds g frontier) (hpop : popMin frontier = some (entry, rest)) :
    g.InBounds entry.vertex ∧ FrontierBounds g rest := by
  obtain ⟨he, hr⟩ := popMin_members hpop
  exact ⟨hf entry he, fun e hm => hf e (hr e hm)⟩

theorem run_bounds {g : Grid} {ends : List Point} {fuel : Nat} {s out : Search}
    {last : Vertex} (hs : FrontierBounds g s.frontier)
    (hrun : g.run ends fuel s = some (last, out)) :
    g.InBounds last ∧ FrontierBounds g out.frontier := by
  induction fuel generalizing s with
  | zero => simp [Grid.run] at hrun
  | succ fuel ih =>
      unfold Grid.run at hrun
      split at hrun
      · simp at hrun
      · rename_i entry rest hpop
        obtain ⟨hentry, hrest⟩ := popMin_bounds hs hpop
        have hremaining : FrontierBounds g ({ s with frontier := rest } : Search).frontier :=
          hrest
        dsimp only at hrun
        split at hrun
        · exact ih hremaining hrun
        · split at hrun
          · exact ih hremaining hrun
          · split at hrun
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              rw [← hrun.1, ← hrun.2]
              exact ⟨hentry, hremaining⟩
            · exact ih (relax_bounds hentry hremaining) hrun

theorem seed_run_bounds {g : Grid} {starts ends : List Point} {fuel : Nat}
    {seeded out : Search} {last : Vertex} (hseed : g.seed starts = some seeded)
    (hrun : g.run ends fuel seeded = some (last, out)) :
    g.InBounds last ∧ FrontierBounds g out.frontier :=
  run_bounds (seed_bounds hseed) hrun

end Elegant.Layered.Visibility
