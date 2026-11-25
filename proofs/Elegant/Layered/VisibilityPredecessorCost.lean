import Elegant.Layered.VisibilityPositiveStep
import Elegant.Layered.VisibilityClearance

set_option autoImplicit false

namespace Elegant.Layered.Visibility

def PrevDistStrict (s : Search) : Prop :=
  ∀ (v parent : Vertex), s.prev[v]? = some parent →
    ∃ (parentCost vertexCost : Cost),
      s.dist[parent]? = some parentCost ∧ s.dist[v]? = some vertexCost ∧
      parentCost.dist < vertexCost.dist

theorem PrevDistStrict.of_prev_empty {s : Search} (hempty : s.prev = {}) :
    PrevDistStrict s := by
  intro v parent hprev
  rw [hempty, Std.HashMap.getElem?_empty] at hprev
  cases hprev

theorem Grid.seed_prev_dist_strict {g : Grid} {starts : List Point} {s : Search}
    (hseed : g.seed starts = some s) : PrevDistStrict s :=
  PrevDistStrict.of_prev_empty (seed_prev_empty hseed)

private theorem neighbour_ne_current {g : Grid} {current next : Vertex}
    (hnext : next ∈ g.neighbours current) : next ≠ current := by
  simp only [Grid.neighbours, List.mem_append, List.mem_ite_nil_right,
    List.mem_singleton, or_assoc] at hnext
  rcases hnext with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
  · intro heq
    have hx : current.x - 1 = current.x := congrArg Vertex.x heq
    omega
  · intro heq
    have hx : current.x + 1 = current.x := congrArg Vertex.x heq
    omega
  · intro heq
    have hy : current.y - 1 = current.y := congrArg Vertex.y heq
    omega
  · intro heq
    have hy : current.y + 1 = current.y := congrArg Vertex.y heq
    omega

private theorem cost_dist_le_of_lt {candidate old : Cost} (h : candidate.lt old = true) :
    candidate.dist ≤ old.dist := by
  simp only [Cost.lt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with hdist | ⟨hdist, _⟩ <;> omega

private theorem lookup_insert_other {α : Type} (m : Std.HashMap Vertex α)
    {key other : Vertex} (hne : key ≠ other) (value : α) :
    (m.insert key value)[other]? = m[other]? := by
  rw [Std.HashMap.getElem?_insert, ite_eq_right (fun h => hne (beq_iff_eq.mp h))]

private theorem relaxStep_prev_dist_strict {g : Grid} {entry : Entry} {s : Search} {next : Vertex}
    (xUnique : g.xs.toList.Nodup) (yUnique : g.ys.toList.Nodup)
    (hx : entry.vertex.x < g.xs.size) (hy : entry.vertex.y < g.ys.size)
    (hnext : next ∈ g.neighbours entry.vertex) (hs : PrevDistStrict s)
    (hentry : s.dist[entry.vertex]? = some entry.cost) :
    PrevDistStrict (relaxStep g entry s next) ∧
      (relaxStep g entry s next).dist[entry.vertex]? = some entry.cost := by
  let candidate := g.step entry.vertex next entry.cost
  let inserted : Search :=
    { frontier := s.frontier.push ⟨candidate, next⟩
      dist := s.dist.insert next candidate
      prev := s.prev.insert next entry.vertex }
  have hpos : entry.cost.dist < candidate.dist :=
    Grid.step_dist_lt_of_neighbour xUnique yUnique hx hy hnext entry.cost
  have hinsert (hle : ∀ old : Cost, s.dist[next]? = some old → candidate.dist ≤ old.dist) :
      PrevDistStrict inserted ∧ inserted.dist[entry.vertex]? = some entry.cost := by
    have hentry' : inserted.dist[entry.vertex]? = some entry.cost :=
      (lookup_insert_other s.dist (neighbour_ne_current hnext) candidate).trans hentry
    refine ⟨?_, hentry'⟩
    intro v parent hprev
    by_cases hv : next = v
    · subst v
      have hnew : (s.prev.insert next entry.vertex)[next]? = some entry.vertex :=
        Std.HashMap.getElem?_insert_self
      have hp : entry.vertex = parent := Option.some.inj (hnew.symm.trans hprev)
      subst parent
      exact ⟨entry.cost, candidate, hentry', Std.HashMap.getElem?_insert_self, hpos⟩
    · have hprev' : s.prev[v]? = some parent :=
        (lookup_insert_other s.prev hv entry.vertex).symm.trans hprev
      obtain ⟨parentCost, vertexCost, hparent, hvertex, hlt⟩ := hs v parent hprev'
      have hvertex' : inserted.dist[v]? = some vertexCost :=
        (lookup_insert_other s.dist hv candidate).trans hvertex
      by_cases hp : next = parent
      · subst parent
        exact ⟨candidate, vertexCost, Std.HashMap.getElem?_insert_self, hvertex',
          Int.lt_of_le_of_lt (hle parentCost hparent) hlt⟩
      · have hparent' : inserted.dist[parent]? = some parentCost :=
          (lookup_insert_other s.dist hp candidate).trans hparent
        exact ⟨parentCost, vertexCost, hparent', hvertex', hlt⟩
  unfold relaxStep
  split
  · exact ⟨hs, hentry⟩
  · dsimp only
    cases hd : s.dist[next]? with
    | none =>
        refine hinsert ?_
        intro old hold
        exact (Option.some_ne_none _ (hold.symm.trans hd)).elim
    | some old =>
        by_cases hbetter : (g.step entry.vertex next entry.cost).lt old = true
        · rw [ite_eq_left hbetter]
          refine hinsert ?_
          intro c hc
          have heq : c = old := Option.some.inj (hc.symm.trans hd)
          exact heq.symm ▸ cost_dist_le_of_lt hbetter
        · rw [ite_eq_right hbetter]
          exact ⟨hs, hentry⟩

theorem Grid.relax_prev_dist_strict {g : Grid} {entry : Entry} {s : Search}
    (xUnique : g.xs.toList.Nodup) (yUnique : g.ys.toList.Nodup)
    (hx : entry.vertex.x < g.xs.size) (hy : entry.vertex.y < g.ys.size)
    (hs : PrevDistStrict s) (hentry : s.dist[entry.vertex]? = some entry.cost) :
    PrevDistStrict (g.relax entry s) ∧ (g.relax entry s).dist[entry.vertex]? = some entry.cost := by
  change PrevDistStrict ((g.neighbours entry.vertex).foldl (relaxStep g entry) s) ∧ _
  suffices fold_dist : ∀ (remaining : List Vertex) (acc : Search),
      (∀ next ∈ remaining, next ∈ g.neighbours entry.vertex) →
      PrevDistStrict acc → acc.dist[entry.vertex]? = some entry.cost →
      PrevDistStrict (remaining.foldl (relaxStep g entry) acc) ∧
        (remaining.foldl (relaxStep g entry) acc).dist[entry.vertex]? = some entry.cost from
    fold_dist _ s (fun _ h => h) hs hentry
  intro remaining
  induction remaining with
  | nil =>
      intro acc _ hacc hcost
      exact ⟨hacc, hcost⟩
  | cons next rest ih =>
      intro acc hsub hacc hcost
      have hnext := hsub next List.mem_cons_self
      obtain ⟨hstrict, hcurrent⟩ :=
        relaxStep_prev_dist_strict xUnique yUnique hx hy hnext hacc hcost
      rw [List.foldl_cons]
      exact ih _ (fun v hv => hsub v (List.mem_cons_of_mem next hv)) hstrict hcurrent

end Elegant.Layered.Visibility
