import Elegant.Ishikawa
import Elegant.ForInFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem place_piece_depth_geometry (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect pts, (i, rect, pts) ∈ placed.pieces →
      i = r.cause ∨ ∃ e ∈ r.entries, i = e.node ∧
        ∃ a b : Point, pts = [a, b] ∧ (e.depth % 2 = 0 → a.y = b.y) := by
  simp only [place] at hrun
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, hloop, hret⟩ := bind_ok hrun
    let P := fun (_ : List (Entry × Nat)) (st : List (Nat × Rect × List Point) × List Bone) =>
      ∀ i rect pts, (i, rect, pts) ∈ st.1 →
        i = r.cause ∨ ∃ e ∈ r.entries, i = e.node ∧
          ∃ a b : Point, pts = [a, b] ∧ (e.depth % 2 = 0 → a.y = b.y)
    have hinv : P ([] ++ r.entries.zipIdx) mid := by
      refine Elegant.forIn_processed [] _ _ _ _ P ?_ ?_ hloop
      · intro i rect pts hmem
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        exact Or.inl hmem.1
      · intro done entry rest state next heq hi hstep
        obtain ⟨e, idx⟩ := entry
        have ha : (e, idx) ∈ r.entries.zipIdx := by
          simp only [List.nil_append] at heq
          rw [heq]
          simp
        have he : e ∈ r.entries := List.fst_mem_of_mem_zipIdx ha
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          cases hpos : r.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            by_cases hg : ((e.depth % 2 == 0) && decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some node =>
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  refine ⟨_, rfl, ?_⟩
                  intro i rect pts hmem
                  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
                  rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
                  · exact hi i rect pts hmem
                  · refine Or.inr ⟨e, he, rfl, _, _, rfl, ?_⟩
                    intro heven
                    have ht := depthBone_even_endpoints p par e.depth
                      (Int.fdiv (r.length * (pos.2 + 1 : Nat))
                        (r.entries.length + 1 : Nat))
                      ((children ns e.node).length : Int)
                      (run p r.heights + 3) heven
                    dsimp only
                    rw [ht.1, ht.2.1]
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    subst placed
    exact hinv

theorem flatten_depth_lookup (ns : List Tree.Node) (depths : List Nat)
    (hchildren : ∀ parent depth, depths[parent]? = some depth →
      ∀ i ∈ children ns parent, depths[i]? = some (depth + 1))
    (up : Bool) (fuel : Nat) :
    ∀ (ids : List Nat) (par : Int) (depth : Nat)
      (entries : List Entry) (order : List Nat),
      (∀ i ∈ ids, depths[i]? = some depth) →
      (∀ e ∈ entries, depths[e.node]? = some e.depth) →
      ∀ e ∈ (flatten ns up fuel ids par depth entries order).1,
        depths[e.node]? = some e.depth := by
  induction fuel with
  | zero =>
    intro ids par depth entries order _ he
    exact he
  | succ fuel ih =>
    intro ids par depth entries order hids he
    have hwalk : ∀ i ∈ (if up then ids.reverse else ids),
        depths[i]? = some depth := by
      cases up <;> simpa using hids
    unfold flatten
    generalize (if up then ids.reverse else ids) = walk at hwalk ⊢
    induction walk generalizing entries order with
    | nil => exact he
    | cons node rest tail =>
      simp only [List.foldl_cons]
      have hn : depths[node]? = some depth := hwalk node (List.mem_cons_self ..)
      have happend : ∀ e ∈ entries ++
          [({ node := node, parent := par, depth := depth } : Entry)],
          depths[e.node]? = some e.depth := by
        intro e hm
        rcases List.mem_append.mp hm with hm | hm
        · exact he e hm
        · simp only [List.mem_singleton] at hm
          subst e
          exact hn
      have hrec := ih (children ns node) (entries.length : Int)
        (depth + 1) (entries ++ [⟨node, par, depth⟩])
        (if depth % 2 == 0 then order ++ [entries.length] else order)
        (hchildren node depth hn) happend
      apply tail
      · exact hrec
      · intro i hi
        exact hwalk i (List.mem_cons_of_mem node hi)

theorem cause_and_flatten_depth_lookup (ns : List Tree.Node) (depths : List Nat)
    (hroot : depths[0]? = some 0)
    (hchildren : ∀ parent depth, depths[parent]? = some depth →
      ∀ i ∈ children ns parent, depths[i]? = some (depth + 1))
    (cause k : Nat) (hcause : cause ∈ children ns 0) :
    depths[cause]? = some 1 ∧
      ∀ e ∈ (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1,
        depths[e.node]? = some e.depth := by
  have hc : depths[cause]? = some 1 := hchildren 0 0 hroot cause hcause
  refine ⟨hc, ?_⟩
  exact flatten_depth_lookup ns depths hchildren (upper k) 64
    (children ns cause) (-1) 2 [] [] (hchildren cause 1 hc) (by simp)

private theorem set_lookup_origin {α : Type} (xs : List α) (i k : Nat)
    (value result : α) (h : (xs.set i value)[k]? = some result) :
    xs[k]? = some result ∨ k = i ∧ result = value := by
  induction xs generalizing i k with
  | nil => cases k <;> simp [List.set] at h
  | cons a xs ih =>
    cases i with
    | zero =>
      cases k with
      | zero =>
        change some value = some result at h
        exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
      | succ k => exact Or.inl h
    | succ i =>
      cases k with
      | zero => exact Or.inl h
      | succ k =>
        change (xs.set i value)[k]? = some result at h
        rcases ih i k h with ho | ⟨hk, hv⟩
        · exact Or.inl ho
        · exact Or.inr ⟨congrArg Nat.succ hk, hv⟩

private theorem forIn_invariant {α β : Type} (xs : List α)
    (step : α → β → Except LayoutError (ForInStep β))
    (P : β → Prop) (initial final : β) (hinit : P initial)
    (hstep : ∀ a ∈ xs, ∀ state next, P state →
      step a state = .ok next → ∃ state', next = .yield state' ∧ P state')
    (hrun : forIn xs initial step = .ok final) : P final := by
  have hp := Elegant.forIn_processed [] xs initial final step (fun _ => P) hinit
    (by
      intro done a rest state next heq hi hs
      apply hstep a ?_ state next hi hs
      simp only [List.nil_append] at heq
      rw [heq]
      simp) hrun
  exact hp

def AssemblyRouteOrigin (spine : Int) (rs : List Rib) (initial : Tree.Layout)
    (k : Nat) (pts : List Point) : Prop :=
  initial.routes[k]? = some pts ∨
    (k = 0 ∧ ∃ x : Int, pts = [⟨x, spine⟩, ⟨0, spine⟩]) ∨
    ∃ r ∈ rs, ∃ rect original dx,
      (k, rect, original) ∈ r.pieces ∧
        pts = original.map (fun q => ({ x := q.x + dx, y := q.y } : Point))

theorem assemblePairs_route_origin (spine : Int) (n : Nat) :
    ∀ (rs : List Rib) (ceiling previous : Int) (initial final : Tree.Layout),
      rs.length ≤ n →
      assemblePairs spine rs ceiling previous initial = .ok final →
      ∀ k pts, final.routes[k]? = some pts →
        AssemblyRouteOrigin spine rs initial k pts := by
  induction n with
  | zero =>
    intro rs ceiling previous initial final hlen hrun k pts hp
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons head tail => simp only [List.length_cons] at hlen; omega
    subst rs
    simp only [assemblePairs, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact Or.inl hp
  | succ n ih =>
    intro rs ceiling previous initial final hlen hrun
    cases rs with
    | nil =>
      simp only [assemblePairs, pure, Except.pure, Except.ok.injEq] at hrun
      subst final
      intro k pts hp
      exact Or.inl hp
    | cons a rest =>
      simp only [assemblePairs] at hrun
      obtain ⟨mid, hloop, htail⟩ := bind_ok hrun
      have hmid : ∀ k pts, mid.routes[k]? = some pts →
          AssemblyRouteOrigin spine (a :: rest) initial k pts := by
        refine forIn_invariant _ _ (fun out : Tree.Layout =>
          ∀ k pts, out.routes[k]? = some pts →
            AssemblyRouteOrigin spine (a :: rest) initial k pts)
          _ _ ?_ ?_ hloop
        · intro k pts hp
          exact Or.inl hp
        · intro r hr state next hi hs
          have hrall : r ∈ a :: rest := by
            simp only [List.mem_cons] at hr ⊢
            rcases hr with hr | hr
            · exact Or.inl hr
            · exact Or.inr (List.mem_of_mem_take hr)
          obtain ⟨inner, hinner, hret⟩ := bind_ok hs
          have hin : ∀ k pts, inner.routes[k]? = some pts →
              AssemblyRouteOrigin spine (a :: rest) initial k pts := by
            refine forIn_invariant _ _ (fun out : Tree.Layout =>
              ∀ k pts, out.routes[k]? = some pts →
                AssemblyRouteOrigin spine (a :: rest) initial k pts)
              _ _ hi ?_ hinner
            intro piece hpiece state2 next2 hi2 hs2
            obtain ⟨i, rect, original⟩ := piece
            split at hs2
            · cases hs2
            · simp only [pure, Except.pure, Except.ok.injEq] at hs2
              subst next2
              refine ⟨_, rfl, ?_⟩
              intro k pts hp
              rcases set_lookup_origin _ _ _ _ _ hp with hold | ⟨hk, hpts⟩
              · exact hi2 k pts hold
              · subst k
                exact Or.inr (Or.inr ⟨r, hrall, rect, original, _, hpiece, hpts⟩)
          cases next with
          | done out => cases hret
          | yield out =>
            cases hret
            exact ⟨_, rfl, hin⟩
      have hdrop : (rest.drop 1).length ≤ n := by
        simp only [List.length_drop]
        simp only [List.length_cons] at hlen
        omega
      intro k pts hp
      have horigin := ih (rest.drop 1) _ _ _ _ hdrop htail k pts hp
      rcases horigin with hold | hroot | hpiece
      · rcases set_lookup_origin _ _ _ _ _ hold with hold | ⟨hk, hpts⟩
        · exact hmid k pts hold
        · exact Or.inr (Or.inl ⟨hk, _, hpts⟩)
      · exact Or.inr (Or.inl hroot)
      · obtain ⟨r, hr, rect, original, dx, hm, he⟩ := hpiece
        exact Or.inr (Or.inr ⟨r, List.mem_cons_of_mem a
          (List.mem_of_mem_drop hr), rect, original, dx, hm, he⟩)

end Elegant.Ishikawa
