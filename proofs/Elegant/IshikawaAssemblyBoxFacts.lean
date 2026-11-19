import Elegant.Ishikawa
import Elegant.ForInFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

inductive AssemblyPairShift : List Rib → Int → Int → Rib → Int → Prop where
  | current (a : Rib) (rest : List Rib) (ceiling previous : Int)
      (r : Rib) (hr : r ∈ a :: rest.take 1) :
      AssemblyPairShift (a :: rest) ceiling previous r
        (min ceiling (previous - (extent (a :: rest.take 1)).2))
  | later (a : Rib) (rest : List Rib) (ceiling previous : Int)
      (r : Rib) (dx : Int)
      (h : AssemblyPairShift (rest.drop 1)
        (min ceiling (previous - (extent (a :: rest.take 1)).2) +
          (extent (a :: rest.take 1)).1)
        (min ceiling (previous - (extent (a :: rest.take 1)).2) +
          (extent (a :: rest.take 1)).1) r dx) :
      AssemblyPairShift (a :: rest) ceiling previous r dx

def AssemblyBoxOrigin (rs : List Rib) (ceiling previous : Int)
    (initial : Tree.Layout) (k : Nat) (box : Rect) : Prop :=
  initial.boxes[k]? = some box ∨
    ∃ r original points dx,
      AssemblyPairShift rs ceiling previous r dx ∧
      (k, original, points) ∈ r.pieces ∧
      box = { original with x := original.x + dx }

theorem assemblyPairShift_mem {rs : List Rib} {ceiling previous : Int}
    {r : Rib} {dx : Int} (h : AssemblyPairShift rs ceiling previous r dx) :
    r ∈ rs := by
  induction h with
  | current a rest ceiling previous r hr =>
    simp only [List.mem_cons] at hr ⊢
    rcases hr with he | hm
    · exact Or.inl he
    · exact Or.inr (List.mem_of_mem_take hm)
  | later a rest ceiling previous r dx h ih =>
    exact List.mem_cons_of_mem a (List.mem_of_mem_drop ih)

theorem assemblyPair_frontier (a : Rib) (rest : List Rib)
    (ceiling previous : Int) :
    let bounds := extent (a :: rest.take 1)
    let attach := min ceiling (previous - bounds.2)
    attach ≤ ceiling ∧ attach + bounds.2 ≤ previous ∧
      attach + bounds.1 ≤ previous - bounds.2 + bounds.1 := by
  dsimp
  omega

private theorem bind_ok {α β : Type}
    {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem set_box_origin {α : Type} (xs : List α) (i : Nat)
    (value : α) (k : Nat) (result : α)
    (h : (xs.set i value)[k]? = some result) :
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

private theorem loop_box_invariant {α : Type} (xs : List α)
    (step : α → Tree.Layout → Except LayoutError (ForInStep Tree.Layout))
    (P : Tree.Layout → Prop) (initial final : Tree.Layout) (hinit : P initial)
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

theorem assemblePairs_box_origin_bounded (spine : Int) (n : Nat) :
    ∀ (rs : List Rib) (ceiling previous : Int) (initial final : Tree.Layout),
      rs.length ≤ n →
      assemblePairs spine rs ceiling previous initial = .ok final →
      ∀ k box, final.boxes[k]? = some box →
        AssemblyBoxOrigin rs ceiling previous initial k box := by
  induction n with
  | zero =>
    intro rs ceiling previous initial final hlen hrun k box hp
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons a rest => simp only [List.length_cons] at hlen; omega
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
      intro k box hp
      exact Or.inl hp
    | cons a rest =>
      simp only [assemblePairs] at hrun
      obtain ⟨mid, hloop, htail⟩ := bind_ok hrun
      have hmid : ∀ k box, mid.boxes[k]? = some box →
          AssemblyBoxOrigin (a :: rest) ceiling previous initial k box := by
        refine loop_box_invariant _ _ (fun out : Tree.Layout =>
          ∀ k box, out.boxes[k]? = some box →
            AssemblyBoxOrigin (a :: rest) ceiling previous initial k box)
          _ _ ?_ ?_ hloop
        · intro k box hp
          exact Or.inl hp
        · intro r hr state next hi hs
          obtain ⟨inner, hinner, hret⟩ := bind_ok hs
          have hin : ∀ k box, inner.boxes[k]? = some box →
              AssemblyBoxOrigin (a :: rest) ceiling previous initial k box := by
            refine loop_box_invariant _ _ (fun out : Tree.Layout =>
              ∀ k box, out.boxes[k]? = some box →
                AssemblyBoxOrigin (a :: rest) ceiling previous initial k box)
              _ _ hi ?_ hinner
            intro piece hpiece state2 next2 hi2 hs2
            obtain ⟨i, rect, original⟩ := piece
            split at hs2
            · cases hs2
            · simp only [pure, Except.pure, Except.ok.injEq] at hs2
              subst next2
              refine ⟨_, rfl, ?_⟩
              intro k box hp
              rcases set_box_origin _ _ _ _ _ hp with hold | ⟨hk, hbox⟩
              · exact hi2 k box hold
              · subst k
                exact Or.inr ⟨r, rect, original, _,
                  AssemblyPairShift.current a rest ceiling previous r hr, hpiece, hbox⟩
          cases next with
          | done out => cases hret
          | yield out =>
            cases hret
            exact ⟨_, rfl, hin⟩
      have hdrop : (rest.drop 1).length ≤ n := by
        simp only [List.length_drop]
        simp only [List.length_cons] at hlen
        omega
      intro k box hp
      have horigin := ih (rest.drop 1) _ _ _ _ hdrop htail k box hp
      rcases horigin with hold | ⟨r, rect, points, dx, hshift, hm, he⟩
      · exact hmid k box hold
      · exact Or.inr ⟨r, rect, points, dx,
          AssemblyPairShift.later a rest ceiling previous r dx hshift, hm, he⟩

theorem assemblePairs_box_origin (spine : Int) (rs : List Rib)
    (ceiling previous : Int) (initial final : Tree.Layout)
    (hrun : assemblePairs spine rs ceiling previous initial = .ok final)
    (k : Nat) (box : Rect) (hbox : final.boxes[k]? = some box) :
    AssemblyBoxOrigin rs ceiling previous initial k box :=
  assemblePairs_box_origin_bounded spine rs.length rs ceiling previous
    initial final (Nat.le_refl _) hrun k box hbox

def AssemblyPieceRouteOrigin (spine : Int) (rs : List Rib) (ceiling previous : Int)
    (initial : Tree.Layout) (k : Nat) (pts : List Point) : Prop :=
  (k = 0 ∧ ∃ a, pts = [⟨a, spine⟩, ⟨0, spine⟩]) ∨
    initial.routes[k]? = some pts ∨
    ∃ r original dx,
      AssemblyPairShift rs ceiling previous r dx ∧
      (∃ rect, (k, rect, original) ∈ r.pieces) ∧
      pts = original.map (fun q => ({ x := q.x + dx, y := q.y } : Point))


private def pairNext (ceiling previous : Int) (pair : List Rib) : Int :=
  min ceiling (previous - (extent pair).2) + (extent pair).1

private def spineRoute (spine next : Int) : List Point :=
  [⟨next, spine⟩, ⟨0, spine⟩]

private def afterSpineSet (mid : Tree.Layout) (spine next : Int) : Tree.Layout :=
  { mid with routes := mid.routes.set 0 (spineRoute spine next) }

private theorem afterSpineSet_routes (mid : Tree.Layout) (spine next : Int) :
    (afterSpineSet mid spine next).routes = mid.routes.set 0 (spineRoute spine next) := rfl

private theorem route_origin_step (spine : Int) (a : Rib) (rest : List Rib)
    (ceiling previous : Int) (initial mid : Tree.Layout) (k : Nat)
    (pts : List Point)
    (hmid : ∀ k pts, mid.routes[k]? = some pts →
      AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts)
    (h : AssemblyPieceRouteOrigin spine (rest.drop 1)
      (pairNext ceiling previous (a :: rest.take 1))
      (pairNext ceiling previous (a :: rest.take 1))
      (afterSpineSet mid spine (pairNext ceiling previous (a :: rest.take 1))) k pts) :
    AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts := by
  rcases h with ⟨hk0, ha⟩ | hinit | ⟨r, original, dx, hshift, hmem, hpts⟩
  · exact Or.inl ⟨hk0, ha⟩
  · by_cases hk : k = 0
    · subst k
      have hlen : 0 < mid.routes.length := by
        have hb := (List.getElem?_eq_some_iff.mp hinit).1
        rw [afterSpineSet_routes, List.length_set] at hb
        omega
      rw [afterSpineSet_routes, List.getElem?_set_self hlen] at hinit
      have hinj := Option.some.inj hinit
      refine Or.inl ⟨rfl, pairNext ceiling previous (a :: rest.take 1), ?_⟩
      exact hinj.symm
    · rw [afterSpineSet_routes, List.getElem?_set_ne (Ne.symm hk)] at hinit
      exact hmid k pts hinit
  · refine Or.inr (Or.inr ⟨r, original, dx, ?_, hmem, hpts⟩)
    exact AssemblyPairShift.later a rest ceiling previous r dx hshift


theorem assemblePairs_piece_route_origin_bounded (spine : Int) (n : Nat) :
    ∀ (rs : List Rib) (ceiling previous : Int) (initial final : Tree.Layout),
      rs.length ≤ n →
      assemblePairs spine rs ceiling previous initial = .ok final →
      ∀ k pts, final.routes[k]? = some pts →
        AssemblyPieceRouteOrigin spine rs ceiling previous initial k pts := by
  induction n with
  | zero =>
    intro rs ceiling previous initial final hlen hrun k pts hp
    have hrs : rs = [] := by
      cases rs with
      | nil => rfl
      | cons a rest => simp only [List.length_cons] at hlen; omega
    subst rs
    simp only [assemblePairs, pure, Except.pure, Except.ok.injEq] at hrun
    subst final
    exact Or.inr (Or.inl hp)
  | succ n ih =>
    intro rs ceiling previous initial final hlen hrun
    cases rs with
    | nil =>
      simp only [assemblePairs, pure, Except.pure, Except.ok.injEq] at hrun
      subst final
      intro k pts hp
      exact Or.inr (Or.inl hp)
    | cons a rest =>
      simp only [assemblePairs] at hrun
      obtain ⟨mid, hloop, htail⟩ := bind_ok hrun
      have hmid : ∀ k pts, mid.routes[k]? = some pts →
          AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts := by
        refine loop_box_invariant _ _ (fun out : Tree.Layout =>
          ∀ k pts, out.routes[k]? = some pts →
            AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts)
          _ _ ?_ ?_ hloop
        · intro k pts hp
          exact Or.inr (Or.inl hp)
        · intro r hr state next hi hs
          obtain ⟨inner, hinner, hret⟩ := bind_ok hs
          have hin : ∀ k pts, inner.routes[k]? = some pts →
              AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts := by
            refine loop_box_invariant _ _ (fun out : Tree.Layout =>
              ∀ k pts, out.routes[k]? = some pts →
                AssemblyPieceRouteOrigin spine (a :: rest) ceiling previous initial k pts)
              _ _ hi ?_ hinner
            intro piece hpiece state2 next2 hi2 hs2
            obtain ⟨i, rect, points⟩ := piece
            split at hs2
            · cases hs2
            · simp only [pure, Except.pure, Except.ok.injEq] at hs2
              subst next2
              refine ⟨_, rfl, ?_⟩
              intro k pts hp
              rcases set_box_origin _ _ _ _ _ hp with hold | ⟨hk, hpts⟩
              · exact hi2 k pts hold
              · subst k
                refine Or.inr (Or.inr ⟨r, points,
                  min ceiling (previous - (extent (a :: rest.take 1)).2),
                  AssemblyPairShift.current a rest ceiling previous r hr,
                  ⟨rect, hpiece⟩, ?_⟩)
                exact hpts
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
      exact route_origin_step spine a rest ceiling previous initial mid k pts hmid horigin

theorem assemblePairs_piece_route_origin (spine : Int) (rs : List Rib)
    (ceiling previous : Int) (initial final : Tree.Layout)
    (hrun : assemblePairs spine rs ceiling previous initial = .ok final)
    (k : Nat) (pts : List Point) (hpts : final.routes[k]? = some pts) :
    AssemblyPieceRouteOrigin spine rs ceiling previous initial k pts :=
  assemblePairs_piece_route_origin_bounded spine rs.length rs ceiling previous
    initial final (Nat.le_refl _) hrun k pts hpts


end Elegant.Ishikawa
