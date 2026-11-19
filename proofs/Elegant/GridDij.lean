import Elegant.GridLat

set_option autoImplicit false

/-! The search of the router only walks lattice steps: every entry of the predecessor table is a
seed or a step, so the path read back from the table is a chain of lattice steps from the
junction of the source port to the junction of the target port. -/

namespace Elegant
namespace Grid

theorem getD_set! (tab : Tab) (i j : Nat) (v : Option Entry) :
    (tab.set! i v).getD j none = if i = j ∧ i < tab.size then v else tab.getD j none := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
    Array.getD_eq_getD_getElem?]
  by_cases h : i = j
  · subst h
    by_cases hs : i < tab.size
    · simp [hs]
    · simp [hs]
  · simp [h]

def NewOk (lat : Lat) (sources : List End) (state : Nat) (src : Int) : Prop :=
  (∃ s : Nat, s < 4 ∧ src = -1 - (s : Int) ∧
      state = (sources.getD s default).vertex * 4 + outward s) ∨
    (0 ≤ src ∧ ∃ len, lat.step (src.toNat / 4) (state % 4) = some (state / 4, len))

def TabOk (lat : Lat) (sources : List End) (tab : Tab) : Prop :=
  ∀ (state : Nat) (e : Entry), tab.getD state none = some e → NewOk lat sources state e.prev

theorem TabOk.set {lat : Lat} {sources : List End} {tab : Tab} (h : TabOk lat sources tab)
    {state : Nat} {cost src : Int} (hn : NewOk lat sources state src) :
    TabOk lat sources (tab.set! state (some ⟨cost, src⟩)) := by
  intro j e he
  rw [getD_set!] at he
  by_cases hc : state = j ∧ state < tab.size
  · obtain ⟨h1, h2⟩ := hc
    subst h1
    simp only [h2, and_self, ↓reduceIte] at he
    have := Option.some.inj he
    subst this
    exact hn
  · simp only [hc, ↓reduceIte] at he
    exact h j e he

theorem relax_ok {lat : Lat} {sources : List End} {tab : Tab} (h : TabOk lat sources tab)
    {heap : Heap} {state : Nat} {cost src : Int} (hn : NewOk lat sources state src) :
    TabOk lat sources (relax tab heap state cost src).1 := by
  unfold relax
  split
  · split
    · exact h
    · exact TabOk.set h hn
  · exact TabOk.set h hn

theorem expand_ok {r : Router} {sources : List End} {used : Used} {cur : Nat} {tab : Tab}
    {heap : Heap} {cost : Int} {state : Nat} (h : TabOk r.lat sources tab) :
    TabOk r.lat sources (expand r used cur tab heap cost state).1 := by
  unfold expand
  have key : ∀ (l : List Nat), (∀ x ∈ l, x < 4) → ∀ (th : Tab × Heap), TabOk r.lat sources th.1 →
      TabOk r.lat sources (l.foldl (fun (th : Tab × Heap) next =>
        match r.lat.step (state / 4) next with
        | some (u, len) =>
          relax th.1 th.2 (u * 4 + next)
            (cost + len + r.turn (state % 4) next + r.crowd used cur (state / 4) u next)
            (state : Int)
        | none => th) th).1 := by
    intro l
    induction l with
    | nil => intro _ th ht; exact ht
    | cons x xs ih =>
      intro hl th ht
      simp only [List.foldl_cons]
      refine ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ ?_
      have hx := hl x (List.mem_cons_self ..)
      cases hs : r.lat.step (state / 4) x with
      | none =>
        simp only
        exact ht
      | some p =>
        obtain ⟨u, len⟩ := p
        simp only
        apply relax_ok ht
        right
        refine ⟨by omega, len, ?_⟩
        have e1 : (u * 4 + x) % 4 = x := by omega
        have e2 : (u * 4 + x) / 4 = u := by omega
        rw [e1, e2, Int.toNat_natCast]
        exact hs
  exact key _ (fun x hx => List.mem_range.mp hx) _ h

def ArrOk (targets : List End) (best : Option Arrival) : Prop :=
  ∀ b, best = some b → b.side < 4 ∧ (targets.getD b.side default).vertex = b.state / 4

theorem arrive_ok {r : Router} {targets : List End} {cost : Int} {state : Nat}
    {best : Option Arrival} (h : ArrOk targets best) :
    ArrOk targets (arrive r targets cost state best) := by
  unfold arrive
  have key : ∀ (l : List Nat), (∀ x ∈ l, x < 4) → ∀ (b0 : Option Arrival), ArrOk targets b0 →
      ArrOk targets (l.foldl (fun best s =>
        if (targets.getD s default).vertex = state / 4 then
          let total := cost + (targets.getD s default).stub + r.turn (state % 4) (inward s)
          match best with
          | some b => if total < b.cost then some ⟨total, state, s⟩ else best
          | none => some ⟨total, state, s⟩
        else best) b0) := by
    intro l
    induction l with
    | nil => intro _ b0 hb; exact hb
    | cons x xs ih =>
      intro hl b0 hb
      simp only [List.foldl_cons]
      refine ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ ?_
      have hx := hl x (List.mem_cons_self ..)
      by_cases hv : (targets.getD x default).vertex = state / 4
      · simp only [hv, ↓reduceIte]
        cases b0 with
        | none =>
          intro b hb'
          have := Option.some.inj hb'
          subst this
          exact ⟨hx, hv⟩
        | some b1 =>
          simp only
          split
          · intro b hb'
            have := Option.some.inj hb'
            subst this
            exact ⟨hx, hv⟩
          · exact hb
      · simp only [hv, ↓reduceIte]
        exact hb
  exact key _ (fun x hx => List.mem_range.mp hx) _ h

theorem dijkstra_ok {r : Router} {used : Used} {cur : Nat} {targets sources : List End} :
    ∀ (fuel : Nat) (tab : Tab) (heap : Heap) (best : Option Arrival) (tab' : Tab)
      (best' : Option Arrival), TabOk r.lat sources tab → ArrOk targets best →
      dijkstra r used cur targets fuel tab heap best = (tab', best') →
      TabOk r.lat sources tab' ∧ ArrOk targets best' := by
  intro fuel
  induction fuel with
  | zero =>
    intro tab heap best tab' best' ht hb h
    simp only [dijkstra, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨ht, hb⟩
  | succ fuel ih =>
    intro tab heap best tab' best' ht hb h
    unfold dijkstra at h
    cases hp : heap.pop with
    | none =>
      simp only [hp, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, hb⟩
    | some p =>
      obtain ⟨cost, state, heap'⟩ := p
      simp only [hp] at h
      by_cases hstop : stopQ best cost = true
      · simp only [hstop, ↓reduceIte, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨ht, hb⟩
      · simp only [hstop] at h
        by_cases hstale : staleQ tab state cost = true
        · simp only [hstale, ↓reduceIte] at h
          exact ih _ _ _ _ _ ht hb h
        · simp only [hstale] at h
          exact ih _ _ _ _ _ (expand_ok ht) (arrive_ok hb) h

/-! ### Chains of points -/

def LatStep (l : Lat) (p q : Point) : Prop :=
  ∃ (v d u : Nat) (len : Int), l.step v d = some (u, len) ∧ l.point v = p ∧ l.point u = q

def Chain (R : Point → Point → Prop) : List Point → Prop
  | p :: q :: rest => R p q ∧ Chain R (q :: rest)
  | _ => True

theorem Chain.mono {R S : Point → Point → Prop} (hrs : ∀ p q, R p q → S p q) :
    ∀ {l : List Point}, Chain R l → Chain S l
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => ⟨hrs _ _ h.1, Chain.mono hrs h.2⟩

theorem chain_snoc {R : Point → Point → Prop} : ∀ {l : List Point} {y x : Point},
    Chain R l → l.getLast? = some y → R y x → Chain R (l ++ [x])
  | [], _, _, _, h, _ => by simp at h
  | [a], y, x, _, h, hr => by
    have : a = y := by simpa using h
    subst this
    exact ⟨hr, trivial⟩
  | a :: b :: rest, y, x, hc, h, hr => by
    have hl : (b :: rest).getLast? = some y := by simpa [List.getLast?_cons_cons] using h
    exact ⟨hc.1, chain_snoc hc.2 hl hr⟩

theorem chain_cons {R : Point → Point → Prop} {p q : Point} {l : List Point} (hl : Chain R (q :: l))
    (hr : R p q) : Chain R (p :: q :: l) := ⟨hr, hl⟩

theorem chain_spec {lat : Lat} {tab : Tab} {sources : List End} (ht : TabOk lat sources tab) :
    ∀ (fuel state : Nat) (acc pts : List Point), chain lat tab sources fuel state acc = some pts →
      ∃ (s : Nat) (mid : List Point), s < 4 ∧
        pts = (sources.getD s default).port :: (mid ++ acc) ∧
        mid.head? = some (lat.point (sources.getD s default).vertex) ∧
        mid.getLast? = some (lat.point (state / 4)) ∧ Chain (LatStep lat) mid := by
  intro fuel
  induction fuel with
  | zero => intro state acc pts h; simp [chain] at h
  | succ fuel ih =>
    intro state acc pts h
    unfold chain at h
    cases he : tab.getD state none with
    | none => simp [he] at h
    | some e =>
      simp only [he] at h
      by_cases hprev : e.prev < 0
      · simp only [hprev, ↓reduceIte] at h
        rcases ht state e he with ⟨s, hs, hsp, hst⟩ | ⟨hge, _⟩
        · have hsn : (-1 - e.prev).toNat = s := by omega
          rw [hsn] at h
          have h' := Option.some.inj h
          have hout : outward s < 4 := by
            unfold outward
            split <;> omega
          refine ⟨s, [lat.point (state / 4)], hs, ?_, ?_, rfl, trivial⟩
          · rw [← h']
            rfl
          · have : state / 4 = (sources.getD s default).vertex := by omega
            rw [this]
            rfl
        · omega
      · simp only [hprev, ↓reduceIte] at h
        obtain ⟨s, mid, hs, hpts, hhead, hlast, hch⟩ := ih e.prev.toNat _ _ h
        rcases ht state e he with ⟨s', _, hsp, _⟩ | ⟨hge, len, hstep⟩
        · omega
        · refine ⟨s, mid ++ [lat.point (state / 4)], hs, ?_, ?_, ?_, ?_⟩
          · rw [hpts]
            simp
          · cases mid with
            | nil => simp at hlast
            | cons a rest => simpa using hhead
          · simp
          · exact chain_snoc hch hlast ⟨e.prev.toNat / 4, state % 4, state / 4, len, hstep, rfl, rfl⟩

theorem seed_ok {lat : Lat} {sources : List End} (states : Nat) :
    TabOk lat sources ((List.range 4).foldl (fun (th : Tab × Heap) s =>
        relax th.1 th.2 ((sources.getD s default).vertex * 4 + outward s)
          (sources.getD s default).stub (-1 - (s : Int)))
      (Array.replicate states none, Heap.nil)).1 := by
  have key : ∀ (l : List Nat), (∀ x ∈ l, x < 4) → ∀ (th : Tab × Heap), TabOk lat sources th.1 →
      TabOk lat sources (l.foldl (fun (th : Tab × Heap) s =>
        relax th.1 th.2 ((sources.getD s default).vertex * 4 + outward s)
          (sources.getD s default).stub (-1 - (s : Int))) th).1 := by
    intro l
    induction l with
    | nil => intro _ th ht; exact ht
    | cons x xs ih =>
      intro hl th ht
      simp only [List.foldl_cons]
      refine ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _ ?_
      exact relax_ok ht (Or.inl ⟨x, hl x (List.mem_cons_self ..), rfl, rfl⟩)
  refine key _ (fun x hx => List.mem_range.mp hx) _ ?_
  intro state e he
  by_cases hlt : state < states
  · simp [hlt] at he
  · simp [hlt] at he

theorem search_spec {r : Router} {used : Used} {cur : Nat} {sources targets : List End}
    {route : List Point} {used' : Used}
    (h : search r used cur sources targets = some (route, used')) :
    ∃ (pts : List Point) (s s' : Nat) (mid : List Point), route = simplify pts ∧ s < 4 ∧ s' < 4 ∧
      pts = (sources.getD s default).port :: (mid ++ [(targets.getD s' default).port]) ∧
      mid.head? = some (r.lat.point (sources.getD s default).vertex) ∧
      mid.getLast? = some (r.lat.point (targets.getD s' default).vertex) ∧
      Chain (LatStep r.lat) mid := by
  unfold search at h
  dsimp only at h
  split at h
  · rename_i tab best heq
    have hd := dijkstra_ok (r := r) (used := used) (cur := cur) (targets := targets)
      (sources := sources) _ _ _ _ _ _ (seed_ok _) (fun b hb => by cases hb) heq
    split at h
    · rename_i pts hc
      have hs := chain_spec hd.1 _ _ _ _ hc
      obtain ⟨s, mid, hs4, hpts, hhead, hlast, hch⟩ := hs
      have hb := hd.2 best rfl
      injection h with h
      have hr := (Prod.mk.inj h).1
      refine ⟨pts, s, best.side, mid, hr.symm, hs4, hb.1, hpts, hhead, ?_, hch⟩
      rw [hlast, hb.2]
    · cases h
  · cases h

end Grid
end Elegant
