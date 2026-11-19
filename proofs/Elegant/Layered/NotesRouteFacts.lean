import Elegant.Layered.NotesFlatRouteClauses
import Elegant.Layered.VisibilityClearance
import Elegant.Layered.RouteTransport

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

 /-!
 ! # Note-stage router facts and flag/side-condition bridges (OPEN FACTS TRACKED).
 !
 ! Status: `notesEndsInBoxes_holds` and `notesFragBoxFirst_holds` are proved.
 ! The other five facts (`notesRouterOrtho`, `notesRouterEnds`, `notesFlagsKept`,
 ! `notesFlagsFragment`, `notesKeptBoxContracted`) stay as their tracked open
 ! defs in `NotesFlatRouteClauses`: the provisional `_holds` theorems that took
 ! their own conclusions as hypotheses were DELETED (no theorem may take its
 ! conclusion as a premise). The designed premise defs no proved theorem
 ! consumes were deleted with them; only `notesFragFirstWins` remains, consumed
 ! by `notesFragBoxFirst_holds`. The private `nrf_*` lemmas below are kept as
 ! proved foundations toward the router proofs. Probe evidence:
 ! `proofs/wip/Probe/NotesRouteFacts2T_probe.lean`.
 ! -/

 /-!
 ! Proof plans for the five open facts (all still valid; none is claimed here).
 ! Each witness shows the unguarded form is false, so each plan names the guard
 ! its future proof must carry.

 * `notesRouterOrtho`, `notesRouterEnds`: unconditional facts about `routeAround`
   (orthogonal output; ends on the looked-up end-rect boundaries). The path comes
   from `Visibility.Grid.shortest`, i.e. `compress (chain prev ..)` mapped through
   `Frame.output`. Invariants: every `prev` edge is an axis-aligned cleared
   neighbour step (`VisibilityClearance.PrevOK` + a dist-decrease invariant, both
   preserved by `relax`/`run`); the reconstructed chain is hence orthogonal and
   runs from a seeded start to the found end; `compress` keeps endpoints and
   orthogonality; `Frame.output` (shift+orient) preserves both; ports of the
   framed rect map back onto the boundary of the source rect.
 * `notesRouterEnds` additionally needs rect nonnegativity (deleted premise):
   on-boundary needs nonneg dims. WITNESS (unguarded form is false): `rects =
   [("a", ⟨0,0,-5,4⟩), ("b", ⟨10,0,5,4⟩)]`, route `a → b`: `routeAround` succeeds
   (grid works on any points) but no point satisfies `onBoundary · ⟨0,0,-5,4⟩`.
 * `notesFlagsKept`, `notesFlagsFragment`: need a base-side premise (deleted:
   box-id list kept, no fabricated route ids, same-id route flags/endpoints
   kept), plus ambient `WellFormed` (for route-id uniqueness), a guard that
   classified routes are input routes, and `contractOne`/fuel induction showing
   kept routes survive contraction with ends unchanged. WITNESS (unguarded form
   is false): `r = {x with orthogonal := !x.orthogonal}` for a real bundle
   route `x` (`r ∉ inp.routes`, same id/ends, flipped flag): same-bundle holds,
   the fragment route keeps `x`'s flags, goal fails.
 * `notesKeptBoxContracted`: kept ends are bundle-external by `bundleOf = none`,
   except note-box ids, which `bundleOf` never sees; needs a guard (deleted)
   that kept ends avoid every layout's note ids. WITNESS: route `t.note → o`
   with the note fragment claiming `t.note`: bundle-external by `bundleOf`,
   but claimed.
 * `notesFragBoxFirst` (proved): per-end-id first-wins `notesFragFirstWins`
   (strictly narrower than the paired conclusion). WITNESS: two fragments
   claiming one id with different shifts.

 Probes: `proofs/wip/Probe/NotesRouteFacts2T_probe.lean` evaluates Bool images
 of all seven facts on state, group, two, and empty note inputs (all true),
 rejects a note with a self-loop target with `LayoutError.domain`, and shows
 `routeAround` succeeding on that self-loop route with synthetic rects.
 -/

 /-! ### The kept premise: per-end-id first-wins -/

/-- Per-end-id first-wins: the fragment lookup for each end id agrees with any
fragment holding that box. Strictly narrower than `notesFragBoxFirst` (single
ids, no pairing). -/
def notesFragFirstWins (fragments : List Placed) (r : ModelRoute) : Prop :=
  ∀ id ∈ [r.fromId, r.toId], ∀ p ∈ fragments, ∀ b ∈ p.scene.boxes, b.id = id →
    fragments.findSome? (fun q => q.rect id) =
      some (shiftRect p.dx p.dy b.rect)

/-! ### Router foundations: counting and grid lines -/
private instance nrfLawfulHashableVertex : LawfulHashable Visibility.Vertex where
  hash_eq := fun a b h => by rw [beq_iff_eq.mp h]

/-- Dedup yields no duplicates. -/
private theorem nrf_eraseDups_nodup : ∀ (l : List Int), l.eraseDups.Nodup := by
  have aux : ∀ (n : Nat) (l : List Int), l.length ≤ n → l.eraseDups.Nodup := by
    intro n
    induction n with
    | zero =>
      intro l hl
      cases l with
      | nil => simp
      | cons a as => simp only [List.length_cons] at hl; omega
    | succ n ih =>
      intro l hl
      cases l with
      | nil => simp
      | cons a as =>
        rw [List.eraseDups_cons]
        show List.Pairwise (· ≠ ·) _
        refine List.Pairwise.cons ?_ ?_
        · intro b hb
          have hb2 := List.mem_eraseDups.mp hb
          obtain ⟨_, hb2⟩ := List.mem_filter.mp hb2
          have hne : b ≠ a := by simpa using hb2
          exact fun he => hne he.symm
        · exact ih _ (by
            have h1 := List.length_filter_le (fun b => !(b == a)) as
            simp only [List.length_cons] at hl
            omega)
  exact fun l => aux l.length l (by omega)

/-- Grid lines are deduplicated. -/
private theorem nrf_sortedLines_nodup (l : List Int) :
    (Visibility.sortedLines l).toList.Nodup := by
  unfold Visibility.sortedLines
  show ((l.mergeSort fun a b => decide (a ≤ b)).eraseDups).Nodup
  exact nrf_eraseDups_nodup _

/-- Adjacent deduped lines differ. -/
private theorem nrf_nodup_adjacent : ∀ (l : List Int), l.Nodup →
    ∀ (i : Nat) (a b : Int), l[i]? = some a → l[i + 1]? = some b → a ≠ b := by
  intro l
  induction l with
  | nil => intro _ i a b h1 _; simp at h1
  | cons x xs ih =>
    intro hn i a b h1 h2
    have hpair : (∀ a', a' ∈ xs → x ≠ a') ∧ List.Pairwise (· ≠ ·) xs := by
      have h0 : List.Pairwise (· ≠ ·) (x :: xs) := hn
      rwa [List.pairwise_cons] at h0
    cases i with
    | zero =>
      have ha : x = a := by simpa using h1
      have hb : b ∈ xs := List.mem_of_getElem? (by simpa using h2)
      intro he
      exact hpair.1 b hb (ha.trans he)
    | succ n =>
      have h1' : xs[n]? = some a := by simpa using h1
      have h2' : xs[n + 1]? = some b := by simpa using h2
      have hxs : xs.Nodup := hpair.2
      exact ih hxs n a b h1' h2'

/-- Adjacent grid lines differ (array form). -/
private theorem nrf_array_adjacent_ne (xs : Array Int) (hn : xs.toList.Nodup)
    (i : Nat) (a b : Int) (h1 : xs[i]? = some a) (h2 : xs[i + 1]? = some b) :
    a ≠ b := by
  have e1 : xs.toList[i]? = some a := by simpa using h1
  have e2 : xs.toList[i + 1]? = some b := by simpa using h2
  exact nrf_nodup_adjacent xs.toList hn i a b e1 e2

/-- Erasing a distinct element keeps members. -/
private theorem nrf_mem_erase : ∀ (a b : Visibility.Vertex) (ks : List Visibility.Vertex),
    a ∈ ks → a ≠ b → a ∈ ks.erase b := by
  intro a b ks
  induction ks with
  | nil => intro h _; simp at h
  | cons x xs ih =>
    intro hm hne
    simp only [List.erase_cons]
    split
    · rename_i hxb
      have hxb2 : x = b := beq_iff_eq.mp hxb
      rcases List.mem_cons.mp hm with rfl | hm2
      · exact absurd hxb2 hne
      · exact hm2
    · rename_i hxb
      rcases List.mem_cons.mp hm with rfl | hm2
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (ih hm2 hne)

/-- Distinct visited keys fit in the key list. -/
private theorem nrf_count : ∀ (seen ks : List Visibility.Vertex),
    seen.Nodup → (∀ u ∈ seen, u ∈ ks) → seen.length ≤ ks.length := by
  intro seen
  induction seen with
  | nil => intro ks _ _; simp
  | cons v vs ih =>
    intro ks hn hm
    have hpair : v ∉ vs ∧ vs.Nodup := by
      have h0 : List.Pairwise (· ≠ ·) (v :: vs) := hn
      rw [List.pairwise_cons] at h0
      exact ⟨fun h => h0.1 v h rfl, h0.2⟩
    have hmem : ∀ u ∈ vs, u ∈ ks.erase v := by
      intro u hu
      have hu2 : u ∈ ks := hm u (List.mem_cons_of_mem _ hu)
      have hne : u ≠ v := fun he => hpair.1 (he ▸ hu)
      exact nrf_mem_erase u v ks hu2 hne
    have ihl := ih (ks.erase v) hpair.2 hmem
    have hpos : 0 < ks.length :=
      List.length_pos_of_mem (hm v (List.mem_cons.mpr (Or.inl rfl)))
    have hlen : (ks.erase v).length = ks.length - 1 :=
      List.length_erase_of_mem (hm v (List.mem_cons.mpr (Or.inl rfl)))
    have e2 : vs.length + 1 ≤ (ks.erase v).length + 1 := Nat.add_le_add_right ihl 1
    have e3 : (ks.erase v).length + 1 = ks.length := by rw [hlen]; omega
    have e1 : List.length (v :: vs) = vs.length + 1 := rfl
    rw [e1]
    rwa [e3] at e2

/-- `Cost` equality is lawful (private; for the stale-entry check in `run`). -/
private instance nrfLawfulBEqCost : LawfulBEq Visibility.Cost where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk da ta =>
      cases b with
      | mk db tb =>
        have h2 : (da == db && ta == tb) = true := h
        rw [Bool.and_eq_true] at h2
        obtain ⟨hd, ht⟩ := h2
        have hd' : da = db := beq_iff_eq.mp hd
        have ht' : ta = tb := beq_iff_eq.mp ht
        subst hd'
        subst ht'
        rfl
  rfl := by
    intro a
    cases a with
    | mk d t =>
      show ((d == d) && (t == t)) = true
      simp

/-- `prev` edges go strictly downhill in `dist` (both ends in `dist`). -/
private def nrfPrevDist (s : Visibility.Search) : Prop :=
  ∀ (v w : Visibility.Vertex), s.prev[v]? = some w → ∃ (dv dw : Visibility.Cost),
    s.dist[v]? = some dv ∧ s.dist[w]? = some dw ∧ dw.dist < dv.dist

/-- `getElem!` agrees with a successful `getElem?`. -/
private theorem nrf_getElem!_of_getElem? : ∀ (xs : Array Int) (i : Nat) (a : Int),
    xs[i]? = some a → xs[i]! = a := by
  intro xs i a h
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, h, Option.getD_some]

/-- Adjacent grid values differ by at least one. -/
private theorem nrf_adjacent_abs_ge : ∀ (xs : Array Int) (_hn : xs.toList.Nodup)
    (i : Nat) (_hi : i + 1 < xs.size),
    1 ≤ (xs[i + 1]! - xs[i]!).natAbs := by
  intro xs hn i hi
  obtain ⟨a, ha⟩ : ∃ a, xs[i]? = some a := ⟨_, Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b, hb⟩ : ∃ b, xs[i + 1]? = some b := ⟨_, Array.getElem?_eq_getElem hi⟩
  have hne := nrf_array_adjacent_ne xs hn i a b ha hb
  have hax : xs[i]! = a := nrf_getElem!_of_getElem? _ _ _ ha
  have hbx : xs[i + 1]! = b := nrf_getElem!_of_getElem? _ _ _ hb
  rw [hax, hbx]
  have h0 : b - a ≠ 0 := by omega
  exact Int.natAbs_pos.mpr h0

/-- Neighbours have exact index forms (guards carried). -/
private theorem nrf_neighbour_form : ∀ {g : Visibility.Grid} {v w : Visibility.Vertex},
    w ∈ g.neighbours v →
    (0 < v.x ∧ w = ⟨v.x - 1, v.y, 0⟩) ∨ (v.x + 1 < g.xs.size ∧ w = ⟨v.x + 1, v.y, 0⟩) ∨
    (0 < v.y ∧ w = ⟨v.x, v.y - 1, 1⟩) ∨ (v.y + 1 < g.ys.size ∧ w = ⟨v.x, v.y + 1, 1⟩) := by
  intro g v w h
  unfold Visibility.Grid.neighbours at h
  simp only [List.mem_append, or_assoc] at h
  rcases h with h | h | h | h
  · split at h
    · rename_i hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inl ⟨hc, h⟩
    · simp at h
  · split at h
    · rename_i hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inl ⟨hc, h⟩)
    · simp at h
  · split at h
    · rename_i hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inr (Or.inl ⟨hc, h⟩))
    · simp at h
  · split at h
    · rename_i hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inr (Or.inr ⟨hc, h⟩))
    · simp at h

/-- Neighbours are distinct vertices. -/
private theorem nrf_neighbour_ne : ∀ {g : Visibility.Grid} {v w : Visibility.Vertex},
    w ∈ g.neighbours v → w ≠ v := by
  intro g v w h
  have hform := nrf_neighbour_form h
  rcases hform with ⟨hgx, rfl⟩ | ⟨hxx, rfl⟩ | ⟨hgy, rfl⟩ | ⟨hyy, rfl⟩
  · intro he
    have hx : v.x - 1 = v.x := congrArg Visibility.Vertex.x he
    omega
  · intro he
    have hx : v.x + 1 = v.x := congrArg Visibility.Vertex.x he
    omega
  · intro he
    have hy : v.y - 1 = v.y := congrArg Visibility.Vertex.y he
    omega
  · intro he
    have hy : v.y + 1 = v.y := congrArg Visibility.Vertex.y he
    omega

/-- Neighbour steps strictly increase the length cost. -/
private theorem nrf_step_pos : ∀ {g : Visibility.Grid} {v w : Visibility.Vertex},
    g.xs.toList.Nodup → g.ys.toList.Nodup →
    v.x < g.xs.size → v.y < g.ys.size → w.x < g.xs.size → w.y < g.ys.size →
    w ∈ g.neighbours v →
    ∀ (e : Visibility.Entry), e.cost.dist < (g.step v w e.cost).dist := by
  intro g v w hxn hyn hxv hyv hxw hyw hmem e
  have hform := nrf_neighbour_form hmem
  rcases hform with ⟨hgx, rfl⟩ | ⟨hxx, rfl⟩ | ⟨hgy, rfl⟩ | ⟨hyy, rfl⟩
  · have heq : v.x - 1 + 1 = v.x := by omega
    have hab := nrf_adjacent_abs_ge g.xs hxn (v.x - 1) (by omega)
    rw [heq] at hab
    have hstep : (g.step v ⟨v.x - 1, v.y, 0⟩ e.cost).dist =
        e.cost.dist + (g.xs[v.x]! - g.xs[v.x - 1]!).natAbs +
          (g.ys[v.y]! - g.ys[v.y]!).natAbs := rfl
    have hy0 : (g.ys[v.y]! - g.ys[v.y]!).natAbs = 0 := by simp
    omega
  · have hab := nrf_adjacent_abs_ge g.xs hxn v.x hxw
    have hstep : (g.step v ⟨v.x + 1, v.y, 0⟩ e.cost).dist =
        e.cost.dist + (g.xs[v.x]! - g.xs[v.x + 1]!).natAbs +
          (g.ys[v.y]! - g.ys[v.y]!).natAbs := rfl
    have hdx : 1 ≤ (g.xs[v.x]! - g.xs[v.x + 1]!).natAbs := by
      have hneg : (g.xs[v.x]! - g.xs[v.x + 1]!) = -((g.xs[v.x + 1]! - g.xs[v.x]!)) := by omega
      rw [hneg, Int.natAbs_neg]; exact hab
    have hy0 : (g.ys[v.y]! - g.ys[v.y]!).natAbs = 0 := by simp
    omega
  · have heq : v.y - 1 + 1 = v.y := by omega
    have hab := nrf_adjacent_abs_ge g.ys hyn (v.y - 1) (by omega)
    rw [heq] at hab
    have hstep : (g.step v ⟨v.x, v.y - 1, 1⟩ e.cost).dist =
        e.cost.dist + (g.xs[v.x]! - g.xs[v.x]!).natAbs +
          (g.ys[v.y]! - g.ys[v.y - 1]!).natAbs := rfl
    have hx0 : (g.xs[v.x]! - g.xs[v.x]!).natAbs = 0 := by simp
    omega
  · have hab := nrf_adjacent_abs_ge g.ys hyn v.y hyw
    have hstep : (g.step v ⟨v.x, v.y + 1, 1⟩ e.cost).dist =
        e.cost.dist + (g.xs[v.x]! - g.xs[v.x]!).natAbs +
          (g.ys[v.y]! - g.ys[v.y + 1]!).natAbs := rfl
    have hdy : 1 ≤ (g.ys[v.y]! - g.ys[v.y + 1]!).natAbs := by
      have hneg : (g.ys[v.y]! - g.ys[v.y + 1]!) = -((g.ys[v.y + 1]! - g.ys[v.y]!)) := by omega
      rw [hneg, Int.natAbs_neg]; exact hab
    have hx0 : (g.xs[v.x]! - g.xs[v.x]!).natAbs = 0 := by simp
    omega




/-- Neighbours of an in-bounds vertex are in-bounds. -/
private theorem nrf_neighbour_bounds : ∀ {g : Visibility.Grid} {v w : Visibility.Vertex},
    w ∈ g.neighbours v → v.x < g.xs.size → v.y < g.ys.size →
    w.x < g.xs.size ∧ w.y < g.ys.size := by
  intro g v w hmem hxv hyv
  have hform := nrf_neighbour_form hmem
  rcases hform with ⟨hgx, rfl⟩ | ⟨hxx, rfl⟩ | ⟨hgy, rfl⟩ | ⟨hyy, rfl⟩ <;> dsimp only <;> omega

/-- Inserting a distinct key leaves other lookups unchanged. -/
private theorem nrf_insert_ne : ∀ {β : Type} (m : Std.HashMap Visibility.Vertex β)
    (nxt a : Visibility.Vertex) (c : β),
    nxt ≠ a → (m.insert nxt c)[a]? = m[a]? := by
  intro β m nxt a c hne
  rw [Std.HashMap.getElem?_insert]
  split
  · rename_i hcon
    exact absurd (beq_iff_eq.mp hcon) hne
  · rfl

/-- Inserting a key sets its lookup. -/
private theorem nrf_insert_eq : ∀ {β : Type} (m : Std.HashMap Visibility.Vertex β)
    (k : Visibility.Vertex) (c : β), (m.insert k c)[k]? = some c := by
  intro β m k c
  rw [Std.HashMap.getElem?_insert]
  split
  · rename_i _
    rfl
  · rename_i hcon
    simp at hcon


/-- Every `dist` entry is seeded or has a `prev` link. -/
private def nrfSeededOrPrev (g : Visibility.Grid) (starts : List Point)
    (s : Visibility.Search) : Prop :=
  ∀ v c, s.dist[v]? = some c →
    (∃ p ∈ starts, g.inside p = true ∧ g.vertexAt p = some v) ∨
    ∃ w, s.prev[v]? = some w

/-- Every frontier vertex is in-bounds. -/
private def nrfFrontierBounds (g : Visibility.Grid) (s : Visibility.Search) : Prop :=
  ∀ e ∈ s.frontier, e.vertex.x < g.xs.size ∧ e.vertex.y < g.ys.size


 /-! ### The two proved facts -/

theorem notesEndsInBoxes_holds {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) : notesEndsInBoxes inp := by
  intro r hr
  have h := (wellFormed_iff (inputModel inp o)).mp hwf
  obtain ⟨_, _, _, _, hroutes, _, _⟩ := h
  obtain ⟨hf, ht⟩ := hroutes r hr
  simp only [inputModel] at hf ht
  exact ⟨by simpa [List.contains_eq_mem] using hf, by simpa [List.contains_eq_mem] using ht⟩

theorem notesFragBoxFirst_holds {fragments : List Placed} {r : ModelRoute}
    (hfirst : notesFragFirstWins fragments r) :
    notesFragBoxFirst fragments r := by
  intro p hp fb0 hmem0f tb0 hmem0t hfb htb
  have e1 := hfirst r.fromId (by simp) p hp fb0 hmem0f hfb
  have e2 := hfirst r.toId (by simp) p hp tb0 hmem0t htb
  rw [← hfb] at e1
  rw [← htb] at e2
  exact ⟨e1, e2⟩

end PipelineImpl
end Layered
end Elegant
