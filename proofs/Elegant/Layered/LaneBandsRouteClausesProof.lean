import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsCoverage
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-! Clause transport of `pinBands` for C4 (routes are orthogonal polylines)
and C5 (route endpoints sit on their endpoint boxes' boundaries).

Phase plan, one named lemma per phase:

* `applyPin`: `applyPin_c4_map` reads every pinned route back to its base
  route (same ids, same orthogonal flag, points unchanged or mapped through
  `routeMove`); `applyPin_c5_box` reads every non frame pinned box back to
  its shifted base box; `applyPin_c5` keeps C5 through the pin.
* `rerouteBands`: `c4c5_reroute_mem` splits every routed route into a kept
  route (same points, with its keep reason) or a freshly re-routed one
  (with its `routeEnds`/`findRoute` witnesses); `rerouteBands_c4` and
  `rerouteBands_c5` close the two clauses using the kept reasons and the
  two `findRoute` residuals below.
* `relocateLabels`, `growCanvas`: routes and boxes are untouched, so both
  clauses transfer by dump equalities.
* `restoreOrigin`: a uniform shift, so orthogonality transfers through
  `isOrthogonal_mapM_move` and boundary attachment through
  `onBoundary_crossShift`.

Residuals (about `findRoute` alone, restricted to ends built by
`routeEnds`; the unrestricted forms are false): `FindRouteOrthoPin` and
`FindRouteEndsPin`. Both are used by the reroute lemmas. `PinDeltaBad` is
not assumed anywhere: the excluded cases (band frame endpoints,
degenerate or duplicate route ids, ends collapse) do not occur on the
executed swimlane layouts probed alongside this file. -/

/-! ## Local copies (renamed; the originals are private or live in
`LaneBandsClearance`, which this file must not import). -/

private theorem c4c5_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem c4c5_find?_idx {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a →
      ∃ j : Nat, l[j]? = some a ∧ p a = true ∧
        ∀ k, k < j → ∀ y, l[k]? = some y → p y = false := by
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons x xs ih =>
    intro a h
    rw [List.find?_cons] at h
    cases hpx : p x with
    | true =>
      simp [hpx] at h
      subst h
      refine ⟨0, rfl, hpx, ?_⟩
      intro k hk _ _
      simp at hk
    | false =>
      simp [hpx] at h
      obtain ⟨j, hjget, hjp, hj4⟩ := ih a h
      refine ⟨j + 1, ?_, hjp, ?_⟩
      · rw [List.getElem?_cons_succ]
        exact hjget
      · intro k hk y hy
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero] at hy
          cases hy
          exact hpx
        | succ k' =>
          rw [List.getElem?_cons_succ] at hy
          exact hj4 k' (by omega) _ hy

private theorem c4c5_find?_ex {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∃ a, a ∈ l ∧ p a = true) →
      ∃ a, l.find? p = some a := by
  intro l
  induction l with
  | nil => intro ⟨a, ha, _⟩; cases ha
  | cons x xs ih =>
    intro ⟨a, ha, hp⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [List.find?_cons]
      cases hpx : p a with
      | true => exact ⟨a, rfl⟩
      | false => rw [hpx] at hp; cases hp
    · obtain ⟨b, hb⟩ := ih ⟨a, ha', hp⟩
      rw [List.find?_cons]
      cases hpx : p x with
      | true => exact ⟨x, rfl⟩
      | false => exact ⟨b, hb⟩

private theorem c4c5_findIdx?_of_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true → ∃ i, l.findIdx? p = some i := by
  intro l
  induction l with
  | nil => intro a ha _; cases ha
  | cons x xs ih =>
    intro a ha hp
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha'
    · exact ⟨0, by simp only [List.findIdx?_cons, hp, ↓reduceIte]⟩
    · cases hpx : p x with
      | true =>
        exact ⟨0, by simp only [List.findIdx?_cons, hpx, ↓reduceIte]⟩
      | false =>
        obtain ⟨i, hi⟩ := ih a ha' hp
        exact ⟨i + 1, by simp only [List.findIdx?_cons, hpx, Bool.false_eq_true,
          ↓reduceIte, hi, Option.map_some]⟩

private theorem c4c5_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
    {l : List α} (h : (l.map g).Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hgx : g x = g y) : x = y := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hnot, htail⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨y, hy', hgx.symm⟩
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exfalso
        apply hnot
        rw [List.mem_map]
        exact ⟨x, hx', hgx⟩
      · exact ih htail hx' hy'

private theorem c4c5_headD_of_head? {α : Type} [Inhabited α] {l : List α} {p d : α}
    (h : l.head? = some p) : l.headD d = p := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    have hx : x = p := by simpa using h
    show x = p
    exact hx

private theorem c4c5_findIdx_lookup {α : Type} (l : List α) (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩

private theorem c4c5_find_of_findIdx {α : Type} (l : List α) (p : α → Bool) (i : Nat)
    (x : α) (hi : l.findIdx? p = some i) (hx : l[i]? = some x) :
    l.find? p = some x := by
  induction l generalizing i with
  | nil => rw [List.findIdx?_nil] at hi; exact absurd hi (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at hi
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at hi
      cases i with
      | zero =>
        have hxy : y = x := by simpa using hx
        subst hxy
        show (match p y with | true => some y | false => List.find? p ys) = some y
        rw [hp]
      | succ j' => exact absurd hi (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at hi
      cases i with
      | zero => exact absurd hi (by simp)
      | succ j' =>
        have hys : ys.findIdx? p = some j' := by simpa using hi
        have hxs : ys[j']? = some x := by simpa using hx
        simp only [List.find?_cons, hp]
        exact ih j' hys hxs

private theorem c4c5_getLast?_some {α : Type} (a : α) (l : List α) :
    ∃ b, (a :: l).getLast? = some b := by
  induction l generalizing a with
  | nil => exact ⟨a, by simp⟩
  | cons y ys ih =>
    have h := ih y
    have heq : (a :: y :: ys).getLast? = (y :: ys).getLast? := by simp
    rw [heq]
    exact h

private theorem c4c5_mapM_point_head {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.head? = some p →
        ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := c4c5_bind h
    obtain ⟨rest', hrest, hrfl⟩ := c4c5_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

private theorem c4c5_mapM_point_getLast? {m : Move} {axis : Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs →
      ∀ p, ps.getLast? = some p →
        ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := c4c5_bind h
    obtain ⟨rest', hrest, hrfl⟩ := c4c5_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at hrest
      subst hrest
      have hpx : p = x := by
        have hgl : (x :: []).getLast? = some x := rfl
        rw [hgl] at hp
        exact (Option.some.inj hp).symm
      subst hpx
      exact ⟨x', rfl, hx'⟩
    | cons y ys =>
      obtain ⟨q, hq, hfun⟩ := ih rest' hrest p hp
      refine ⟨q, ?_, hfun⟩
      rw [List.getLast?_cons, hq]
      rfl

private theorem c4c5_mapIdx_kept_get (place : Rect → Rect) (idx : Nat) :
    ∀ (l : List Box) (n k : Nat), k + n ≠ idx → ∀ (b : Box), l[k]? = some b →
    (l.mapIdx fun j b => if j + n = idx then ({ b with rect := place b.rect } : Box) else b)[k]? = some b := by
  intro l
  induction l with
  | nil =>
    intro n k hk b hbk
    have hlt := (List.getElem?_eq_some_iff.mp hbk).1
    simp at hlt
  | cons head tail ih =>
    intro n k hk b hbk
    cases k with
    | zero =>
      have hhead : head = b := by
        rw [List.getElem?_cons_zero] at hbk
        exact Option.some.inj hbk
      subst hhead
      rw [List.mapIdx_cons, List.getElem?_cons_zero]
      show (if 0 + n = idx then ({ head with rect := place head.rect } : Box) else head) = some head
      rw [ite_eq_right hk]
    | succ k' =>
      rw [List.mapIdx_cons] at ⊢
      rw [List.getElem?_cons_succ] at hbk
      rw [List.getElem?_cons_succ] at ⊢
      show ((tail.mapIdx fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b)[k']? = some b)
      have heq : (fun i b => if i + 1 + n = idx then ({ b with rect := place b.rect } : Box) else b) =
          (fun j b => if j + (n + 1) = idx then ({ b with rect := place b.rect } : Box) else b) := by
        funext j b
        have h : j + 1 + n = j + (n + 1) := by omega
        rw [h]
      rw [heq]
      exact ih (n + 1) k' (by omega) b hbk

private theorem c4c5_replaceFrame_kept {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') (b : Box) (hb : b ∈ s.boxes)
    (hne : b.id ≠ band.id) :
    ∃ b' ∈ s'.boxes, b'.id = b.id ∧ b'.rect = b.rect ∧ b'.parent = b.parent ∧
      b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl⟩
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok start =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok thickness =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb
        have hkk : k + 0 ≠ idx := by
          intro hkk
          have hkz : k = idx := by omega
          rw [hkz] at hk
          obtain ⟨x, hx, hpx⟩ := c4c5_findIdx_lookup s.boxes _ idx hfind
          rw [hk] at hx
          have hbx : b = x := Option.some.inj hx
          have hbe : b.id = band.id := by rw [hbx]; exact beq_iff_eq.mp hpx
          exact hne hbe
        have hkept := c4c5_mapIdx_kept_get (placeRect axis start thickness) idx s.boxes 0 k hkk b hk
        have hmem : b ∈ s'.boxes := by
          rw [← h]
          exact List.mem_iff_getElem?.mpr ⟨k, hkept⟩
        exact ⟨b, hmem, rfl, rfl, rfl, rfl, rfl⟩

private theorem c4c5_mapM_zip_mem {α β γ : Type} (f : α × β → Except LayoutError γ)
    (l₁ : List α) (l₂ : List β) (out : List γ)
    (h : (l₁.zip l₂).mapM f = .ok out) (x : γ) (hx : x ∈ out) :
    ∃ a ∈ l₁, ∃ b ∈ l₂, (a, b) ∈ l₁.zip l₂ ∧ f (a, b) = .ok x := by
  induction l₁ generalizing l₂ out with
  | nil =>
    have hzip : ([] : List α).zip l₂ = [] := rfl
    rw [hzip] at h
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hx
  | cons a as ih =>
    cases l₂ with
    | nil =>
      have hzip : (a :: as).zip ([] : List β) = [] := rfl
      rw [hzip] at h
      simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp at hx
    | cons b bs =>
      simp only [List.zip_cons_cons] at h
      rw [List.mapM_cons] at h
      obtain ⟨y, hfy, hrest⟩ := c4c5_bind h
      obtain ⟨tl, htl, hpure⟩ := c4c5_bind hrest
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
      subst hpure
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp only [List.zip_cons_cons]
        exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, List.mem_cons_self, hfy⟩
      · obtain ⟨a', ha', b', hb', hpair, hf⟩ := ih _ _ htl hx
        refine ⟨a', List.mem_cons_of_mem a ha', b', List.mem_cons_of_mem b hb', ?_, hf⟩
        simp only [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hpair

private theorem c4c5_foldKeptBox (bands : List Band) (axis : Axis) (s : Scene) :
    ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    ∀ b ∈ s.boxes, (∀ band ∈ bands, band.id ≠ b.id) →
    ∃ b' ∈ s'.boxes, b'.id = b.id ∧ b'.rect = b.rect ∧ b'.parent = b.parent ∧
      b'.role = b.role ∧ b'.exclusive = b.exclusive := by
  induction bands generalizing s with
  | nil =>
    intro s' h b hb _
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl⟩
  | cons band rest ih =>
    intro s' h b hb hnf
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := c4c5_bind h
    have hband : b.id ≠ band.id := Ne.symm (hnf band List.mem_cons_self)
    obtain ⟨bm, hbmm, hidm, hrectm, hparm, hrolem, hexclm⟩ :=
      c4c5_replaceFrame_kept hmid b hb hband
    have hrest' : ∀ band' ∈ rest, band'.id ≠ bm.id := by
      intro band' hmem
      rw [hidm]
      exact hnf band' (List.mem_cons_of_mem band hmem)
    obtain ⟨b', hb', hid', hrect', hpar', hrole', hexcl'⟩ :=
      ih mid s' hrest bm hbmm hrest'
    exact ⟨b', hb', hid'.trans hidm, hrect'.trans hrectm, hpar'.trans hparm,
      hrole'.trans hrolem, hexcl'.trans hexclm⟩

private theorem c4c5_replaceFrame_rev {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') (b' : Box) (hb' : b' ∈ s'.boxes)
    (hne : b'.id ≠ band.id) :
    ∃ b ∈ s.boxes, b'.id = b.id ∧ b'.rect = b.rect := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨b', hb', rfl, rfl⟩
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok start =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok thickness =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        rw [← h] at hb'
        simp only at hb'
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hb'
        have hlen : (s.boxes.mapIdx fun j b =>
            if j = idx then ({ b with rect :=
              (placeRect axis start thickness) b.rect } : Box) else b).length =
            s.boxes.length := List.length_mapIdx
        have hklen : k < s.boxes.length := by
          have := (List.getElem?_eq_some_iff.mp hk).1
          omega
        have hbk : s.boxes[k]? = some s.boxes[k] := List.getElem?_eq_getElem hklen
        have hmap := List.getElem?_mapIdx (f := fun j b =>
          if j = idx then ({ b with rect :=
            (placeRect axis start thickness) b.rect } : Box) else b)
          (l := s.boxes) (i := k)
        rw [hk, hbk] at hmap
        simp only [Option.map_some] at hmap
        by_cases hkk : k = idx
        · have hkk2 : idx = k := hkk.symm
          subst hkk2
          obtain ⟨x, hx, hpx⟩ := c4c5_findIdx_lookup s.boxes _ idx hfind
          rw [hbk] at hx
          have hbx : s.boxes[idx] = x := Option.some.inj hx
          rw [ite_eq_left rfl] at hmap
          have hbeq2 := Option.some.inj hmap
          have hid : s.boxes[idx].id = band.id := by
            rw [hbx]
            exact beq_iff_eq.mp hpx
          have hproj : b'.id = s.boxes[idx].id := by rw [hbeq2]
          have hbid : b'.id = band.id := hproj.trans hid
          exact absurd hbid hne
        · rw [ite_eq_right hkk] at hmap
          have hbeq : b' = s.boxes[k] := Option.some.inj hmap
          exact ⟨s.boxes[k], List.mem_iff_getElem.mpr ⟨k, hklen, rfl⟩,
            by rw [hbeq], by rw [hbeq]⟩

private theorem c4c5_foldRevBox (bands : List Band) (axis : Axis) (s : Scene) :
    ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    ∀ b' ∈ s'.boxes, (∀ band ∈ bands, band.id ≠ b'.id) →
    ∃ b ∈ s.boxes, b'.id = b.id ∧ b'.rect = b.rect := by
  induction bands generalizing s with
  | nil =>
    intro s' h b' hb' _
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨b', hb', rfl, rfl⟩
  | cons band rest ih =>
    intro s' h b' hb' hnf
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := c4c5_bind h
    have hrest' : ∀ band' ∈ rest, band'.id ≠ b'.id := fun band' hmem =>
      hnf band' (List.mem_cons_of_mem band hmem)
    obtain ⟨bm, hbmm, hidm, hrectm⟩ := ih mid s' hrest b' hb' hrest'
    have hband : bm.id ≠ band.id := by
      rw [← hidm]
      exact Ne.symm (hnf band List.mem_cons_self)
    obtain ⟨b, hbm, hid, hrect⟩ := c4c5_replaceFrame_rev hmid bm hbmm hband
    exact ⟨b, hbm, hidm.trans hid, hrectm.trans hrect⟩

/-! ## Residuals: the two `findRoute` obligations, restricted to ends built
by `routeEnds` (the unrestricted forms are false). -/

/-- Residual for C4: a polyline returned by the grid search is orthogonal,
for ends built by `routeEnds`. -/
def FindRouteOrthoPin : Prop :=
  ∀ (axis : Axis) (sp : Spacing) (pin : Pin) (fb tb : Box)
    (original : List Point) (ends : RouteEnds)
    (obs : List Obstacle) (bend : Int) (pts : List Point),
    routeEnds axis sp pin fb tb original = .ok ends →
    findRoute axis ends obs bend [sp.slot, 0] = .ok pts →
    Polyline.isOrthogonal pts = true

/-- Residual for C5: a polyline returned by the grid search keeps the
route ends, for ends built by `routeEnds`. -/
def FindRouteEndsPin : Prop :=
  ∀ (axis : Axis) (sp : Spacing) (pin : Pin) (fb tb : Box)
    (original : List Point) (ends : RouteEnds)
    (obs : List Obstacle) (bend : Int) (pts : List Point),
    routeEnds axis sp pin fb tb original = .ok ends →
    findRoute axis ends obs bend [sp.slot, 0] = .ok pts →
    pts.head? = some ends.source ∧ pts.getLast? = some ends.target

/-! ## `buildPin` entry consequences. -/

/-- A found route delta is the canonical `buildPin` entry of its route:
band shifts at both ends and the endpoint cross coordinates. -/
theorem c4c5_route_deltas {axis : Axis} {bands : List Band} {s : Scene}
    {r : Route} {d : RouteDelta}
    (hr : r ∈ s.routes) (hnodup : (s.routes.map (·.id)).Nodup)
    (hd : (buildPin axis bands s).route r.id = some d) :
    d.fromDelta = bandShift bands r.fromId ∧ d.toDelta = bandShift bands r.toId ∧
    d.first = axis.point (r.points.head?.getD ⟨0, 0⟩) ∧
    d.last = axis.point (r.points.getLast?.getD ⟨0, 0⟩) := by
  unfold Pin.route buildPin at hd
  obtain ⟨r2, hr2, hr2e⟩ :=
    List.mem_filterMap.mp (List.mem_of_find?_eq_some hd)
  cases hh2 : r2.points.head? with
  | none => simp [hh2] at hr2e
  | some f2 =>
    cases hl2 : r2.points.getLast? with
    | none => simp [hh2, hl2] at hr2e
    | some l2 =>
      rw [hh2, hl2] at hr2e
      dsimp only at hr2e
      obtain ⟨j, hjget, hjpred, _⟩ := c4c5_find?_idx _ _ _ hd
      have hdid : d.id = r.id := beq_iff_eq.mp hjpred
      have hdeq : d =
          ⟨r2.id, bandShift bands r2.fromId, bandShift bands r2.toId,
            axis.point f2, axis.point l2⟩ := (Option.some.inj hr2e).symm
      have hid2 : d.id = r2.id := by rw [hdeq]
      have heq : r2 = r :=
        c4c5_nodup_map_inj (·.id) hnodup hr2 hr (hid2.symm.trans hdid)
      rw [heq] at hh2 hl2 hdeq
      have hhd : r.points.head?.getD ⟨0, 0⟩ = f2 := by simp [hh2]
      have hgd : r.points.getLast?.getD ⟨0, 0⟩ = l2 := by simp [hl2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hdeq]
      · rw [hdeq]
      · rw [hdeq, hhd]
      · rw [hdeq, hgd]

/-- A route with no `buildPin` entry is empty. -/
theorem c4c5_pinRoute_none_empty {axis : Axis} {bands : List Band} {s : Scene}
    {r : Route} (hr : r ∈ s.routes)
    (h : (buildPin axis bands s).route r.id = none) : r.points = [] := by
  unfold Pin.route buildPin at h
  cases hp : r.points with
  | nil => rfl
  | cons first rest =>
    have hmem : (⟨r.id, bandShift bands r.fromId, bandShift bands r.toId,
        axis.point first,
        axis.point ((first :: rest).getLast?.getD ⟨0, 0⟩)⟩ : RouteDelta) ∈
        (s.routes.filterMap fun r =>
          match r.points.head?, r.points.getLast? with
          | some f, some l =>
            some ⟨r.id, bandShift bands r.fromId, bandShift bands r.toId,
              axis.point f, axis.point l⟩
          | _, _ => none) := by
      apply List.mem_filterMap.mpr
      refine ⟨r, hr, ?_⟩
      have hh : r.points.head? = some first := by simp [hp]
      have hl : r.points.getLast? = some ((first :: rest).getLast?.getD ⟨0, 0⟩) := by
        cases hgl : (first :: rest).getLast? with
        | none => rw [List.getLast?_eq_none_iff] at hgl; simp at hgl
        | some l => rw [hp, hgl, Option.getD_some]
      simp only [hh, hl]
    obtain ⟨d, hd⟩ := c4c5_find?_ex (fun d : RouteDelta => d.id == r.id) _ ⟨_, hmem, beq_self_eq_true _⟩
    have hcontra : some d = none := hd.symm.trans h
    cases hcontra

/-- Same-band endpoints share one shift. -/
theorem c4c5_sameBand_shift {bands : List Band} {fromId toId : String} {fi : Nat}
    (hfi : bands.findIdx? (fun b => b.id == fromId || b.members.contains fromId) = some fi)
    (hti : bands.findIdx? (fun b => b.id == toId || b.members.contains toId) = some fi) :
    bandShift bands fromId = bandShift bands toId := by
  obtain ⟨x, hx, hpx⟩ := c4c5_findIdx_lookup bands _ fi hfi
  obtain ⟨y, hy, hpy⟩ := c4c5_findIdx_lookup bands _ fi hti
  have hfx : bands.find? (fun b => b.id == fromId || b.members.contains fromId) = some x :=
    c4c5_find_of_findIdx bands _ fi x hfi hx
  have hfy : bands.find? (fun b => b.id == toId || b.members.contains toId) = some y :=
    c4c5_find_of_findIdx bands _ fi y hti hy
  have hxy : x = y := by rw [hx] at hy; exact Option.some.inj hy
  unfold bandShift
  rw [hfx, hfy, hxy]

/-! ## Phase `applyPin`: route and non frame box correspondence. -/

/-- Every pinned route comes from a base route with the same ids and
orthogonal flag, with points unchanged or mapped through `routeMove`. -/
theorem applyPin_c4_map {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned)
    {i : Nat} (_hiP : i < pinned.routes.length) (hiS : i < s.routes.length)
    {rP rB : Route} (hP : pinned.routes[i]? = some rP) (hB : s.routes[i]? = some rB) :
    rP.id = rB.id ∧ rP.fromId = rB.fromId ∧ rP.toId = rB.toId ∧
    rP.orthogonal = rB.orthogonal ∧
    ((pin.route rP.id = none ∧ rP.points = rB.points) ∨ ∃ d, pin.route rP.id = some d ∧
      rB.points.mapM ((routeMove d).point pin.axis) = .ok rP.points) := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
    hboxes, hlabels, hroutes, hitems, hfold⟩ := applyPin_shifted h
  have hrr : pinned.routes = shiftedRoutes := foldlM_replaceFrame_routes hfold
  have hspec := mapM_except_spec _ s.routes shiftedRoutes hroutes
  have hlen := hspec.1
  have hiS' : i < shiftedRoutes.length := by omega
  rw [hrr] at hP
  obtain ⟨a, b, ha, hb, hfab⟩ := hspec.2 i hiS hiS'
  have haE : a = rB := Option.some.inj (ha.symm.trans hB)
  have hbE : b = rP := Option.some.inj (hb.symm.trans hP)
  rw [haE, hbE] at hfab
  cases hroute : pin.route rB.id with
  | none =>
    simp only [hroute, Pure.pure, Except.pure, Except.ok.injEq] at hfab
    have hEq : rP = rB := hfab.symm
    subst hEq
    exact ⟨rfl, rfl, rfl, rfl, Or.inl ⟨hroute, rfl⟩⟩
  | some d =>
    simp only [hroute] at hfab
    obtain ⟨pts, hpts, hrfl⟩ := c4c5_bind hfab
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    exact ⟨rfl, rfl, rfl, rfl, Or.inr ⟨d, hroute, hpts⟩⟩

/-- A non frame pinned box is its shifted base box. -/
theorem applyPin_c5_box {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned)
    (b' : Box) (hb' : b' ∈ pinned.boxes)
    (hnf : ∀ band ∈ bands, band.id ≠ b'.id) :
    ∃ b ∈ s.boxes, ∃ w, b'.id = b.id ∧
      Measure.checkedI32 (pin.axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
      b'.rect = pin.axis.withStart b.rect w ∧ w = pin.axis.start b.rect + pin.boxDelta b.id := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
    hboxes, hlabels, hroutes, hitems, hfold⟩ := applyPin_shifted h
  obtain ⟨bm, hbmm, hidm, hrectm⟩ :=
    c4c5_foldRevBox bands pin.axis _ pinned hfold b' hb' hnf
  obtain ⟨b, hbm, hid, _, w, hw, hrectb, hval⟩ :=
    pinShiftBoxes_mem s.boxes pin pin.axis shiftedBoxes hboxes bm hbmm
  exact ⟨b, hbm, w, hidm.trans hid, hw, hrectm.trans hrectb, hval⟩

/-- A base endpoint box has a pinned box with the same id. -/
theorem c4c5_pinned_box_some {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned) (fid : String)
    (hex : ∃ bx ∈ s.boxes, bx.id = fid) :
    (pinned.boxes.find? (fun b => b.id == fid)).isSome = true := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems,
    hboxes, hlabels, hroutes, hitems, hfold⟩ := applyPin_shifted h
  obtain ⟨_, hid1, _, _, _⟩ :=
    pinShiftBoxes_maps s.boxes pin pin.axis shiftedBoxes hboxes
  obtain ⟨_, hid2, _, _, _, _, _, _⟩ :=
    foldReplaceFrame_all bands pin.axis _ pinned hfold
  have hid2' : pinned.boxes.map (·.id) = shiftedBoxes.map (·.id) := hid2
  obtain ⟨bx, hbxmem, hbxid⟩ := hex
  have hmem : fid ∈ pinned.boxes.map (·.id) := by
    rw [hid2', hid1]
    exact List.mem_map.mpr ⟨bx, hbxmem, hbxid⟩
  obtain ⟨bp, hbpm, hbid⟩ := List.mem_map.mp hmem
  have hbid' : bp.id = fid := hbid
  obtain ⟨a, ha⟩ := c4c5_find?_ex (fun b : Box => b.id == fid) _ ⟨bp, hbpm, beq_iff_eq.mpr hbid'⟩
  have hsome : (pinned.boxes.find? (fun b => b.id == fid)).isSome = true := by
    rw [ha]
    rfl
  exact hsome
/-! ## Phase `applyPin` keeps C5. -/

theorem applyPin_c5 {axis : Axis} {bands : List Band} {s pinned : Scene}
    (h : applyPin (buildPin axis bands s) bands s = .ok pinned)
    (hC5 : Validator.C5 s.layoutDump)
    (hnodupR : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hEnds : ∀ rt ∈ s.routes,
      bandShift bands rt.fromId = bandShift bands rt.toId ∨
      (axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
        axis.point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hNoBandEnds : ∀ rt ∈ s.routes, ∀ b ∈ bands,
      b.id ≠ rt.fromId ∧ b.id ≠ rt.toId) :
    Validator.C5 pinned.layoutDump := by
  have hax : (buildPin axis bands s).axis = axis := rfl
  intro rP hrP
  obtain ⟨i, hiP, rfl⟩ := List.mem_iff_getElem.mp hrP
  have hlen : pinned.routes.length = s.routes.length := by
    obtain ⟨_, _, shiftedRoutes, _, _, _, hroutes, _, hfold⟩ := applyPin_shifted h
    have hrr : pinned.routes = shiftedRoutes := foldlM_replaceFrame_routes hfold
    have hlen2 := (mapM_except_spec _ s.routes shiftedRoutes hroutes).1
    rw [hrr]
    exact hlen2
  have hiS : i < s.routes.length := by
    have hld : pinned.layoutDump.routes.length = pinned.routes.length := rfl
    omega
  have hP : pinned.routes[i]? = some pinned.routes[i] :=
    List.getElem?_eq_some_iff.mpr ⟨hiP, rfl⟩
  have hB : s.routes[i]? = some s.routes[i] :=
    List.getElem?_eq_some_iff.mpr ⟨hiS, rfl⟩
  have hrBmem : s.routes[i] ∈ s.routes :=
    List.mem_iff_getElem.mpr ⟨i, hiS, rfl⟩
  obtain ⟨hid, hfrom, hto, _, hmapOr⟩ := applyPin_c4_map h hiP hiS hP hB
  have hrBD : s.routes[i] ∈ s.layoutDump.routes := hrBmem
  obtain ⟨p, q, fb0, tb0, hp, hq, hfb0, htb0, hb1, hb2⟩ := hC5 s.routes[i] hrBD
  have hfb0F : s.boxes.find? (fun b => b.id == s.routes[i].fromId) = some fb0 := hfb0
  have htb0F : s.boxes.find? (fun b => b.id == s.routes[i].toId) = some tb0 := htb0
  have hfb0M : fb0 ∈ s.boxes := List.mem_of_find?_eq_some hfb0F
  have htb0M : tb0 ∈ s.boxes := List.mem_of_find?_eq_some htb0F
  obtain ⟨_, _, hjpredF, _⟩ := c4c5_find?_idx _ _ _ hfb0F
  obtain ⟨_, _, hjpredT, _⟩ := c4c5_find?_idx _ _ _ htb0F
  have hfb0id : fb0.id = s.routes[i].fromId := beq_iff_eq.mp hjpredF
  have htb0id : tb0.id = s.routes[i].toId := beq_iff_eq.mp hjpredT
  have hnfF : ∀ band ∈ bands, band.id ≠ pinned.routes[i].fromId := by
    intro band hbm
    have hne := (hNoBandEnds s.routes[i] hrBmem band hbm).1
    rw [hfrom]
    exact hne
  have hnfT : ∀ band ∈ bands, band.id ≠ pinned.routes[i].toId := by
    intro band hbm
    have hne := (hNoBandEnds s.routes[i] hrBmem band hbm).2
    rw [hto]
    exact hne
  have hpbF : ∃ bx ∈ s.boxes, bx.id = pinned.routes[i].fromId :=
    ⟨fb0, hfb0M, by rw [hfb0id, ← hfrom]⟩
  have hpbT : ∃ bx ∈ s.boxes, bx.id = pinned.routes[i].toId :=
    ⟨tb0, htb0M, by rw [htb0id, ← hto]⟩
  have hsomeF := c4c5_pinned_box_some h pinned.routes[i].fromId hpbF
  have hsomeT := c4c5_pinned_box_some h pinned.routes[i].toId hpbT
  obtain ⟨bpF, hbpF⟩ := Option.isSome_iff_exists.mp hsomeF
  obtain ⟨bpT, hbpT⟩ := Option.isSome_iff_exists.mp hsomeT
  have hbpFM : bpF ∈ pinned.boxes := List.mem_of_find?_eq_some hbpF
  have hbpTM : bpT ∈ pinned.boxes := List.mem_of_find?_eq_some hbpT
  obtain ⟨_, _, hjpredBF, _⟩ := c4c5_find?_idx _ _ _ hbpF
  obtain ⟨_, _, hjpredBT, _⟩ := c4c5_find?_idx _ _ _ hbpT
  have hbpFid : bpF.id = pinned.routes[i].fromId := beq_iff_eq.mp hjpredBF
  have hbpTid : bpT.id = pinned.routes[i].toId := beq_iff_eq.mp hjpredBT
  obtain ⟨bF, hbFmem, wF, hidbF, hwF, hrectbF, hvalF⟩ :=
    applyPin_c5_box h bpF hbpFM (by rw [hbpFid]; exact hnfF)
  obtain ⟨bT, hbTmem, wT, hidbT, hwT, hrectbT, hvalT⟩ :=
    applyPin_c5_box h bpT hbpTM (by rw [hbpTid]; exact hnfT)
  have hbidF : bF.id = s.routes[i].fromId := by rw [← hidbF, hbpFid, hfrom]
  have hbidT : bT.id = s.routes[i].toId := by rw [← hidbT, hbpTid, hto]
  have hbeqF : bF = fb0 :=
    c4c5_nodup_map_inj (·.id) hnodupB hbFmem hfb0M (by rw [hbidF, hfb0id])
  have hbeqT : bT = tb0 :=
    c4c5_nodup_map_inj (·.id) hnodupB hbTmem htb0M (by rw [hbidT, htb0id])
  have hshiftF : (buildPin axis bands s).boxDelta bF.id =
      bandShift bands s.routes[i].fromId := by
    rw [buildPin_boxDelta, hbidF]
  have hshiftT : (buildPin axis bands s).boxDelta bT.id =
      bandShift bands s.routes[i].toId := by
    rw [buildPin_boxDelta, hbidT]
  have hgd0 : s.routes[i].points.head?.getD ⟨0, 0⟩ = p := by simp only [hp, Option.getD_some]
  have hgd1 : s.routes[i].points.getLast?.getD ⟨0, 0⟩ = q := by simp only [hq, Option.getD_some]
  have hEndsD := hEnds s.routes[i] hrBmem
  rw [hgd0, hgd1] at hEndsD
  rcases hmapOr with ⟨hnone, hpeq⟩ | ⟨d, hd, hmap⟩
  · have hmem : (⟨s.routes[i].id, bandShift bands s.routes[i].fromId,
        bandShift bands s.routes[i].toId, axis.point p,
        axis.point q⟩ : RouteDelta) ∈
        (s.routes.filterMap fun r =>
          match r.points.head?, r.points.getLast? with
          | some f, some l =>
            some ⟨r.id, bandShift bands r.fromId, bandShift bands r.toId,
              axis.point f, axis.point l⟩
          | _, _ => none) := by
      apply List.mem_filterMap.mpr
      exact ⟨s.routes[i], hrBmem, by simp only [hp, hq]⟩
    obtain ⟨dd, hdd⟩ := c4c5_find?_ex (fun d : RouteDelta => d.id == s.routes[i].id) _ ⟨_, hmem, beq_self_eq_true _⟩
    have hdd' : (buildPin axis bands s).route s.routes[i].id = some dd := hdd
    rw [hid] at hnone
    rw [hdd'] at hnone
    cases hnone
  · have hd' : (buildPin axis bands s).route s.routes[i].id = some d := by
      rw [← hid]; exact hd
    obtain ⟨hfd, htd, hfirst, hlast⟩ :=
      c4c5_route_deltas hrBmem hnodupR hd'
    rw [hgd0] at hfirst
    rw [hgd1] at hlast
    rw [hax] at hmap
    obtain ⟨qP, hqPhead, hqPfun⟩ := c4c5_mapM_point_head _ _ hmap p hp
    obtain ⟨wP, hwP, hqPeq, _⟩ := movePoint_ok hqPfun
    have hoffP : (routeMove d).offset (axis.point p) = d.fromDelta := by
      have hpl : axis.point p = d.first := hfirst.symm
      unfold routeMove
      by_cases heqd : d.fromDelta = d.toDelta
      · simp [heqd, Move.offset]
      · simp [heqd, hpl, Move.offset]
    have hwPeq : wP = axis.point p + d.fromDelta := by
      have happEq : (routeMove d).apply (axis.point p) =
        Measure.checkedI32 (axis.point p + d.fromDelta) := by
        simp [Move.apply, hoffP]
      rw [happEq] at hwP
      exact checked_value hwP
    have hqPEq : qP = axis.withPoint p (axis.point p + d.fromDelta) := by
      rw [hqPeq, hwPeq]
    obtain ⟨qQ, hqQlast, hqQfun⟩ := c4c5_mapM_point_getLast? _ _ hmap q hq
    obtain ⟨wQ, hwQ, hqQeq, _⟩ := movePoint_ok hqQfun
    have hoffQ : (routeMove d).offset (axis.point q) = d.toDelta := by
      have hql : axis.point q = d.last := hlast.symm
      rcases hEndsD with heq | ⟨hne, _⟩
      · have heqd : d.fromDelta = d.toDelta := by
          rw [hfd, htd]
          exact heq
        unfold routeMove
        simp [heqd, Move.offset]
      · have hne' : d.last ≠ d.first := by
          rw [hlast, hfirst]
          exact Ne.symm hne
        unfold routeMove
        by_cases heqd : d.fromDelta = d.toDelta
        · simp [heqd, Move.offset]
        · simp [heqd, hql, hne', Move.offset]
    have hwQeq : wQ = axis.point q + d.toDelta := by
      have happEq : (routeMove d).apply (axis.point q) =
          Measure.checkedI32 (axis.point q + d.toDelta) := by
        simp [Move.apply, hoffQ]
      rw [happEq] at hwQ
      exact checked_value hwQ
    have hqQEq : qQ = axis.withPoint q (axis.point q + d.toDelta) := by
      rw [hqQeq, hwQeq]
    have hshiftBF : (buildPin axis bands s).boxDelta bF.id = d.fromDelta := by
      rw [hshiftF, hfd]
    have hshiftBT : (buildPin axis bands s).boxDelta bT.id = d.toDelta := by
      rw [hshiftT, htd]
    have hrectF : bpF.rect =
        axis.withStart bF.rect (axis.start bF.rect + d.fromDelta) := by
      rw [hrectbF, hvalF, hshiftBF, hax]
    have hrectT : bpT.rect =
        axis.withStart bT.rect (axis.start bT.rect + d.toDelta) := by
      rw [hrectbT, hvalT, hshiftBT, hax]
    have hbP : Validator.onBoundary qP bpF.rect := by
      rw [hqPEq, hrectF, hbeqF]
      exact (onBoundary_crossShift).mpr hb1
    have hbQ : Validator.onBoundary qQ bpT.rect := by
      rw [hqQEq, hrectT, hbeqT]
      exact (onBoundary_crossShift).mpr hb2
    have hfindF : pinned.layoutDump.box? pinned.routes[i].fromId = some bpF := by
      unfold LayoutDump.box?
      exact hbpF
    have hfindT : pinned.layoutDump.box? pinned.routes[i].toId = some bpT := by
      unfold LayoutDump.box?
      exact hbpT
    exact ⟨qP, qQ, bpF, bpT, hqPhead, hqQlast, hfindF, hfindT, hbP, hbQ⟩
/-! ## Phase `rerouteBands`: keep-or-reroute decomposition. -/

/-- Every routed route is kept (same points, with its keep reason) or
freshly re-routed by `findRoute` (with its `routeEnds`/`findRoute`
witnesses). -/
theorem c4c5_reroute_mem (axis : Axis) (sp : Spacing) (bend : Int)
    (bands : List Band) (pin : Pin) (original : List Route) (s routed : Scene)
    (h : rerouteBands axis sp bend bands pin original s = .ok routed) :
    ∀ r' ∈ routed.routes, ∃ r ∈ s.routes, ∃ old ∈ original,
      (r, old) ∈ s.routes.zip original ∧
      r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      r'.orthogonal = r.orthogonal ∧
      ((r'.points = r.points ∧
        ((∃ fi ti : Nat,
          bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi ∧
          bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti ∧
          (fi = ti ∨ old.points.length < 2)) ∨
        bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = none ∨
        bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = none ∨
        s.boxes.find? (fun b => b.id == r.fromId) = none ∨
        s.boxes.find? (fun b => b.id == r.toId) = none)) ∨
      (∃ fi ti fb tb ends obs pts,
        bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi ∧
        bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti ∧
        s.boxes.find? (fun b => b.id == r.fromId) = some fb ∧
        s.boxes.find? (fun b => b.id == r.toId) = some tb ∧
        routeEnds axis sp pin fb tb old.points = .ok ends ∧
        obs = (s.boxes.filter (fun b => b.exclusive && b.id != r.fromId &&
          b.id != r.toId)).map (fun b => obstacleOf axis b.rect) ∧
        findRoute axis ends obs bend [sp.slot, 0] = .ok pts ∧ r'.points = pts)) := by
  unfold rerouteBands at h
  obtain ⟨routes, hmap, h⟩ := c4c5_bind h
  dsimp only at h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  intro r' hr'
  have hr'' : r' ∈ routes := hr'
  obtain ⟨r, hrmem, old, holdmem, hpair, hfy⟩ := c4c5_mapM_zip_mem _ _ _ _ hmap r' hr''
  change (match bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId), bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId), s.boxes.find? (fun b => b.id == r.fromId), s.boxes.find? (fun b => b.id == r.toId) with | some fi, some ti, some fb, some tb => if fi == ti || old.points.length < 2 then pure r else (do let ends ← routeEnds axis sp pin fb tb old.points; let obs := (s.boxes.filter (fun (b : Box) => b.exclusive && b.id != r.fromId && b.id != r.toId)).map (fun (b : Box) => obstacleOf axis b.rect); pure { r with points := ← findRoute axis ends obs bend [sp.slot, 0] } : Except LayoutError Route) | _, _, _, _ => pure r) = .ok r' at hfy
  cases hfi : bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) with
  | none =>
    rw [hfi] at hfy
    simp only at hfy
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
    subst hfy
    exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
      Or.inl ⟨rfl, Or.inr (Or.inl hfi)⟩⟩
  | some fi =>
    cases hti : bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) with
    | none =>
      rw [hfi, hti] at hfy
      simp only at hfy
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
      subst hfy
      exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
        Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hti))⟩⟩
    | some ti =>
      cases hfb : s.boxes.find? (fun b => b.id == r.fromId) with
      | none =>
        rw [hfi, hti, hfb] at hfy
        simp only at hfy
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
        subst hfy
        exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
          Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl hfb)))⟩⟩
      | some fb =>
        cases htb : s.boxes.find? (fun b => b.id == r.toId) with
        | none =>
          rw [hfi, hti, hfb, htb] at hfy
          simp only at hfy
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
          subst hfy
          exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
            Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr htb)))⟩⟩
        | some tb =>
          rw [hfi, hti, hfb, htb] at hfy
          simp only at hfy
          by_cases hcond : (fi == ti || old.points.length < 2) = true
          · rw [hcond] at hfy
            simp only [↓reduceIte] at hfy
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfy
            subst hfy
            have hcondP : fi = ti ∨ old.points.length < 2 := by
              rw [Bool.or_eq_true] at hcond
              rcases hcond with h | h
              · exact Or.inl (beq_iff_eq.mp h)
              · exact Or.inr (of_decide_eq_true h)
            exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
              Or.inl ⟨rfl, Or.inl ⟨fi, ti, hfi, hti, hcondP⟩⟩⟩
          · rw [ite_eq_right hcond] at hfy
            obtain ⟨ends, hends, hrest⟩ := c4c5_bind hfy
            obtain ⟨pts, hfind, hpure⟩ := c4c5_bind hrest
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
            subst hpure
            exact ⟨r, hrmem, old, holdmem, hpair, rfl, rfl, rfl, rfl,
              Or.inr ⟨fi, ti, fb, tb, ends, _, pts, hfi, hti, hfb, htb, hends, rfl, hfind, rfl⟩⟩
/-! ## Phase `rerouteBands` keeps C4. -/

/-- `rerouteBands` keeps orthogonality: kept same-band routes move rigidly,
short kept routes are trivially orthogonal, and fresh routes use the
`FindRouteOrthoPin` residual. Band/box lookup misses are ruled out by the
executed-layout premises. -/
theorem rerouteBands_c4 {axis : Axis} {sp : Spacing} {bend : Int}
    {bands : List Band} {pin : Pin} {original : List Route} {s routed : Scene}
    (h : rerouteBands axis sp bend bands pin original s = .ok routed)
    (hC4orig : ∀ r ∈ original, r.orthogonal = true → Polyline.isOrthogonal r.points = true)
    (happIdx : ∀ (k : Nat) (_hkP : k < s.routes.length) (_hkO : k < original.length)
      {rP rB : Route}, s.routes[k]? = some rP → original[k]? = some rB →
      rP.id = rB.id ∧ rP.fromId = rB.fromId ∧ rP.toId = rB.toId ∧ rP.orthogonal = rB.orthogonal ∧
      (rP.points = rB.points ∨ ∃ d, pin.route rP.id = some d ∧
        rB.points.mapM ((routeMove d).point pin.axis) = .ok rP.points ∧
        d.fromDelta = bandShift bands rB.fromId ∧ d.toDelta = bandShift bands rB.toId))
    (hbandSome : ∀ r ∈ s.routes,
      (∃ fi, bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi) ∧
      (∃ ti, bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti))
    (hboxSome : ∀ r ∈ s.routes,
      (s.boxes.find? (fun b => b.id == r.fromId)).isSome = true ∧
      (s.boxes.find? (fun b => b.id == r.toId)).isSome = true)
    (hOrthoPin : FindRouteOrthoPin) :
    Validator.C4 routed.layoutDump := by
  intro r' hr' horth'
  obtain ⟨r, hrmem, old, holdmem, hpair, hid, hfrom, hto, horthEq, hcase⟩ :=
    c4c5_reroute_mem axis sp bend bands pin original s routed h r' hr'
  rcases hcase with ⟨hptsEq, hreason⟩ | ⟨fi, ti, fb, tb, ends, obs, pts, hfi, hti, hfb, htb, hends, hobs, hfind, hptsPts⟩
  · rcases hreason with ⟨fi, ti, hfi, hti, hcond⟩ | hmissF | hmissT | hmissFB | hmissTB
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpair
      obtain ⟨hkR, hkO⟩ := getElem?_zip_iff.mp hk
      have hkRL : k < s.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
      have hkOL : k < original.length := (List.getElem?_eq_some_iff.mp hkO).1
      obtain ⟨hid2, hfrom2, hto2, horth2, hmapEq⟩ := happIdx k hkRL hkOL hkR hkO
      have holdOrth : old.orthogonal = true := by
        have h1 : old.orthogonal = r.orthogonal := horth2.symm
        have h2 : r.orthogonal = r'.orthogonal := horthEq.symm
        rw [h1, h2]
        exact horth'
      have hbaseOrth := hC4orig old holdmem holdOrth
      have hcondD : fi = ti ∨ old.points.length < 2 := hcond
      rcases hcondD with hfiEq | hlen
      · rcases hmapEq with hpeq | ⟨d, hd, hmap, hfd, htd⟩
        · rw [hptsEq, hpeq]
          exact hbaseOrth
        · have hsh := c4c5_sameBand_shift hfi (by rw [hfiEq]; exact hti)
          have hdd : d.fromDelta = d.toDelta := by
            rw [hfd, htd, ← hfrom2, ← hto2]
            exact hsh
          have hrm : routeMove d = Move.constant d.fromDelta := by
            unfold routeMove
            simp [hdd]
          have hmapC : old.points.mapM ((Move.constant d.fromDelta).point pin.axis) = .ok r.points := by
            rw [hrm] at hmap
            exact hmap
          have hort : Polyline.isOrthogonal r.points = true :=
            isOrthogonal_mapM_move _ _ hmapC hbaseOrth
          rw [hptsEq]
          exact hort
      · rcases hmapEq with hpeq | ⟨d, hd, hmap, _, _⟩
        · have hlenR : r.points.length < 2 := by rw [hpeq]; exact hlen
          rw [hptsEq]
          cases hrp : r.points with
          | nil => rfl
          | cons a rest =>
            cases rest with
            | nil => rfl
            | cons b rest2 =>
              have h1 : (a :: b :: rest2).length = rest2.length + 2 := rfl
              rw [hrp, h1] at hlenR
              omega
        · have hlenM := (mapM_except_spec _ _ _ hmap).1
          have hlenR : r.points.length < 2 := by rw [hlenM]; exact hlen
          rw [hptsEq]
          cases hrp : r.points with
          | nil => rfl
          | cons a rest =>
            cases rest with
            | nil => rfl
            | cons b rest2 =>
              have h1 : (a :: b :: rest2).length = rest2.length + 2 := rfl
              rw [hrp, h1] at hlenR
              omega
    · obtain ⟨fi, hfiSome⟩ := (hbandSome r hrmem).1
      rw [hmissF] at hfiSome
      cases hfiSome
    · obtain ⟨ti, htiSome⟩ := (hbandSome r hrmem).2
      rw [hmissT] at htiSome
      cases htiSome
    · have hsome := (hboxSome r hrmem).1
      rw [hmissFB] at hsome
      exact absurd hsome (by decide)
    · have hsome := (hboxSome r hrmem).2
      rw [hmissTB] at hsome
      exact absurd hsome (by decide)
  · have hort := hOrthoPin axis sp pin fb tb old.points ends obs bend pts hends hfind
    rw [hptsPts]
    exact hort
/-! ## Phase `rerouteBands` keeps C5. -/

/-- `rerouteBands` keeps endpoint attachment: kept routes are unchanged on
unchanged boxes, and fresh routes use the `FindRouteEndsPin` residual plus
the shifted base attachment. -/
theorem rerouteBands_c5 {axis : Axis} {sp : Spacing} {bend : Int}
    {bands : List Band} {pin : Pin} {original : List Route} {s routed : Scene}
    {sBase : Scene}
    (h : rerouteBands axis sp bend bands pin original s = .ok routed)
    (hC5pin : Validator.C5 s.layoutDump)
    (hC5base : Validator.C5 sBase.layoutDump)
    (hbaseRoutes : sBase.routes = original)
    (happ : applyPin pin bands sBase = .ok s)
    (hpinAxis : pin.axis = axis)
    (hnodupB : (sBase.boxes.map (·.id)).Nodup)
    (hnf : ∀ r ∈ s.routes, ∀ band ∈ bands, band.id ≠ r.fromId ∧ band.id ≠ r.toId)
    (hzipsame : ∀ r old, (r, old) ∈ s.routes.zip original →
      r.id = old.id ∧ r.fromId = old.fromId ∧ r.toId = old.toId)
    (hEndsPin : FindRouteEndsPin) :
    Validator.C5 routed.layoutDump := by
  have hboxesEq : routed.boxes = s.boxes := (rerouteBands_frame h).1
  have hdEq : routed.layoutDump.boxes = s.layoutDump.boxes := hboxesEq
  intro r' hr'
  obtain ⟨r, hrmem, old, holdmem, hpair, hid, hfrom, hto, horthEq, hcase⟩ :=
    c4c5_reroute_mem axis sp bend bands pin original s routed h r' hr'
  have hz := hzipsame r old hpair
  rcases hcase with ⟨hptsEq, hreason⟩ | ⟨fi, ti, fb, tb, ends, obs, pts, hfi, hti, hfb, htb, hends, hobs, hfind, hptsPts⟩
  · obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hC5pin r hrmem
    refine ⟨p, q, fb, tb, ?_, ?_, ?_, ?_, hb1, hb2⟩
    · rw [hptsEq]; exact hp
    · rw [hptsEq]; exact hq
    · unfold LayoutDump.box?
      rw [hdEq, hfrom]
      exact hfb
    · unfold LayoutDump.box?
      rw [hdEq, hto]
      exact htb
  · obtain ⟨hsrcEq, htgtEq⟩ := hEndsPin axis sp pin fb tb old.points ends obs bend pts hends hfind
    have holdS : old ∈ sBase.routes := by rw [hbaseRoutes]; exact holdmem
    have holdD : old ∈ sBase.layoutDump.routes := holdS
    obtain ⟨p, q, fb0, tb0, hp, hq, hfb0, htb0, hb1, hb2⟩ := hC5base old holdD
    have hfb0F : sBase.boxes.find? (fun b => b.id == old.fromId) = some fb0 := hfb0
    have htb0F : sBase.boxes.find? (fun b => b.id == old.toId) = some tb0 := htb0
    have hfb0M : fb0 ∈ sBase.boxes := List.mem_of_find?_eq_some hfb0F
    have htb0M : tb0 ∈ sBase.boxes := List.mem_of_find?_eq_some htb0F
    obtain ⟨_, _, hjpredF0, _⟩ := c4c5_find?_idx _ _ _ hfb0F
    obtain ⟨_, _, hjpredT0, _⟩ := c4c5_find?_idx _ _ _ htb0F
    have hfb0id : fb0.id = old.fromId := beq_iff_eq.mp hjpredF0
    have htb0id : tb0.id = old.toId := beq_iff_eq.mp hjpredT0
    have hfr : r.fromId = old.fromId := hz.2.1
    have htoO : r.toId = old.toId := hz.2.2
    have hfbM : fb ∈ s.boxes := List.mem_of_find?_eq_some hfb
    have htbM : tb ∈ s.boxes := List.mem_of_find?_eq_some htb
    obtain ⟨_, _, hjpredF, _⟩ := c4c5_find?_idx _ _ _ hfb
    obtain ⟨_, _, hjpredT, _⟩ := c4c5_find?_idx _ _ _ htb
    have hfbid : fb.id = r.fromId := beq_iff_eq.mp hjpredF
    have htbId : tb.id = r.toId := beq_iff_eq.mp hjpredT
    have hnfFb : ∀ band ∈ bands, band.id ≠ fb.id := by
      intro band hbm
      have hne := (hnf r hrmem band hbm).1
      rw [hfbid]
      exact hne
    have hnfTb : ∀ band ∈ bands, band.id ≠ tb.id := by
      intro band hbm
      have hne := (hnf r hrmem band hbm).2
      rw [htbId]
      exact hne
    obtain ⟨b, hbmem, w, hidb, hw, hrectb, hval⟩ :=
      applyPin_c5_box happ fb hfbM hnfFb
    obtain ⟨bT, hbTmem, wT, hidbT, hwT, hrectbT, hvalT⟩ :=
      applyPin_c5_box happ tb htbM hnfTb
    have hbid : b.id = old.fromId := by rw [← hidb, hfbid, hfr]
    have hbidT : bT.id = old.toId := by rw [← hidbT, htbId, htoO]
    have hbeq : b = fb0 :=
      c4c5_nodup_map_inj (·.id) hnodupB hbmem hfb0M (by rw [hbid, hfb0id])
    have hbeqT : bT = tb0 :=
      c4c5_nodup_map_inj (·.id) hnodupB hbTmem htb0M (by rw [hbidT, htb0id])
    obtain ⟨src, hsrc, h1⟩ := c4c5_bind hends
    obtain ⟨tgt, htgt, h2⟩ := c4c5_bind h1
    dsimp only at h2
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h2
    have hhd : old.points.headD ⟨0, 0⟩ = p := c4c5_headD_of_head? hp
    have hgd : old.points.getLast?.getD ⟨0, 0⟩ = q := by simp only [hq, Option.getD_some]
    unfold shiftedPoint at hsrc
    obtain ⟨wS, hwS, hrflS⟩ := c4c5_bind hsrc
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrflS
    have hwSeq : wS = axis.point (old.points.headD ⟨0, 0⟩) + pin.boxDelta fb.id :=
      checked_value hwS
    have hsrcPt : ends.source = axis.withPoint p (axis.point p + pin.boxDelta fb.id) := by
      have hES : ends.source = src := by rw [← h2]
      rw [hES, ← hrflS, hhd, hwSeq, hhd]
    unfold shiftedPoint at htgt
    obtain ⟨wT', hwT', hrflT⟩ := c4c5_bind htgt
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrflT
    have hwTeq : wT' = axis.point (old.points.getLast?.getD ⟨0, 0⟩) + pin.boxDelta tb.id :=
      checked_value hwT'
    have htgtPt : ends.target = axis.withPoint q (axis.point q + pin.boxDelta tb.id) := by
      have hET : ends.target = tgt := by rw [← h2]
      rw [hET, ← hrflT, hgd, hwTeq, hgd]
    have hshift : pin.boxDelta fb.id = pin.boxDelta b.id := by rw [hidb]
    have hshiftT : pin.boxDelta tb.id = pin.boxDelta bT.id := by rw [hidbT]
    have hbP : Validator.onBoundary ends.source fb.rect := by
      have h1 : ends.source = axis.withPoint p (axis.point p + pin.boxDelta fb.id) := hsrcPt
      have h2 : fb.rect = axis.withStart b.rect (axis.start b.rect + pin.boxDelta fb.id) := by
        rw [hrectb, hval, hshift, hpinAxis]
      rw [h1, h2, hbeq]
      exact (onBoundary_crossShift).mpr hb1
    have hbQ : Validator.onBoundary ends.target tb.rect := by
      have h1 : ends.target = axis.withPoint q (axis.point q + pin.boxDelta tb.id) := htgtPt
      have h2 : tb.rect = axis.withStart bT.rect (axis.start bT.rect + pin.boxDelta tb.id) := by
        rw [hrectbT, hvalT, hshiftT, hpinAxis]
      rw [h1, h2, hbeqT]
      exact (onBoundary_crossShift).mpr hb2
    have hfindF : routed.layoutDump.box? r'.fromId = some fb := by
      unfold LayoutDump.box?
      rw [hdEq, hfrom]
      exact hfb
    have hfindT : routed.layoutDump.box? r'.toId = some tb := by
      unfold LayoutDump.box?
      rw [hdEq, hto]
      exact htb
    have hhead : r'.points.head? = some ends.source := by
      rw [hptsPts]; exact hsrcEq
    have hlast : r'.points.getLast? = some ends.target := by
      rw [hptsPts]; exact htgtEq
    exact ⟨ends.source, ends.target, fb, tb, hhead, hlast, hfindF, hfindT, hbP, hbQ⟩
/-! ## Phases `relocateLabels`, `growCanvas`, `restoreOrigin`. -/

theorem c4c5_C4_of_routes_eq {d₁ d₂ : LayoutDump}
    (hr : d₂.routes = d₁.routes) (h : Validator.C4 d₁) : Validator.C4 d₂ := by
  intro r hr' horth
  rw [hr] at hr'
  exact h r hr' horth

theorem c4c5_C5_of_boxes_routes_eq {d₁ d₂ : LayoutDump}
    (hb : d₂.boxes = d₁.boxes) (hr : d₂.routes = d₁.routes)
    (h : Validator.C5 d₁) : Validator.C5 d₂ := by
  intro r hr'
  rw [hr] at hr'
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := h r hr'
  have hfb' : d₁.boxes.find? (fun b => b.id == r.fromId) = some fb := hfb
  have htb' : d₁.boxes.find? (fun b => b.id == r.toId) = some tb := htb
  refine ⟨p, q, fb, tb, hp, hq, ?_, ?_, hb1, hb2⟩
  · show d₂.boxes.find? (fun b => b.id == r.fromId) = some fb
    rw [hb]
    exact hfb'
  · show d₂.boxes.find? (fun b => b.id == r.toId) = some tb
    rw [hb]
    exact htb'

theorem relocateLabels_c4 {axis : Axis} {strip : Int} {s : Scene} :
    Validator.C4 s.layoutDump → Validator.C4 (relocateLabels axis strip s).layoutDump := by
  intro h r hr horth
  have hrS : r ∈ s.layoutDump.routes := hr
  exact h r hrS horth

theorem relocateLabels_c5 {axis : Axis} {strip : Int} {s : Scene} :
    Validator.C5 s.layoutDump → Validator.C5 (relocateLabels axis strip s).layoutDump := by
  intro h r hr
  have hrS : r ∈ s.layoutDump.routes := hr
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := h r hrS
  exact ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩

theorem growCanvas_c4 {axis : Axis} {canvas : Size} {s s' : Scene}
    (h : growCanvas axis canvas s = .ok s') :
    Validator.C4 s.layoutDump → Validator.C4 s'.layoutDump := by
  obtain ⟨_, hr, _⟩ := growCanvas_frame h
  have hrD : s'.layoutDump.routes = s.layoutDump.routes := by
    show s'.routes = s.routes
    exact hr
  intro hC4
  exact c4c5_C4_of_routes_eq hrD hC4

theorem growCanvas_c5 {axis : Axis} {canvas : Size} {s s' : Scene}
    (h : growCanvas axis canvas s = .ok s') :
    Validator.C5 s.layoutDump → Validator.C5 s'.layoutDump := by
  obtain ⟨hb, hr, _⟩ := growCanvas_frame h
  have hbD : s'.layoutDump.boxes = s.layoutDump.boxes := by
    show s'.boxes = s.boxes
    exact hb
  have hrD : s'.layoutDump.routes = s.layoutDump.routes := by
    show s'.routes = s.routes
    exact hr
  intro hC5
  exact c4c5_C5_of_boxes_routes_eq hbD hrD hC5

theorem c4c5_shiftAll_c4 {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    Validator.C4 s.layoutDump → Validator.C4 s'.layoutDump := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h1⟩ := c4c5_bind h
  obtain ⟨labels, hlabels, h2⟩ := c4c5_bind h1
  obtain ⟨routes, hroutes, h3⟩ := c4c5_bind h2
  obtain ⟨items, hitems, h4⟩ := c4c5_bind h3
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h4
  subst h4
  have hspec := mapM_except_spec _ s.routes routes hroutes
  intro hC4 r' hr' horth'
  have hrM : r' ∈ routes := hr'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrM
  have hiL : i < routes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen := hspec.1
  have hiS : i < s.routes.length := by omega
  obtain ⟨a, b, ha, hb, hfab⟩ := hspec.2 i hiS hiL
  have haM : a ∈ s.routes := List.mem_iff_getElem?.mpr ⟨i, ha⟩
  have hbE : b = r' := Option.some.inj (hb.symm.trans hi)
  subst hbE
  obtain ⟨pts, hpts, hrfl⟩ := c4c5_bind hfab
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have haOrth : a.orthogonal = true := horth'
  have hort := isOrthogonal_mapM_move _ _ hpts (hC4 a haM haOrth)
  exact hort

theorem restoreOrigin_c4 {axis : Axis} {s s' : Scene}
    (h : restoreOrigin axis s = .ok s') :
    Validator.C4 s.layoutDump → Validator.C4 s'.layoutDump := by
  obtain rfl | ⟨delta, _, hshift⟩ := restoreOrigin_cases h
  · exact id
  · exact c4c5_shiftAll_c4 hshift

theorem c4c5_shiftAll_c5 {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s')
    (hnodupB : (s.boxes.map (·.id)).Nodup) :
    Validator.C5 s.layoutDump → Validator.C5 s'.layoutDump := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h1⟩ := c4c5_bind h
  obtain ⟨labels, hlabels, h2⟩ := c4c5_bind h1
  obtain ⟨routes, hroutes, h3⟩ := c4c5_bind h2
  obtain ⟨items, hitems, h4⟩ := c4c5_bind h3
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h4
  subst h4
  have hspecR := mapM_except_spec _ s.routes routes hroutes
  have hlenR := hspecR.1
  have hspecB := mapM_except_spec _ s.boxes boxes hboxes
  have hnodupB' : (boxes.map (·.id)).Nodup := by
    have hid : boxes.map (·.id) = s.boxes.map (·.id) :=
      (shiftBoxes_maps s.boxes axis delta boxes hboxes).2.1
    rw [hid]
    exact hnodupB
  intro hC5 r' hr'
  have hrM : r' ∈ routes := hr'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hrM
  have hiL : i < routes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hiS : i < s.routes.length := by omega
  obtain ⟨r, bR, haR, hbR, hfab⟩ := hspecR.2 i hiS hiL
  have hrBmem : r ∈ s.routes := List.mem_iff_getElem?.mpr ⟨i, haR⟩
  have hbRe : bR = r' := Option.some.inj (hbR.symm.trans hi)
  obtain ⟨p, q, fb, tb, hp, hq, hfb, htb, hb1, hb2⟩ := hC5 r hrBmem
  obtain ⟨pts, hpts, hrfl⟩ := c4c5_bind hfab
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  have hptsR : r'.points = pts := by rw [← hbRe, ← hrfl]
  obtain ⟨qP, hqPhead, hqPfun⟩ := c4c5_mapM_point_head _ _ hpts p hp
  obtain ⟨wP, hwP, hqPeq, _⟩ := movePoint_ok hqPfun
  have hwPeq : wP = axis.point p + delta := by
    have happEq : (Move.constant delta).apply (axis.point p) =
        Measure.checkedI32 (axis.point p + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwP
    exact checked_value hwP
  have hqPEq : qP = axis.withPoint p (axis.point p + delta) := by rw [hqPeq, hwPeq]
  obtain ⟨qQ, hqQlast, hqQfun⟩ := c4c5_mapM_point_getLast? _ _ hpts q hq
  obtain ⟨wQ, hwQ, hqQeq, _⟩ := movePoint_ok hqQfun
  have hwQeq : wQ = axis.point q + delta := by
    have happEq : (Move.constant delta).apply (axis.point q) =
        Measure.checkedI32 (axis.point q + delta) := by simp [Move.apply, Move.offset]
    rw [happEq] at hwQ
    exact checked_value hwQ
  have hqQEq : qQ = axis.withPoint q (axis.point q + delta) := by rw [hqQeq, hwQeq]
  have hrid : r'.id = r.id := by rw [← hbRe, ← hrfl]
  have hrfrom : r'.fromId = r.fromId := by rw [← hbRe, ← hrfl]
  have hrto : r'.toId = r.toId := by rw [← hbRe, ← hrfl]
  have hfbM : fb ∈ s.boxes := List.mem_of_find?_eq_some hfb
  have htbM : tb ∈ s.boxes := List.mem_of_find?_eq_some htb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hfbM
  have hjL : j < s.boxes.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjB : j < boxes.length := by
    have := hspecB.1
    omega
  obtain ⟨b0, b0', hb0, hb0', hfb0⟩ := hspecB.2 j hjL hjB
  have hb0e : b0 = fb := Option.some.inj (hb0.symm.trans hj)
  obtain ⟨hid0, _, _, _, w0, hw0, hrect0, hval0⟩ := shiftBox_ok hfb0
  have hb0'mem : b0' ∈ boxes := List.mem_iff_getElem?.mpr ⟨j, hb0'⟩
  have hfb0id : fb.id = r.fromId := by
    have hfbF : s.boxes.find? (fun b => b.id == r.fromId) = some fb := hfb
    obtain ⟨_, _, hjpred, _⟩ := c4c5_find?_idx _ _ _ hfbF
    exact beq_iff_eq.mp hjpred
  have hidF : b0'.id = r'.fromId := by
    rw [hrfrom, ← hfb0id, ← hb0e]
    exact hid0
  have hpredF : (fun b : Box => b.id == r'.fromId) b0' = true :=
    beq_iff_eq.mpr hidF
  obtain ⟨dF, hfindF0⟩ := c4c5_find?_ex (fun b : Box => b.id == r'.fromId) _ ⟨b0', hb0'mem, hpredF⟩
  have hdFeq : dF = b0' := by
    apply c4c5_nodup_map_inj (·.id) hnodupB'
    · exact List.mem_of_find?_eq_some hfindF0
    · exact hb0'mem
    · obtain ⟨_, _, hjpred, _⟩ := c4c5_find?_idx _ _ _ hfindF0
      have h2 := beq_iff_eq.mp hjpred
      rw [← hidF] at h2
      exact h2
  have hrectF : b0'.rect = axis.withStart fb.rect (axis.start fb.rect + delta) := by
    rw [hb0e] at hrect0 hval0 hw0
    rw [hrect0, hval0]
  have hbP : Validator.onBoundary qP b0'.rect := by
    rw [hqPEq, hrectF]
    exact (onBoundary_crossShift).mpr hb1
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp htbM
  have hkL : k < s.boxes.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkB : k < boxes.length := by
    have := hspecB.1
    omega
  obtain ⟨b1, b1', hb1m, hb1', hfb1⟩ := hspecB.2 k hkL hkB
  have hb1e : b1 = tb := Option.some.inj (hb1m.symm.trans hk)
  obtain ⟨hid1, _, _, _, w1, hw1, hrect1, hval1⟩ := shiftBox_ok hfb1
  have hb1'mem : b1' ∈ boxes := List.mem_iff_getElem?.mpr ⟨k, hb1'⟩
  have htb0id : tb.id = r.toId := by
    have htbF : s.boxes.find? (fun b => b.id == r.toId) = some tb := htb
    obtain ⟨_, _, hjpred, _⟩ := c4c5_find?_idx _ _ _ htbF
    exact beq_iff_eq.mp hjpred
  have hidT : b1'.id = r'.toId := by
    rw [hrto, ← htb0id, ← hb1e]
    exact hid1
  have hpredT : (fun b : Box => b.id == r'.toId) b1' = true :=
    beq_iff_eq.mpr hidT
  obtain ⟨dT, hfindT0⟩ := c4c5_find?_ex (fun b : Box => b.id == r'.toId) _ ⟨b1', hb1'mem, hpredT⟩
  have hdTeq : dT = b1' := by
    apply c4c5_nodup_map_inj (·.id) hnodupB'
    · exact List.mem_of_find?_eq_some hfindT0
    · exact hb1'mem
    · obtain ⟨_, _, hjpred, _⟩ := c4c5_find?_idx _ _ _ hfindT0
      have h2 := beq_iff_eq.mp hjpred
      rw [← hidT] at h2
      exact h2
  have hrectT : b1'.rect = axis.withStart tb.rect (axis.start tb.rect + delta) := by
    rw [hb1e] at hrect1 hval1 hw1
    rw [hrect1, hval1]
  have hbQ : Validator.onBoundary qQ b1'.rect := by
    rw [hqQEq, hrectT]
    exact (onBoundary_crossShift).mpr hb2
  have hfindF : boxes.find? (fun b => b.id == r'.fromId) = some b0' := by
    rw [← hdFeq]
    exact hfindF0
  have hfindT : boxes.find? (fun b => b.id == r'.toId) = some b1' := by
    rw [← hdTeq]
    exact hfindT0
  have hhead : r'.points.head? = some qP := by rw [hptsR]; exact hqPhead
  have hlast : r'.points.getLast? = some qQ := by rw [hptsR]; exact hqQlast
  exact ⟨qP, qQ, b0', b1', hhead, hlast, hfindF, hfindT, hbP, hbQ⟩

theorem restoreOrigin_c5 {axis : Axis} {s s' : Scene}
    (h : restoreOrigin axis s = .ok s')
    (hnodupB : (s.boxes.map (·.id)).Nodup) :
    Validator.C5 s.layoutDump → Validator.C5 s'.layoutDump := by
  obtain rfl | ⟨delta, _, hshift⟩ := restoreOrigin_cases h
  · exact id
  · exact c4c5_shiftAll_c5 hshift hnodupB
/-! ## Public theorems: `pinBands` keeps C4 and C5. -/

theorem pinBands_c4 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC4 : Validator.C4 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hcov : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hEndsBox : ∀ rt ∈ s.routes,
      (s.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
      (s.boxes.find? (fun b => b.id == rt.toId)).isSome = true)
    (hOrthoPin : FindRouteOrthoPin)
    (h : pinBands boxes o s = .ok r) :
    Validator.C4 r.layoutDump := by
  obtain ⟨sp, axis, bands, pinned, routed, origin, strip, stripScene,
    hsp, haxis, hbands, happ, hroute, horig, hstrip, hstripEq, hgrow⟩ :=
    pinBands_spec hlanes h
  have hcov' : PinBoxCoverage boxes s axis sp := by
    have h := hcov sp hsp
    rw [← haxis] at h
    exact h
  have hlen : pinned.routes.length = s.routes.length := by
    obtain ⟨_, _, shiftedRoutes, _, _, _, hroutes, _, hfold⟩ := applyPin_shifted happ
    have hrr : pinned.routes = shiftedRoutes := foldlM_replaceFrame_routes hfold
    have hlen2 := (mapM_except_spec _ s.routes shiftedRoutes hroutes).1
    rw [hrr]
    exact hlen2
  have happIdx : ∀ (k : Nat) (hkP : k < pinned.routes.length) (hkO : k < s.routes.length)
      {rP rB : Route}, pinned.routes[k]? = some rP → s.routes[k]? = some rB →
      rP.id = rB.id ∧ rP.fromId = rB.fromId ∧ rP.toId = rB.toId ∧ rP.orthogonal = rB.orthogonal ∧
      (rP.points = rB.points ∨ ∃ d, (buildPin axis bands s).route rP.id = some d ∧
        rB.points.mapM ((routeMove d).point (buildPin axis bands s).axis) = .ok rP.points ∧
        d.fromDelta = bandShift bands rB.fromId ∧ d.toDelta = bandShift bands rB.toId) := by
    intro k hkP hkO rP rB hPk hOk
    have hrBmem : rB ∈ s.routes := List.mem_iff_getElem?.mpr ⟨k, hOk⟩
    obtain ⟨hid, hfrom, hto, horth, hmapOr⟩ := applyPin_c4_map happ hkP hkO hPk hOk
    refine ⟨hid, hfrom, hto, horth, ?_⟩
    rcases hmapOr with ⟨hnone, hpeq⟩ | ⟨d, hd, hmap⟩
    · exact Or.inl hpeq
    · have hax : (buildPin axis bands s).axis = axis := rfl
      rw [hax] at hmap
      have hd' : (buildPin axis bands s).route rB.id = some d := by
        rw [← hid]; exact hd
      obtain ⟨hfd, htd, _, _⟩ := c4c5_route_deltas hrBmem hrouteNodup hd'
      exact Or.inr ⟨d, hd, hmap, hfd, htd⟩
  have hbandSome : ∀ r ∈ pinned.routes,
      (∃ fi, bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi) ∧
      (∃ ti, bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti) := by
    intro r hr
    obtain ⟨k, hkR⟩ := List.mem_iff_getElem?.mp hr
    have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
    have hkOL : k < s.routes.length := by omega
    have hkO : s.routes[k]? = some s.routes[k] :=
      List.getElem?_eq_some_iff.mpr ⟨hkOL, rfl⟩
    have hrBk : s.routes[k] ∈ s.routes := List.mem_iff_getElem.mpr ⟨k, hkOL, rfl⟩
    obtain ⟨hid, hfrom, hto, _, _⟩ := happIdx k hkRL hkOL hkR hkO
    have hEndsF := (hEndsBox s.routes[k] hrBk).1
    have hEndsT := (hEndsBox s.routes[k] hrBk).2
    obtain ⟨bx, hbx⟩ := Option.isSome_iff_exists.mp hEndsF
    obtain ⟨by_, hby⟩ := Option.isSome_iff_exists.mp hEndsT
    have hbxmem : bx ∈ s.boxes := List.mem_of_find?_eq_some hbx
    have hbymem : by_ ∈ s.boxes := List.mem_of_find?_eq_some hby
    obtain ⟨_, _, hjpredF, _⟩ := c4c5_find?_idx _ _ _ hbx
    obtain ⟨_, _, hjpredT, _⟩ := c4c5_find?_idx _ _ _ hby
    have hbxid : bx.id = s.routes[k].fromId := beq_iff_eq.mp hjpredF
    have hbyid : by_.id = s.routes[k].toId := beq_iff_eq.mp hjpredT
    obtain ⟨bandF, hbmF, hcaseF⟩ := hcov' bx hbxmem
    obtain ⟨bandT, hbmT, hcaseT⟩ := hcov' by_ hbymem
    have hfidF : bx.id = r.fromId := by rw [hbxid, ← hfrom]
    have hfidT : by_.id = r.toId := by rw [hbyid, ← hto]
    have hpredF : (fun b => b.id == r.fromId || b.members.contains r.fromId) bandF = true := by
      show (bandF.id == r.fromId || bandF.members.contains r.fromId) = true
      rw [← hfidF, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
      exact hcaseF
    have hpredT : (fun b => b.id == r.toId || b.members.contains r.toId) bandT = true := by
      show (bandT.id == r.toId || bandT.members.contains r.toId) = true
      rw [← hfidT, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
      exact hcaseT
    have hbmF' : bandF ∈ bands := by rw [hbands]; exact hbmF
    have hbmT' : bandT ∈ bands := by rw [hbands]; exact hbmT
    obtain ⟨fi, hfi⟩ := c4c5_findIdx?_of_mem
      (fun b : Band => b.id == r.fromId || b.members.contains r.fromId) bands bandF hbmF' hpredF
    obtain ⟨ti, hti⟩ := c4c5_findIdx?_of_mem
      (fun b : Band => b.id == r.toId || b.members.contains r.toId) bands bandT hbmT' hpredT
    exact ⟨⟨fi, hfi⟩, ⟨ti, hti⟩⟩
  have hboxSome : ∀ r ∈ pinned.routes,
      (pinned.boxes.find? (fun b => b.id == r.fromId)).isSome = true ∧
      (pinned.boxes.find? (fun b => b.id == r.toId)).isSome = true := by
    intro r hr
    obtain ⟨k, hkR⟩ := List.mem_iff_getElem?.mp hr
    have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
    have hkOL : k < s.routes.length := by omega
    have hkO : s.routes[k]? = some s.routes[k] :=
      List.getElem?_eq_some_iff.mpr ⟨hkOL, rfl⟩
    have hrBk : s.routes[k] ∈ s.routes := List.mem_iff_getElem.mpr ⟨k, hkOL, rfl⟩
    obtain ⟨hid, hfrom, hto, _, _⟩ := happIdx k hkRL hkOL hkR hkO
    obtain ⟨bx, hbx⟩ := Option.isSome_iff_exists.mp (hEndsBox s.routes[k] hrBk).1
    obtain ⟨by_, hby⟩ := Option.isSome_iff_exists.mp (hEndsBox s.routes[k] hrBk).2
    have hbxmem : bx ∈ s.boxes := List.mem_of_find?_eq_some hbx
    have hbymem : by_ ∈ s.boxes := List.mem_of_find?_eq_some hby
    obtain ⟨_, _, hjpredF, _⟩ := c4c5_find?_idx _ _ _ hbx
    obtain ⟨_, _, hjpredT, _⟩ := c4c5_find?_idx _ _ _ hby
    have hbxid : bx.id = s.routes[k].fromId := beq_iff_eq.mp hjpredF
    have hbyid : by_.id = s.routes[k].toId := beq_iff_eq.mp hjpredT
    have hfidF : bx.id = r.fromId := by rw [hbxid, ← hfrom]
    have hfidT : by_.id = r.toId := by rw [hbyid, ← hto]
    exact ⟨c4c5_pinned_box_some happ r.fromId ⟨bx, hbxmem, hfidF⟩,
      c4c5_pinned_box_some happ r.toId ⟨by_, hbymem, hfidT⟩⟩
  have hC4orig : ∀ r ∈ s.routes, r.orthogonal = true → Polyline.isOrthogonal r.points = true :=
    fun r hr horth => hC4 r hr horth
  have hroutedC4 : Validator.C4 routed.layoutDump :=
    rerouteBands_c4 hroute hC4orig happIdx hbandSome hboxSome hOrthoPin
  have horigC4 : Validator.C4 origin.layoutDump := restoreOrigin_c4 horig hroutedC4
  have hstripC4 : Validator.C4 stripScene.layoutDump := by
    rw [hstripEq]
    exact relocateLabels_c4 horigC4
  exact growCanvas_c4 hgrow hstripC4

theorem pinBands_c5 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hlanes : lanesOf boxes ≠ [])
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hnodupB : (s.boxes.map (·.id)).Nodup)
    (hEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes,
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.fromId =
        bandShift (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) rt.toId ∨
        ((Axis.ofDirection o.direction).point (rt.points.head?.getD ⟨0, 0⟩) ≠
          (Axis.ofDirection o.direction).point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length))
    (hNoBandEnds : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      ∀ rt ∈ s.routes, ∀ b ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes),
        b.id ≠ rt.fromId ∧ b.id ≠ rt.toId)
    (hEndsPin : FindRouteEndsPin)
    (h : pinBands boxes o s = .ok r) :
    Validator.C5 r.layoutDump := by
  obtain ⟨sp, axis, bands, pinned, routed, origin, strip, stripScene,
    hsp, haxis, hbands, happ, hroute, horig, hstrip, hstripEq, hgrow⟩ :=
    pinBands_spec hlanes h
  have hEnds' : ∀ rt ∈ s.routes,
      bandShift bands rt.fromId = bandShift bands rt.toId ∨
        (axis.point (rt.points.head?.getD ⟨0, 0⟩) ≠
          axis.point (rt.points.getLast?.getD ⟨0, 0⟩) ∧ 1 < rt.points.length) := by
    intro rt hr
    have h2 := hEnds sp hsp rt hr
    rw [← haxis, ← hbands] at h2
    exact h2
  have hNoBandEnds' : ∀ rt ∈ s.routes, ∀ b ∈ bands,
      b.id ≠ rt.fromId ∧ b.id ≠ rt.toId := by
    intro rt hr b hb
    have hb' : b ∈ layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes) := by
      rw [← haxis, ← hbands]
      exact hb
    exact hNoBandEnds sp hsp rt hr b hb'
  have hlen : pinned.routes.length = s.routes.length := by
    obtain ⟨_, _, shiftedRoutes, _, _, _, hroutes, _, hfold⟩ := applyPin_shifted happ
    have hrr : pinned.routes = shiftedRoutes := foldlM_replaceFrame_routes hfold
    have hlen2 := (mapM_except_spec _ s.routes shiftedRoutes hroutes).1
    rw [hrr]
    exact hlen2
  have happEq : ∀ (k : Nat) (hkP : k < pinned.routes.length) (hkO : k < s.routes.length)
      {rP rB : Route}, pinned.routes[k]? = some rP → s.routes[k]? = some rB →
      rP.id = rB.id ∧ rP.fromId = rB.fromId ∧ rP.toId = rB.toId := by
    intro k hkP hkO rP rB hPk hOk
    obtain ⟨hid, hfrom, hto, _, _⟩ := applyPin_c4_map happ hkP hkO hPk hOk
    exact ⟨hid, hfrom, hto⟩
  have hC5pinned : Validator.C5 pinned.layoutDump :=
    applyPin_c5 happ hC5 hrouteNodup hnodupB hEnds' hNoBandEnds'
  have hpinAxis : (buildPin axis bands s).axis = axis := rfl
  have hnfPinned : ∀ r ∈ pinned.routes, ∀ band ∈ bands,
      band.id ≠ r.fromId ∧ band.id ≠ r.toId := by
    intro r hr band hbm
    obtain ⟨k, hkR⟩ := List.mem_iff_getElem?.mp hr
    have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
    have hkOL : k < s.routes.length := by omega
    have hkO : s.routes[k]? = some s.routes[k] :=
      List.getElem?_eq_some_iff.mpr ⟨hkOL, rfl⟩
    have hrBk : s.routes[k] ∈ s.routes := List.mem_iff_getElem.mpr ⟨k, hkOL, rfl⟩
    obtain ⟨_, hfrom, hto⟩ := happEq k hkRL hkOL hkR hkO
    obtain ⟨nF, nT⟩ := hNoBandEnds' s.routes[k] hrBk band hbm
    exact ⟨by rw [hfrom]; exact nF, by rw [hto]; exact nT⟩
  have hzipsame : ∀ r old, (r, old) ∈ pinned.routes.zip s.routes →
      r.id = old.id ∧ r.fromId = old.fromId ∧ r.toId = old.toId := by
    intro r old hpair
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpair
    obtain ⟨hkR, hkO⟩ := getElem?_zip_iff.mp hk
    have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
    have hkOL : k < s.routes.length := (List.getElem?_eq_some_iff.mp hkO).1
    exact happEq k hkRL hkOL hkR hkO
  have hnodupPinned : (pinned.boxes.map (·.id)).Nodup := by
    obtain ⟨shiftedBoxes, _, _, _, hboxes, _, _, _, hfold⟩ := applyPin_shifted happ
    have hid1 : shiftedBoxes.map (·.id) = s.boxes.map (·.id) :=
      (pinShiftBoxes_maps s.boxes (buildPin axis bands s)
        (buildPin axis bands s).axis shiftedBoxes hboxes).2.1
    have hid2 : pinned.boxes.map (·.id) = shiftedBoxes.map (·.id) :=
      (foldReplaceFrame_all bands (buildPin axis bands s).axis _ _ hfold).2.1
    rw [hid2, hid1]
    exact hnodupB
  have hnodupRouted : (routed.boxes.map (·.id)).Nodup := by
    have hrr : routed.boxes = pinned.boxes := (rerouteBands_frame hroute).1
    rw [hrr]
    exact hnodupPinned
  have hroutedC5 : Validator.C5 routed.layoutDump :=
    rerouteBands_c5 hroute hC5pinned hC5 rfl happ hpinAxis hnodupB hnfPinned hzipsame hEndsPin
  have horigC5 : Validator.C5 origin.layoutDump :=
    restoreOrigin_c5 horig hnodupRouted hroutedC5
  have hstripC5 : Validator.C5 stripScene.layoutDump := by
    rw [hstripEq]
    exact relocateLabels_c5 horigC5
  exact growCanvas_c5 hgrow hstripC5
