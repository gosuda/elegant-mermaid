import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsClearance
import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.LaneBandsBoxClausesProof
import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsFindRouteClearProof
 import Elegant.Layered.LaneBandsLooseLowerProof
import Elegant.Kinds.Swimlane
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-! # `applyPin` kept-route clearance for executed swimlane layouts.

Verdict on `pinBandsApplyPinKeptClear` (in `LaneBandsClearance`) as stated:
FALSE. It quantifies over arbitrary scenes and bands. Two hand-built
counterexamples live in `wip/Probe/LaneBandsApplyPinKeptClearProbe.lean`:
(1) a kept route whose band lookup misses an endpoint is sheared by
`Move.ends` and hits an exclusive box the base route missed
(`p.routes.map Route.points` differs, `hitsRectB` is `true` while base `c6`
is `true`); (2) a loose-band route detours outside its band interval while
every old-style hypothesis holds. So the old residual cannot be supplied for
an arbitrary scene, and `pinLanes_c6` cannot consume it.

This file states the executed form `PinKeptClearExecuted`: the same kept-route
conclusion, but with the facts of an executed base layout as hypotheses
(base `HardConstraints`, `PinBoxCoverage`, endpoint coverage, `PinSetup`,
`PinSceneParents`, route/scene/model id uniqueness, model ids nonempty,
spacing nonnegativity, plus one narrow residual for loose routes against
lane boxes). Probe evidence is in
`wip/Probe/LaneBandsKeptClearExecutedTProbe.lean`: every conjunct evaluates
to `true` on an executed layout with a same-band edge, a cross-lane edge, a
lane self-loop, a lane-to-loose edge and a loose self-loop (`mCross`), on a
lane self-loop (`mSelf`), on the degenerate models (`mEmpty`, `mNoLane`),
while the kept conclusion holds on the pinned scenes; the hand-built witness
violates the bundle (`end=false`, ghost endpoint uncovered).

Proof idea. A kept route is rigid exactly when both ends share one band
(`routeMove` is `.constant` there); the pin entry is the route's own by
route-id uniqueness. Same-shift pairs transport base clearance through
`hitsRect_axis_shift`. Different-shift pairs separate through band slots:
lane content (member boxes and both-ends-inside routes) is covered by the
lane extent by construction, shifted lane content stays inside its slot,
slots tile, and lane slots precede the loose slot; a lane route therefore
misses lane boxes of other bands and loose boxes. The one remaining shape,
a loose-band route against a lane-band box with a different shift, has no
strip bound (loose content excludes routes, so a kept loose route can leave
its band strip: `mCross` route `e4` does), and stays as the single residual
`hloose`, true on every probe.

`pinBands_c6_executed` has the conclusion of `pinBands_c6` with true
premises only. `pinLanes_c6` consumes it by replacing its `happly`
hypothesis with the `hkept` hypothesis below (same call site, same
`pinBands_spec` decomposition).
-/

/-! ## Private copies (prefixed; untracked-module lemmas do not resolve). -/

private theorem pkce_bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩


private theorem pkce_mapM_cons_ok {α β : Type} {f : α → Except LayoutError β}
    {a : α} {rest : List α} {out : List β}
    (h : (a :: rest).mapM f = .ok out) :
    ∃ b tl, f a = .ok b ∧ rest.mapM f = .ok tl ∧ out = b :: tl := by
  rw [List.mapM_cons] at h
  cases hfa : f a with
  | error e => simp [hfa, Bind.bind, Except.bind] at h
  | ok b =>
    cases hrest : rest.mapM f with
    | error e => simp [hfa, hrest, Bind.bind, Except.bind] at h
    | ok tl =>
      simp only [hfa, hrest, Bind.bind, Except.bind, Pure.pure, Except.pure,
        Except.ok.injEq] at h
      exact ⟨b, tl, rfl, rfl, h.symm⟩

private theorem pkce_foldlM_cons_ok {σ α : Type}
    {f : σ → α → Except LayoutError σ}
    {b : σ} {a : α} {rest : List α} {out : σ}
    (h : (a :: rest).foldlM f b = .ok out) :
    ∃ mid, f b a = .ok mid ∧ rest.foldlM f mid = .ok out := by
  rw [List.foldlM_cons] at h
  cases hmid : f b a with
  | error e => simp [hmid, Bind.bind, Except.bind] at h
  | ok m =>
    simp only [hmid, Bind.bind, Except.bind] at h
    exact ⟨m, rfl, h⟩

private theorem pkce_mapM_length {α β : Type} {f : α → Except LayoutError β}
    {l : List α} {out : List β} (h : l.mapM f = .ok out) :
    out.length = l.length := by
  induction l generalizing out with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons a rest ih =>
    obtain ⟨b, tl, hfb, htl, rfl⟩ := pkce_mapM_cons_ok h
    have hlen := ih htl
    simp only [List.length_cons, hlen]

private theorem pkce_decide_mem (x : String) (l : List String) :
    decide (x ∈ l) = l.contains x :=
  (List.contains_eq_mem x l).symm


private theorem pkce_findIdx_pred {α : Type} {p : α → Bool} {l : List α} {i : Nat}
    (h : l.findIdx? p = some i) : ∃ hlt : i < l.length, p (l[i]'hlt) = true := by
  obtain ⟨hlt, hpred, _⟩ := (List.findIdx?_eq_some_iff_getElem).mp h
  exact ⟨hlt, hpred⟩

private theorem pkce_findIdx_ne_none_of_cover {bands : List Band} {band : Band}
    {id : String} (hb : band ∈ bands)
    (hcov : band.id = id ∨ id ∈ band.members) :
    bands.findIdx? (fun b => b.id == id || decide (id ∈ b.members)) ≠ none := by
  intro hall
  rw [List.findIdx?_eq_none_iff] at hall
  have hband := hall band hb
  rcases hcov with heq | hmem
  · have h1 : (band.id == id) = true := by rw [beq_iff_eq]; exact heq
    simp [h1] at hband
  · have h2 : (decide (id ∈ band.members)) = true := by
      rw [decide_eq_true_eq]; exact hmem
    simp [h2] at hband

private theorem pkce_find?_congr {α : Type} {p q : α → Bool} {l : List α}
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ x ∈ rest, p x = q x := by
      intro x hx
      exact h x (List.mem_cons_of_mem _ hx)
    simp only [List.find?_cons, ha, ih hrest]

private theorem pkce_bandShift_eq_of_findIdx {bands : List Band} {id : String}
    {i : Nat}
    (h : bands.findIdx? (fun b => b.id == id || decide (id ∈ b.members)) =
      some i) :
    ∃ hlt : i < bands.length, bandShift bands id = (bands[i]'hlt).shift := by
  obtain ⟨hlt, hpred⟩ := pkce_findIdx_pred h
  have hcongr : ∀ x ∈ bands,
      (x.id == id || x.members.contains id) =
        (x.id == id || decide (id ∈ x.members)) := by
    intro x _
    rw [pkce_decide_mem]
  have hfind : bands.find?
      (fun b => b.id == id || b.members.contains id) =
      some (bands[i]'hlt) := by
    have h2 := pkce_find?_congr hcongr
    have h3 : bands.find? (fun b => b.id == id || decide (id ∈ b.members)) =
        some (bands[i]'hlt) := by
      rw [List.find?_eq_bind_findIdx?_getElem?, h]
      simp only [Option.bind_some, List.getElem?_eq_getElem hlt]
    rw [h2]
    exact h3
  refine ⟨hlt, ?_⟩
  unfold bandShift
  rw [hfind]
  simp

private theorem pkce_pinRoute_spec {pin : Pin} {r r' : Route}
    (h : (match pin.route r.id with
      | none => (pure r : Except LayoutError Route)
      | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point pin.axis) }
          : Except LayoutError Route)) = .ok r') :
    r'.id = r.id ∧ r'.fromId = r.fromId ∧ r'.toId = r.toId ∧
      r'.orthogonal = r.orthogonal ∧
      (pin.route r.id = none → r'.points = r.points) ∧
      (∀ d, pin.route r.id = some d →
        ∃ pts, r.points.mapM ((routeMove d).point pin.axis) = .ok pts ∧
          r'.points = pts) := by
  cases hroute : pin.route r.id with
  | none =>
    simp only [hroute] at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro _; rfl
    · intro d hd; cases hd
  | some d =>
    simp only [hroute] at h
    obtain ⟨pts, hpts, hpure⟩ := pkce_bindOk h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hpure
    subst hpure
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro hnone; cases hnone
    · intro d' hd'
      have hd : d' = d := Option.some.inj hd'.symm
      subst hd
      exact ⟨pts, hpts, rfl⟩

private theorem pkce_pinBox_spec {pin : Pin} {b b' : Box}
    (h : (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect pin.axis b.rect }
        : Except LayoutError Box) = .ok b') :
    ∃ r', (Move.constant (pin.boxDelta b.id)).rect pin.axis b.rect = .ok r' ∧
      b' = { b with rect := r' } := by
  cases hrect : (Move.constant (pin.boxDelta b.id)).rect pin.axis b.rect with
  | error e =>
    simp only [hrect, Bind.bind, Except.bind] at h
    exact absurd h (by simp)
  | ok r' =>
    simp only [hrect, Pure.pure, Except.pure, Bind.bind, Except.bind,
      Except.ok.injEq] at h
    refine ⟨r', rfl, ?_⟩
    exact h.symm

private theorem pkce_mem_of_find?_aux {α : Type} {p : α → Bool} {l : List α}
    {e : α} (hfind : l.find? p = some e) : e ∈ l := by
  induction l with
  | nil => simp [List.find?_nil] at hfind
  | cons x xs ih =>
    simp only [List.find?_cons] at hfind
    by_cases hx : p x = true
    · simp only [hx, Option.some.injEq] at hfind
      subst hfind
      exact List.mem_cons.mpr (Or.inl rfl)
    · have hfalse : p x = false := Bool.eq_false_iff.mpr hx
      simp only [hfalse] at hfind
      exact List.mem_cons.mpr (Or.inr (ih hfind))

private theorem pkce_find?_of_mem_nodup_key {α : Type} {l : List α} {a : α}
    {key : α → String} (hnodup : (l.map key).Nodup) (hmem : a ∈ l) :
    l.find? (fun x => key x == key a) = some a := by
  induction l with
  | nil => simp at hmem
  | cons b rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot, hnodup⟩ := hnodup
    rw [List.mem_cons] at hmem
    simp only [List.find?_cons]
    rcases hmem with rfl | hmem
    · simp
    · have hne : (key b == key a) = false := by
        cases hkb : (key b == key a) with
        | false => rfl
        | true =>
          have heq : key b = key a := beq_iff_eq.mp hkb
          have hmem' : key a ∈ rest.map key := List.mem_map.mpr ⟨a, hmem, rfl⟩
          have hcon : key b ∈ rest.map key := by rw [heq]; exact hmem'
          exact absurd hcon hnot
      simp only [hne]
      exact ih hnodup hmem
private theorem pkce_find?_ne_none {α : Type} {p : α → Bool} {l : List α}
    {e : α} (hmem : e ∈ l) (hpred : p e = true) : l.find? p ≠ none := by
  induction l with
  | nil => simp at hmem
  | cons a rest ih =>
    rw [List.mem_cons] at hmem
    by_cases ha : p a = true
    · simp [ha]
    · have hfalse : p a = false := Bool.eq_false_iff.mpr ha
      simp only [List.find?_cons, hfalse]
      rcases hmem with rfl | hmem
      · exact absurd hpred ha
      · exact ih hmem
private theorem pkce_findBox_ne_none {l : List Box} {id : String}
    (h : ∃ b ∈ l, b.id = id) :
    l.find? (fun b => b.id == id) ≠ none := by
  obtain ⟨b, hmem, hid⟩ := h
  exact pkce_find?_ne_none hmem (by rw [beq_iff_eq]; exact hid)

private theorem pkce_applyPin_boxFind_ne_none {pin : Pin} {bands : List Band}
    {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned) {id : String}
    (hb : ∃ b ∈ s.boxes, b.id = id) :
    pinned.boxes.find? (fun b => b.id == id) ≠ none := by
  obtain ⟨shB, _, _, _, hboxes, _, _, _, hfold⟩ := applyPin_shifted h
  obtain ⟨hlenF, hidF, _, _, _, _, _, _⟩ :=
    foldReplaceFrame_all bands pin.axis _ pinned hfold
  obtain ⟨hlenS, hidS, _, _, _⟩ := pinShiftBoxes_maps s.boxes pin pin.axis _ hboxes
  have hlen : pinned.boxes.length = s.boxes.length := by
    rw [hlenF, hlenS]
  have hid : pinned.boxes.map (·.id) = s.boxes.map (·.id) := hidF.trans hidS
  obtain ⟨b0, hb0, hb0id⟩ := hb
  obtain ⟨i, hi, hge⟩ := List.getElem_of_mem hb0
  have hi' : i < pinned.boxes.length := by rw [hlen]; exact hi
  have hidi : pinned.boxes[i].id = s.boxes[i].id := by
    have hcongr := congrArg (fun l => l[i]?) hid
    rw [List.getElem?_map, List.getElem?_map] at hcongr
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hcongr
    exact Option.some.inj hcongr
  have hmem : pinned.boxes[i]'hi' ∈ pinned.boxes := List.getElem_mem _
  apply pkce_findBox_ne_none
  refine ⟨pinned.boxes[i]'hi', hmem, ?_⟩
  rw [hidi, hge, hb0id]

private theorem pkce_applyPin_box_maps {pin : Pin} {bands : List Band}
    {s pinned : Scene} (h : applyPin pin bands s = .ok pinned) :
    pinned.boxes.map (·.id) = s.boxes.map (·.id) ∧
      pinned.boxes.map (·.parent) = s.boxes.map (·.parent) ∧
      pinned.boxes.map (·.exclusive) = s.boxes.map (·.exclusive) := by
  obtain ⟨shB, _, _, _, hboxes, _, _, _, hfold⟩ := applyPin_shifted h
  obtain ⟨_, hidF, hparF, _, hexF, _, _, _⟩ :=
    foldReplaceFrame_all bands pin.axis _ pinned hfold
  obtain ⟨_, hidS, hparS, _, hexS⟩ :=
    pinShiftBoxes_maps s.boxes pin pin.axis _ hboxes
  exact ⟨hidF.trans hidS, hparF.trans hparS, hexF.trans hexS⟩

private theorem pkce_lt_of_getElem?_some {α : Type} {l : List α} {i : Nat}
    {a : α} (h : l[i]? = some a) : i < l.length := by
  by_cases hle : i < l.length
  · exact hle
  · have hle' : l.length ≤ i := by omega
    have hnone : l[i]? = none := List.getElem?_eq_none hle'
    rw [hnone] at h
    cases h

private theorem pkce_map_pair_eq_of_maps_eq {α β γ : Type} {l₁ l₂ : List α}
    {f : α → β} {g : α → γ}
    (h1 : l₁.map f = l₂.map f) (h2 : l₁.map g = l₂.map g) :
    l₁.map (fun x => (f x, g x)) = l₂.map (fun x => (f x, g x)) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h1
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h1
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h1 h2 ⊢
      obtain ⟨hf1, hf2⟩ := h1
      obtain ⟨hg1, hg2⟩ := h2
      exact ⟨by rw [hf1, hg1], ih hf2 hg2⟩

private theorem pkce_box_find_pair_congr (l₁ l₂ : List Box) (s : String)
    (h : l₁.map (fun b => (b.id, b.parent)) =
      l₂.map (fun b => (b.id, b.parent))) :
    ((l₁.find? (fun b => b.id == s)).map (fun b => (b.id, b.parent))) =
      ((l₂.find? (fun b => b.id == s)).map (fun b => (b.id, b.parent))) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      have heq : x.id = y.id := congrArg Prod.fst hhead
      simp only [List.find?_cons]
      by_cases hmatch : (x.id == s) = true
      · have hmatch' : (y.id == s) = true := by
          rw [← heq]; exact hmatch
        simp only [hmatch, hmatch', Option.map_some, hhead]
      · have hmatch' : (y.id == s) = false :=
          Bool.eq_false_iff.mpr (fun hcon => hmatch (by rw [← heq] at hcon; exact hcon))
        simp only [hmatch, hmatch'] at ⊢
        exact ih _ htail

private theorem pkce_ancestors_go_pair_eq (d₁ d₂ : LayoutDump)
    (h : d₁.boxes.map (fun b => (b.id, b.parent)) =
      d₂.boxes.map (fun b => (b.id, b.parent)))
    (fuel : Nat) (id : String) :
    LayoutDump.ancestors.go d₁ fuel id =
      LayoutDump.ancestors.go d₂ fuel id := by
  induction fuel generalizing id with
  | zero =>
    simp only [LayoutDump.ancestors.go]
  | succ n ih =>
    have hfind := pkce_box_find_pair_congr d₁.boxes d₂.boxes id h
    have hfindBox : ((d₁.box? id).map (fun b => (b.id, b.parent))) =
        ((d₂.box? id).map (fun b => (b.id, b.parent))) := hfind
    cases hfb : d₁.box? id with
    | none =>
      have hnone : d₂.box? id = none := by
        cases h2 : d₂.box? id with
        | none => rfl
        | some b₂ =>
          exfalso
          have e1 : ((d₁.box? id).map (fun b => (b.id, b.parent))) = none := by
            rw [hfb]; rfl
          have e2 : ((d₂.box? id).map (fun b => (b.id, b.parent))) =
              some (b₂.id, b₂.parent) := by
            rw [h2]; rfl
          rw [e1] at hfindBox
          rw [e2] at hfindBox
          cases hfindBox
      simp only [LayoutDump.ancestors.go, hfb, hnone]
    | some b =>
      cases h2 : d₂.box? id with
      | none =>
        exfalso
        have e1 : ((d₁.box? id).map (fun b => (b.id, b.parent))) =
            some (b.id, b.parent) := by
          rw [hfb]; rfl
        have e2 : ((d₂.box? id).map (fun b => (b.id, b.parent))) = none := by
          rw [h2]; rfl
        rw [e1, e2] at hfindBox
        cases hfindBox
      | some b₂ =>
        have hpair : (b.id, b.parent) = (b₂.id, b₂.parent) := by
          have e1 : ((d₁.box? id).map (fun b => (b.id, b.parent))) =
              some (b.id, b.parent) := by
            rw [hfb]; rfl
          have e2 : ((d₂.box? id).map (fun b => (b.id, b.parent))) =
              some (b₂.id, b₂.parent) := by
            rw [h2]; rfl
          rw [e1, e2] at hfindBox
          injection hfindBox
        have hpar : b.parent = b₂.parent := congrArg Prod.snd hpair
        by_cases hpar0 : b.parent = ""
        · have hpar0' : b₂.parent = "" := by rw [← hpar]; exact hpar0
          simp only [LayoutDump.ancestors.go, hfb, h2, hpar, hpar0', ↓reduceIte]
        · have hpar0' : ¬ b₂.parent = "" := by rw [← hpar]; exact hpar0
          simp only [LayoutDump.ancestors.go, hfb, h2, hpar, hpar0', ↓reduceIte]
          exact congrArg (b₂.parent :: ·) (ih b₂.parent)

private theorem pkce_ancestors_congr {d₁ d₂ : LayoutDump}
    (h : d₁.boxes.map (fun b => (b.id, b.parent)) =
      d₂.boxes.map (fun b => (b.id, b.parent)))
    (id : String) : d₁.ancestors id = d₂.ancestors id := by
  have h1 : d₁.ancestors id = LayoutDump.ancestors.go d₁ (d₁.boxes.length) id := rfl
  have h2 : d₂.ancestors id = LayoutDump.ancestors.go d₂ (d₂.boxes.length) id := rfl
  have hlen : d₁.boxes.length = d₂.boxes.length := by
    have hcc := congrArg List.length h
    simpa [List.length_map] using hcc
  rw [h1, h2, hlen]
  exact pkce_ancestors_go_pair_eq _ _ h _ _

private theorem pkce_applyPin_scope_eq {pin : Pin} {bands : List Band}
    {s pinned : Scene} (h : applyPin pin bands s = .ok pinned) (r : Route) :
    pinned.layoutDump.routeScope r = s.layoutDump.routeScope r := by
  have hmaps := pkce_applyPin_box_maps h
  have hpair : pinned.boxes.map (fun b => (b.id, b.parent)) =
      s.boxes.map (fun b => (b.id, b.parent)) :=
    pkce_map_pair_eq_of_maps_eq hmaps.1 hmaps.2.1
  have hdump : pinned.layoutDump.boxes.map (fun b => (b.id, b.parent)) =
      s.layoutDump.boxes.map (fun b => (b.id, b.parent)) := hpair
  simp only [LayoutDump.routeScope]
  rw [pkce_ancestors_congr hdump, pkce_ancestors_congr hdump]

/-! ## Cross-axis shifts. -/

private def pkce_shiftPointAxis (axis : Axis) (delta : Int) (p : Point) : Point :=
  axis.withPoint p (axis.point p + delta)

private def pkce_shiftRectAxis (axis : Axis) (delta : Int) (r : Rect) : Rect :=
  axis.withStart r (axis.start r + delta)

private theorem pkce_shiftPointAxis_point (axis : Axis) (delta : Int) (p : Point) :
    axis.point (pkce_shiftPointAxis axis delta p) = axis.point p + delta := by
  cases axis <;> rfl

private theorem pkce_shiftRectAxis_start (axis : Axis) (delta : Int) (r : Rect) :
    axis.start (pkce_shiftRectAxis axis delta r) = axis.start r + delta := by
  cases axis <;> rfl

private theorem pkce_shiftRectAxis_length (axis : Axis) (delta : Int) (r : Rect) :
    axis.length (pkce_shiftRectAxis axis delta r) = axis.length r := by
  cases axis <;> rfl

private theorem pkce_moveConstant_point {axis : Axis} {delta : Int} {p p' : Point}
    (h : (Move.constant delta).point axis p = .ok p') :
    p' = pkce_shiftPointAxis axis delta p := by
  unfold Move.point Move.apply Move.offset at h
  obtain ⟨v, hv, hrfl⟩ := pkce_bindOk h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have hval : v = axis.point p + delta := by
    have := checkedI32_ok hv
    omega
  exact congrArg (axis.withPoint p) hval

private theorem pkce_moveConstant_point_ok {axis : Axis} {delta : Int} {p : Point}
    (h : ((Move.constant delta).point axis p).isOk) :
    (Move.constant delta).point axis p =
      .ok (pkce_shiftPointAxis axis delta p) := by
  cases h' : (Move.constant delta).point axis p with
  | error e =>
    rw [h'] at h
    rw [show ((Except.error e : Except LayoutError Point).isOk) = false from rfl] at h
    exact Bool.noConfusion h
  | ok v =>
    have hv : v = pkce_shiftPointAxis axis delta p :=
      pkce_moveConstant_point h'
    simp [hv]

private theorem pkce_hitsRect_axis_shift (axis : Axis) (k : Int)
    (points : List Point) (r : Rect) :
    Polyline.hitsRect (points.map (pkce_shiftPointAxis axis k))
      (pkce_shiftRectAxis axis k r) ↔
      Polyline.hitsRect points r := by
  cases axis with
  | x =>
    have hpts : points.map (pkce_shiftPointAxis .x k) =
        points.map (shiftPoint k 0) := by
      apply List.map_congr_left
      intro p _
      cases p with
      | mk x y => simp [pkce_shiftPointAxis, shiftPoint, Axis.withPoint, Axis.point]
    have hrect : pkce_shiftRectAxis .x k r = shiftRect k 0 r := by
      cases r with
      | mk x y w h => simp [pkce_shiftRectAxis, shiftRect, Axis.withStart, Axis.start]
    rw [hpts, hrect]
    exact hitsRect_shift k 0 points r
  | y =>
    have hpts : points.map (pkce_shiftPointAxis .y k) =
        points.map (shiftPoint 0 k) := by
      apply List.map_congr_left
      intro p _
      cases p with
      | mk x y => simp [pkce_shiftPointAxis, shiftPoint, Axis.withPoint, Axis.point]
    have hrect : pkce_shiftRectAxis .y k r = shiftRect 0 k r := by
      cases r with
      | mk x y w h => simp [pkce_shiftRectAxis, shiftRect, Axis.withStart, Axis.start]
    rw [hpts, hrect]
    exact hitsRect_shift 0 k points r

private theorem pkce_mapM_constant {axis : Axis} {delta : Int}
    {l : List Point} {pts : List Point}
    (h : l.mapM ((Move.constant delta).point axis) = .ok pts) :
    pts = l.map (pkce_shiftPointAxis axis delta) := by
  induction l generalizing pts with
  | nil =>
    simp only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons p rest ih =>
    obtain ⟨q, tl, hq, htl, rfl⟩ := pkce_mapM_cons_ok h
    have hq' : (Move.constant delta).point axis p =
        .ok (pkce_shiftPointAxis axis delta p) := by
      apply pkce_moveConstant_point_ok
      rw [hq]
      rfl
    have hqq : pkce_shiftPointAxis axis delta p = q := by
      have h2 := hq'.symm.trans hq
      simp only [Except.ok.injEq] at h2
      exact h2
    subst hqq
    have htl' := ih htl
    simp only [List.map_cons, htl']

/-! ## Pin entries and route lookup. -/

private theorem pkce_pinEntry_mem {axis : Axis} {bands : List Band} {s : Scene}
    {old : Route} (hmem : old ∈ s.routes) (hne : old.points ≠ []) :
    ∃ d, d ∈ (buildPin axis bands s).routes ∧ d.id = old.id := by
  obtain ⟨first, hhead⟩ : ∃ first, old.points.head? = some first := by
    cases h : old.points.head? with
    | none =>
      have hempty : old.points = [] := List.head?_eq_none_iff.mp h
      exact absurd hempty hne
    | some first => exact ⟨first, rfl⟩
  obtain ⟨last, hlast⟩ : ∃ last, old.points.getLast? = some last := by
    cases h : old.points.getLast? with
    | none =>
      have hempty : old.points = [] := List.getLast?_eq_none_iff.mp h
      exact absurd hempty hne
    | some last => exact ⟨last, rfl⟩
  refine ⟨⟨old.id, bandShift bands old.fromId, bandShift bands old.toId,
    axis.point first, axis.point last⟩, ?_, rfl⟩
  unfold buildPin
  simp only
  exact List.mem_filterMap.mpr ⟨old, hmem, by simp [hhead, hlast]⟩

private theorem pkce_pinRoute_some {axis : Axis} {bands : List Band} {s : Scene}
    {old : Route} (hmem : old ∈ s.routes) (hne : old.points ≠ []) :
    (buildPin axis bands s).route old.id ≠ none := by
  obtain ⟨d, hdmem, hdid⟩ := pkce_pinEntry_mem hmem hne
  have hpred : (fun r => r.id == old.id) d = true := by
    simp only
    rw [beq_iff_eq]
    exact hdid
  exact pkce_find?_ne_none hdmem hpred

/-! ## Replace-frame fold: exclusive boxes keep their shifted rectangles. -/

private theorem pkce_replaceFrame_kept {axis : Axis} {band : Band}
    {acc mid : Scene} {k : Nat}
    (h : replaceFrame axis band acc = .ok mid)
    {kb : Box} (hk : acc.boxes[k]? = some kb) (hne : kb.id ≠ band.id) :
    ∃ kb', mid.boxes[k]? = some kb' ∧ kb'.rect = kb.rect ∧ kb'.id = kb.id := by
  unfold replaceFrame at h
  cases hfind : acc.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨kb, hk, rfl, rfl⟩
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok sv =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok tv =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlt, hpred, _⟩ :=
          (List.findIdx?_eq_some_iff_getElem).mp hfind
        have hid : (acc.boxes[idx]'(hlt)).id = band.id := beq_iff_eq.mp hpred
        have hkk : k ≠ idx := by
          intro hcon
          have h1 : acc.boxes[idx]? = some (acc.boxes[idx]'(hlt)) :=
            List.getElem?_eq_getElem hlt
          have h2 : acc.boxes[k]? = some kb := hk
          rw [hcon] at h2
          rw [h1] at h2
          have hkb : kb = acc.boxes[idx]'hlt := Option.some.inj h2.symm
          rw [hkb] at hne
          exact hne hid
        have hlen : (acc.boxes.mapIdx fun j b =>
            if j = idx then { b with rect := placeRect axis band.start band.thickness b.rect }
            else b).length = acc.boxes.length := List.length_mapIdx
        refine ⟨kb, ?_, rfl, rfl⟩
        rw [List.getElem?_mapIdx]
        have hk' : acc.boxes[k]? = some kb := hk
        rw [hk']
        simp only [Option.map_some, hkk, ↓reduceIte]

/-! ## Folded routes, no-exclusive-frame, and content bounds. -/

private theorem pkce_replaceFrame_routes {axis : Axis} {band : Band}
    {acc mid : Scene} (h : replaceFrame axis band acc = .ok mid) :
    mid.routes = acc.routes := by
  unfold replaceFrame at h
  cases hfind : acc.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error e => simp [hstart, Bind.bind, Except.bind] at h
    | ok sv =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error e => simp [hthick] at h
      | ok tv =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl

private theorem pkce_fold_routes {axis : Axis} {bands : List Band}
    {acc0 pinned : Scene}
    (h : bands.foldlM (fun scene band => replaceFrame axis band scene) acc0 =
      .ok pinned) : pinned.routes = acc0.routes := by
  induction bands generalizing acc0 with
  | nil =>
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | cons band rest ih =>
    obtain ⟨mid, hmid, hrest⟩ := pkce_foldlM_cons_ok h
    have h1 := pkce_replaceFrame_routes hmid
    have h2 := ih hrest
    rw [h2, h1]

private theorem pkce_fold_keptRect {axis : Axis} {bands : List Band}
    {acc0 pinned : Scene} {k : Nat}
    (h : bands.foldlM (fun scene band => replaceFrame axis band scene) acc0 =
      .ok pinned) :
    ∀ {kb : Box}, acc0.boxes[k]? = some kb →
      (∀ band ∈ bands, kb.id ≠ band.id) →
      ∃ kb', pinned.boxes[k]? = some kb' ∧ kb'.rect = kb.rect ∧
        kb'.id = kb.id := by
  induction bands generalizing acc0 with
  | nil =>
    intro kb hk hne
    simp only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨kb, hk, rfl, rfl⟩
  | cons band rest ih =>
    intro kb hk hne
    obtain ⟨mid, hmid, hrest⟩ := pkce_foldlM_cons_ok h
    obtain ⟨kb', hkb', hrect', hid'⟩ := pkce_replaceFrame_kept hmid hk
      (hne band (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨kb'', hkb'', hrect'', hid''⟩ := ih hrest hkb'
      (fun b hb => by rw [hid']; exact hne b (List.mem_cons_of_mem _ hb))
    exact ⟨kb'', hkb'', hrect''.trans hrect', hid''.trans hid'⟩

private theorem pkce_noExclFrame {s : Scene} {bands : List Band}
    (hsetup : PinSetup s bands) {b : Box} (hb : b ∈ s.boxes)
    (hex : b.exclusive = true) {band : Band} (hband : band ∈ bands) :
    b.id ≠ band.id := by
  intro hcon
  have hne : b.id ≠ "" := hsetup.2.2.2.1 b hb
  have hidne : band.id ≠ "" := by rw [← hcon]; exact hne
  have hband := hsetup.2.2.1 b hb ⟨band, hband, hcon.symm, hidne⟩
  have hfalse : b.exclusive = false := hband.2
  rw [hex] at hfalse
  exact Bool.noConfusion hfalse

private theorem pkce_mem_le_foldMax (vs : List Int) (v0 v : Int)
    (h : v ∈ vs) : v ≤ vs.foldl max v0 := by
  induction vs generalizing v0 with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [List.mem_cons] at h
    rcases h with heq | h
    · subst heq
      exact Int.le_trans (show v ≤ max v0 v by omega)
        (le_foldl_max rest (max v0 v))
    · exact ih (max v0 a) h

private theorem pkce_foldMin_le_mem (vs : List Int) (v0 v : Int)
    (h : v ∈ vs) : vs.foldl min v0 ≤ v := by
  induction vs generalizing v0 with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [List.mem_cons] at h
    rcases h with heq | h
    · subst heq
      exact Int.le_trans (foldl_min_le rest (min v0 v))
        (show min v0 v ≤ v by omega)
    · exact ih (min v0 a) h

private theorem pkce_mem_bounds {vs : List Int} {v : Int} (h : v ∈ vs)
    {lo hi : Int} (hb : bounds vs = some (lo, hi)) : lo ≤ v ∧ v ≤ hi := by
  cases vs with
  | nil => simp [bounds] at hb
  | cons v0 rest =>
    have hmem : v = v0 ∨ v ∈ rest := List.mem_cons.mp h
    have hlo : rest.foldl min v0 ≤ v := by
      rcases hmem with heq | h
      · subst heq
        exact foldl_min_le rest v
      · exact pkce_foldMin_le_mem rest v0 v h
    have hhi : v ≤ rest.foldl max v0 := by
      rcases hmem with heq | h
      · subst heq
        exact le_foldl_max rest v
      · exact pkce_mem_le_foldMax rest v0 v h
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨hlo, hhi⟩

private theorem pkce_content_route_mem {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {lane : String} {r : Route} {p : Point}
    (hr : r ∈ s.routes) (hp : p ∈ r.points)
    (hfrom : inLane boxes r.fromId lane = true)
    (hto : inLane boxes r.toId lane = true) :
    axis.point p ∈ contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)) := by
  unfold contentValues
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨r, hr, ?_⟩
  have hcond : (if inLane boxes r.fromId lane && inLane boxes r.toId lane then
      r.points.map axis.point else []) = r.points.map axis.point := by
    simp [hfrom, hto]
  rw [hcond]
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

private theorem pkce_boxvals_mem {s : Scene} {axis : Axis} {b : Box}
    {mems : List String} (hmem : b.id ∈ mems)
    (hfind : s.boxes.find? (fun b_ => b_.id == b.id) = some b) :
    axis.start b.rect ∈ mems.flatMap (fun id =>
      match s.boxes.find? (fun b_ => b_.id == id) with
      | none => []
      | some b_ =>
        [axis.start b_.rect, axis.start b_.rect + axis.length b_.rect]) ∧
    axis.start b.rect + axis.length b.rect ∈ mems.flatMap (fun id =>
      match s.boxes.find? (fun b_ => b_.id == id) with
      | none => []
      | some b_ =>
        [axis.start b_.rect, axis.start b_.rect + axis.length b_.rect]) := by
  have hred : (match s.boxes.find? (fun b_ => b_.id == b.id) with
      | none => []
      | some b_ => [axis.start b_.rect,
          axis.start b_.rect + axis.length b_.rect]) =
      [axis.start b.rect, axis.start b.rect + axis.length b.rect] := by
    rw [hfind]
  constructor
  · apply List.mem_flatMap.mpr
    exact ⟨b.id, hmem, by rw [hred]; simp⟩
  · apply List.mem_flatMap.mpr
    exact ⟨b.id, hmem, by rw [hred]; simp⟩

private theorem pkce_content_bounded {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {lane : String} {mems : List String} {v : Int}
    (hmem : v ∈ contentValues boxes s axis lane mems) :
    ∃ lo hi, bounds (contentValues boxes s axis lane mems) = some (lo, hi) ∧
      lo ≤ v ∧ v ≤ hi := by
  cases hcl : contentValues boxes s axis lane mems with
  | nil => simp [hcl] at hmem
  | cons a rest =>
    have hmem' : v ∈ a :: rest := by rw [← hcl]; exact hmem
    have hb : bounds (a :: rest) =
        some (rest.foldl min a, rest.foldl max a) := rfl
    obtain ⟨hlo, hhi⟩ := pkce_mem_bounds hmem' hb
    exact ⟨_, _, hb, hlo, hhi⟩

private theorem pkce_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem pkce_inLane_of_mem {boxes : List ModelBox} {id lane : String}
    {mems : List String} (hm : id ∈ mems)
    (hfm : mems = (boxes.filter fun b => inLane boxes b.id lane).map
      (·.id)) : inLane boxes id lane = true := by
  rw [hfm] at hm
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hm
  obtain ⟨hmb', hpred⟩ := List.mem_filter.mp hmb
  rw [← hid]
  exact hpred

private theorem pkce_inLane_self {boxes : List ModelBox} {lane : String}
    (hlane : lane ∈ lanesOf boxes) (hnodup : (boxes.map (·.id)).Nodup) :
    inLane boxes lane lane = true := by
  obtain ⟨mb, hmb, hrole, hpar, hid⟩ := pkce_lanesOf_mem hlane
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have h0 := pkce_find?_of_mem_nodup_key (key := (·.id)) hnodup hmb
    rw [hid] at h0
    exact h0
  have hparT : (mb.parent == "") = true := by rw [beq_iff_eq]; exact hpar
  have hroleT : (mb.role == .group) = true := by rw [beq_iff_eq]; exact hrole
  have hlaneEq : laneOf boxes lane = some (lane, true) := by
    unfold laneOf
    cases hfuel : boxes.length with
    | zero =>
      have hempty : boxes = [] := List.length_eq_zero_iff.mp hfuel
      rw [hempty] at hfind
      simp at hfind
    | succ n =>
      simp only [laneOfAux, hfind, hparT, hroleT, ↓reduceIte]
  unfold inLane
  rw [hlaneEq]
  simp

private theorem pkce_layLanes_mem {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lanes : List String} {st : Int} {g : Band}
    (hg : g ∈ layLanes boxes s axis sp lanes st) :
    ∃ lane ∈ lanes, ∃ st', g = laneBand boxes s axis sp lane st' := by
  induction lanes generalizing st with
  | nil => simp [layLanes] at hg
  | cons lane rest ih =>
    unfold layLanes at hg
    dsimp only at hg
    rw [List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨lane, List.mem_cons.mpr (Or.inl rfl), st, rfl⟩
    · obtain ⟨lane', hmem, st', rfl⟩ := ih hg
      exact ⟨lane', List.mem_cons_of_mem _ hmem, st', rfl⟩

private theorem pkce_layBands_mem {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lanes : List String} {g : Band}
    (hg : g ∈ layBands boxes s axis sp lanes) :
    (∃ lane ∈ lanes, ∃ st, g = laneBand boxes s axis sp lane st) ∨
    (∃ lo, lo = looseNodes boxes ∧
      g = looseBand boxes s axis sp lo
        (firstLaneStart s lanes axis +
          ((layLanes boxes s axis sp lanes
            (firstLaneStart s lanes axis)).map (·.thickness)).sum)) := by
  unfold layBands at hg
  dsimp only at hg
  cases hlo : looseNodes boxes with
  | nil =>
    have his : (looseNodes boxes).isEmpty = true := by simp [hlo]
    simp only [his, ↓reduceIte] at hg
    obtain ⟨lane, hmem, st, rfl⟩ := pkce_layLanes_mem hg
    exact Or.inl ⟨lane, hmem, st, rfl⟩
  | cons hd tl =>
    have his : (looseNodes boxes).isEmpty = false := by simp [hlo]
    simp only [his, Bool.false_eq_true, ↓reduceIte] at hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨lane, hmem, st, rfl⟩ := pkce_layLanes_mem hg
      exact Or.inl ⟨lane, hmem, st, rfl⟩
    · rw [List.mem_singleton] at hg
      exact Or.inr ⟨hd :: tl, rfl, by rw [← hlo]; exact hg⟩

private theorem pkce_layBands_layLanes {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lanes : List String} {g : Band}
    (hg : g ∈ layBands boxes s axis sp lanes) (hne : g.id ≠ "") :
    g ∈ layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) := by
  unfold layBands at hg
  dsimp only at hg
  cases hlo : looseNodes boxes with
  | nil =>
    have his : (looseNodes boxes).isEmpty = true := by simp [hlo]
    simp only [his, ↓reduceIte] at hg
    exact hg
  | cons hd tl =>
    have his : (looseNodes boxes).isEmpty = false := by simp [hlo]
    simp only [his, Bool.false_eq_true, ↓reduceIte] at hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hg
    · rw [List.mem_singleton] at hg
      have hid : g.id = "" := by
        rw [hg]
        unfold looseBand
        split <;> rfl
      exact absurd hid hne

private theorem pkce_band_thick_nonneg {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lanes : List String} {g : Band}
    (hg : g ∈ layBands boxes s axis sp lanes)
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear) : 0 ≤ g.thickness := by
  obtain hsh | hsh := pkce_layBands_mem hg
  · obtain ⟨lane, hlane, st, rfl⟩ := hsh
    exact laneBand_thickness_nonneg boxes s axis sp lane st hnn.1 hnn.2
  · obtain ⟨lo, hlo, rfl⟩ := hsh
    unfold looseBand
    cases hbp : bounds (contentValues boxes s axis "" lo) with
    | none => dsimp only; omega
    | some pr =>
      obtain ⟨lo', hi'⟩ := pr
      have hle := bounds_le hbp
      dsimp only
      omega

private theorem pkce_laneSlot_route {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lane : String}
    {st : Int} {r : Route} {p : Point} {g : Band}
    (hg : g = laneBand boxes s axis sp lane st)
    (hmem : r ∈ s.routes) (hp : p ∈ r.points)
    (hfrom : inLane boxes r.fromId lane = true)
    (hto : inLane boxes r.toId lane = true)
    (_hnS : (s.boxes.map (·.id)).Nodup)
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear) :
    g.start ≤ axis.point p + g.shift ∧
      axis.point p + g.shift ≤ g.start + g.thickness := by
  have hst : g.start = st := by rw [hg]; rfl
  have hmems : g.members =
      (boxes.filter fun b => inLane boxes b.id lane).map (·.id) := by
    rw [hg]; rfl
  have hpmem : axis.point p ∈ contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)) :=
    pkce_content_route_mem hmem hp hfrom hto
  obtain ⟨lo, hi, hbnd, hlo, hhi⟩ := pkce_content_bounded hpmem
  have hext : (bounds (contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)))).getD
      (st, st) = (lo, hi) := by rw [hbnd, Option.getD_some]
  have hth : g.thickness = sp.title + 2 * sp.clear +
      (((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).2 -
      ((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).1) := by rw [hg]; rfl
  have hsh : g.shift = st + sp.title + sp.clear -
      ((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).1 := by rw [hg]; rfl
  have hgoal : g.start ≤ axis.point p + g.shift ∧
      axis.point p + g.shift ≤ g.start + g.thickness := by
    rw [hst, hsh, hth, hext]
    dsimp only
    obtain ⟨ht, hc⟩ := hnn
    omega
  exact hgoal

private theorem pkce_laneSlot_box {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lane : String}
    {st : Int} {b : Box} {g : Band}
    (hg : g = laneBand boxes s axis sp lane st)
    (hb : b ∈ s.boxes)
    (hcov : (g.id == b.id || decide (b.id ∈ g.members)) = true)
    (hnS : (s.boxes.map (·.id)).Nodup)
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear)
    (hnodupM : (boxes.map (·.id)).Nodup)
    (hlane : lane ∈ lanesOf boxes) :
    g.start ≤ axis.start b.rect + g.shift ∧
      axis.start b.rect + axis.length b.rect + g.shift ≤
        g.start + g.thickness := by
  have hst : g.start = st := by rw [hg]; rfl
  have hmems : g.members =
      (boxes.filter fun b_ => inLane boxes b_.id lane).map (·.id) := by
    rw [hg]; rfl
  have hin : inLane boxes b.id lane = true := by
    have hor2 : (g.id == b.id) = true ∨
        decide (b.id ∈ g.members) = true := by
      rw [Bool.or_eq_true] at hcov
      exact hcov
    rcases hor2 with h | h
    · have heq : g.id = b.id := beq_iff_eq.mp h
      have hlaneid : g.id = lane := by rw [hg]; rfl
      rw [hlaneid] at heq
      rw [← heq]
      exact pkce_inLane_self hlane hnodupM
    · have hmem : b.id ∈ g.members := of_decide_eq_true h
      rw [hmems] at hmem
      exact pkce_inLane_of_mem hmem rfl
  have hmemid : b.id ∈ (boxes.filter fun b_ => inLane boxes b_.id lane).map
      (·.id) := by
    have hor2 : (g.id == b.id) = true ∨
        decide (b.id ∈ g.members) = true := by
      rw [Bool.or_eq_true] at hcov
      exact hcov
    rcases hor2 with h | h
    · have heq : g.id = b.id := beq_iff_eq.mp h
      have hlaneid : g.id = lane := by rw [hg]; rfl
      rw [hlaneid] at heq
      obtain ⟨mb, hmb, _, _, hmid⟩ := pkce_lanesOf_mem hlane
      have hinmb : mb ∈ boxes.filter
          (fun b_ => inLane boxes b_.id lane) := by
        apply List.mem_filter.mpr
        refine ⟨hmb, ?_⟩
        rw [hmid]
        exact pkce_inLane_self hlane hnodupM
      refine List.mem_map.mpr ⟨mb, hinmb, ?_⟩
      show mb.id = b.id
      rw [hmid, heq]
    · have hmem : b.id ∈ g.members := of_decide_eq_true h
      rw [hmems] at hmem
      exact hmem
  have hfind : s.boxes.find? (fun b_ => b_.id == b.id) = some b :=
    pkce_find?_of_mem_nodup_key hnS hb
  have hsmem : axis.start b.rect ∈ contentValues boxes s axis lane
      ((boxes.filter fun b_ => inLane boxes b_.id lane).map (·.id)) := by
    unfold contentValues
    exact List.mem_append.mpr
      (Or.inl (pkce_boxvals_mem (axis := axis) hmemid hfind).1)
  have hemem : axis.start b.rect + axis.length b.rect ∈ contentValues boxes s axis lane
      ((boxes.filter fun b_ => inLane boxes b_.id lane).map (·.id)) := by
    unfold contentValues
    exact List.mem_append.mpr
      (Or.inl (pkce_boxvals_mem (axis := axis) hmemid hfind).2)
  obtain ⟨lo, hi, hbnd, hlo, _⟩ := pkce_content_bounded hsmem
  have hhi := (pkce_mem_bounds hemem hbnd).2
  have hext : (bounds (contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map (·.id)))).getD
      (st, st) = (lo, hi) := by rw [hbnd, Option.getD_some]
  have hth : g.thickness = sp.title + 2 * sp.clear +
      (((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).2 -
      ((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).1) := by rw [hg]; rfl
  have hsh : g.shift = st + sp.title + sp.clear -
      ((bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map
          (·.id)))).getD (st, st)).1 := by rw [hg]; rfl
  have hgoal : g.start ≤ axis.start b.rect + g.shift ∧
      axis.start b.rect + axis.length b.rect + g.shift ≤
        g.start + g.thickness := by
    rw [hst, hsh, hth, hext]
    dsimp only
    obtain ⟨ht, hc⟩ := hnn
    omega
  exact hgoal

/-! ## Tiling order and strip separation. -/

private theorem pkce_tiled_start_ge {s0 : Int} {bs : List Band}
    (ht : Tiled s0 bs) (hth : ∀ g ∈ bs, 0 ≤ g.thickness)
    {k : Nat} (hk : k < bs.length) : s0 ≤ bs[k].start := by
  induction bs generalizing s0 k with
  | nil => simp at hk
  | cons b rest ih =>
    obtain ⟨hstart, htt⟩ := ht
    have htail : ∀ g ∈ rest, 0 ≤ g.thickness := fun g hg =>
      hth g (List.mem_cons_of_mem _ hg)
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at *
      omega
    | succ k =>
      have hk' : k < rest.length := by
        simp only [List.length_cons] at hk; omega
      have hge := ih htt htail hk'
      have h0 : 0 ≤ b.thickness :=
        hth b (List.mem_cons.mpr (Or.inl rfl))
      simp only [List.getElem_cons_succ]
      omega

private theorem pkce_tiled_upper_le {s0 : Int} {bs : List Band}
    {i j : Nat} (ht : Tiled s0 bs)
    (hi : i < bs.length) (hj : j < bs.length) (hij : i < j)
    (hth : ∀ g ∈ bs, 0 ≤ g.thickness) :
    bs[i].start + bs[i].thickness ≤ bs[j].start := by
  induction bs generalizing s0 i j with
  | nil => simp at hi
  | cons b rest ih =>
    obtain ⟨hstart, htt⟩ := ht
    have htail : ∀ g ∈ rest, 0 ≤ g.thickness := fun g hg =>
      hth g (List.mem_cons_of_mem _ hg)
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        have hj' : j < rest.length := by
          simp only [List.length_cons] at hj; omega
        have hge := pkce_tiled_start_ge htt htail hj'
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hi' : i < rest.length := by
          simp only [List.length_cons] at hi; omega
        have hj' : j < rest.length := by
          simp only [List.length_cons] at hj; omega
        have hij' : i < j := by omega
        have hrec := ih htt hi' hj' hij' htail
        exact hrec

private theorem pkce_tiled_disjoint {s0 : Int} {bs : List Band} {a b : Band}
    (ht : Tiled s0 bs) (hth : ∀ g ∈ bs, 0 ≤ g.thickness)
    (ha : a ∈ bs) (hb : b ∈ bs) (hne : a ≠ b) :
    a.start + a.thickness ≤ b.start ∨ b.start + b.thickness ≤ a.start := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hij : i ≠ j := by
    intro hcon
    subst hcon
    exact hne rfl
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Or.inl (pkce_tiled_upper_le ht hi hj h hth)
  · exact Or.inr (pkce_tiled_upper_le ht hj hi h hth)

private theorem pkce_sum_map_nonneg {l : List Band}
    (h : ∀ b ∈ l, 0 ≤ b.thickness) : 0 ≤ (l.map (·.thickness)).sum := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb : 0 ≤ b.thickness := h b (List.mem_cons.mpr (Or.inl rfl))
    have hrest : 0 ≤ (rest.map (·.thickness)).sum :=
      ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    omega

private theorem pkce_lane_before_loose {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {lanes : List String} {st0 : Int} {g : Band}
    (hg : g ∈ layLanes boxes s axis sp lanes st0)
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear) :
    g.start + g.thickness ≤
      st0 + ((layLanes boxes s axis sp lanes st0).map (·.thickness)).sum := by
  induction lanes generalizing st0 with
  | nil => simp [layLanes] at hg
  | cons lane rest ih =>
    unfold layLanes at hg
    dsimp only at hg
    have hsum : 0 ≤ ((layLanes boxes s axis sp rest
        (st0 + (laneBand boxes s axis sp lane st0).thickness)).map
        (·.thickness)).sum := by
      apply pkce_sum_map_nonneg
      intro b' hb'
      obtain ⟨lane', hmem', st', rfl⟩ := pkce_layLanes_mem hb'
      exact laneBand_thickness_nonneg boxes s axis sp lane' st' hnn.1 hnn.2
    rw [List.mem_cons] at hg
    rcases hg with rfl | hg
    · have hstart : (laneBand boxes s axis sp lane st0).start = st0 := rfl
      have hth := laneBand_thickness_nonneg boxes s axis sp lane st0
        hnn.1 hnn.2
      have hcons : layLanes boxes s axis sp (lane :: rest) st0 =
          laneBand boxes s axis sp lane st0 ::
            layLanes boxes s axis sp rest
              (st0 + (laneBand boxes s axis sp lane st0).thickness) := rfl
      have hsumrw : ((layLanes boxes s axis sp (lane :: rest) st0).map
          (·.thickness)).sum =
          (laneBand boxes s axis sp lane st0).thickness +
            ((layLanes boxes s axis sp rest
              (st0 + (laneBand boxes s axis sp lane st0).thickness)).map
              (·.thickness)).sum := by
        rw [hcons, List.map_cons, List.sum_cons]
      rw [hsumrw]
      omega
    · have hrec := ih hg
      have hcons : layLanes boxes s axis sp (lane :: rest) st0 =
          laneBand boxes s axis sp lane st0 ::
            layLanes boxes s axis sp rest
              (st0 + (laneBand boxes s axis sp lane st0).thickness) := rfl
      have hsumrw : ((layLanes boxes s axis sp (lane :: rest) st0).map
          (·.thickness)).sum =
          (laneBand boxes s axis sp lane st0).thickness +
            ((layLanes boxes s axis sp rest
              (st0 + (laneBand boxes s axis sp lane st0).thickness)).map
              (·.thickness)).sum := by
        rw [hcons, List.map_cons, List.sum_cons]
      rw [hsumrw]
      have hth := laneBand_thickness_nonneg boxes s axis sp lane st0
        hnn.1 hnn.2
      omega

private theorem pkce_stripMiss {axis : Axis} {pts : List Point} {r : Rect}
    {Slo Shi Tlo Thi : Int}
    (hpts : ∀ p ∈ pts, Slo ≤ axis.point p ∧ axis.point p ≤ Shi)
    (hbox : Tlo ≤ axis.start r ∧ axis.start r + axis.length r ≤ Thi)
    (hdisj : Shi ≤ Tlo ∨ Thi ≤ Slo) : ¬ Polyline.hitsRect pts r := by
  have hall : Polyline.allSegsMiss pts r := by
    induction pts with
    | nil => trivial
    | cons p rest ih =>
      cases rest with
      | nil => trivial
      | cons q rest2 =>
        have hpm : p ∈ p :: q :: rest2 := List.mem_cons.mpr (Or.inl rfl)
        have hqm : q ∈ p :: q :: rest2 :=
          List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))
        have hp := hpts p hpm
        have hq := hpts q hqm
        refine ⟨?_, ih (fun p' hp' => hpts p' (List.mem_cons_of_mem _ hp'))⟩
        cases axis with
        | x =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox hdisj ⊢
          rcases hdisj with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inl (by omega))
        | y =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox hdisj ⊢
          rcases hdisj with h | h
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  intro hhit
  obtain ⟨_, _, hmiss⟩ := hhit
  exact hmiss hall


/-! ## Executed bundle, kept-route theorem, and C6 transport. -/

/-- The executed `applyPin` kept-route bundle: `pinBandsApplyPinKeptClear`
restricted to one executed base layout. Every conjunct is a concrete fact
about `layBands`/`applyPin` output, checked on executed probes
(`LaneBandsKeptClearExecutedTProbe`: `cov`, `end`, `setup`, `par`,
`nodup`, `noEF`, `c6` all `true` on `mCross`/`mSelf`/`mEmpty`/`mNoLane`).
The single narrow residual for loose-band routes against lane-band victims
lives in `PinLooseRouteLaneVictimClear`. -/
def PinKeptClearExecuted (axis : Axis) (bands : List Band) (s pinned : Scene)
    (boxes : List ModelBox) (sp : Spacing) : Prop :=
  bands = layBands boxes s axis sp (lanesOf boxes) ∧
  applyPin (buildPin axis bands s) bands s = .ok pinned ∧
  HardConstraints s.layoutDump ∧
  PinBoxCoverage boxes s axis sp ∧
  (∀ r ∈ s.routes,
    (∃ fb ∈ s.boxes, fb.id = r.fromId) ∧ ∃ tb ∈ s.boxes, tb.id = r.toId) ∧
  PinSetup s bands ∧
  PinSceneParents boxes s bands ∧
  (s.routes.map (·.id)).Nodup ∧
  (s.boxes.map (·.id)).Nodup ∧
  (boxes.map (·.id)).Nodup ∧
  (∀ b ∈ boxes, b.id ≠ "") ∧
  (0 ≤ sp.title ∧ 0 ≤ sp.clear)

/-- The single narrow residual: a loose-band route against a lane-band box.
Loose content excludes routes, so no strip bound applies to a kept loose
route (probe `mCross` route `e4` leaves its band strip); the miss against a
differently-shifted lane victim is therefore supplied by the caller. This is
strictly narrower than the target (one subcase only: same-index loose
covering plus lane victim with shifted-values hypotheses), true on every
executed probe. -/
def PinLooseRouteLaneVictimClear (axis : Axis) (bands : List Band)
    (s : Scene) : Prop :=
  ∀ (r old : Route) (b b_old : Box) (j1 j : Nat),
    old ∈ s.routes → b_old ∈ s.boxes →
    (hj1 : j1 < bands.length) → (bands[j1]'(hj1)).id = "" →
    bands.findIdx? (fun b_ => b_.id == old.fromId ||
      decide (old.fromId ∈ b_.members)) = some j1 →
    bands.findIdx? (fun b_ => b_.id == old.toId ||
      decide (old.toId ∈ b_.members)) = some j1 →
    (hj : j < bands.length) → (bands[j]'(hj)).id ≠ "" →
    bands.findIdx? (fun b_ => b_.id == b_old.id ||
      decide (b_old.id ∈ b_.members)) = some j →
    r.points = old.points.map (pkce_shiftPointAxis axis (bands[j1]'(hj1)).shift) →
    b.rect = pkce_shiftRectAxis axis (bands[j]'(hj)).shift b_old.rect →
    b.id = b_old.id → b_old.exclusive = true →
    b.id ∉ s.layoutDump.routeScope old →
    ¬ Polyline.hitsRect r.points b.rect

/-- The kept-route conclusion needed by `pinBands_c6`, from the executed
bundle and the one narrow loose-pair residual. -/
theorem pinKeptClearExecuted_holds (axis : Axis) (bands : List Band)
    (s pinned : Scene) (boxes : List ModelBox) (sp : Spacing)
    (hex : PinKeptClearExecuted axis bands s pinned boxes sp)
    (hloose : PinLooseRouteLaneVictimClear axis bands s) :
    ∀ (r : Route) (b : Box) (old : Route),
      r ∈ pinned.routes → old ∈ s.routes →
      (r, old) ∈ pinned.routes.zip s.routes →
      b ∈ pinned.boxes →
      b.exclusive = true → b.id ∉ pinned.layoutDump.routeScope r →
      ((∃ fi ti : Nat,
        bands.findIdx? (fun b_ => b_.id == r.fromId ||
          decide (r.fromId ∈ b_.members)) = some fi ∧
        bands.findIdx? (fun b_ => b_.id == r.toId ||
          decide (r.toId ∈ b_.members)) = some ti ∧
        (fi = ti ∨ old.points.length < 2)) ∨
      bands.findIdx? (fun b_ => b_.id == r.fromId ||
        decide (r.fromId ∈ b_.members)) = none ∨
      bands.findIdx? (fun b_ => b_.id == r.toId ||
        decide (r.toId ∈ b_.members)) = none ∨
      pinned.boxes.find? (fun b_ => b_.id == r.fromId) = none ∨
      pinned.boxes.find? (fun b_ => b_.id == r.toId) = none) →
      ¬ Polyline.hitsRect r.points b.rect := by
  obtain ⟨hbBands, happ, hbase, hcov, hend, hsetup, hpar, hnodupR, hnodupS,
    hnodupM, hneM, hnn⟩ := hex
  have hbaseC6 : Validator.C6 s.layoutDump := hbase.2.2.2.2.2.1
  obtain ⟨shB, shL, shR, shI, hboxes, hlabels, hroutes, hitems, hfold⟩ :=
    applyPin_shifted happ
  have hshlen : shR.length = s.routes.length := pkce_mapM_length hroutes
  have hrouteEq : pinned.routes = shR := pkce_fold_routes hfold
  have hplen : pinned.routes.length = s.routes.length := by
    rw [hrouteEq, hshlen]
  have hmaps := pkce_applyPin_box_maps happ
  intro r b old hr hold hpair hb hexcl hscope hreason
  have hzip : ∃ (i : Nat), pinned.routes[i]? = some r ∧ s.routes[i]? = some old := by
    have hmem : (r, old) ∈ pinned.routes.zip s.routes := hpair
    rw [List.mem_iff_getElem?] at hmem
    obtain ⟨i, hi⟩ := hmem
    rw [getElem?_zip_iff] at hi
    exact ⟨i, hi.1, hi.2⟩
  obtain ⟨i, hri, hoi⟩ := hzip
  have hi2 : i < s.routes.length := pkce_lt_of_getElem?_some hoi
  have hilen : i < shR.length := by rw [hshlen]; exact hi2
  obtain ⟨a_old, b_new, ha_old, hb_new, hfab⟩ :=
    getElem?_mapM_of_spec hroutes hi2 hilen
  obtain ⟨rid, rfrom, rto, rorth, hnonebr, hsomebr⟩ := pkce_pinRoute_spec hfab
  have hao_eq : a_old = old := Option.some.inj (ha_old.symm.trans hoi)
  have hrsh : shR[i]? = some r := by rw [← hrouteEq]; exact hri
  have hbr_eq : b_new = r := Option.some.inj (hb_new.symm.trans hrsh)
  have hr_from : r.fromId = old.fromId := by
    rw [← hbr_eq, ← hao_eq]; exact rfrom
  have hr_to : r.toId = old.toId := by
    rw [← hbr_eq, ← hao_eq]; exact rto
  have hr_pts : r.points = b_new.points := congrArg Route.points hbr_eq.symm
  have hscopeS : pinned.layoutDump.routeScope r = s.layoutDump.routeScope r :=
    pkce_applyPin_scope_eq happ r
  have hscope_old : b.id ∉ s.layoutDump.routeScope old := by
    rw [hscopeS] at hscope
    have hrr : s.layoutDump.routeScope r = s.layoutDump.routeScope old := by
      simp only [LayoutDump.routeScope, hr_from, hr_to]
    rw [hrr] at hscope
    exact hscope
  obtain ⟨k2, hk2lt, hkb2⟩ := List.getElem_of_mem hb
  have hblen : pinned.boxes.length = s.boxes.length := by
    have hlen := congrArg List.length hmaps.1
    simpa [List.length_map] using hlen
  have hk2s : k2 < s.boxes.length := by rw [← hblen]; exact hk2lt
  have hb_old_mem : s.boxes[k2]'hk2s ∈ s.boxes := List.getElem_mem _
  have hid_bo : (s.boxes[k2]'hk2s).id = b.id := by
    have hcongr := congrArg (fun l => l[k2]?) hmaps.1
    rw [List.getElem?_map, List.getElem?_map] at hcongr
    rw [List.getElem?_eq_getElem hk2lt, List.getElem?_eq_getElem hk2s] at hcongr
    have hid := Option.some.inj hcongr
    rw [hkb2] at hid
    exact hid.symm

  have hex_bo : (s.boxes[k2]'hk2s).exclusive = true := by
    have hcongr := congrArg (fun l => l[k2]?) hmaps.2.2
    rw [List.getElem?_map, List.getElem?_map] at hcongr
    rw [List.getElem?_eq_getElem hk2lt, List.getElem?_eq_getElem hk2s] at hcongr
    have hex := Option.some.inj hcongr
    rw [hkb2] at hex
    simp only [] at hex
    rw [hex] at hexcl
    exact hexcl
  have hscope_bo : (s.boxes[k2]'hk2s).id ∉ s.layoutDump.routeScope old := by
    rw [hid_bo]; exact hscope_old
  have hnoExcl : ∀ band ∈ bands, (s.boxes[k2]'hk2s).id ≠ band.id :=
    fun band hband => pkce_noExclFrame hsetup hb_old_mem hex_bo hband
  rcases hreason with ⟨fi, ti, hfi, hti, hor⟩ | hfiN | htiN | hpinF | hpinT
  · obtain ⟨hfi_lt, hfi_pred⟩ := pkce_findIdx_pred hfi
    obtain ⟨hti_lt, hti_pred⟩ := pkce_findIdx_pred hti
    rcases hor with hfi_eq | hshort
    · subst hfi_eq
      cases he : (buildPin axis bands s).route old.id with
      | none =>
        have hempty : old.points = [] := by
          by_cases hne : old.points = []
          · exact hne
          · exact absurd he (pkce_pinRoute_some hold hne)
        have earg : a_old.id = old.id := congrArg Route.id hao_eq
        have harg : (buildPin axis bands s).route a_old.id = none := by
          rw [earg]; exact he
        have hyp : b_new.points = old.points := by
          rw [← hao_eq]; exact hnonebr harg
        have hrnil : r.points = [] := by rw [hr_pts, hyp, hempty]
        intro hhit
        rw [hrnil] at hhit
        exact absurd trivial hhit.2.2
      | some d =>
        have earg : a_old.id = old.id := congrArg Route.id hao_eq
        have he' : (buildPin axis bands s).route a_old.id = some d := by
          rw [earg]; exact he
        have he'' : (buildPin axis bands s).route old.id = some d := by
          rw [← hao_eq]; exact he'
        obtain ⟨hd1, hd2, _, _⟩ := buildPin_route_find hnodupR hold he''
        have hfiδ : bandShift bands old.fromId = (bands[fi]'(hfi_lt)).shift := by
          have hfi' : bands.findIdx? (fun b_ => b_.id == old.fromId ||
            decide (old.fromId ∈ b_.members)) = some fi := by
            rw [← hr_from]; exact hfi
          obtain ⟨_, hshift⟩ := pkce_bandShift_eq_of_findIdx hfi'
          exact hshift
        have htiδ : bandShift bands old.toId = (bands[fi]'(hfi_lt)).shift := by
          have hti' : bands.findIdx? (fun b_ => b_.id == old.toId ||
            decide (old.toId ∈ b_.members)) = some fi := by
            rw [← hr_to]; exact hti
          obtain ⟨_, hshift⟩ := pkce_bandShift_eq_of_findIdx hti'
          exact hshift
        have hδeq : d.fromDelta = d.toDelta := by rw [hd1, hd2, hfiδ, htiδ]
        have hrm : routeMove d = Move.constant d.fromDelta := by
          unfold routeMove; simp [hδeq]
        obtain ⟨pts, hpts, hyeq2⟩ := hsomebr d he'
        have hpts2 : old.points.mapM ((Move.constant d.fromDelta).point axis) =
            .ok pts := by
          have hax : (buildPin axis bands s).axis = axis := rfl
          rw [hrm, hax, hao_eq] at hpts
          exact hpts
        have hyshift : b_new.points =
            old.points.map (pkce_shiftPointAxis axis d.fromDelta) := by
          rw [hyeq2]
          exact pkce_mapM_constant hpts2
        have hrshift : r.points =
            old.points.map (pkce_shiftPointAxis axis d.fromDelta) := by
          rw [hr_pts, hyshift]
        obtain ⟨g2, hg2mem, hg2cov⟩ := hcov _ hb_old_mem
        rw [← hbBands] at hg2mem
        have hjne := pkce_findIdx_ne_none_of_cover hg2mem hg2cov
        obtain ⟨j, hj⟩ : ∃ j, bands.findIdx? (fun b_ => b_.id ==
            (s.boxes[k2]'hk2s).id ||
            decide ((s.boxes[k2]'hk2s).id ∈ b_.members)) = some j := by
          cases hhj : bands.findIdx? (fun b_ => b_.id ==
              (s.boxes[k2]'hk2s).id ||
              decide ((s.boxes[k2]'hk2s).id ∈ b_.members)) with
          | none => exact absurd hhj hjne
          | some j => exact ⟨j, rfl⟩
        obtain ⟨hj_lt, hj_pred⟩ := pkce_findIdx_pred hj

        have hδj : (buildPin axis bands s).boxDelta (s.boxes[k2]'hk2s).id =
            (bands[j]'(hj_lt)).shift := by
          obtain ⟨_, hshift⟩ := pkce_bandShift_eq_of_findIdx hj
          exact (buildPin_boxDelta _).trans hshift
        have hk2len : k2 < shB.length := by
          have hlen := pkce_mapM_length hboxes
          rw [hlen]; exact hk2s
        obtain ⟨ba_old, bb_new, ha_oldB, hb_newB, hfbry⟩ :=
          getElem?_mapM_of_spec hboxes hk2s hk2len
        have hba_eq : ba_old = s.boxes[k2]'hk2s :=
          Option.some.inj
            (ha_oldB.symm.trans (List.getElem?_eq_getElem hk2s))
        rw [hba_eq] at hfbry
        obtain ⟨br', hbr', hbrfl⟩ := pkce_pinBox_spec hfbry
        obtain ⟨w, hw, hrectEq, hval⟩ := moveConstant_rect_value hbr'
        have hacc : shB[k2]? = some bb_new := hb_newB
        have hbrid : bb_new.id = (s.boxes[k2]'(hk2s)).id := by rw [hbrfl]
        have hneFold : ∀ band ∈ bands, bb_new.id ≠ band.id := by
          intro band hband
          rw [hbrid]
          exact hnoExcl band hband
        obtain ⟨kb', hkb', hrect', hid'⟩ :=
          pkce_fold_keptRect hfold hacc hneFold
        have hpb : pinned.boxes[k2]? = some b := by
          rw [List.getElem?_eq_getElem hk2lt, hkb2]
        have hbb' : kb' = b := Option.some.inj (hkb'.symm.trans hpb)
        have hbrr : bb_new.rect = br' := by rw [hbrfl]
        have hbrect : b.rect = pkce_shiftRectAxis axis
            ((buildPin axis bands s).boxDelta (s.boxes[k2]'hk2s).id)
            (s.boxes[k2]'hk2s).rect := by
          have h1 : b.rect = br' := by rw [← hbb', hrect', hbrr]
          rw [h1, hrectEq, hval]
          rfl
        have hδ : d.fromDelta = (bands[fi]'(hfi_lt)).shift := by
          rw [hd1]; exact hfiδ
        have hδjj : (buildPin axis bands s).boxDelta
            (s.boxes[k2]'hk2s).id = (bands[j]'(hj_lt)).shift := hδj
        by_cases hdeq : (buildPin axis bands s).boxDelta
            (s.boxes[k2]'hk2s).id = d.fromDelta
        · have hrshift' : r.points = old.points.map
              (pkce_shiftPointAxis axis ((buildPin axis bands s).boxDelta
                (s.boxes[k2]'hk2s).id)) := by
            rw [hdeq]; exact hrshift
          have hscope_bo : (s.boxes[k2]'hk2s).id ∉
              s.layoutDump.routeScope old := by
            rw [hid_bo]; exact hscope_old
          have hbase_hit := hbaseC6 old hold _ hb_old_mem hex_bo hscope_bo
          rw [hrshift', hbrect]
          have hiff := pkce_hitsRect_axis_shift axis
            ((buildPin axis bands s).boxDelta (s.boxes[k2]'hk2s).id)
            old.points (s.boxes[k2]'hk2s).rect
          exact fun h => hbase_hit (hiff.mp h)
        · have hneδ : (bands[fi]'(hfi_lt)).shift ≠ (bands[j]'(hj_lt)).shift := by
            rw [← hδ, ← hδjj]; exact Ne.symm hdeq
          have hnegg : bands[fi]'(hfi_lt) ≠ bands[j]'(hj_lt) := by
            intro hcon
            apply hneδ
            rw [hcon]
          have hgfiL : bands[fi]'(hfi_lt) ∈
              layBands boxes s axis sp (lanesOf boxes) := by
            rw [← hbBands]
            exact List.getElem_mem hfi_lt
          have hgjL : bands[j]'(hj_lt) ∈
              layBands boxes s axis sp (lanesOf boxes) := by
            rw [← hbBands]
            exact List.getElem_mem hj_lt
          obtain hsh_fi | hsh_fi :=
            pkce_layBands_mem hgfiL
          · obtain ⟨lane, hlane, st, hgeq⟩ := hsh_fi
            have hfromL : inLane boxes r.fromId lane = true := by
              have hor2 : ((bands[fi]'(hfi_lt)).id == r.fromId) = true ∨
                  decide (r.fromId ∈ (bands[fi]'(hfi_lt)).members) = true := by
                rw [Bool.or_eq_true] at hfi_pred
                exact hfi_pred
              rcases hor2 with h | h
              · have heq : (bands[fi]'(hfi_lt)).id = r.fromId :=
                  beq_iff_eq.mp h
                have hlaneid : (bands[fi]'(hfi_lt)).id = lane := by rw [hgeq]; rfl
                rw [hlaneid] at heq
                rw [← heq]
                exact pkce_inLane_self hlane hnodupM
              · have hmem : r.fromId ∈ (bands[fi]'(hfi_lt)).members :=
                  of_decide_eq_true h
                have hmemL : (bands[fi]'(hfi_lt)).members =
                    (boxes.filter fun b_ => inLane boxes b_.id lane).map
                      (·.id) := by rw [hgeq]; rfl
                rw [hmemL] at hmem
                exact pkce_inLane_of_mem hmem rfl
            have htoL : inLane boxes r.toId lane = true := by
              have hor2 : ((bands[fi]'(hfi_lt)).id == r.toId) = true ∨
                  decide (r.toId ∈ (bands[fi]'(hfi_lt)).members) = true := by
                rw [Bool.or_eq_true] at hti_pred
                exact hti_pred
              rcases hor2 with h | h
              · have heq : (bands[fi]'(hfi_lt)).id = r.toId :=
                  beq_iff_eq.mp h
                have hlaneid : (bands[fi]'(hfi_lt)).id = lane := by rw [hgeq]; rfl
                rw [hlaneid] at heq
                rw [← heq]
                exact pkce_inLane_self hlane hnodupM
              · have hmem : r.toId ∈ (bands[fi]'(hfi_lt)).members :=
                  of_decide_eq_true h
                have hmemL : (bands[fi]'(hfi_lt)).members =
                    (boxes.filter fun b_ => inLane boxes b_.id lane).map
                      (·.id) := by rw [hgeq]; rfl
                rw [hmemL] at hmem
                exact pkce_inLane_of_mem hmem rfl
            have hrshift' : r.points = old.points.map
                (pkce_shiftPointAxis axis (bands[fi]'(hfi_lt)).shift) := by
              rw [hrshift, hδ]
            have hroute_slot : ∀ p ∈ r.points,
                (bands[fi]'(hfi_lt)).start ≤ axis.point p ∧
                axis.point p ≤ (bands[fi]'(hfi_lt)).start +
                  (bands[fi]'(hfi_lt)).thickness := by
              intro p hp
              rw [hrshift'] at hp
              obtain ⟨p_old, hp_old, rfl⟩ := List.mem_map.mp hp
              have hslot := pkce_laneSlot_route hgeq hold hp_old
                (by rw [← hr_from]; exact hfromL)
                (by rw [← hr_to]; exact htoL) hnodupS hnn
              rw [pkce_shiftPointAxis_point]
              exact hslot
            obtain hsh_j | hsh_j := pkce_layBands_mem hgjL
            · obtain ⟨lane2, hlane2, st2, hgeq2⟩ := hsh_j
              have hcov2 : ((bands[j]'(hj_lt)).id ==
                  (s.boxes[k2]'hk2s).id ||
                  decide ((s.boxes[k2]'hk2s).id ∈
                    (bands[j]'(hj_lt)).members)) = true := hj_pred
              have hbox_slot := pkce_laneSlot_box hgeq2 hb_old_mem hcov2
                hnodupS hnn hnodupM hlane2
              have hbshift : b.rect = pkce_shiftRectAxis axis
                  (bands[j]'(hj_lt)).shift (s.boxes[k2]'hk2s).rect := by
                rw [← hδjj]; exact hbrect
              have hbox_span : (bands[j]'(hj_lt)).start ≤ axis.start b.rect ∧
                  axis.start b.rect + axis.length b.rect ≤
                  (bands[j]'(hj_lt)).start + (bands[j]'(hj_lt)).thickness := by
                rw [hbshift, pkce_shiftRectAxis_start,
                  pkce_shiftRectAxis_length]
                obtain ⟨hs1, hs2⟩ := hbox_slot
                exact ⟨hs1, by omega⟩
              have hth : ∀ g ∈ layBands boxes s axis sp (lanesOf boxes),
                  0 ≤ g.thickness := by
                intro g hg
                exact pkce_band_thick_nonneg hg hnn
              have hdisj := pkce_tiled_disjoint
                (layBands_tiled boxes s axis sp (lanesOf boxes)) hth
                hgfiL hgjL hnegg
              exact pkce_stripMiss hroute_slot hbox_span hdisj
            · obtain ⟨lo, hlo, hgeq2⟩ := hsh_j
              have hgjid : (bands[j]'(hj_lt)).id = "" := by
                rw [hgeq2]
                unfold looseBand
                split <;> rfl
              have hlo_mem : (s.boxes[k2]'hk2s).id ∈ lo := by
                have hor3 : ((bands[j]'(hj_lt)).id ==
                    (s.boxes[k2]'hk2s).id) = true ∨
                  decide ((s.boxes[k2]'hk2s).id ∈
                    (bands[j]'(hj_lt)).members) = true := by
                  rw [Bool.or_eq_true] at hj_pred
                  exact hj_pred
                rcases hor3 with h | h
                · have heq : (bands[j]'(hj_lt)).id =
                      (s.boxes[k2]'hk2s).id := beq_iff_eq.mp h
                  rw [hgjid] at heq
                  exact absurd heq.symm
                    (hsetup.2.2.2.1 _ hb_old_mem)
                · have hmem : (s.boxes[k2]'hk2s).id ∈
                      (bands[j]'(hj_lt)).members := of_decide_eq_true h
                  have hgm : (bands[j]'(hj_lt)).members = lo := by
                    rw [hgeq2]
                    unfold looseBand
                    split <;> rfl
                  rw [hgm] at hmem
                  exact hmem
              have hfindv := pkce_find?_of_mem_nodup_key (key := (·.id))
                hnodupS hb_old_mem
              have hloose_mem_s : axis.start (s.boxes[k2]'hk2s).rect ∈
                  contentValues boxes s axis "" lo := by
                have hred : (s.boxes.find? (fun b_ => b_.id ==
                    (s.boxes[k2]'hk2s).id)) = some (s.boxes[k2]'(hk2s)) := hfindv
                have hm := pkce_boxvals_mem (axis := axis) hlo_mem hred
                exact List.mem_append.mpr (Or.inl hm.1)
              have hloose_mem_e : axis.start (s.boxes[k2]'hk2s).rect +
                  axis.length (s.boxes[k2]'hk2s).rect ∈
                  contentValues boxes s axis "" lo := by
                have hred : (s.boxes.find? (fun b_ => b_.id ==
                    (s.boxes[k2]'hk2s).id)) = some (s.boxes[k2]'(hk2s)) := hfindv
                have hm := pkce_boxvals_mem (axis := axis) hlo_mem hred
                exact List.mem_append.mpr (Or.inl hm.2)
              obtain ⟨lo_l, hi_l, hbnd, hlo_le, _⟩ :=
                pkce_content_bounded hloose_mem_s
              have hshift2 : (bands[j]'(hj_lt)).shift =
                  (firstLaneStart s (lanesOf boxes) axis +
                    ((layLanes boxes s axis sp (lanesOf boxes)
                      (firstLaneStart s (lanesOf boxes) axis)).map
                      (·.thickness)).sum) + sp.clear - lo_l := by
                have hsh : (looseBand boxes s axis sp lo
                    (firstLaneStart s (lanesOf boxes) axis +
                      ((layLanes boxes s axis sp (lanesOf boxes)
                        (firstLaneStart s (lanesOf boxes) axis)).map
                        (·.thickness)).sum)).shift =
                    (firstLaneStart s (lanesOf boxes) axis +
                      ((layLanes boxes s axis sp (lanesOf boxes)
                        (firstLaneStart s (lanesOf boxes) axis)).map
                        (·.thickness)).sum) + sp.clear - lo_l := by
                  unfold looseBand
                  rw [hbnd]
                rw [hgeq2]
                exact hsh
              have hfiLne : (bands[fi]'(hfi_lt)).id ≠ "" := by
                have hid : (bands[fi]'(hfi_lt)).id = lane := by rw [hgeq]; rfl
                rw [hid]
                obtain ⟨mb, hmb, _, _, hmid⟩ := pkce_lanesOf_mem hlane
                have hne := hneM mb hmb
                rw [← hmid]
                exact hne
              have hgfiL : bands[fi]'(hfi_lt) ∈
                  layBands boxes s axis sp (lanesOf boxes) := by
                rw [← hbBands]
                exact List.getElem_mem hfi_lt
              have hmemL : bands[fi]'(hfi_lt) ∈ layLanes boxes s axis sp
                  (lanesOf boxes)
                  (firstLaneStart s (lanesOf boxes) axis) :=
                pkce_layBands_layLanes hgfiL hfiLne
              have hupper : (bands[fi]'(hfi_lt)).start +
                  (bands[fi]'(hfi_lt)).thickness ≤
                  firstLaneStart s (lanesOf boxes) axis +
                    ((layLanes boxes s axis sp (lanesOf boxes)
                      (firstLaneStart s (lanesOf boxes) axis)).map
                      (·.thickness)).sum :=
                pkce_lane_before_loose hmemL hnn
              have hvlower : firstLaneStart s (lanesOf boxes) axis +
                  ((layLanes boxes s axis sp (lanesOf boxes)
                    (firstLaneStart s (lanesOf boxes) axis)).map
                    (·.thickness)).sum ≤ axis.start b.rect := by
                rw [hbrect, pkce_shiftRectAxis_start, hδj, hshift2]
                have h2 : 0 ≤ sp.clear := hnn.2
                omega
              exact pkce_stripMiss hroute_slot
                ⟨Int.le_refl _, Int.le_refl _⟩
                (Or.inl (Int.le_trans hupper hvlower))
          · obtain ⟨lo1, hlo1, hgeq1⟩ := hsh_fi
            have hfiL : (bands[fi]'(hfi_lt)).id = "" := by
              rw [hgeq1]
              unfold looseBand
              split <;> rfl
            by_cases hjL : (bands[j]'(hj_lt)).id = ""
            · obtain hsh_j2 | hsh_j2 := pkce_layBands_mem hgjL
              · obtain ⟨lane2, hlane2, st2, hgeq2⟩ := hsh_j2
                have hid2 : (bands[j]'(hj_lt)).id = lane2 := by rw [hgeq2]; rfl
                rw [hid2] at hjL
                obtain ⟨mb, hmb, _, _, hmid⟩ := pkce_lanesOf_mem hlane2
                exact absurd hjL (by rw [← hmid]; exact hneM mb hmb)
              · obtain ⟨lo2, hlo2, hgeq2⟩ := hsh_j2
                have heq : bands[fi]'(hfi_lt) = bands[j]'(hj_lt) := by
                  rw [hgeq1, hgeq2, hlo1, hlo2]
                exact absurd heq hnegg
            · have hfi' : bands.findIdx? (fun b_ => b_.id == old.fromId ||
                  decide (old.fromId ∈ b_.members)) = some fi := by
                rw [← hr_from]; exact hfi
              have hti' : bands.findIdx? (fun b_ => b_.id == old.toId ||
                  decide (old.toId ∈ b_.members)) = some fi := by
                rw [← hr_to]; exact hti
              have hrshift' : r.points = old.points.map
                  (pkce_shiftPointAxis axis (bands[fi]'(hfi_lt)).shift) := by
                rw [hrshift, hδ]
              have hbrect' : b.rect = pkce_shiftRectAxis axis
                  (bands[j]'(hj_lt)).shift (s.boxes[k2]'hk2s).rect := by
                rw [← hδjj]; exact hbrect
              have hbid : b.id = (s.boxes[k2]'hk2s).id := hid_bo.symm
              have hscope' : b.id ∉ s.layoutDump.routeScope old := by
                rw [← hid_bo]; exact hscope_bo
              exact hloose r old b _ fi j hold hb_old_mem hfi_lt hfiL hfi'
                hti' hj_lt hjL hj hrshift' hbrect' hbid hex_bo hscope'
    · -- Short preimage: fewer than two points never hit.
      cases he : (buildPin axis bands s).route old.id with
      | none =>
        have earg : a_old.id = old.id := congrArg Route.id hao_eq
        have harg : (buildPin axis bands s).route a_old.id =
            none := by rw [earg]; exact he
        have hyp : b_new.points = old.points := by
          rw [← hao_eq]; exact hnonebr harg
        rw [hr_pts, hyp]
        exact not_hits_of_short hshort
      | some d =>
        have earg : a_old.id = old.id := congrArg Route.id hao_eq
        have he' : (buildPin axis bands s).route a_old.id =
            some d := by rw [earg]; exact he
        obtain ⟨pts, hpts, hyeq2⟩ := hsomebr d he'
        have hlen := pkce_mapM_length hpts
        rw [hr_pts, hyeq2]
        have hlen2 : pts.length < 2 := by rw [hlen, hao_eq]; exact hshort
        exact not_hits_of_short hlen2
  · -- From-endpoint lookup misses: coverage contradicts it.
    obtain ⟨fb, hfbmem, hfbid⟩ := (hend old hold).1
    obtain ⟨g, hgmem, hgcov⟩ := hcov fb hfbmem
    rw [← hbBands] at hgmem
    have hgcov' : g.id = r.fromId ∨ r.fromId ∈ g.members := by
      rw [hfbid, ← hr_from] at hgcov
      exact hgcov
    exact absurd hfiN (pkce_findIdx_ne_none_of_cover hgmem hgcov')
  · -- To-endpoint lookup misses: coverage contradicts it.
    obtain ⟨fb, hfbmem, hfbid⟩ := (hend old hold).2
    obtain ⟨g, hgmem, hgcov⟩ := hcov fb hfbmem
    rw [← hbBands] at hgmem
    have hgcov' : g.id = r.toId ∨ r.toId ∈ g.members := by
      rw [hfbid, ← hr_to] at hgcov
      exact hgcov
    exact absurd htiN (pkce_findIdx_ne_none_of_cover hgmem hgcov')
  · -- Pinned from-endpoint box missing: id preservation contradicts it.
    obtain ⟨fb, hfbmem, hfbid⟩ := (hend old hold).1
    have hmem : ∃ b_ ∈ s.boxes, b_.id = r.fromId :=
      ⟨fb, hfbmem, by rw [hfbid, hr_from]⟩
    exact absurd hpinF (pkce_applyPin_boxFind_ne_none happ hmem)
  · -- Pinned to-endpoint box missing: id preservation contradicts it.
    obtain ⟨fb, hfbmem, hfbid⟩ := (hend old hold).2
    have hmem : ∃ b_ ∈ s.boxes, b_.id = r.toId :=
      ⟨fb, hfbmem, by rw [hfbid, hr_to]⟩
    exact absurd hpinT (pkce_applyPin_boxFind_ne_none happ hmem)

/-- Pinning keeps clause C6 (route clearance) for an executed swimlane
layout: the `pinBands_c6` conclusion with true premises only. The
`hkept` hypothesis is the executed replacement for the false universal
`pinBandsApplyPinKeptClear`; the caller supplies the bundle facts
(`PinBoxCoverage`, endpoint coverage, `PinSetup`, `PinSceneParents`,
uniqueness, model ids, spacing bounds, and the narrow loose-pair
residual), all of which hold on every executed probe. -/
theorem pinBands_c6_executed {m : Model} {base : FamilyResult}
    {pinned : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hpin : pinBands m.boxes m.options base.scene = .ok pinned)
    (hbase : HardConstraints base.scene.layoutDump)
    (hkept : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ (s1 : Scene),
        applyPin (buildPin (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
            sp (lanesOf m.boxes)) base.scene)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
            sp (lanesOf m.boxes)) base.scene = .ok s1 →
        PinKeptClearExecuted (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
            sp (lanesOf m.boxes)) base.scene s1 m.boxes sp ∧
        PinLooseRouteLaneVictimClear (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
            sp (lanesOf m.boxes)) base.scene) :
    Validator.C6 pinned.layoutDump := by
  have _ := hfam
  cases hlanes : lanesOf m.boxes with
  | nil =>
    rw [pinBands_no_lanes hlanes] at hpin
    have heq : base.scene = pinned := Except.ok.inj hpin
    subst heq
    exact hbase.2.2.2.2.2.1
  | cons _ _ =>
    have hlanes' : lanesOf m.boxes ≠ [] := by
      rw [hlanes]
      intro h
      cases h
    obtain ⟨sp, axis, bands, s1, s2, s3, strip, s4, hsp, haxis, hbands, happ,
        hroute, horig, hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec (boxes := m.boxes) (o := m.options)
        (s := base.scene) (r := pinned) hlanes' hpin
    have hbaseC6 : Validator.C6 base.scene.layoutDump := hbase.2.2.2.2.2.1
    have happ' : applyPin (buildPin (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
          sp (lanesOf m.boxes)) base.scene)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
          sp (lanesOf m.boxes)) base.scene = .ok s1 := by
      rw [← haxis, ← hbands]
      exact happ
    have hfr := rerouteBands_frame hroute
    have hfr1 : s2.layoutDump.boxes = s1.layoutDump.boxes := hfr.1
    obtain ⟨hhex, hloose⟩ := hkept sp hsp s1 happ'
    rw [← haxis, ← hbands] at hhex hloose
    have hC6s2 : Validator.C6 s2.layoutDump := by
      intro r' hr' b' hb' hex hscope
      have hb's1 : b' ∈ s1.boxes := by
        have hbeq : s2.layoutDump.boxes = s1.layoutDump.boxes := hfr.1
        rw [hbeq] at hb'
        exact hb'
      obtain ⟨r, hrmem, old, holdmem, hpair, _hidr, hfromr, htor, hcase⟩ :=
        rerouteBands_mem axis sp (LayoutConst.rank_gap.get m.options.profile)
        bands (buildPin axis bands base.scene) base.scene.routes s1 s2 hroute r' hr'
      have hscope1 : b'.id ∉ s1.layoutDump.routeScope r := by
        have heq : s2.layoutDump.routeScope r' = s1.layoutDump.routeScope r := by
          simp only [LayoutDump.routeScope, hfromr, htor]
          rw [ancestors_boxes_eq hfr1, ancestors_boxes_eq hfr1]
        rw [heq] at hscope
        exact hscope
      rcases hcase with ⟨hpts, hreason⟩ | ⟨fi, ti, fb, tb, ends, obs, pts,
        hfi, hti, hfb, htb, hends, hobs, hfind_pt, hpts⟩
      · -- Kept route: the executed bundle plus the loose-pair residual.
        have hclear := pinKeptClearExecuted_holds axis bands base.scene s1
          m.boxes sp hhex hloose r b' old hrmem holdmem hpair
          hb's1 hex hscope1 hreason
        rw [hpts]
        exact hclear
      · -- Fresh route: proved `findRoute` soundness plus obstacle coverage.
        have hmem : obstacleOf axis b'.rect ∈ obs := by
          rw [hobs]
          exact obstacle_cover s1 axis r b' hb's1 hex hscope1
        have hclear := pinBandsFindRouteClear_holds axis sp
          (buildPin axis bands base.scene) fb tb
          old.points ends hends obs (LayoutConst.rank_gap.get m.options.profile)
          pts hfind_pt (obstacleOf axis b'.rect) hmem b'.rect rfl
        rw [hpts]
        exact hclear
    have hC6s3 : Validator.C6 s3.layoutDump :=
      restoreOrigin_C6 axis s2 s3 horig hC6s2
    have hb43 : s4.layoutDump.boxes = s3.layoutDump.boxes := by
      rw [hstripEq]
      exact relocateLabels_boxes axis strip s3
    have hr43 : s4.layoutDump.routes = s3.layoutDump.routes := by
      rw [hstripEq]
      exact relocateLabels_routes axis strip s3
    have hC6s4 : Validator.C6 s4.layoutDump :=
      C6_of_boxes_routes_eq hb43 hr43 hC6s3
    have hgrowF := growCanvas_frame hgrow
    have hbP : pinned.layoutDump.boxes = s4.layoutDump.boxes := hgrowF.1
    have hrP : pinned.layoutDump.routes = s4.layoutDump.routes := hgrowF.2.1
    exact C6_of_boxes_routes_eq hbP hrP hC6s4

 /-- The per-pair above-box bound implies the original loose-pair residual:
 `pinLooseVictimMissOfAboveLane` applied after unfolding the private shift
 helpers to the public copies. -/
 theorem pinLooseRouteLaneVictimClear_of_above {axis : Axis} {bands : List Band}
     {s : Scene}
     (habove : PinLooseRouteAboveLaneBox axis bands s) :
     PinLooseRouteLaneVictimClear axis bands s := by
   intro r old b b_old j1 j hold hbmem hj1 hfiL hfi hti hj hjL hjcov hrshift hbrect hbid hexcl hscope
   have hscope' : b_old.id ∉ s.layoutDump.routeScope old := by
     rw [hbid] at hscope
     exact hscope
   have hweak : ∀ p ∈ old.points,
       axis.start b_old.rect + axis.length b_old.rect + (bands[j]'hj).shift ≤
         axis.point p + (bands[j1]'hj1).shift :=
     habove old hold b_old hbmem hexcl hscope' j1 hj1 hfiL hfi hti j hj hjL hjcov
   have hrPts' : r.points =
       old.points.map (lvShiftPoint axis (bands[j1]'hj1).shift) := by
     rw [hrshift]
     rfl
   have hbRect' : b.rect =
       lvShiftRect axis (bands[j]'hj).shift b_old.rect := by
     rw [hbrect]
     rfl
   exact pinLooseVictimMissOfAboveLane hrPts' hbRect' hweak

 /-- Closed C6 after the swimlane pin: the executed bundle plus the corrected
 loose-route above-box bound. The original residual is discharged by
 `pinLooseRouteLaneVictimClear_of_above`. -/
 theorem pinBands_c6_executed_closed {m : Model} {base : FamilyResult}
     {pinned : Scene}
     (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
     (hpin : pinBands m.boxes m.options base.scene = .ok pinned)
     (hbase : HardConstraints base.scene.layoutDump)
     (hkept : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
       ∀ (s1 : Scene),
         applyPin (buildPin (Axis.ofDirection m.options.direction)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene = .ok s1 →
         PinKeptClearExecuted (Axis.ofDirection m.options.direction)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene s1 m.boxes sp)
     (habove : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
       ∀ (s1 : Scene),
         applyPin (buildPin (Axis.ofDirection m.options.direction)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene = .ok s1 →
         PinLooseRouteAboveLaneBox (Axis.ofDirection m.options.direction)
           (layBands m.boxes base.scene (Axis.ofDirection m.options.direction)
             sp (lanesOf m.boxes)) base.scene) :
     Validator.C6 pinned.layoutDump := by
   exact pinBands_c6_executed hfam hpin hbase (fun sp hsp s1 happ =>
     ⟨hkept sp hsp s1 happ,
      pinLooseRouteLaneVictimClear_of_above (habove sp hsp s1 happ)⟩)

end LaneBands
end Layered
end Elegant
