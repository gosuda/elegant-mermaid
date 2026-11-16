import Elegant.GridDij

set_option autoImplicit false

/-! `simplify` drops repeated points and the middle of three collinear points. It keeps the
first and the last point, and it keeps every relation that survives the merge of two collinear
steps: axis alignment, and a miss of a rectangle of positive size. -/

namespace Elegant
namespace Grid

local instance : Inhabited ModelBox := ⟨{ id := "" }⟩

/-- A relation that two collinear steps merge into one. -/
def Mrg (R : Point → Point → Prop) : Prop :=
  ∀ a b p, collinear a b p = true → R a b → R b p → R a p

theorem collinear_iff (a b c : Point) :
    collinear a b c = true ↔ (a.x = b.x ∧ b.x = c.x) ∨ (a.y = b.y ∧ b.y = c.y) := by
  unfold collinear
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]

theorem mrg_aligned : Mrg Aligned := by
  intro a b p h _ _
  rw [collinear_iff] at h
  unfold Aligned
  omega

theorem mrg_axmiss {o : Rect} (hw : 0 < o.w) (hh : 0 < o.h) : Mrg (AxMiss o) := by
  intro a b p h h1 h2
  rw [collinear_iff] at h
  unfold AxMiss at *
  omega

/-- The accumulator of `simplify` holds the points in reverse order. -/
def RChain (R : Point → Point → Prop) : List Point → Prop
  | b :: a :: rest => R a b ∧ RChain R (a :: rest)
  | _ => True

theorem chain_reverse {R : Point → Point → Prop} : ∀ {l : List Point}, RChain R l →
    Chain R l.reverse
  | [], _ => trivial
  | [_], _ => trivial
  | b :: a :: rest, h => by
    have ih := chain_reverse h.2
    have hl : (a :: rest).reverse.getLast? = some a := by simp
    have := chain_snoc ih hl h.1
    simpa using this

theorem popCollinear_spec {R : Point → Point → Prop} (hm : Mrg R) (p : Point) :
    ∀ (acc : List Point), RChain R acc → (∀ b, acc.head? = some b → R b p) →
      RChain R (popCollinear acc p) ∧
        (∀ b, acc.head? = some b → ∃ h, (popCollinear acc p).head? = some h ∧ R h p) ∧
        (popCollinear acc p).getLast? = acc.getLast? := by
  intro acc
  induction acc with
  | nil => intro _ _; simp [popCollinear, RChain]
  | cons b rest ih =>
    intro hc hp
    cases rest with
    | nil =>
      change RChain R [b] ∧
        (∀ b', some b = some b' → ∃ h, some b = some h ∧ R h p) ∧
        ([b] : List Point).getLast? = [b].getLast?
      refine ⟨hc, fun b' hb' => ⟨b, rfl, ?_⟩, rfl⟩
      have := hp b (by simp)
      have hb := Option.some.inj hb'
      subst hb
      exact this
    | cons a rest' =>
      by_cases hcol : collinear a b p = true
      · have hrab := hc.1
        have hbp := hp b (by simp)
        have hap := hm a b p hcol hrab hbp
        have hdef : popCollinear (b :: a :: rest') p = popCollinear (a :: rest') p := by
          simp [popCollinear, hcol]
        rw [hdef]
        obtain ⟨i1, i2, i3⟩ := ih hc.2 (fun x hx => by
          have := Option.some.inj hx
          subst this
          exact hap)
        refine ⟨i1, fun b' _ => i2 a rfl, ?_⟩
        rw [i3]
        simp
      · have hdef : popCollinear (b :: a :: rest') p = b :: a :: rest' := by
          simp [popCollinear, hcol]
        rw [hdef]
        refine ⟨hc, fun b' hb' => ⟨b, rfl, ?_⟩, rfl⟩
        have hb := Option.some.inj hb'
        subst hb
        exact hp b (by simp)

def simplifyStep (acc : List Point) (p : Point) : List Point :=
  if acc.head? = some p then acc else p :: popCollinear acc p

theorem simplifyStep_chain {R : Point → Point → Prop} (hm : Mrg R)
    {acc : List Point} {p : Point} (hc : RChain R acc)
    (hp : ∀ b, acc.head? = some b → R b p) :
    RChain R (simplifyStep acc p) := by
  unfold simplifyStep
  split
  · exact hc
  · obtain ⟨hchain, hnext, _⟩ := popCollinear_spec hm p acc hc hp
    cases he : popCollinear acc p with
    | nil => trivial
    | cons b rest =>
      refine ⟨?_, ?_⟩
      · cases ha : acc with
        | nil => simp [ha, popCollinear] at he
        | cons a tail =>
          obtain ⟨b', hb', hr⟩ := hnext a (by rw [ha]; rfl)
          rw [he] at hb'
          have hbb : b = b' := Option.some.inj hb'
          simpa only [hbb] using hr
      · simpa only [he] using hchain

theorem simplifyStep_head (acc : List Point) (p : Point) :
    (simplifyStep acc p).head? = some p := by
  unfold simplifyStep
  split
  · assumption
  · rfl

theorem simplifyStep_last (acc : List Point) (p : Point) :
    (simplifyStep acc p).getLast? = (if acc = [] then some p else acc.getLast?) := by
  cases acc with
  | nil => simp [simplifyStep, popCollinear]
  | cons a rest =>
    have hlast := (popCollinear_spec (R := fun _ _ => True)
      (fun _ _ _ _ _ _ => trivial) p (a :: rest) (by
        induction rest generalizing a with
        | nil => trivial
        | cons b tail ih => exact ⟨trivial, ih b⟩)
      (fun _ _ => trivial)).2.2
    have hne : (a :: rest : List Point) ≠ [] := by simp
    simp only [hne, ↓reduceIte]
    unfold simplifyStep
    split
    · rfl
    · cases he : popCollinear (a :: rest) p with
      | nil =>
        have hnone : (a :: rest).getLast? = none := by
          rw [← hlast, he]
          rfl
        exact False.elim (hne (List.getLast?_eq_none_iff.mp hnone))
      | cons b tail =>
        simpa only [he, List.getLast?_cons_cons] using hlast

theorem simplifyFold_chain {R : Point → Point → Prop} (hm : Mrg R) :
    ∀ (ps acc : List Point), RChain R acc → Chain R ps →
      (∀ p, ps.head? = some p → ∀ b, acc.head? = some b → R b p) →
      RChain R (ps.foldl simplifyStep acc) := by
  intro ps
  induction ps with
  | nil => intro acc hc _ _; exact hc
  | cons p ps ih =>
    intro acc hc hps hp
    simp only [List.foldl_cons]
    apply ih _ (simplifyStep_chain hm hc (hp p rfl))
    · cases ps with
      | nil => trivial
      | cons q tail => exact hps.2
    · intro q hq b hb
      rw [simplifyStep_head] at hb
      have hpb : p = b := Option.some.inj hb
      subst b
      cases ps with
      | nil => simp at hq
      | cons q' tail =>
        have he : q' = q := Option.some.inj hq
        subst q
        exact hps.1

theorem simplify_chain {R : Point → Point → Prop} (hm : Mrg R)
    {ps : List Point} (hc : Chain R ps) : Chain R (simplify ps) := by
  unfold simplify
  apply chain_reverse
  exact simplifyFold_chain hm ps [] trivial hc (by
    intro p _ b hb
    simp at hb)

theorem simplify_aligned {ps : List Point} (h : Chain Aligned ps) :
    Chain Aligned (simplify ps) :=
  simplify_chain mrg_aligned h

theorem simplify_misses {o : Rect} (hw : 0 < o.w) (hh : 0 < o.h)
    {ps : List Point} (h : Chain (AxMiss o) ps) :
    Chain (AxMiss o) (simplify ps) :=
  simplify_chain (mrg_axmiss hw hh) h

theorem simplifyFold_head :
    ∀ (ps acc : List Point), (ps.foldl simplifyStep acc).head? =
      (match ps.getLast? with | some p => some p | none => acc.head?) := by
  intro ps
  induction ps with
  | nil => intro acc; rfl
  | cons p ps ih =>
    intro acc
    simp only [List.foldl_cons, ih]
    cases ps with
    | nil => exact simplifyStep_head acc p
    | cons q tail =>
      simp only [List.getLast?_cons_cons]
      cases hl : (q :: tail).getLast? with
      | none =>
        have hempty := List.getLast?_eq_none_iff.mp hl
        contradiction
      | some _last => rfl

theorem simplifyFold_last :
    ∀ (ps acc : List Point), (ps.foldl simplifyStep acc).getLast? =
      (if acc = [] then ps.head? else acc.getLast?) := by
  intro ps
  induction ps with
  | nil =>
    intro acc
    cases acc <;> simp
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, ih]
    have hnonempty : simplifyStep acc p ≠ [] := by
      intro he
      have hh := simplifyStep_head acc p
      rw [he] at hh
      contradiction
    simp only [hnonempty, ite_false]
    rw [simplifyStep_last]
    cases acc <;> simp

theorem simplify_endpoints (ps : List Point) :
    (simplify ps).head? = ps.head? ∧ (simplify ps).getLast? = ps.getLast? := by
  unfold simplify
  constructor
  · rw [List.head?_reverse]
    exact simplifyFold_last ps []
  · change (ps.foldl simplifyStep []).reverse.getLast? = ps.getLast?
    rw [List.getLast?_reverse, simplifyFold_head]
    cases ps.getLast? <;> rfl

theorem LatStep.geometry {lat : Lat} (hs : lat.Sorted) {o : Rect}
    (ho : o ∈ lat.leaves) {p q : Point} (h : LatStep lat p q) :
    AxMiss o p q ∧ Aligned p q := by
  obtain ⟨v, d, u, len, hstep, hp, hq⟩ := h
  rw [← hp, ← hq]
  exact Lat.step_geom hs hstep ho

theorem lattice_chain_geometry {lat : Lat} (hs : lat.Sorted) {o : Rect}
    (ho : o ∈ lat.leaves) {ps : List Point} (hc : Chain (LatStep lat) ps) :
    Chain (AxMiss o) ps ∧ Chain Aligned ps :=
  ⟨Chain.mono (fun _ _ h => (LatStep.geometry hs ho h).1) hc,
    Chain.mono (fun _ _ h => (LatStep.geometry hs ho h).2) hc⟩

/-- Search's unsimplified result is a source stub, a lattice walk, and a target stub.
The caller supplies the two stub facts, independently of Dijkstra's chosen walk. -/
theorem search_chain {r : Router} {used used' : Used} {cur : Nat}
    {sources targets : List End} {route : List Point}
    {R : Point → Point → Prop} (hm : Mrg R)
    (hl : ∀ p q, LatStep r.lat p q → R p q)
    (hsrc : ∀ s, s < 4 → R (sources.getD s default).port
      (r.lat.point (sources.getD s default).vertex))
    (htgt : ∀ s, s < 4 → R (r.lat.point (targets.getD s default).vertex)
      (targets.getD s default).port)
    (h : search r used cur sources targets = some (route, used')) :
    Chain R route := by
  obtain ⟨pts, s, t, mid, hr, hs, ht, hpts, hhead, hlast, hc⟩ := search_spec h
  rw [hr, hpts]
  apply simplify_chain hm
  have hmid := Chain.mono hl hc
  have htail := chain_snoc hmid hlast (htgt t ht)
  cases mid with
  | nil => simp at hhead
  | cons p rest =>
    have hp : p = r.lat.point (sources.getD s default).vertex := Option.some.inj hhead
    exact ⟨by simpa only [hp] using hsrc s hs, htail⟩

theorem search_endpoints {r : Router} {used used' : Used} {cur : Nat}
    {sources targets : List End} {route : List Point}
    (h : search r used cur sources targets = some (route, used')) :
    ∃ s t, s < 4 ∧ t < 4 ∧
      route.head? = some (sources.getD s default).port ∧
      route.getLast? = some (targets.getD t default).port := by
  obtain ⟨pts, s, t, mid, hr, hs, ht, hpts, _, _, _⟩ := search_spec h
  refine ⟨s, t, hs, ht, ?_, ?_⟩
  · rw [hr, (simplify_endpoints pts).1, hpts]
    rfl
  · rw [hr, (simplify_endpoints pts).2, hpts]
    have last_append (xs : List Point) (p : Point) :
        (xs ++ [p]).getLast? = some p := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        cases xs with
        | nil => rfl
        | cons y ys => exact ih
    exact last_append ((sources.getD s default).port :: mid) _

theorem Chain.orthogonal : ∀ {ps : List Point}, Chain Aligned ps →
    Polyline.isOrthogonal ps = true
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: rest, h => by
    rw [Polyline.isOrthogonal_cons, Bool.and_eq_true]
    refine ⟨?_, Chain.orthogonal h.2⟩
    simpa only [Aligned, Bool.or_eq_true, decide_eq_true_eq] using h.1

theorem Chain.misses {o : Rect} : ∀ {ps : List Point}, Chain (AxMiss o) ps →
    Polyline.allSegsMiss ps o
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => ⟨h.1.segMisses, Chain.misses h.2⟩

theorem Chain.not_hits {o : Rect} {ps : List Point} (h : Chain (AxMiss o) ps) :
    ¬ Polyline.hitsRect ps o := by
  intro hit
  exact hit.2.2 (Chain.misses h)

def PointIn (r : Rect) (p : Point) : Prop :=
  r.x ≤ p.x ∧ p.x ≤ r.x + r.w ∧ r.y ≤ p.y ∧ p.y ≤ r.y + r.h

theorem portOf_boundary (pad gx gy : Int) (r : Rect) (side : Nat)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) :
    Validator.onBoundary (portOf pad gx gy r side).1 r := by
  have hwd := fdiv_fmod_nonneg (pos := r.w) (columns := 2) hw (by omega)
  have hhd := fdiv_fmod_nonneg (pos := r.h) (columns := 2) hh (by omega)
  obtain rfl | rfl | rfl | hs : side = 0 ∨ side = 1 ∨ side = 2 ∨ 3 ≤ side := by omega
  · simp [portOf, Validator.onBoundary]
    omega
  · simp [portOf, Validator.onBoundary]
    omega
  · simp [portOf, Validator.onBoundary]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, side = k + 3 := ⟨side - 3, by omega⟩
    simp [portOf, Validator.onBoundary]
    omega

theorem portOf_aligned (pad gx gy : Int) (r : Rect) (side : Nat) :
    Aligned (portOf pad gx gy r side).1 (portOf pad gx gy r side).2 := by
  obtain rfl | rfl | rfl | hs : side = 0 ∨ side = 1 ∨ side = 2 ∨ 3 ≤ side := by omega
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨k, rfl⟩ : ∃ k, side = k + 3 := ⟨side - 3, by omega⟩
    exact Or.inr rfl

theorem portOf_grown (pad gx gy : Int) (r : Rect) (side : Nat)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (hp : 0 ≤ pad)
    (hx : pad ≤ gx) (hy : pad ≤ gy) :
    PointIn (grow r gx gy) (portOf pad gx gy r side).1 ∧
      PointIn (grow r gx gy) (portOf pad gx gy r side).2 := by
  have hwd := fdiv_fmod_nonneg (pos := r.w) (columns := 2) hw (by omega)
  have hhd := fdiv_fmod_nonneg (pos := r.h) (columns := 2) hh (by omega)
  obtain rfl | rfl | rfl | hs : side = 0 ∨ side = 1 ∨ side = 2 ∨ 3 ≤ side := by omega
  · simp only [portOf, PointIn, grow]
    omega
  · simp only [portOf, PointIn, grow]
    omega
  · simp only [portOf, PointIn, grow]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, side = k + 3 := ⟨side - 3, by omega⟩
    simp only [portOf, PointIn, grow]
    omega

theorem Sep.segment_misses {o band : Rect} {p q : Point}
    (hs : Sep o band) (hp : PointIn band p) (hq : PointIn band q) :
    AxMiss o p q := by
  unfold Sep at hs
  unfold PointIn at hp hq
  unfold AxMiss
  omega

theorem portOf_misses {o r : Rect} {pad gx gy : Int} {side : Nat}
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (hp : 0 ≤ pad)
    (hx : pad ≤ gx) (hy : pad ≤ gy) (hsep : Sep o (grow r gx gy)) :
    AxMiss o (portOf pad gx gy r side).1 (portOf pad gx gy r side).2 := by
  have hb := portOf_grown pad gx gy r side hw hh hp hx hy
  exact hsep.segment_misses hb.1 hb.2

theorem Lat.vertex_point {lat : Lat} {p : Point} {v : Nat}
    (h : lat.vertex p = some v) : lat.point v = p := by
  unfold Lat.vertex at h
  cases hx : lat.xs.findIdx? (· == p.x) with
  | none => simp [hx] at h
  | some i =>
    cases hy : lat.ys.findIdx? (· == p.y) with
    | none => simp [hx, hy] at h
    | some j =>
      have hv : i * lat.ny + j = v := Option.some.inj (by simpa [hx, hy] using h)
      obtain ⟨hi, hxi, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hx
      obtain ⟨hj, hyj, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hy
      rw [← hv, Lat.point_vertex lat hj]
      have hxi' : lat.xs.getD i 0 = p.x := by
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
          Option.getD_some, beq_iff_eq] using hxi
      have hyj' : lat.ys.getD j 0 = p.y := by
        simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj,
          Option.getD_some, beq_iff_eq] using hyj
      rw [hxi', hyj']

theorem endsOf_spec {lat : Lat} {pad gx gy : Int} {rect : Rect} {ends : List End}
    (h : endsOf lat pad gx gy rect = some ends) :
    ends.length = 4 ∧ ∀ side, side < 4 →
      (ends.getD side default).port = (portOf pad gx gy rect side).1 ∧
      lat.point (ends.getD side default).vertex = (portOf pad gx gy rect side).2 := by
  cases h0 : lat.vertex (portOf pad gx gy rect 0).2 with
  | none => simp [endsOf, List.range_succ, h0] at h
  | some v0 =>
    cases h1 : lat.vertex (portOf pad gx gy rect 1).2 with
    | none => simp [endsOf, List.range_succ, h0, h1] at h
    | some v1 =>
      cases h2 : lat.vertex (portOf pad gx gy rect 2).2 with
      | none => simp [endsOf, List.range_succ, h0, h1, h2] at h
      | some v2 =>
        cases h3 : lat.vertex (portOf pad gx gy rect 3).2 with
        | none => simp [endsOf, List.range_succ, h0, h1, h2, h3] at h
        | some v3 =>
          simp [endsOf, List.range_succ, h0, h1, h2, h3] at h
          subst ends
          refine ⟨rfl, ?_⟩
          intro side hs
          obtain rfl | rfl | rfl | rfl : side = 0 ∨ side = 1 ∨ side = 2 ∨ side = 3 := by omega
          · exact ⟨rfl, Lat.vertex_point h0⟩
          · exact ⟨rfl, Lat.vertex_point h1⟩
          · exact ⟨rfl, Lat.vertex_point h2⟩
          · exact ⟨rfl, Lat.vertex_point h3⟩

theorem overlaps_false_sep {a b : Rect} (h : overlaps a b = false) : Sep a b := by
  have hnot : ¬ (a.x < b.x + b.w ∧ b.x < a.x + a.w ∧
      a.y < b.y + b.h ∧ b.y < a.y + a.h) := by
    intro hp
    have ht : overlaps a b = true := by
      simpa only [overlaps, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hp
    rw [h] at ht
    contradiction
  unfold Sep
  omega

theorem Site.vacant_leaf {s : Site} {thick : Int} {r o : Rect}
    (hv : s.vacant thick r = true) (ho : o ∈ s.leaves) : Sep r o := by
  apply overlaps_false_sep
  cases he : overlaps r o with
  | false => rfl
  | true =>
    have hany : s.leaves.any (fun b => overlaps r b) = true :=
      List.any_eq_true.mpr ⟨o, ho, he⟩
    simp [Site.vacant, hany] at hv

theorem Site.vacant_placed {s : Site} {thick : Int} {r o : Rect}
    (hv : s.vacant thick r = true) (ho : o ∈ s.placed) : Sep r o := by
  apply overlaps_false_sep
  cases he : overlaps r o with
  | false => rfl
  | true =>
    have hany : s.placed.any (fun b => overlaps r b) = true :=
      List.any_eq_true.mpr ⟨o, ho, he⟩
    simp [Site.vacant, hany] at hv

theorem loopOf_orthogonal (pad : Int) (r : Rect) :
    Polyline.isOrthogonal (loopOf pad r) = true := by
  apply Chain.orthogonal
  apply simplify_aligned
  simp only [Chain, Aligned]
  exact ⟨Or.inr True.intro, Or.inl True.intro, Or.inr True.intro, trivial⟩

theorem loopOf_ports (pad : Int) (r : Rect) (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) :
    ∃ p q, (loopOf pad r).head? = some p ∧ (loopOf pad r).getLast? = some q ∧
      Validator.onBoundary p r ∧ Validator.onBoundary q r := by
  have hthird := fdiv_fmod_nonneg (pos := r.h) (columns := 3) hh (by omega)
  have htwo := fdiv_fmod_nonneg (pos := 2 * r.h) (columns := 3) (by omega) (by omega)
  refine ⟨⟨r.x + r.w, r.y + Int.fdiv r.h 3⟩,
    ⟨r.x + r.w, r.y + Int.fdiv (2 * r.h) 3⟩, ?_, ?_, ?_, ?_⟩
  · exact (simplify_endpoints _).1
  · change (simplify _).getLast? = _
    rw [(simplify_endpoints _).2]
    rfl
  · simp [Validator.onBoundary]
    omega
  · simp [Validator.onBoundary]
    omega

theorem loopOf_not_hits {pad gx gy : Int} {r o : Rect}
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (hp : 0 ≤ pad)
    (hx : pad ≤ gx) (hy : 0 ≤ gy) (hsep : Sep o (grow r gx gy)) :
    ¬ Polyline.hitsRect (loopOf pad r) o := by
  by_cases how : 0 < o.w
  · by_cases hoh : 0 < o.h
    · apply Chain.not_hits
      apply simplify_misses how hoh
      have hthird := fdiv_fmod_nonneg (pos := r.h) (columns := 3) hh (by omega)
      have htwo := fdiv_fmod_nonneg (pos := 2 * r.h) (columns := 3) (by omega) (by omega)
      have h1 : PointIn (grow r gx gy) ⟨r.x + r.w, r.y + Int.fdiv r.h 3⟩ := by
        dsimp [PointIn, grow]
        omega
      have h2 : PointIn (grow r gx gy) ⟨r.x + r.w + pad, r.y + Int.fdiv r.h 3⟩ := by
        dsimp [PointIn, grow]
        omega
      have h3 : PointIn (grow r gx gy) ⟨r.x + r.w + pad, r.y + Int.fdiv (2 * r.h) 3⟩ := by
        dsimp [PointIn, grow]
        omega
      have h4 : PointIn (grow r gx gy) ⟨r.x + r.w, r.y + Int.fdiv (2 * r.h) 3⟩ := by
        dsimp [PointIn, grow]
        omega
      exact ⟨hsep.segment_misses h1 h2, hsep.segment_misses h2 h3,
        hsep.segment_misses h3 h4, trivial⟩
    · intro hit
      exact hoh hit.2.1
  · intro hit
    exact how hit.1

theorem search_orthogonal {r : Router} {used used' : Used} {cur : Nat}
    {sources targets : List End} {route : List Point} {a b : Rect} {pad gx gy : Int}
    (ha : endsOf r.lat pad gx gy a = some sources)
    (hb : endsOf r.lat pad gx gy b = some targets)
    (h : search r used cur sources targets = some (route, used')) :
    Polyline.isOrthogonal route = true := by
  apply Chain.orthogonal
  apply search_chain mrg_aligned
  · intro p q hpq
    obtain ⟨v, d, u, len, hs, hp, hq⟩ := hpq
    rw [← hp, ← hq]
    exact Lat.step_aligned hs
  · intro side hs
    have he := (endsOf_spec ha).2 side hs
    rw [he.1, he.2]
    exact portOf_aligned pad gx gy a side
  · intro side hs
    have he := (endsOf_spec hb).2 side hs
    rw [he.1, he.2]
    rcases portOf_aligned pad gx gy b side with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · exact h

theorem search_ports {r : Router} {used used' : Used} {cur : Nat}
    {sources targets : List End} {route : List Point} {a b : Rect} {pad gx gy : Int}
    (ha : endsOf r.lat pad gx gy a = some sources)
    (hb : endsOf r.lat pad gx gy b = some targets)
    (haw : 0 ≤ a.w) (hah : 0 ≤ a.h) (hbw : 0 ≤ b.w) (hbh : 0 ≤ b.h)
    (h : search r used cur sources targets = some (route, used')) :
    ∃ p q, route.head? = some p ∧ route.getLast? = some q ∧
      Validator.onBoundary p a ∧ Validator.onBoundary q b := by
  obtain ⟨s, t, hs, ht, hfirst, hlast⟩ := search_endpoints h
  refine ⟨_, _, hfirst, hlast, ?_, ?_⟩
  · rw [((endsOf_spec ha).2 s hs).1]
    exact portOf_boundary pad gx gy a s haw hah
  · rw [((endsOf_spec hb).2 t ht).1]
    exact portOf_boundary pad gx gy b t hbw hbh

theorem search_not_hits {r : Router} {used used' : Used} {cur : Nat}
    {sources targets : List End} {route : List Point} {a b o : Rect} {pad gx gy : Int}
    (hsorted : r.lat.Sorted) (ho : o ∈ r.lat.leaves)
    (ha : endsOf r.lat pad gx gy a = some sources)
    (hb : endsOf r.lat pad gx gy b = some targets)
    (haw : 0 ≤ a.w) (hah : 0 ≤ a.h) (hbw : 0 ≤ b.w) (hbh : 0 ≤ b.h)
    (hp : 0 ≤ pad) (hx : pad ≤ gx) (hy : pad ≤ gy)
    (hasep : Sep o (grow a gx gy)) (hbsep : Sep o (grow b gx gy))
    (h : search r used cur sources targets = some (route, used')) :
    ¬ Polyline.hitsRect route o := by
  by_cases hw : 0 < o.w
  · by_cases hh : 0 < o.h
    · apply Chain.not_hits
      apply search_chain (mrg_axmiss hw hh)
      · intro p q hpq
        exact (LatStep.geometry hsorted ho hpq).1
      · intro side hs
        have he := (endsOf_spec ha).2 side hs
        rw [he.1, he.2]
        exact portOf_misses haw hah hp hx hy hasep
      · intro side hs
        have he := (endsOf_spec hb).2 side hs
        rw [he.1, he.2]
        exact (portOf_misses hbw hbh hp hx hy hbsep).symm
      · exact h
    · intro hit
      exact hh hit.2.1
  · intro hit
    exact hw hit.1

theorem routeEdges_orthogonal {inp : RouteIn} {r : Router} :
    ∀ (es : List Edge) (k : Nat) (used : Used) (acc out : List (List Point)),
      (∀ pts ∈ acc, Polyline.isOrthogonal pts = true) →
      routeEdges inp r k es used acc = some out →
      ∀ pts ∈ out, Polyline.isOrthogonal pts = true := by
  intro es
  induction es with
  | nil =>
    intro k used acc out hacc h pts hpts
    simp only [routeEdges, Option.some.injEq] at h
    subst out
    exact hacc pts (List.mem_reverse.mp hpts)
  | cons e es ih =>
    intro k used acc out hacc h
    by_cases heq : e.fromBox = e.toBox
    · simp only [routeEdges, heq, ↓reduceIte] at h
      apply ih (k + 1) used _ out _ h
      intro pts hpts
      rcases List.mem_cons.mp hpts with hloop | hpts
      · subst pts
        exact loopOf_orthogonal inp.pad (inp.rects.getD e.toBox default)
      · exact hacc pts hpts
    · simp only [routeEdges, heq, ↓reduceIte] at h
      cases hsrc : endsOf r.lat inp.pad inp.gapX inp.gapY
          (inp.rects.getD e.fromBox default) with
      | none => simp only [List.getD_eq_getElem?_getD] at hsrc; simp [hsrc] at h
      | some src =>
        cases htgt : endsOf r.lat inp.pad inp.gapX inp.gapY
            (inp.rects.getD e.toBox default) with
        | none =>
          simp only [List.getD_eq_getElem?_getD] at hsrc htgt
          simp [hsrc, htgt] at h
        | some tgt =>
          simp only [hsrc, htgt] at h
          cases hs : search r used k src tgt with
          | none => simp [hs] at h
          | some pair =>
            obtain ⟨path, used'⟩ := pair
            simp only [hs] at h
            apply ih (k + 1) used' _ out _ h
            intro pts hpts
            rcases List.mem_cons.mp hpts with hpath | hpts
            · subst pts
              exact search_orthogonal hsrc htgt hs
            · exact hacc pts hpts

theorem routes_orthogonal {inp : RouteIn} {out : List (List Point)}
    (h : routes inp = .ok out) :
    ∀ pts ∈ out, Polyline.isOrthogonal pts = true := by
  unfold routes at h
  cases he : inp.edges with
  | nil => simp [he] at h; subst out; simp
  | cons e es =>
    simp only [he] at h
    cases hl : buildLat inp with
    | error err => simp [hl] at h
    | ok lat =>
      simp only [hl] at h
      cases hr : routeEdges inp ⟨lat, inp.bend, (e :: es).map fun e => (e.fromBox, e.toBox)⟩
          0 (e :: es) (Used.empty lat.cells) [] with
      | none => simp only [List.map_cons] at hr; simp [hr] at h
      | some paths =>
        simp only [hr, Except.ok.injEq] at h
        subst out
        exact routeEdges_orthogonal _ _ _ _ _ (by simp) hr

theorem strictlyInside_contained {outer inner : Rect}
    (h : strictlyInside outer inner = true) : outer.Contained inner := by
  simp only [strictlyInside, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold Rect.Contained
  omega

theorem Site.vacant_inside {s : Site} {thick : Int} {r : Rect}
    (h : s.vacant thick r = true) : s.canvas.Contained r := by
  apply strictlyInside_contained
  cases hi : strictlyInside s.canvas r with
  | false => simp [Site.vacant, hi] at h
  | true => rfl

theorem fitLabel_vacant {s : Site} {pad thick : Int} {route : List Point}
    {size : Size} {rect : Rect} (h : fitLabel s pad thick route size = some rect) :
    s.vacant thick rect = true :=
  List.find?_some h

theorem fitLabel_clear {s : Site} {pad thick : Int} {route : List Point}
    {size : Size} {rect : Rect} (h : fitLabel s pad thick route size = some rect) :
    s.canvas.Contained rect ∧ (∀ o ∈ s.leaves, Disjoint rect o) ∧
      (∀ o ∈ s.placed, Disjoint rect o) := by
  have hv := fitLabel_vacant h
  exact ⟨Site.vacant_inside hv,
    fun _ ho => (Site.vacant_leaf hv ho).disjoint,
    fun _ ho => (Site.vacant_placed hv ho).disjoint⟩

theorem routeEdges_length {inp : RouteIn} {r : Router} :
    ∀ (es : List Edge) (k : Nat) (used : Used) (acc out : List (List Point)),
      routeEdges inp r k es used acc = some out →
      out.length = es.length + acc.length := by
  intro es
  induction es with
  | nil =>
    intro k used acc out h
    simp only [routeEdges, Option.some.injEq] at h
    subst out
    simp
  | cons e es ih =>
    intro k used acc out h
    by_cases heq : e.fromBox = e.toBox
    · simp only [routeEdges, heq, ↓reduceIte] at h
      have hi := ih (k + 1) used _ out h
      simp only [List.length_cons] at hi ⊢
      omega
    · simp only [routeEdges, heq, ↓reduceIte] at h
      cases hsrc : endsOf r.lat inp.pad inp.gapX inp.gapY
          (inp.rects.getD e.fromBox default) with
      | none => simp only [List.getD_eq_getElem?_getD] at hsrc; simp [hsrc] at h
      | some src =>
        cases htgt : endsOf r.lat inp.pad inp.gapX inp.gapY
            (inp.rects.getD e.toBox default) with
        | none =>
          simp only [List.getD_eq_getElem?_getD] at hsrc htgt
          simp [hsrc, htgt] at h
        | some tgt =>
          simp only [hsrc, htgt] at h
          cases hs : search r used k src tgt with
          | none => simp [hs] at h
          | some pair =>
            obtain ⟨path, used'⟩ := pair
            simp only [hs] at h
            have hi := ih (k + 1) used' (path :: acc) out h
            simp only [List.length_cons] at hi ⊢
            omega

theorem block_routes_orthogonal {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) :
    ∀ pts ∈ res.routes, Polyline.isOrthogonal pts = true := by
  by_cases hv : inp.valid p.padding = true
  · simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i rts hr
            split at h
            · cases h
            · injection h with he
              subst res
              exact routes_orthogonal hr
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem BlockPlan.scene_orthogonal {pl : BlockPlan} {res : GLayout}
    (h : block pl.input pl.params = .ok res) :
    Validator.C4 (pl.scene res).layoutDump := by
  intro route hroute _horthogonal
  change route ∈ (pl.m.routes.zip res.routes).map
    (fun (r, pts) => (⟨r.id, r.fromId, r.toId, true, pts⟩ : Route)) at hroute
  obtain ⟨⟨modelRoute, points⟩, hzip, heq⟩ := List.mem_map.mp hroute
  subst route
  exact block_routes_orthogonal h points (List.of_mem_zip hzip).2

theorem layout_orthogonal {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C4 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_orthogonal hr

/-- A composite endpoint's stub is outside its frame, so it also misses every
descendant leaf inside that frame. -/
theorem portOf_misses_contained {r o : Rect} {pad gx gy : Int} {side : Nat}
    (hp : 0 ≤ pad) (hx : pad ≤ gx) (hy : pad ≤ gy) (hcontained : r.Contained o) :
    AxMiss o (portOf pad gx gy r side).1 (portOf pad gx gy r side).2 := by
  unfold Rect.Contained at hcontained
  obtain rfl | rfl | rfl | hs : side = 0 ∨ side = 1 ∨ side = 2 ∨ 3 ≤ side := by omega
  · simp only [portOf, AxMiss]
    omega
  · simp only [portOf, AxMiss]
    omega
  · simp only [portOf, AxMiss]
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, side = k + 3 := ⟨side - 3, by omega⟩
    simp only [portOf, AxMiss]
    omega

theorem loopOf_not_hits_contained {r o : Rect} {pad : Int}
    (hp : 0 ≤ pad) (hcontained : r.Contained o) :
    ¬ Polyline.hitsRect (loopOf pad r) o := by
  by_cases hw : 0 < o.w
  · by_cases hh : 0 < o.h
    · apply Chain.not_hits
      apply simplify_misses hw hh
      unfold Rect.Contained at hcontained
      change Chain (AxMiss o)
        [⟨r.x + r.w, r.y + Int.fdiv r.h 3⟩,
         ⟨r.x + r.w + pad, r.y + Int.fdiv r.h 3⟩,
         ⟨r.x + r.w + pad, r.y + Int.fdiv (2 * r.h) 3⟩,
         ⟨r.x + r.w, r.y + Int.fdiv (2 * r.h) 3⟩]
      refine ⟨Or.inr (Or.inl ?_), Or.inr (Or.inl ?_),
        Or.inr (Or.inl ?_), True.intro⟩ <;>
        dsimp <;> omega
    · intro hit
      exact hh hit.2.1
  · intro hit
    exact hw hit.1

theorem Ctx.stub_misses_leaf {c : Ctx} (hc : c.Wf) {i j side : Nat} {pad : Int}
    (hi : i < c.n) (hj : j < c.n) (hne : i ≠ j)
    (hkind : (c.box j).kind = Kind.leaf)
    (hp : 0 ≤ pad) (hx : pad ≤ c.gapX) (hy : pad ≤ c.gapY) :
    AxMiss (c.rect j) (portOf pad c.gapX c.gapY (c.rect i) side).1
      (portOf pad c.gapX c.gapY (c.rect i) side).2 := by
  by_cases hij : c.Up i j
  · exact portOf_misses_contained hp hx hy (c.rect_inside_ancestor hc hi hj hij)
  · have hji : ¬ c.Up j i := by
      intro hup
      have hcomposite := c.up_composite hc hup hne.symm hj
      rw [hkind] at hcomposite
      cases hcomposite
    have hsep := c.grown_sep hc j i hi hj hij hji
    have hf := c.rect_facts hc hi
    exact portOf_misses hf.wNonneg hf.hNonneg hp hx hy hsep

theorem Ctx.loop_misses_leaf {c : Ctx} (hc : c.Wf) {i j : Nat} {pad : Int}
    (hi : i < c.n) (hj : j < c.n) (hne : i ≠ j)
    (hkind : (c.box j).kind = Kind.leaf)
    (hp : 0 ≤ pad) (hx : pad ≤ c.gapX) :
    ¬ Polyline.hitsRect (loopOf pad (c.rect i)) (c.rect j) := by
  by_cases hij : c.Up i j
  · exact loopOf_not_hits_contained hp (c.rect_inside_ancestor hc hi hj hij)
  · have hji : ¬ c.Up j i := by
      intro hup
      have hcomposite := c.up_composite hc hup hne.symm hj
      rw [hkind] at hcomposite
      cases hcomposite
    have hsep := c.grown_sep hc j i hi hj hij hji
    have hf := c.rect_facts hc hi
    exact loopOf_not_hits hf.wNonneg hf.hNonneg hp hx hc.gapY hsep

theorem routeEdges_pairs {inp : RouteIn} {r : Router}
    {R : Edge → List Point → Prop}
    (hself : ∀ e, e.fromBox = e.toBox → R e (loopOf inp.pad (inp.rects.getD e.fromBox default)))
    (hsearch : ∀ e used k src tgt pts used',
      endsOf r.lat inp.pad inp.gapX inp.gapY (inp.rects.getD e.fromBox default) = some src →
      endsOf r.lat inp.pad inp.gapX inp.gapY (inp.rects.getD e.toBox default) = some tgt →
      search r used k src tgt = some (pts, used') → R e pts) :
    ∀ (es : List Edge) (k : Nat) (used : Used) (acc out : List (List Point)),
      routeEdges inp r k es used acc = some out →
      ∃ emitted, out = acc.reverse ++ emitted ∧ emitted.length = es.length ∧
        ∀ e pts, (e, pts) ∈ es.zip emitted → R e pts := by
  intro es
  induction es with
  | nil =>
    intro k used acc out h
    simp only [routeEdges, Option.some.injEq] at h
    exact ⟨[], by simpa using h.symm, rfl, by simp⟩
  | cons e es ih =>
    intro k used acc out h
    have nextCase : ∀ pts used', R e pts →
        routeEdges inp r (k + 1) es used' (pts :: acc) = some out →
        ∃ emitted, out = acc.reverse ++ emitted ∧ emitted.length = (e :: es).length ∧
          ∀ edge path, (edge, path) ∈ (e :: es).zip emitted → R edge path := by
      intro pts used' hp hn
      obtain ⟨tail, hout, hlen, hrel⟩ := ih (k + 1) used' (pts :: acc) out hn
      refine ⟨pts :: tail, ?_, by simp only [List.length_cons, hlen], ?_⟩
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hout
      · intro edge path hm
        simp only [List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with heq | hm
        · cases heq
          exact hp
        · exact hrel edge path hm
    by_cases heq : e.fromBox = e.toBox
    · simp only [routeEdges, heq, ↓reduceIte] at h
      apply nextCase _ used (hself e heq)
      simpa only [heq] using h
    · simp only [routeEdges, heq, ↓reduceIte] at h
      cases hsrc : endsOf r.lat inp.pad inp.gapX inp.gapY
          (inp.rects.getD e.fromBox default) with
      | none => simp only [List.getD_eq_getElem?_getD] at hsrc; simp [hsrc] at h
      | some src =>
        cases htgt : endsOf r.lat inp.pad inp.gapX inp.gapY
            (inp.rects.getD e.toBox default) with
        | none =>
          simp only [List.getD_eq_getElem?_getD] at hsrc htgt
          simp [hsrc, htgt] at h
        | some tgt =>
          simp only [hsrc, htgt] at h
          cases hs : search r used k src tgt with
          | none => simp [hs] at h
          | some pair =>
            obtain ⟨path, used'⟩ := pair
            simp only [hs] at h
            exact nextCase path used' (hsearch e used k src tgt path used' hsrc htgt hs) h

theorem Ctx.routeIn_rect {c : Ctx} {p : GParams} {i : Nat} (hi : i < c.n) :
    (c.routeIn p).rects.getD i default = c.rect i := by
  change ((List.range c.n).map c.rect).getD i default = c.rect i
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem Ctx.routeIn_leaf {c : Ctx} {p : GParams} {i : Nat}
    (hi : i < c.n) (hk : (c.box i).kind = Kind.leaf) :
    c.rect i ∈ (c.routeIn p).leaves := by
  change c.rect i ∈ ((List.range c.n).filter fun j => (c.box j).kind = Kind.leaf).map c.rect
  apply List.mem_map.mpr
  refine ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, ?_⟩, rfl⟩
  simp [hk]

theorem Ctx.search_misses_leaf {c : Ctx} (hc : c.Wf) {p : GParams}
    {r : Router} {used used' : Used} {cur i j k : Nat}
    {sources targets : List End} {route : List Point}
    (hi : i < c.n) (hj : j < c.n) (hk : k < c.n)
    (hki : i ≠ k) (hkj : j ≠ k) (hkind : (c.box k).kind = Kind.leaf)
    (hp : 0 ≤ p.padding) (hx : p.padding ≤ c.gapX) (hy : p.padding ≤ c.gapY)
    (hsorted : r.lat.Sorted) (hleaves : r.lat.leaves = (c.routeIn p).leaves)
    (ha : endsOf r.lat p.padding c.gapX c.gapY (c.rect i) = some sources)
    (hb : endsOf r.lat p.padding c.gapX c.gapY (c.rect j) = some targets)
    (h : search r used cur sources targets = some (route, used')) :
    ¬ Polyline.hitsRect route (c.rect k) := by
  by_cases hw : 0 < (c.rect k).w
  · by_cases hh : 0 < (c.rect k).h
    · apply Chain.not_hits
      apply search_chain (mrg_axmiss hw hh)
      · intro a b hab
        apply (LatStep.geometry hsorted ?_ hab).1
        rw [hleaves]
        exact c.routeIn_leaf hk hkind
      · intro side hs
        have he := (endsOf_spec ha).2 side hs
        rw [he.1, he.2]
        exact c.stub_misses_leaf hc hi hk hki hkind hp hx hy
      · intro side hs
        have he := (endsOf_spec hb).2 side hs
        rw [he.1, he.2]
        exact (c.stub_misses_leaf hc hj hk hkj hkind hp hx hy).symm
      · exact h
    · intro hit
      exact hh hit.2.1
  · intro hit
    exact hw hit.1

structure EdgeGeometry (c : Ctx) (e : Edge) (pts : List Point) : Prop where
  orthogonal : Polyline.isOrthogonal pts = true
  ports : ∃ a b, pts.head? = some a ∧ pts.getLast? = some b ∧
    Validator.onBoundary a (c.rect e.fromBox) ∧ Validator.onBoundary b (c.rect e.toBox)
  clearance : ∀ k, k < c.n → (c.box k).kind = Kind.leaf →
    e.fromBox ≠ k → e.toBox ≠ k → ¬ Polyline.hitsRect pts (c.rect k)

theorem Ctx.routeEdges_geometry {c : Ctx} (hc : c.Wf) {p : GParams} {r : Router}
    {used : Used} {paths : List (List Point)}
    (hbound : ∀ e ∈ c.inp.edges, e.fromBox < c.n ∧ e.toBox < c.n)
    (hp : 0 ≤ p.padding) (hx : p.padding ≤ c.gapX) (hy : p.padding ≤ c.gapY)
    (hsorted : r.lat.Sorted) (hleaves : r.lat.leaves = (c.routeIn p).leaves)
    (h : routeEdges (c.routeIn p) r 0 c.inp.edges used [] = some paths) :
    ∀ e pts, (e, pts) ∈ c.inp.edges.zip paths → EdgeGeometry c e pts := by
  have hself : ∀ (e : Edge), e.fromBox = e.toBox →
      (e ∈ c.inp.edges → EdgeGeometry c e
        (loopOf (c.routeIn p).pad ((c.routeIn p).rects.getD e.fromBox default))) := by
    intro e heq he
    have hb := hbound e he
    rw [c.routeIn_rect hb.1]
    have hf := c.rect_facts hc hb.1
    refine ⟨loopOf_orthogonal p.padding _, ?_, ?_⟩
    · rw [← heq]
      exact loopOf_ports p.padding _ hf.wNonneg hf.hNonneg
    · intro k hk hkind hne _hne'
      exact c.loop_misses_leaf hc hb.1 hk hne hkind hp hx
  have hsearch : ∀ (e : Edge) used cur src tgt pts used',
      endsOf r.lat (c.routeIn p).pad (c.routeIn p).gapX (c.routeIn p).gapY
        ((c.routeIn p).rects.getD e.fromBox default) = some src →
      endsOf r.lat (c.routeIn p).pad (c.routeIn p).gapX (c.routeIn p).gapY
        ((c.routeIn p).rects.getD e.toBox default) = some tgt →
      search r used cur src tgt = some (pts, used') →
      (e ∈ c.inp.edges → EdgeGeometry c e pts) := by
    intro e used cur src tgt pts used' ha hb hs he
    have hends := hbound e he
    rw [c.routeIn_rect hends.1] at ha
    rw [c.routeIn_rect hends.2] at hb
    have hf := c.rect_facts hc hends.1
    have ht := c.rect_facts hc hends.2
    refine ⟨search_orthogonal ha hb hs,
      search_ports ha hb hf.wNonneg hf.hNonneg ht.wNonneg ht.hNonneg hs, ?_⟩
    intro k hk hkind hki hkj
    exact c.search_misses_leaf hc hends.1 hends.2 hk hki hkj hkind hp hx hy
      hsorted hleaves ha hb hs
  obtain ⟨emitted, hout, _hlen, hrel⟩ := routeEdges_pairs hself hsearch _ _ _ _ _ h
  have heq : paths = emitted := by simpa only [List.reverse_nil, List.nil_append] using hout
  subst emitted
  intro e pts hm
  exact hrel e pts hm (List.of_mem_zip hm).1

theorem Ctx.routes_geometry {c : Ctx} (hc : c.Wf) {p : GParams}
    {paths : List (List Point)}
    (hbound : ∀ e ∈ c.inp.edges, e.fromBox < c.n ∧ e.toBox < c.n)
    (hp : 0 ≤ p.padding) (hx : p.padding ≤ c.gapX) (hy : p.padding ≤ c.gapY)
    (h : routes (c.routeIn p) = .ok paths) :
    ∀ e pts, (e, pts) ∈ c.inp.edges.zip paths → EdgeGeometry c e pts := by
  unfold routes at h
  change (match c.inp.edges with
    | [] => Except.ok []
    | edges =>
      match buildLat (c.routeIn p) with
      | .error err => .error err
      | .ok lat =>
        match routeEdges (c.routeIn p)
            ⟨lat, (c.routeIn p).bend, edges.map fun (e : Edge) => (e.fromBox, e.toBox)⟩
            0 edges (Used.empty lat.cells) [] with
        | some rs => .ok rs
        | none => .error .domain) = .ok paths at h
  cases he : c.inp.edges with
  | nil =>
    intro e pts hm
    simp only [List.zip_nil_left, List.not_mem_nil] at hm
  | cons edge rest =>
    rw [he] at h
    cases hl : buildLat (c.routeIn p) with
    | error err => rw [hl] at h; cases h
    | ok lat =>
      rw [hl] at h
      cases hr : routeEdges (c.routeIn p)
          ⟨lat, (c.routeIn p).bend, (edge :: rest).map fun e => (e.fromBox, e.toBox)⟩
          0 (edge :: rest) (Used.empty lat.cells) [] with
      | none =>
        dsimp only at h
        rw [hr] at h
        cases h
      | some out =>
        simp only [hr, Except.ok.injEq] at h
        subst paths
        have hroute : routeEdges (c.routeIn p)
            ⟨lat, (c.routeIn p).bend, c.inp.edges.map fun e => (e.fromBox, e.toBox)⟩
            0 c.inp.edges (Used.empty lat.cells) [] = some out := by
          simpa only [he] using hr
        simpa only [he] using c.routeEdges_geometry hc hbound hp hx hy
          (buildLat_sorted hl) (buildLat_leaves hl) hroute

theorem placeAll_canvas {inp : RouteIn} {rts : List (List Point)} {canvas out : Rect}
    {labels : List Rect} (h : placeAll inp rts canvas = .ok (labels, out)) :
    out.x = canvas.x ∧ out.y = canvas.y ∧ canvas.w ≤ out.w ∧ canvas.h ≤ out.h := by
  unfold placeAll at h
  dsimp only at h
  split at h
  · cases h
  · rename_i st hf
    have hout : st.canvas = out := (Prod.mk.inj (Except.ok.inj h)).2
    rw [← hout]
    refine foldlM_preserves _
      (fun st : Spill => st.canvas.x = canvas.x ∧ st.canvas.y = canvas.y ∧
        canvas.w ≤ st.canvas.w ∧ canvas.h ≤ st.canvas.h) ?_ _ _ _ ?_ hf
    · intro before ke after hbefore hstep
      split at hstep
      · injection hstep with heq
        subst after
        exact hbefore
      · split at hstep
        · injection hstep with heq
          subst after
          exact hbefore
        · split at hstep
          · cases hstep
          · injection hstep with heq
            subst after
            dsimp only
            exact ⟨hbefore.1, hbefore.2.1,
              Int.le_trans hbefore.2.2.1 (Int.le_max_left ..),
              Int.le_trans hbefore.2.2.2 (Int.le_max_left ..)⟩
    · exact ⟨rfl, rfl, Int.le_refl _, Int.le_refl _⟩

theorem block_canvas_contains_rects {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) :
    ∀ rect ∈ res.rects, (⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect).Contained rect := by
  by_cases hv : inp.valid p.padding = true
  · let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    have hc : c.Wf := Ctx.wf_of_valid hv
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i labels canvas hplace
              injection h with he
              subst res
              have hcan := placeAll_canvas hplace
              change ∀ rect ∈ (c.routeIn p).rects,
                (⟨0, 0, canvas.w, canvas.h⟩ : Rect).Contained rect
              intro rect hrect
              change rect ∈ (List.range c.n).map c.rect at hrect
              obtain ⟨i, hi, heq⟩ := List.mem_map.mp hrect
              subst rect
              have hold := c.rect_inside_root hc (List.mem_range.mp hi)
              simp only [Ctx.frame, ↓reduceIte, Ctx.rootFrame, Rect.Contained] at hold
              dsimp only [Ctx.rootFrame] at hcan
              have hsize : c.rootPlan.width ≤ canvas.w ∧ c.rootPlan.height ≤ canvas.h := by
                simpa only [c] using hcan.2.2
              dsimp [Rect.Contained]
              omega
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem BlockPlan.scene_canvas {pl : BlockPlan} {res : GLayout}
    (h : block pl.input pl.params = .ok res) :
    Validator.C1 (pl.scene res).layoutDump := by
  intro box hb
  change box ∈ (pl.m.boxes.zip
    ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects)).map
      (fun (b, r) => (⟨b.id, b.role.id, r, b.parent, b.exclusive⟩ : Box)) at hb
  obtain ⟨⟨modelBox, rect⟩, hzip, heq⟩ := List.mem_map.mp hb
  subst box
  have hrect := (List.of_mem_zip hzip).2
  rcases List.mem_cons.mp hrect with heq | hmem
  · subst rect
    exact Rect.Contained.refl _
  · exact block_canvas_contains_rects h rect hmem

theorem Site.vacant_frame {s : Site} {thick : Int} {r frame : Rect}
    (h : s.vacant thick r = true) (hf : frame ∈ s.frames) :
    Disjoint frame r ∨ frame.StrictInside r := by
  have hall : (s.frames.all fun f => !overlaps f r || strictlyInside f r) = true := by
    cases he : (s.frames.all fun f => !overlaps f r || strictlyInside f r) with
    | false => simp [Site.vacant, he] at h
    | true => rfl
  have hrow := List.all_eq_true.mp hall frame hf
  by_cases ho : overlaps frame r = true
  · right
    have hs : strictlyInside frame r = true := by simpa [ho] using hrow
    simp only [strictlyInside, Bool.and_eq_true, decide_eq_true_eq] at hs
    unfold Rect.StrictInside
    omega
  · left
    have ho' : overlaps frame r = false := by
      cases he : overlaps frame r
      · rfl
      · exact False.elim (ho he)
    exact (overlaps_false_sep ho').disjoint

theorem fitLabel_frame_clear {s : Site} {pad thick : Int} {route : List Point}
    {size : Size} {rect frame : Rect} (h : fitLabel s pad thick route size = some rect)
    (hf : frame ∈ s.frames) :
    Disjoint frame rect ∨ frame.StrictInside rect :=
  Site.vacant_frame (fitLabel_vacant h) hf

theorem layout_canvas {m : Model} {s : Scene} (h : layout m = .ok s) :
    Validator.C1 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_canvas hr

theorem BlockPlan.sibling_rects {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    {i j : Nat} (hi : i < pl.input.boxes.length) (hj : j < pl.input.boxes.length)
    (hne : i ≠ j)
    (hparent : (m.boxes.getD (i + 1) default).parent =
      (m.boxes.getD (j + 1) default).parent) :
    let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
      (gapsOf pl.input pl.params.padding).2⟩
    Disjoint (c.rect i) (c.rect j) := by
  let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
    (gapsOf pl.input pl.params.padding).2⟩
  have hw : c.Wf := (block_rects hr).1
  have hpa := gridBox_same_parent (BlockPlan.gridBox_at hb hi)
    (BlockPlan.gridBox_at hb hj) hparent
  have hs : c.slotOf i = c.slotOf j := by
    unfold Ctx.slotOf Ctx.box
    rw [hpa]
  exact (c.rect_sep hw hi hj hne hs).disjoint

theorem BlockPlan.scene_box_index {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (_hr : block pl.input pl.params = .ok res)
    {box : Box} (hbox : box ∈ (pl.scene res).boxes) :
    ∃ i, i < m.boxes.length ∧
      box.id = (m.boxes.getD i default).id ∧
      box.parent = (m.boxes.getD i default).parent ∧
      box.exclusive = (m.boxes.getD i default).exclusive ∧
      box.role = (m.boxes.getD i default).role.id ∧
      box.rect = ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects).getD i default := by
  change box ∈ (pl.m.boxes.zip
    ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects)).map
      (fun (b, r) => (⟨b.id, b.role.id, r, b.parent, b.exclusive⟩ : Box)) at hbox
  rw [BlockPlan.success_model hb] at hbox
  obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hbox
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hpair
  have him : i < m.boxes.length := by
    have := hi
    simp only [List.length_zip] at this
    omega
  have hir : i < ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects).length := by
    have := hi
    simp only [List.length_zip] at this
    omega
  have hleft : pair.1 = m.boxes.getD i default := by
    rw [← hget]
    simp only [List.getElem_zip, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem him,
      Option.getD_some]
  have hright : pair.2 =
      ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects).getD i default := by
    rw [← hget]
    simp only [List.getElem_zip, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir,
      Option.getD_some]
  subst box
  exact ⟨i, him, by simp only [← hleft], by simp only [← hleft],
    by simp only [← hleft], by simp only [← hleft], hright⟩

theorem BlockPlan.scene_siblings {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C2 (pl.scene res).layoutDump := by
  intro a ha b hbm hab hax hbx hparent
  obtain ⟨i, hi, hai, hpa, hxa, _hra, hra⟩ := BlockPlan.scene_box_index hb hr ha
  obtain ⟨j, hj, hbi, hpb, hxb, _hrb, hrb⟩ := BlockPlan.scene_box_index hb hr hbm
  have hroot := BlockPlan.root_nonexclusive hb hwf
  have hi0 : i ≠ 0 := by
    intro heq
    rw [heq, hroot] at hxa
    rw [hxa] at hax
    contradiction
  have hj0 : j ≠ 0 := by
    intro heq
    rw [heq, hroot] at hxb
    rw [hxb] at hbx
    contradiction
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hc := BlockPlan.success_box_count hb
  have hi' : i' < pl.input.boxes.length := by omega
  have hj' : j' < pl.input.boxes.length := by omega
  have hij : i' ≠ j' := by
    intro heq
    rw [heq] at hai
    exact hab (hai.trans hbi.symm)
  have hp : (m.boxes.getD (i' + 1) default).parent =
      (m.boxes.getD (j' + 1) default).parent := by
    rw [← hpa, ← hpb]
    exact hparent
  have hsep := BlockPlan.sibling_rects hb hr hi' hj' hij hp
  have hrects := (block_rects hr).2
  rw [hra, hrb]
  simp only [List.getD_cons_succ]
  rw [hrects]
  have hlookup : ∀ k, k < pl.input.boxes.length →
      ((List.range pl.input.boxes.length).map
        (⟨pl.input, (gapsOf pl.input pl.params.padding).1,
          (gapsOf pl.input pl.params.padding).2⟩ : Ctx).rect).getD k default =
        (⟨pl.input, (gapsOf pl.input pl.params.padding).1,
          (gapsOf pl.input pl.params.padding).2⟩ : Ctx).rect k := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    rfl
  simp only [Ctx.n] at *
  rw [hlookup i' hi', hlookup j' hj']
  exact hsep

theorem layout_siblings {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C2 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_siblings hb hr hwf

theorem block_rect_at {input : GInput} {params : GParams} {res : GLayout}
    (h : block input params = .ok res) {i : Nat} (hi : i < input.boxes.length) :
    res.rects.getD i default =
      (⟨input, (gapsOf input params.padding).1,
        (gapsOf input params.padding).2⟩ : Ctx).rect i := by
  rw [(block_rects h).2]
  simp only [Ctx.n, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem block_parent_contains_rect {input : GInput} {params : GParams} {res : GLayout}
    (h : block input params = .ok res) {i : Nat} (hi : i < input.boxes.length) :
    let c : Ctx := ⟨input, (gapsOf input params.padding).1,
      (gapsOf input params.padding).2⟩
    (c.frame (c.slotOf i)).Contained (res.rects.getD i default) := by
  let c : Ctx := ⟨input, (gapsOf input params.padding).1,
    (gapsOf input params.padding).2⟩
  have hw : c.Wf := (block_rects h).1
  rw [block_rect_at h hi]
  exact c.rect_contained hw hi

theorem BlockPlan.scene_parent {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C3 (pl.scene res).layoutDump := by
  intro b hbm hnon p hp
  have hpm : p ∈ (pl.scene res).boxes := List.mem_of_find?_eq_some hp
  have hpid : p.id = b.parent := by
    simpa only [beq_iff_eq] using List.find?_some hp
  obtain ⟨i, hi, _hid, hparent, _hex, _hrole, hrect⟩ :=
    BlockPlan.scene_box_index hb hr hbm
  obtain ⟨j, hj, hjid, _hjparent, _hjex, _hjrole, hjrect⟩ :=
    BlockPlan.scene_box_index hb hr hpm
  have hi0 : i ≠ 0 := by
    intro he
    apply hnon
    rw [hparent, he, BlockPlan.root_parent hb]
  obtain ⟨k, hik⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst i
  have hcount := BlockPlan.success_box_count hb
  have hk : k < pl.input.boxes.length := by omega
  obtain ⟨mb, parent, hmb, hlookup, _hn, hslot⟩ := BlockPlan.parent_slot hb hk
  have hmbD : m.boxes.getD (k + 1) default = mb := by
    rw [List.getD_eq_getElem?_getD, hmb]
    rfl
  have hpj : parent = j := by
    apply model_box_index_unique hwf (indexOf_lt hlookup) hj
    rw [indexOf_id hlookup, ← hmbD, ← hparent, ← hpid, hjid]
  subst parent
  by_cases hj0 : j = 0
  · rw [hjrect, hj0]
    simp only [List.getD_cons_zero]
    exact BlockPlan.scene_canvas hr b hbm
  · obtain ⟨q, hjq⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    subst j
    have hq : q < pl.input.boxes.length := by omega
    let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
      (gapsOf pl.input pl.params.padding).2⟩
    have hc : c.Wf := (block_rects hr).1
    have hs : c.slotOf k = q := by
      have hzero : q + 1 ≠ 0 := by omega
      simpa only [hzero, ite_false, Nat.add_sub_cancel] using hslot c rfl
    have hqn : q ≠ c.n := by
      change q ≠ pl.input.boxes.length
      omega
    have hcontained := c.rect_contained hc hk
    rw [hs] at hcontained
    simp only [Ctx.frame, hqn, ite_false] at hcontained
    rw [hjrect, hrect]
    simp only [List.getD_cons_succ]
    rw [block_rect_at hr hq, block_rect_at hr hk]
    exact hcontained

theorem layout_parent {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C3 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_parent hb hr hwf

theorem block_routes_geometry {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) :
    let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    ∀ e pts, (e, pts) ∈ inp.edges.zip res.routes → EdgeGeometry c e pts := by
  by_cases hv : inp.valid p.padding = true
  · have hp := GInput.valid_padding hv
    have hg := gapsOf_ge_padding (inp := inp) hp
    have hc := Ctx.wf_of_valid hv
    have hb : ∀ e ∈ inp.edges,
        e.fromBox < inp.boxes.length ∧ e.toBox < inp.boxes.length := by
      intro e he
      have he' := GInput.valid_edge hv he
      exact ⟨he'.1, he'.2.1⟩
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i rts hr
            split at h
            · cases h
            · injection h with he
              subst res
              exact Ctx.routes_geometry hc hb hp hg.1 hg.2 hr
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem block_route_ports {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {e : Edge} {pts : List Point}
    (he : (e, pts) ∈ inp.edges.zip res.routes) :
    ∃ a b, pts.head? = some a ∧ pts.getLast? = some b ∧
      Validator.onBoundary a (res.rects.getD e.fromBox default) ∧
      Validator.onBoundary b (res.rects.getD e.toBox default) := by
  have hv : inp.valid p.padding = true := by
    cases hf : inp.valid p.padding with
    | false => simp [block, hf] at h
    | true => rfl
  have hb := GInput.valid_edge hv (List.of_mem_zip he).1
  rw [block_rect_at h hb.1, block_rect_at h hb.2.1]
  exact (block_routes_geometry h e pts he).ports

theorem block_route_clearance {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {e : Edge} {pts : List Point}
    (he : (e, pts) ∈ inp.edges.zip res.routes) {k : Nat}
    (hk : k < inp.boxes.length)
    (hkind : (inp.boxes.getD k default).kind = Kind.leaf)
    (hfrom : e.fromBox ≠ k) (hto : e.toBox ≠ k) :
    ¬ Polyline.hitsRect pts (res.rects.getD k default) := by
  rw [block_rect_at h hk]
  exact (block_routes_geometry h e pts he).clearance k hk hkind hfrom hto

theorem block_foreign_rects_disjoint {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {i j : Nat}
    (hi : i < inp.boxes.length) (hj : j < inp.boxes.length)
    (hij : ¬ (⟨inp, (gapsOf inp p.padding).1,
      (gapsOf inp p.padding).2⟩ : Ctx).Up i j)
    (hji : ¬ (⟨inp, (gapsOf inp p.padding).1,
      (gapsOf inp p.padding).2⟩ : Ctx).Up j i) :
    Disjoint (res.rects.getD j default) (res.rects.getD i default) := by
  let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
  have hc : c.Wf := (block_rects h).1
  have hs := c.grown_sep hc j i hi hj hij hji
  have hin : (grow (c.rect i) c.gapX c.gapY).Contained (c.rect i) := by
    have hx := hc.gapX
    have hy := hc.gapY
    dsimp only [grow, Rect.Contained]
    omega
  rw [block_rect_at h hj, block_rect_at h hi]
  exact (Sep.shrink hin hs).disjoint

private theorem find_box_of_unique {boxes : List Box} {b : Box}
    (hb : b ∈ boxes) (hu : ∀ a ∈ boxes, a.id = b.id → a = b) :
    boxes.find? (fun a => a.id == b.id) = some b := by
  induction boxes with
  | nil => cases hb
  | cons a rest ih =>
    by_cases he : a.id = b.id
    · have hab := hu a (by simp) he
      subst a
      simp
    · have hrest : b ∈ rest := by
        rcases List.mem_cons.mp hb with hab | hmem
        · subst a
          exact False.elim (he rfl)
        · exact hmem
      simpa only [List.find?_cons, show (a.id == b.id) = false by simp [he]] using
        ih hrest (fun c hc => hu c (List.mem_cons_of_mem _ hc))

theorem BlockPlan.scene_box_at {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) {i : Nat} (hi : i < m.boxes.length) :
    ∃ b : Box, (pl.scene res).layoutDump.box? (m.boxes.getD i default).id = some b ∧
      b.rect = ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects).getD i default := by
  let rects := (⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects
  let mb := m.boxes.getD i default
  let b : Box := ⟨mb.id, mb.role.id, rects.getD i default, mb.parent, mb.exclusive⟩
  have hlen : res.rects.length = pl.input.boxes.length := by
    rw [(block_rects hr).2]
    simp [Ctx.n]
  have hcount := BlockPlan.success_box_count hb
  have hir : i < rects.length := by
    dsimp only [rects]
    simp only [List.length_cons]
    omega
  have hmem : b ∈ (pl.scene res).boxes := by
    change b ∈ (pl.m.boxes.zip rects).map
      (fun (a, r) => (⟨a.id, a.role.id, r, a.parent, a.exclusive⟩ : Box))
    rw [BlockPlan.success_model hb]
    apply List.mem_map.mpr
    refine ⟨(mb, rects.getD i default), ?_, rfl⟩
    apply List.mem_iff_getElem.mpr
    refine ⟨i, by simp only [List.length_zip]; omega, ?_⟩
    simp only [List.getElem_zip]
    simp only [mb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hir, Option.getD_some]
  refine ⟨b, ?_, rfl⟩
  change (pl.scene res).boxes.find? (fun a => a.id == mb.id) = some b
  apply find_box_of_unique hmem
  intro a ha hid
  obtain ⟨j, hj, haj, hp, hx, hrole, hrect⟩ := BlockPlan.scene_box_index hb hr ha
  have hji : j = i := model_box_index_unique hwf hj hi (by
    change (m.boxes.getD j default).id = mb.id
    exact haj.symm.trans hid)
  subst j
  cases a
  simp_all [b, mb, rects]

theorem BlockPlan.scene_route_input {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) {route : Route}
    (hroute : route ∈ (pl.scene res).routes) :
    ∃ mr : ModelRoute, ∃ e : Edge, ∃ pts : List Point,
      route = ⟨mr.id, mr.fromId, mr.toId, true, pts⟩ ∧
      (mr, e) ∈ m.routes.zip pl.input.edges ∧
      (e, pts) ∈ pl.input.edges.zip res.routes := by
  change route ∈ (pl.m.routes.zip res.routes).map
    (fun (r, pts) => (⟨r.id, r.fromId, r.toId, true, pts⟩ : Route)) at hroute
  rw [BlockPlan.success_model hb] at hroute
  obtain ⟨⟨mr, pts⟩, hpair, hroute⟩ := List.mem_map.mp hroute
  obtain ⟨k, hk, hkpair⟩ := List.mem_iff_getElem.mp hpair
  have hkm : k < m.routes.length := by
    simp only [List.length_zip] at hk
    omega
  have hkp : k < res.routes.length := by
    simp only [List.length_zip] at hk
    omega
  have hke : k < pl.input.edges.length := by
    rw [BlockPlan.success_edge_count hb]
    exact hkm
  let e := pl.input.edges[k]
  have hmr : m.routes[k] = mr := by
    exact congrArg Prod.fst (by simpa only [List.getElem_zip] using hkpair)
  have hpts : res.routes[k] = pts := by
    exact congrArg Prod.snd (by simpa only [List.getElem_zip] using hkpair)
  have hme : (mr, e) ∈ m.routes.zip pl.input.edges := by
    apply List.mem_iff_getElem.mpr
    refine ⟨k, by simp only [List.length_zip]; omega, ?_⟩
    simp only [List.getElem_zip, hmr, e]
  have hep : (e, pts) ∈ pl.input.edges.zip res.routes := by
    apply List.mem_iff_getElem.mpr
    refine ⟨k, by simp only [List.length_zip]; omega, ?_⟩
    simp only [List.getElem_zip, hpts, e]
  exact ⟨mr, e, pts, hroute.symm, hme, hep⟩

theorem BlockPlan.scene_ports {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C5 (pl.scene res).layoutDump := by
  intro route hroute
  obtain ⟨mr, e, pts, hroute, hme, hep⟩ := BlockPlan.scene_route_input hb hroute
  obtain ⟨src, dst, hsrc, hdst, hs0, ht0, hs, ht⟩ :=
    gridEdge_endpoints (BlockPlan.gridEdge_pair hb hme)
  obtain ⟨a, b, ha, hb', hab, hbb⟩ := block_route_ports hr hep
  obtain ⟨fb, hfb, hfr⟩ := BlockPlan.scene_box_at hb hr hwf (indexOf_lt hsrc)
  obtain ⟨tb, htb, htr⟩ := BlockPlan.scene_box_at hb hr hwf (indexOf_lt hdst)
  rw [indexOf_id hsrc] at hfb
  rw [indexOf_id hdst] at htb
  have hsrcEq : src = e.fromBox + 1 := by omega
  have hdstEq : dst = e.toBox + 1 := by omega
  rw [hsrcEq, List.getD_cons_succ] at hfr
  rw [hdstEq, List.getD_cons_succ] at htr
  subst route
  exact ⟨a, b, fb, tb, ha, hb', hfb, htb,
    by simpa only [hfr] using hab, by simpa only [htr] using hbb⟩

theorem layout_ports {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C5 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_ports hb hr hwf
theorem BlockPlan.scene_route_clearance {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C6 (pl.scene res).layoutDump := by
  intro route hroute box hbox hex hscope
  obtain ⟨mr, e, pts, hrouteEq, hme, hep⟩ := BlockPlan.scene_route_input hb hroute
  obtain ⟨i, hi, hid, hparent, hexclusive, hrole, hrect⟩ :=
    BlockPlan.scene_box_index hb hr hbox
  have hi0 : i ≠ 0 := by
    intro he
    rw [he, BlockPlan.root_nonexclusive hb hwf] at hexclusive
    rw [hexclusive] at hex
    contradiction
  obtain ⟨k, hik⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst i
  have hcount := BlockPlan.success_box_count hb
  have hk : k < pl.input.boxes.length := by omega
  have hkind := BlockPlan.exclusive_leaf hb hwf hk (hexclusive ▸ hex)
  obtain ⟨src, dst, hsrc, hdst, hs0, ht0, hs, ht⟩ :=
    gridEdge_endpoints (BlockPlan.gridEdge_pair hb hme)
  have hfrom : e.fromBox ≠ k := by
    intro heq
    have hsrcEq : src = k + 1 := by omega
    have hbid : box.id = mr.fromId := by
      rw [hid, ← hsrcEq, indexOf_id hsrc]
    apply hscope
    simp only [LayoutDump.routeScope, hrouteEq, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl (Or.inl (Or.inl hbid))
  have hto : e.toBox ≠ k := by
    intro heq
    have hdstEq : dst = k + 1 := by omega
    have hbid : box.id = mr.toId := by
      rw [hid, ← hdstEq, indexOf_id hdst]
    apply hscope
    simp only [LayoutDump.routeScope, hrouteEq, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inl (Or.inl (Or.inr hbid))
  rw [hrouteEq, hrect]
  simp only [List.getD_cons_succ]
  exact block_route_clearance hr hep hk hkind hfrom hto

theorem layout_route_clearance {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C6 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_route_clearance hb hr hwf


theorem default_rect_disjoint_left (r : Rect) : Disjoint (default : Rect) r := by
  change ¬ (max 0 r.x < min 0 (r.x + r.w) ∧
    max 0 r.y < min 0 (r.y + r.h))
  omega

theorem default_rect_disjoint_right (r : Rect) : Disjoint r (default : Rect) := by
  change ¬ (max r.x 0 < min (r.x + r.w) 0 ∧
    max r.y 0 < min (r.y + r.h) 0)
  omega

theorem placeAll_labels_clear_leaves {inp : RouteIn} {rts : List (List Point)}
    {canvas out : Rect} {labels : List Rect}
    (hleaves : ∀ o ∈ inp.leaves, 0 ≤ o.x ∧ o.x + o.w ≤ canvas.w)
    (h : placeAll inp rts canvas = .ok (labels, out)) :
    ∀ label ∈ labels, ∀ o ∈ inp.leaves, Disjoint label o := by
  unfold placeAll at h
  dsimp only at h
  split at h
  · cases h
  · rename_i st hf
    have hout : st.labels.reverse = labels := (Prod.mk.inj (Except.ok.inj h)).1
    have hinv : ∀ label ∈ st.labels, ∀ o ∈ inp.leaves, Disjoint label o := by
      refine foldlM_preserves _
        (fun s : Spill => ∀ label ∈ s.labels, ∀ o ∈ inp.leaves, Disjoint label o)
        ?_ _ _ _ ?_ hf
      · intro before ke after hbefore hstep
        split at hstep
        · injection hstep with heq
          subst after
          intro label hlabel o ho
          rcases List.mem_cons.mp hlabel with he | he
          · subst label
            exact default_rect_disjoint_left o
          · exact hbefore label he o ho
        · split at hstep
          · rename_i rect hfit
            injection hstep with heq
            subst after
            intro label hlabel o ho
            rcases List.mem_cons.mp hlabel with he | he
            · subst label
              exact (fitLabel_clear hfit).2.1 o ho
            · exact hbefore label he o ho
          · split at hstep
            · cases hstep
            · injection hstep with heq
              subst after
              intro label hlabel o ho
              rcases List.mem_cons.mp hlabel with he | he
              · subst label
                have hx := (hleaves o ho).2
                unfold Disjoint Rect.meetsInterior
                dsimp only
                omega
              · exact hbefore label he o ho
      · intro label hlabel
        cases hlabel
    intro label hlabel o ho
    apply hinv label
    · rw [← hout, List.mem_reverse] at hlabel
      exact hlabel
    · exact ho

theorem block_labels_clear_leaf {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {k : Nat} (hk : k < inp.boxes.length)
    (hkind : (inp.boxes.getD k default).kind = Kind.leaf) :
    ∀ label ∈ res.labels, Disjoint label (res.rects.getD k default) := by
  by_cases hv : inp.valid p.padding = true
  · let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    have hc : c.Wf := Ctx.wf_of_valid hv
    have hleaves : ∀ o ∈ (c.routeIn p).leaves,
        0 ≤ o.x ∧ o.x + o.w ≤ c.rootFrame.w := by
      intro o ho
      change o ∈ ((List.range c.n).filter
        (fun i => (c.box i).kind = Kind.leaf)).map c.rect at ho
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ho
      have hjn : j < c.n := List.mem_range.mp (List.mem_filter.mp hj).1
      have hin := c.rect_inside_root hc hjn
      simpa only [Ctx.frame, ↓reduceIte, Ctx.rootFrame, Int.zero_add] using
        (⟨hin.1, hin.2.1⟩ : (c.frame c.n).x ≤ (c.rect j).x ∧
          (c.rect j).x + (c.rect j).w ≤ (c.frame c.n).x + (c.frame c.n).w)
    have hleaf : c.rect k ∈ (c.routeIn p).leaves := by
      change c.rect k ∈ ((List.range c.n).filter
        (fun i => (c.box i).kind = Kind.leaf)).map c.rect
      apply List.mem_map.mpr
      exact ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk,
        by
          change decide ((inp.boxes.getD k default).kind = Kind.leaf) = true
          rw [hkind]
          rfl⟩, rfl⟩
    have hrect := block_rect_at h hk
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i labels canvas hlabels
              injection h with he
              subst res
              intro label hl
              rw [hrect]
              exact placeAll_labels_clear_leaves hleaves hlabels label hl _ hleaf
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem block_label_at_clear_leaf {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {k : Nat} (hk : k < inp.boxes.length)
    (hkind : (inp.boxes.getD k default).kind = Kind.leaf) (n : Nat) :
    Disjoint (res.labels.getD n default) (res.rects.getD k default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hn : res.labels[n]? with
  | some label =>
    exact block_labels_clear_leaf h hk hkind label (List.mem_of_getElem? hn)
  | none =>
    have hc := (block_rects h).1
    have hin := Ctx.rect_inside_root hc hk
    rw [block_rect_at h hk]
    simp only [Ctx.frame, ↓reduceIte, Ctx.rootFrame, Rect.Contained] at hin
    change Disjoint (default : Rect) _
    exact default_rect_disjoint_left _

theorem BlockPlan.scene_label_clearance {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C7 (pl.scene res).layoutDump := by
  intro label hlabel box hbox hex _hscope
  obtain ⟨i, hi, _hid, _hp, hexclusive, _hrole, hrect⟩ :=
    BlockPlan.scene_box_index hb hr hbox
  have hi0 : i ≠ 0 := by
    intro he
    rw [he, BlockPlan.root_nonexclusive hb hwf] at hexclusive
    rw [hexclusive] at hex
    contradiction
  obtain ⟨k, hik⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst i
  have hcount := BlockPlan.success_box_count hb
  have hk : k < pl.input.boxes.length := by omega
  have hkind := BlockPlan.exclusive_leaf hb hwf hk (hexclusive ▸ hex)
  change label ∈ ((pl.m.labels.zip pl.labelLines).map fun (l, lines) =>
    (⟨⟨l.id, l.owner,
      res.labels.getD ((pl.m.routes.findIdx? fun (r : ModelRoute) => r.id == l.owner).getD
        pl.m.routes.length) default, lineTexts lines⟩, l.text⟩ : SceneLabel)).map
      (·.toLabel) at hlabel
  obtain ⟨sl, hsl, hslEq⟩ := List.mem_map.mp hlabel
  obtain ⟨⟨ml, lines⟩, _hml, hslDef⟩ := List.mem_map.mp hsl
  subst sl
  subst label
  rw [hrect]
  simp only [List.getD_cons_succ]
  exact block_label_at_clear_leaf hr hk hkind _

theorem layout_label_clearance {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C7 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_label_clearance hb hr hwf

theorem placeAll_labels_clear_frames {inp : RouteIn} {rts : List (List Point)}
    {canvas out : Rect} {labels : List Rect}
    (hframes : ∀ f ∈ inp.frames, 0 ≤ f.x ∧ f.x + f.w ≤ canvas.w)
    (h : placeAll inp rts canvas = .ok (labels, out)) :
    ∀ label ∈ labels, ∀ f ∈ inp.frames,
      Disjoint f label ∨ f.StrictInside label := by
  unfold placeAll at h
  dsimp only at h
  split at h
  · cases h
  · rename_i st hf
    have hout : st.labels.reverse = labels := (Prod.mk.inj (Except.ok.inj h)).1
    have hinv : ∀ label ∈ st.labels, ∀ f ∈ inp.frames,
        Disjoint f label ∨ f.StrictInside label := by
      refine foldlM_preserves _
        (fun s : Spill => ∀ label ∈ s.labels, ∀ f ∈ inp.frames,
          Disjoint f label ∨ f.StrictInside label) ?_ _ _ _ ?_ hf
      · intro before ke after hbefore hstep
        split at hstep
        · injection hstep with heq
          subst after
          intro label hlabel f hframe
          rcases List.mem_cons.mp hlabel with he | he
          · subst label
            left
            exact default_rect_disjoint_right f
          · exact hbefore label he f hframe
        · split at hstep
          · rename_i rect hfit
            injection hstep with heq
            subst after
            intro label hlabel f hframe
            rcases List.mem_cons.mp hlabel with he | he
            · subst label
              exact fitLabel_frame_clear hfit hframe
            · exact hbefore label he f hframe
          · split at hstep
            · cases hstep
            · injection hstep with heq
              subst after
              intro label hlabel f hframe
              rcases List.mem_cons.mp hlabel with he | he
              · subst label
                left
                have hx := (hframes f hframe).2
                unfold Disjoint Rect.meetsInterior
                dsimp only
                omega
              · exact hbefore label he f hframe
      · intro label hlabel
        cases hlabel
    intro label hlabel f hframe
    apply hinv label
    · rw [← hout, List.mem_reverse] at hlabel
      exact hlabel
    · exact hframe

theorem block_labels_clear_frame {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {k : Nat} (hk : k < inp.boxes.length)
    (hkind : (inp.boxes.getD k default).kind = Kind.composite) :
    ∀ label ∈ res.labels,
      Disjoint (res.rects.getD k default) label ∨
        (res.rects.getD k default).StrictInside label := by
  by_cases hv : inp.valid p.padding = true
  · let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    have hc : c.Wf := Ctx.wf_of_valid hv
    have hframes : ∀ f ∈ (c.routeIn p).frames,
        0 ≤ f.x ∧ f.x + f.w ≤ c.rootFrame.w := by
      intro f hf
      change f ∈ ((List.range c.n).filter
        (fun i => (c.box i).kind = Kind.composite)).map c.rect at hf
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
      have hjn : j < c.n := List.mem_range.mp (List.mem_filter.mp hj).1
      have hin := c.rect_inside_root hc hjn
      simpa only [Ctx.frame, ↓reduceIte, Ctx.rootFrame, Int.zero_add] using
        (⟨hin.1, hin.2.1⟩ : (c.frame c.n).x ≤ (c.rect j).x ∧
          (c.rect j).x + (c.rect j).w ≤ (c.frame c.n).x + (c.frame c.n).w)
    have hframe : c.rect k ∈ (c.routeIn p).frames := by
      change c.rect k ∈ ((List.range c.n).filter
        (fun i => (c.box i).kind = Kind.composite)).map c.rect
      apply List.mem_map.mpr
      exact ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk,
        by
          change decide ((inp.boxes.getD k default).kind = Kind.composite) = true
          rw [hkind]
          rfl⟩, rfl⟩
    have hrect := block_rect_at h hk
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i labels canvas hlabels
              injection h with he
              subst res
              intro label hl
              rw [hrect]
              exact placeAll_labels_clear_frames hframes hlabels label hl _ hframe
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h

theorem block_label_at_clear_frame {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) {k : Nat} (hk : k < inp.boxes.length)
    (hkind : (inp.boxes.getD k default).kind = Kind.composite) (n : Nat) :
    Disjoint (res.rects.getD k default) (res.labels.getD n default) ∨
      (res.rects.getD k default).StrictInside (res.labels.getD n default) := by
  simp only [List.getD_eq_getElem?_getD] at *
  cases hn : res.labels[n]? with
  | some label =>
    simpa only [List.getD_eq_getElem?_getD, hn, Option.getD_some] using
      block_labels_clear_frame h hk hkind label (List.mem_of_getElem? hn)
  | none =>
    left
    have hc := (block_rects h).1
    have hin := Ctx.rect_inside_root hc hk
    simpa only [List.getD_eq_getElem?_getD, hn, Option.getD_none] using
      default_rect_disjoint_right (res.rects.getD k default)

theorem BlockPlan.scene_nonroot_frame_labels {m : Model} {pl : BlockPlan}
    {res : GLayout} (hb : BlockPlan.build m = .ok pl)
    (hr : block pl.input pl.params = .ok res) {frame : Box}
    (hf : frame ∈ (pl.scene res).boxes) (hrole : frame.role = "group")
    (hroot : frame.id ≠ (m.boxes.getD 0 default).id) :
    ∀ label ∈ (pl.scene res).layoutDump.labels,
      Disjoint frame.rect label.rect ∨ frame.rect.StrictInside label.rect := by
  obtain ⟨i, hi, hid, _hp, _hex, hrole', hrect⟩ :=
    BlockPlan.scene_box_index hb hr hf
  have hi0 : i ≠ 0 := by
    intro he
    exact hroot (he ▸ hid)
  obtain ⟨k, hik⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst i
  have hcount := BlockPlan.success_box_count hb
  have hk : k < pl.input.boxes.length := by omega
  obtain ⟨mb, hmb, hkind⟩ := gridBox_kind (BlockPlan.gridBox_at hb hk)
  have hmbD : m.boxes.getD (k + 1) default = mb := by
    rw [List.getD_eq_getElem?_getD, hmb]
    rfl
  have hgroup : mb.role = .group := by
    rw [hmbD] at hrole'
    have hidrole : mb.role.id = "group" := hrole'.symm.trans hrole
    cases he : mb.role with
    | node => simp [he, BoxRole.id] at hidrole
    | group => rfl
  have hcomposite : (pl.input.boxes.getD k default).kind = Kind.composite := by
    simpa only [hgroup, beq_self_eq_true, ↓reduceIte] using hkind
  intro label hlabel
  change label ∈ ((pl.m.labels.zip pl.labelLines).map fun (l, lines) =>
    (⟨⟨l.id, l.owner,
      res.labels.getD ((pl.m.routes.findIdx? fun (r : ModelRoute) => r.id == l.owner).getD
        pl.m.routes.length) default, lineTexts lines⟩, l.text⟩ : SceneLabel)).map
      (·.toLabel) at hlabel
  obtain ⟨sl, hsl, _hslEq⟩ := List.mem_map.mp hlabel
  obtain ⟨⟨ml, lines⟩, _hml, _hslDef⟩ := List.mem_map.mp hsl
  subst sl
  subst label
  rw [hrect]
  simp only [List.getD_cons_succ]
  exact block_label_at_clear_frame hr hk hcomposite _


theorem Site.vacant_strictInside {s : Site} {thick : Int} {r : Rect}
    (h : s.vacant thick r = true) : s.canvas.StrictInside r := by
  have hi : strictlyInside s.canvas r = true := by
    cases he : strictlyInside s.canvas r with
    | false => simp [Site.vacant, he] at h
    | true => rfl
  simpa only [strictlyInside, Bool.and_eq_true, decide_eq_true_eq,
    Rect.StrictInside, and_assoc] using hi

theorem foldlM_preserves_mem {α β ε : Type}
    (step : β → α → Except ε β) (P : β → Prop) (xs : List α)
    (hstep : ∀ st a next, a ∈ xs → P st → step st a = .ok next → P next)
    (st out : β) (hp : P st) (h : xs.foldlM step st = .ok out) : P out := by
  induction xs generalizing st with
  | nil =>
    simp only [List.foldlM_nil, except_pure, Except.ok.injEq] at h
    subst out
    exact hp
  | cons a xs ih =>
    simp only [List.foldlM_cons] at h
    cases hs : step st a with
    | error err => simp [hs] at h
    | ok next =>
      simp only [hs, except_bind_ok] at h
      exact ih (fun st b next hb => hstep st b next (List.mem_cons_of_mem _ hb))
        next (hstep st a next (List.mem_cons_self ..) hp hs) h

theorem placeAll_labels_inside_canvas {inp : RouteIn} {rts : List (List Point)}
    {canvas out : Rect} {labels : List Rect}
    (hx : canvas.x = 0) (hy : canvas.y = 0) (hcw : 0 ≤ canvas.w)
    (heights : ∀ e ∈ inp.edges, 0 ≤ e.label.h)
    (h : placeAll inp rts canvas = .ok (labels, out)) :
    ∀ label ∈ labels, label = default ∨ out.StrictInside label := by
  unfold placeAll at h
  dsimp only at h
  split at h
  · cases h
  · rename_i st hf
    have hout := Prod.mk.inj (Except.ok.inj h)
    have hinv : st.canvas.x = 0 ∧ st.canvas.y = 0 ∧
        canvas.w ≤ st.canvas.w ∧ 0 < st.spillY ∧
        ∀ label ∈ st.labels, label = default ∨ st.canvas.StrictInside label := by
      refine foldlM_preserves_mem _
        (fun s : Spill => s.canvas.x = 0 ∧ s.canvas.y = 0 ∧
          canvas.w ≤ s.canvas.w ∧ 0 < s.spillY ∧
          ∀ label ∈ s.labels, label = default ∨ s.canvas.StrictInside label)
        _ ?_ _ _ ?_ hf
      · intro before ke after hke hbefore hstep
        have hheight := heights ke.1 (List.fst_mem_of_mem_zipIdx hke)
        have hmargin : 0 < max inp.pad 1 := by omega
        split at hstep
        · injection hstep with he
          subst after
          refine ⟨hbefore.1, hbefore.2.1, hbefore.2.2.1, hbefore.2.2.2.1, ?_⟩
          intro label hl
          rcases List.mem_cons.mp hl with he | hm
          · exact Or.inl he
          · exact hbefore.2.2.2.2 label hm
        · split at hstep
          · rename_i rect hfit
            injection hstep with he
            subst after
            refine ⟨hbefore.1, hbefore.2.1, hbefore.2.2.1, hbefore.2.2.2.1, ?_⟩
            intro label hl
            rcases List.mem_cons.mp hl with he | hm
            · subst label
              exact Or.inr (Site.vacant_strictInside (fitLabel_vacant hfit))
            · exact hbefore.2.2.2.2 label hm
          · split at hstep
            · cases hstep
            · injection hstep with he
              subst after
              refine ⟨hbefore.1, hbefore.2.1,
                Int.le_trans hbefore.2.2.1 (Int.le_max_left ..), ?_, ?_⟩
              · have := hbefore.2.2.2.1
                dsimp only
                omega
              · intro label hl
                rcases List.mem_cons.mp hl with he | hm
                · subst label
                  right
                  have hw := Int.le_max_right before.canvas.w
                    (canvas.w + max inp.pad 1 + ke.1.label.w + max inp.pad 1)
                  have hh := Int.le_max_right before.canvas.h
                    (before.spillY + ke.1.label.h + max inp.pad 1)
                  have := hbefore.2.2.2.1
                  dsimp only [Rect.StrictInside]
                  omega
                · rcases hbefore.2.2.2.2 label hm with he | hi
                  · exact Or.inl he
                  · right
                    have hw := Int.le_max_left before.canvas.w
                      (canvas.w + max inp.pad 1 + ke.1.label.w + max inp.pad 1)
                    have hh := Int.le_max_left before.canvas.h
                      (before.spillY + ke.1.label.h + max inp.pad 1)
                    dsimp only [Rect.StrictInside] at hi ⊢
                    omega
      · exact ⟨hx, hy, Int.le_refl _, by dsimp only; omega,
          fun _ hm => False.elim (List.not_mem_nil hm)⟩
    intro label hl
    rw [← hout.1, List.mem_reverse] at hl
    rw [← hout.2]
    exact hinv.2.2.2.2 label hl
theorem block_labels_inside_canvas {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) :
    ∀ label ∈ res.labels, label = default ∨
      (⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect).StrictInside label := by
  by_cases hv : inp.valid p.padding = true
  · let c : Ctx := ⟨inp, (gapsOf inp p.padding).1, (gapsOf inp p.padding).2⟩
    have hc : c.Wf := Ctx.wf_of_valid hv
    have ht := c.rootPlan_wf hc
    have hw : 0 ≤ c.rootFrame.w := by
      change 0 ≤ c.rootPlan.width
      rw [ht.width]
      exact Int.add_nonneg (Int.mul_nonneg ht.ncolsNonneg ht.unitNonneg)
        (Int.mul_nonneg (by have := ht.ncolsNonneg; omega) hc.gapX)
    have hh : ∀ e ∈ (c.routeIn p).edges, 0 ≤ e.label.h := by
      intro e he
      exact (GInput.valid_edge hv he).2.2.2
    simp only [block, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · rename_i labels canvas hplace
              injection h with he
              subst res
              have hcan := placeAll_canvas hplace
              have hl := placeAll_labels_inside_canvas
                (inp := c.routeIn p) rfl rfl hw hh hplace
              have hx : canvas.x = 0 := hcan.1
              have hy : canvas.y = 0 := hcan.2.1
              intro label hlabel
              rcases hl label hlabel with he | hi
              · exact Or.inl he
              · right
                simpa only [Rect.StrictInside, hx, hy] using hi
  · have hf : inp.valid p.padding = false := by
      cases he : inp.valid p.padding
      · rfl
      · exact False.elim (hv he)
    simp [block, hf] at h


theorem block_label_at_inside_canvas {inp : GInput} {p : GParams} {res : GLayout}
    (h : block inp p = .ok res) (n : Nat) :
    let root : Rect := ⟨0, 0, res.canvas.w, res.canvas.h⟩
    Disjoint root (res.labels.getD n default) ∨
      root.StrictInside (res.labels.getD n default) := by
  dsimp only
  rw [List.getD_eq_getElem?_getD]
  cases hn : res.labels[n]? with
  | none =>
    left
    simpa only [hn, Option.getD_none] using
      default_rect_disjoint_right (⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect)
  | some label =>
    rcases block_labels_inside_canvas h label (List.mem_of_getElem? hn) with he | hi
    · left
      subst label
      exact default_rect_disjoint_right _
    · exact Or.inr hi

theorem BlockPlan.scene_root_frame_labels {m : Model} {pl : BlockPlan}
    {res : GLayout} (hb : BlockPlan.build m = .ok pl)
    (hr : block pl.input pl.params = .ok res) (hwf : WellFormed m)
    {frame : Box} (hf : frame ∈ (pl.scene res).boxes)
    (hroot : frame.id = (m.boxes.getD 0 default).id) :
    ∀ label ∈ (pl.scene res).layoutDump.labels,
      Disjoint frame.rect label.rect ∨ frame.rect.StrictInside label.rect := by
  obtain ⟨i, hi, hid, _hp, _hex, _hrole, hrect⟩ :=
    BlockPlan.scene_box_index hb hr hf
  have hi0 : i = 0 := by
    apply model_box_index_unique hwf hi (BlockPlan.success_nonempty hb)
    exact hid.symm.trans hroot
  rw [hi0] at hrect
  simp only [List.getD_cons_zero] at hrect
  intro label hlabel
  change label ∈ ((pl.m.labels.zip pl.labelLines).map fun (l, lines) =>
    (⟨⟨l.id, l.owner,
      res.labels.getD ((pl.m.routes.findIdx? fun (r : ModelRoute) => r.id == l.owner).getD
        pl.m.routes.length) default, lineTexts lines⟩, l.text⟩ : SceneLabel)).map
      (·.toLabel) at hlabel
  obtain ⟨sl, hsl, _hslEq⟩ := List.mem_map.mp hlabel
  obtain ⟨⟨ml, lines⟩, _hml, _hslDef⟩ := List.mem_map.mp hsl
  subst sl
  subst label
  rw [hrect]
  exact block_label_at_inside_canvas hr _

theorem BlockPlan.scene_frame_labels {m : Model} {pl : BlockPlan}
    {res : GLayout} (hb : BlockPlan.build m = .ok pl)
    (hr : block pl.input pl.params = .ok res) (hwf : WellFormed m)
    {frame : Box} (hf : frame ∈ (pl.scene res).boxes)
    (hrole : frame.role = "group") :
    ∀ label ∈ (pl.scene res).layoutDump.labels,
      Disjoint frame.rect label.rect ∨ frame.rect.StrictInside label.rect := by
  by_cases hroot : frame.id = (m.boxes.getD 0 default).id
  · exact BlockPlan.scene_root_frame_labels hb hr hwf hf hroot
  · exact BlockPlan.scene_nonroot_frame_labels hb hr hf hrole hroot

theorem BlockPlan.scene_parent_lookup {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) {k : Nat} (hk : k < pl.input.boxes.length) :
    let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
      (gapsOf pl.input pl.params.padding).2⟩
    ∃ b, (pl.scene res).layoutDump.box? (m.boxes.getD (k + 1) default).id = some b ∧
      b.parent = (m.boxes.getD
        (if c.slotOf k = c.n then 0 else c.slotOf k + 1) default).id ∧
      b.parent ≠ "" := by
  let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
    (gapsOf pl.input pl.params.padding).2⟩
  have hc : c.Wf := (block_rects hr).1
  have hcount := BlockPlan.success_box_count hb
  have hkm : k + 1 < m.boxes.length := by omega
  obtain ⟨b, hlookup, _⟩ := BlockPlan.scene_box_at hb hr hwf hkm
  have hmem := List.mem_of_find?_eq_some hlookup
  have hbid : b.id = (m.boxes.getD (k + 1) default).id := by
    simpa only [beq_iff_eq] using List.find?_some hlookup
  obtain ⟨i, hi, hid, hp, _hx, _hrole, _hrect⟩ :=
    BlockPlan.scene_box_index hb hr hmem
  have hiEq : i = k + 1 := model_box_index_unique hwf hi hkm (hid.symm.trans hbid)
  subst i
  obtain ⟨mb, parent, hmb, hparent, hn, hs⟩ := BlockPlan.parent_slot hb hk
  have hmbD : m.boxes.getD (k + 1) default = mb := by
    rw [List.getD_eq_getElem?_getD, hmb]
    rfl
  have hslot := hs c rfl
  have hidx : (if c.slotOf k = c.n then 0 else c.slotOf k + 1) = parent := by
    by_cases hp0 : parent = 0
    · simp only [hp0, ↓reduceIte] at hslot
      simp [hslot, hp0]
    · have hpn := indexOf_lt hparent
      have hpn' : parent - 1 < c.n := by
        change parent - 1 < pl.input.boxes.length
        omega
      simp only [hp0, ite_false] at hslot
      have hsn : c.slotOf k ≠ c.n := by omega
      rw [ite_eq_right hsn]
      omega
  refine ⟨b, hlookup, ?_, ?_⟩
  · rw [hp, hmbD, hidx, indexOf_id hparent]
  · rw [hp, hmbD]
    exact hn

theorem BlockPlan.scene_up_ancestors {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) :
    let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
      (gapsOf pl.input pl.params.padding).2⟩
    ∀ {a k}, c.Up a k → a ≤ c.n → k < c.n → a ≠ k →
      (m.boxes.getD (if a = c.n then 0 else a + 1) default).id ∈
        (pl.scene res).layoutDump.ancestors (m.boxes.getD (k + 1) default).id := by
  let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
    (gapsOf pl.input pl.params.padding).2⟩
  let d := (pl.scene res).layoutDump
  have hc : c.Wf := (block_rects hr).1
  have hcount := BlockPlan.success_box_count hb
  have hdcount : d.boxes.length = c.n + 1 := by
    have hrlen : res.rects.length = pl.input.boxes.length := by
      rw [(block_rects hr).2]
      simp [Ctx.n]
    change ((pl.m.boxes.zip
      ((⟨0, 0, res.canvas.w, res.canvas.h⟩ : Rect) :: res.rects)).map
      (fun (b, r) => (⟨b.id, b.role.id, r, b.parent, b.exclusive⟩ : Box))).length = _
    rw [List.length_map, List.length_zip, BlockPlan.success_model hb]
    have hn := BlockPlan.success_nonempty hb
    have hm : pl.input.boxes.length + 1 = m.boxes.length := by omega
    simp only [List.length_cons, hrlen, hm, Nat.min_self]
    change m.boxes.length = pl.input.boxes.length + 1
    exact hm.symm
  have hgo : ∀ {a k}, c.Up a k → a ≤ c.n → k < c.n → a ≠ k →
      ∀ fuel, k + 1 < fuel →
        (m.boxes.getD (if a = c.n then 0 else a + 1) default).id ∈
          LayoutDump.ancestors.go d fuel (m.boxes.getD (k + 1) default).id := by
    intro a k hup
    induction hup with
    | refl => intro _ _ hne; exact False.elim (hne rfl)
    | @step k hk hup ih =>
      intro ha _hk hne fuel hfuel
      obtain ⟨b, hlookup, hparent, hnonempty⟩ :=
        BlockPlan.scene_parent_lookup hb hr hwf hk
      change d.box? (m.boxes.getD (k + 1) default).id = some b at hlookup
      change b.parent = (m.boxes.getD
        (if c.slotOf k = c.n then 0 else c.slotOf k + 1) default).id at hparent
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [LayoutDump.ancestors.go, hlookup, hnonempty, ite_false,
          List.mem_cons]
        by_cases he : a = c.slotOf k
        · left
          simpa only [he] using hparent.symm
        · right
          rw [hparent]
          rcases c.slotOf_cases hc hk with hs | ⟨hs, _⟩
          · rw [hs] at hup
            exact False.elim (he (hup.root_eq.trans hs.symm))
          · have hsn : c.slotOf k ≠ c.n := by omega
            simp only [hsn, ite_false]
            exact ih ha (by omega) he fuel (by omega)
  dsimp only
  intro a k hup ha hk hne
  change k < c.n at hk
  change _ ∈ LayoutDump.ancestors.go d d.boxes.length _
  exact hgo hup ha hk hne _ (by rw [hdcount]; omega)

theorem BlockPlan.scene_foreign_frames {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C8a (pl.scene res).layoutDump := by
  intro frame hf _hrole box hbox hne hnotChild hnotAncestor
  obtain ⟨i, hi, hid, _hp, _hx, _hrole, hrect⟩ :=
    BlockPlan.scene_box_index hb hr hf
  obtain ⟨j, hj, hbid, _hbp, _hbx, _hbrole, hbrect⟩ :=
    BlockPlan.scene_box_index hb hr hbox
  let c : Ctx := ⟨pl.input, (gapsOf pl.input pl.params.padding).1,
    (gapsOf pl.input pl.params.padding).2⟩
  have hc : c.Wf := (block_rects hr).1
  have hcount := BlockPlan.success_box_count hb
  have hij : i ≠ j := by
    intro he
    exact hne (hbid.trans (he ▸ hid).symm)
  rw [hid, hbid] at hnotChild hnotAncestor
  have hi0 : i ≠ 0 := by
    intro he
    subst i
    have hj0 : j ≠ 0 := by omega
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < c.n := by change k < pl.input.boxes.length; omega
    apply hnotChild
    have hu := BlockPlan.scene_up_ancestors hb hr hwf
      (c.up_root hc k (Nat.le_of_lt hk)) (Nat.le_refl _) hk (by omega)
    simpa only [c, ↓reduceIte] using hu
  have hj0 : j ≠ 0 := by
    intro he
    subst j
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < c.n := by change k < pl.input.boxes.length; omega
    apply hnotAncestor
    have hu := BlockPlan.scene_up_ancestors hb hr hwf
      (c.up_root hc k (Nat.le_of_lt hk)) (Nat.le_refl _) hk (by omega)
    simpa only [c, ↓reduceIte] using hu
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have ha : a < c.n := by change a < pl.input.boxes.length; omega
  have hk : k < c.n := by change k < pl.input.boxes.length; omega
  have hak : a ≠ k := by omega
  have hnak : ¬ c.Up a k := by
    intro hu
    apply hnotChild
    have hmem := BlockPlan.scene_up_ancestors hb hr hwf hu (Nat.le_of_lt ha) hk hak
    have han : a ≠ c.n := by omega
    change (m.boxes.getD (if a = c.n then 0 else a + 1) default).id ∈
      (pl.scene res).layoutDump.ancestors (m.boxes.getD (k + 1) default).id at hmem
    simpa only [ite_eq_right han] using hmem
  have hnka : ¬ c.Up k a := by
    intro hu
    apply hnotAncestor
    have hmem := BlockPlan.scene_up_ancestors hb hr hwf hu (Nat.le_of_lt hk) ha
      (Ne.symm hak)
    have hkn : k ≠ c.n := by omega
    change (m.boxes.getD (if k = c.n then 0 else k + 1) default).id ∈
      (pl.scene res).layoutDump.ancestors (m.boxes.getD (a + 1) default).id at hmem
    simpa only [ite_eq_right hkn] using hmem
  rw [hrect, hbrect]
  simp only [List.getD_cons_succ]
  exact block_foreign_rects_disjoint hr hk ha hnka hnak

theorem BlockPlan.scene_frame_clearance {m : Model} {pl : BlockPlan} {res : GLayout}
    (hb : BlockPlan.build m = .ok pl) (hr : block pl.input pl.params = .ok res)
    (hwf : WellFormed m) : Validator.C8 (pl.scene res).layoutDump :=
  ⟨BlockPlan.scene_foreign_frames hb hr hwf,
    fun _ hf hrole => BlockPlan.scene_frame_labels hb hr hwf hf hrole⟩

theorem layout_frame_clearance {m : Model} {s : Scene} (hwf : WellFormed m)
    (h : layout m = .ok s) : Validator.C8 s.layoutDump := by
  unfold layout at h
  cases hb : BlockPlan.build m with
  | error err => simp [hb] at h
  | ok pl =>
    simp only [hb, except_bind_ok] at h
    cases hr : block pl.input pl.params with
    | error err => simp [hr] at h
    | ok res =>
      simp only [hr, except_bind_ok, except_pure, Except.ok.injEq] at h
      subst s
      exact BlockPlan.scene_frame_clearance hb hr hwf

end Grid
end Elegant
