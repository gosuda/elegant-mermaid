import Elegant.Chart.Radar

set_option autoImplicit false

namespace Elegant.Chart.Radar

theorem unshifted_angle_bounds {i n : Int} (hi : 0 ≤ i) (hin : i < n) (hn : n ≤ 65536) :
    0 ≤ Int.fdiv (i * 65536) n ∧ Int.fdiv (i * 65536) n ≤ 65535 := by
  exact fdiv_between (i * 65536) n 0 65535 (by omega) (by omega) (by omega)

theorem unshifted_angle_strict {i j n : Int} (hi : 0 ≤ i) (hij : i < j)
    (hj : j < n) (hn : n ≤ 65536) :
    Int.fdiv (i * 65536) n < Int.fdiv (j * 65536) n := by
  have hp : 0 < n := by omega
  have hm := fdiv_mono (D := n) hp (show i * 65536 ≤ j * 65536 by omega)
  by_cases hlt : Int.fdiv (i * 65536) n < Int.fdiv (j * 65536) n
  · exact hlt
  · have heq : Int.fdiv (i * 65536) n = Int.fdiv (j * 65536) n := by omega
    have hqi := Int.mul_fdiv_add_fmod (i * 65536) n
    have hqj := Int.mul_fdiv_add_fmod (j * 65536) n
    have hri := Int.fmod_nonneg_of_pos (i * 65536) hp
    have hrj := Int.fmod_lt_of_pos (j * 65536) hp
    rw [heq] at hqi
    omega

theorem radar_axis_angles_distinct {i j n : Int} (hi : 0 ≤ i) (hij : i < j)
    (hj : j < n) (hn : n ≤ 65536) : angle i n ≠ angle j n := by
  have bi := unshifted_angle_bounds hi (by omega : i < n) hn
  have bj := unshifted_angle_bounds (by omega : 0 ≤ j) hj hn
  have hs := unshifted_angle_strict hi hij hj hn
  intro heq
  unfold angle at heq
  have qi := Int.mul_fdiv_add_fmod (Int.fdiv (i * 65536) n - 16384) 65536
  have qj := Int.mul_fdiv_add_fmod (Int.fdiv (j * 65536) n - 16384) 65536
  rw [heq] at qi
  omega

theorem radar_radius_bounded {radius lo hi value : Int} (hr : 0 ≤ radius) (hd : lo < hi) :
    0 ≤ valueRadius radius lo hi value ∧ valueRadius radius lo hi value ≤ radius := by
  have hc := clamp_between value lo hi
  have hclip : 0 ≤ clamp value lo hi - lo ∧ clamp value lo hi - lo ≤ hi - lo := by omega
  have h := fdiv_scaled_between (clamp value lo hi - lo) (hi - lo) radius
    (by omega) hclip.1 hclip.2
  unfold valueRadius
  rw [Int.mul_comm]
  omega

-- The generated array has 1025 entries; kernel reduction traverses its literal spine.
set_option maxRecDepth 8192 in
theorem sine_table_all_bounded :
    sineTable.all (fun n => decide (0 ≤ n ∧ n ≤ 32768)) = true := by
  rw [← Array.all_toList]
  decide

set_option maxRecDepth 8192 in
theorem sine_table_size : sineTable.size = 1025 := by decide

theorem sine_entry_bounded {i : Int} (h0 : 0 ≤ i) (h1 : i ≤ 1024) :
    0 ≤ sineEntry i ∧ sineEntry i ≤ 32768 := by
  have hi : i.toNat < sineTable.size := by rw [sine_table_size]; omega
  have hb := (Array.all_eq_true.mp sine_table_all_bounded) i.toNat hi
  have hb' : 0 ≤ sineTable[i.toNat] ∧ sineTable[i.toNat] ≤ 32768 :=
    of_decide_eq_true hb
  rw [Array.getElem_eq_getD 0] at hb'
  exact hb'

theorem sine_lookup_bounded {k : Int} (h0 : 0 ≤ k) (h1 : k ≤ 16384) :
    0 ≤ sineLookup k ∧ sineLookup k ≤ 32768 := by
  have hq := Int.mul_fdiv_add_fmod k 16
  have hr0 := Int.fmod_nonneg_of_pos k (by decide : (0 : Int) < 16)
  have hr1 := Int.fmod_lt_of_pos k (by decide : (0 : Int) < 16)
  have ha := sine_entry_bounded (i := Int.fdiv k 16) (by omega) (by omega)
  unfold sineLookup
  dsimp only
  split
  · exact ha
  · rename_i hf
    have hb := sine_entry_bounded (i := Int.fdiv k 16 + 1) (by omega) (by omega)
    let f := k - 16 * Int.fdiv k 16
    have hf0 : 0 ≤ f := by dsimp [f]; omega
    have hf1 : f ≤ 16 := by dsimp [f]; omega
    have a0 := Int.mul_nonneg ha.1 (show 0 ≤ 16 - f by omega)
    have b0 := Int.mul_nonneg hb.1 hf0
    have a1 := Int.mul_le_mul_of_nonneg_right ha.2 (show 0 ≤ 16 - f by omega)
    have b1 := Int.mul_le_mul_of_nonneg_right hb.2 hf0
    simp only [Int.mul_sub] at a0 a1
    have hprod : 0 ≤ 16 * sineEntry (Int.fdiv k 16) +
        (sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f ∧
        16 * sineEntry (Int.fdiv k 16) +
        (sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f ≤ 524288 := by
      simp only [Int.sub_mul]
      omega
    have hdiv := Int.mul_fdiv_add_fmod
      ((sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f + 8) 16
    have hlo := Int.fmod_nonneg_of_pos
      ((sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f + 8)
      (by decide : (0 : Int) < 16)
    have hhi := Int.fmod_lt_of_pos
      ((sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f + 8)
      (by decide : (0 : Int) < 16)
    change 0 ≤ sineEntry (Int.fdiv k 16) +
        Int.fdiv ((sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f + 8) 16 ∧
      sineEntry (Int.fdiv k 16) +
        Int.fdiv ((sineEntry (Int.fdiv k 16 + 1) - sineEntry (Int.fdiv k 16)) * f + 8) 16 ≤ 32768
    omega

theorem sin_at_bounded {r : Int} (_h0 : 0 ≤ r) (_h1 : r < 65536) :
    -32768 ≤ sinAt r ∧ sinAt r ≤ 32768 := by
  have hq := Int.mul_fdiv_add_fmod r 16384
  have hr0 := Int.fmod_nonneg_of_pos r (by decide : (0 : Int) < 16384)
  have hr1 := Int.fmod_lt_of_pos r (by decide : (0 : Int) < 16384)
  have hu := sine_lookup_bounded (k := r - 16384 * Int.fdiv r 16384) (by omega) (by omega)
  have hv := sine_lookup_bounded (k := 16384 - (r - 16384 * Int.fdiv r 16384)) (by omega) (by omega)
  unfold sinAt
  dsimp only
  split <;> (try split) <;> (try split) <;> omega

theorem sine_bounded (a : Int) : -32768 ≤ sinQ15 a ∧ sinQ15 a ≤ 32768 :=
  sin_at_bounded (Int.fmod_nonneg_of_pos _ (by decide)) (Int.fmod_lt_of_pos _ (by decide))

theorem cosine_bounded (a : Int) : -32768 ≤ cosQ15 a ∧ cosQ15 a ≤ 32768 :=
  sin_at_bounded (Int.fmod_nonneg_of_pos _ (by decide)) (Int.fmod_lt_of_pos _ (by decide))

theorem polar_in_square {radius : Int} (hr : 0 ≤ radius) (theta : Int) :
    -radius ≤ (polar radius theta).x ∧ (polar radius theta).x ≤ radius ∧
    -radius ≤ (polar radius theta).y ∧ (polar radius theta).y ≤ radius := by
  have hc := cosine_bounded theta
  have hs := sine_bounded theta
  have cx0 := Int.mul_le_mul_of_nonneg_left hc.1 hr
  have cx1 := Int.mul_le_mul_of_nonneg_left hc.2 hr
  have sy0 := Int.mul_le_mul_of_nonneg_left hs.1 hr
  have sy1 := Int.mul_le_mul_of_nonneg_left hs.2 hr
  have hx := fdiv_between (radius * cosQ15 theta) 32768 (-radius) radius (by decide)
    (by simpa [Int.mul_comm, Int.mul_neg, Int.neg_mul] using cx0) (by simpa [Int.mul_comm] using cx1)
  have hy := fdiv_between (radius * sinQ15 theta) 32768 (-radius) radius (by decide)
    (by simpa [Int.mul_comm, Int.mul_neg, Int.neg_mul] using sy0) (by simpa [Int.mul_comm] using sy1)
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

theorem radar_points_in_plot {radius lo hi value : Int} (hr : 0 ≤ radius)
    (hd : lo < hi) (theta : Int) :
    let p := polar (valueRadius radius lo hi value) theta;
    -radius ≤ p.x ∧ p.x ≤ radius ∧ -radius ≤ p.y ∧ p.y ≤ radius := by
  have hb := radar_radius_bounded (value := value) hr hd
  have hp := polar_in_square hb.1 theta
  dsimp only
  omega

def extendExtrema (a : Int × Int × Int × Int) (p : Point) : Int × Int × Int × Int :=
  (min a.1 p.x, min a.2.1 p.y, max a.2.2.1 p.x, max a.2.2.2 p.y)

theorem extrema_enlarges (ps : List Point) (a : Int × Int × Int × Int) :
    let b := ps.foldl extendExtrema a
    b.1 ≤ a.1 ∧ b.2.1 ≤ a.2.1 ∧ a.2.2.1 ≤ b.2.2.1 ∧ a.2.2.2 ≤ b.2.2.2 := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    have h := ih (extendExtrema a p)
    simp only [List.foldl_cons]
    dsimp only [extendExtrema] at h ⊢
    omega

theorem extrema_contains (ps : List Point) (a : Int × Int × Int × Int)
    (p : Point) (hp : p ∈ ps) :
    let b := ps.foldl extendExtrema a
    b.1 ≤ p.x ∧ b.2.1 ≤ p.y ∧ p.x ≤ b.2.2.1 ∧ p.y ≤ b.2.2.2 := by
  induction ps generalizing a with
  | nil => simp at hp
  | cons q ps ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with heq | hmem
    · subst p
      have h := extrema_enlarges ps (extendExtrema a q)
      dsimp only [extendExtrema] at h ⊢
      omega
    · exact ih (extendExtrema a q) hmem

theorem extrema_inside (ps : List Point) (a : Int × Int × Int × Int) (e : Int)
    (ha : -e ≤ a.1 ∧ -e ≤ a.2.1 ∧ a.2.2.1 ≤ e ∧ a.2.2.2 ≤ e)
    (hp : ∀ p ∈ ps, -e ≤ p.x ∧ -e ≤ p.y ∧ p.x ≤ e ∧ p.y ≤ e) :
    let b := ps.foldl extendExtrema a;
    -e ≤ b.1 ∧ -e ≤ b.2.1 ∧ b.2.2.1 ≤ e ∧ b.2.2.2 ≤ e := by
  induction ps generalizing a with
  | nil => exact ha
  | cons p ps ih =>
    have h := hp p (by simp)
    simp only [List.foldl_cons]
    apply ih (extendExtrema a p)
    · dsimp only [extendExtrema]
      omega
    · intro q hq
      exact hp q (by simp [hq])

theorem bounds_contains_point {ps : List Point} {p : Point} (hp : p ∈ ps) :
    (bounds ps).x ≤ p.x ∧ (bounds ps).y ≤ p.y ∧
    p.x ≤ (bounds ps).x + (bounds ps).w ∧ p.y ≤ (bounds ps).y + (bounds ps).h := by
  have h := extrema_contains ps
    ((ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y,
     (ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y) p hp
  change (ps.foldl extendExtrema _).1 ≤ p.x ∧
    (ps.foldl extendExtrema _).2.1 ≤ p.y ∧
    p.x ≤ (ps.foldl extendExtrema _).1 +
      ((ps.foldl extendExtrema _).2.2.1 - (ps.foldl extendExtrema _).1) ∧
    p.y ≤ (ps.foldl extendExtrema _).2.1 +
      ((ps.foldl extendExtrema _).2.2.2 - (ps.foldl extendExtrema _).2.1)
  omega

theorem bounds_contains_rect {ps : List Point} {r : Rect}
    (hp : ∀ p ∈ corners r, p ∈ ps) : (bounds ps).Contained r := by
  have a := bounds_contains_point (hp ⟨r.x, r.y⟩ (by simp [corners]))
  have b := bounds_contains_point (hp ⟨r.x + r.w, r.y + r.h⟩ (by simp [corners]))
  exact ⟨a.1, b.2.2.1, a.2.1, b.2.2.2⟩

theorem bounds_in_square {ps : List Point} {e : Int} (he : 0 ≤ e)
    (hp : ∀ p ∈ ps, -e ≤ p.x ∧ -e ≤ p.y ∧ p.x ≤ e ∧ p.y ≤ e) :
    (⟨-e, -e, 2 * e, 2 * e⟩ : Rect).Contained (bounds ps) := by
  have hfirst : -e ≤ (ps.headD ⟨0, 0⟩).x ∧ -e ≤ (ps.headD ⟨0, 0⟩).y ∧
      (ps.headD ⟨0, 0⟩).x ≤ e ∧ (ps.headD ⟨0, 0⟩).y ≤ e := by
    cases ps with
    | nil => simp; omega
    | cons p ps => simpa using hp p (by simp)
  have h := extrema_inside ps
    ((ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y,
     (ps.headD ⟨0, 0⟩).x, (ps.headD ⟨0, 0⟩).y) e hfirst hp
  change -e ≤ (ps.foldl extendExtrema _).1 ∧
    (ps.foldl extendExtrema _).1 +
      ((ps.foldl extendExtrema _).2.2.1 - (ps.foldl extendExtrema _).1) ≤ -e + 2 * e ∧
    -e ≤ (ps.foldl extendExtrema _).2.1 ∧
    (ps.foldl extendExtrema _).2.1 +
      ((ps.foldl extendExtrema _).2.2.2 - (ps.foldl extendExtrema _).2.1) ≤ -e + 2 * e
  omega

theorem shift_containment {outer inner : Rect} (h : outer.Contained inner) (dx dy : Int) :
    (shiftRect dx dy outer).Contained (shiftRect dx dy inner) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  dsimp only [shiftRect, Rect.Contained] at *
  omega

theorem max_fold_ge (xs : List Int) (a : Int) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h := ih (max a x)
    simp only [List.foldl_cons]
    omega

theorem plan_extent_ge (c : Constants) (inp : Input) (hi : Int) (texts : List Caption) :
    (plan c inp hi texts).radius ≤ (plan c inp hi texts).extent := by
  exact max_fold_ge _ _

theorem plan_radius_nonneg {c : Constants} (hw : 0 ≤ c.width) (hh : 0 ≤ c.height)
    (inp : Input) (hi : Int) (texts : List Caption) :
    0 ≤ (plan c inp hi texts).radius := by
  change 0 ≤ Int.fdiv (min c.width c.height) 2
  exact le_fdiv_of_mul_le (by decide) (by omega)

theorem plan_curve_bounds {c : Constants} {inp : Input} {hi : Int} {texts : List Caption}
    (hw : 0 ≤ c.width) (hh : 0 ≤ c.height)
    {curve : Nat × List Point} (hc : curve ∈ (plan c inp hi texts).curves) :
    (plan c inp hi texts).plot.Contained (bounds curve.2) := by
  have hr := plan_radius_nonneg hw hh inp hi texts
  have he := plan_extent_ge c inp hi texts
  have he0 : 0 ≤ (plan c inp hi texts).extent := by omega
  apply bounds_in_square he0
  intro p hp
  change curve ∈
    (inp.curves.zipIdx.filter (fun (curve, _) =>
      !inp.axes.isEmpty && hi > inp.minimum && curve.values.length == inp.axes.length)).map
      (fun (curve, i) => (i, curvePoints inp.axes.length (plan c inp hi texts).radius inp.minimum hi curve)) at hc
  obtain ⟨⟨cv, i⟩, hcv, hcurve⟩ := List.mem_map.mp hc
  have hd : inp.minimum < hi := by
    have hfilter := (List.mem_filter.mp hcv).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfilter
    exact hfilter.1.2
  cases hcurve
  obtain ⟨⟨v, j⟩, _, hpoint⟩ := List.mem_map.mp hp
  have hb := radar_points_in_plot (value := v) hr hd (angle j inp.axes.length)
  cases hpoint
  dsimp only at hb ⊢
  omega

theorem plan_plot_in_canvas (c : Constants) (inp : Input) (hi : Int) (texts : List Caption) :
    let p := plan c inp hi texts
    (⟨0, 0, p.enclosing.w, p.enclosing.h⟩ : Rect).Contained
      (shiftRect (-p.enclosing.x) (-p.enclosing.y) p.plot) := by
  let p := plan c inp hi texts
  have hc : (bounds p.allPoints).Contained p.plot := by
    apply bounds_contains_rect
    intro q hq
    change q ∈
      [⟨0, 0⟩] ++ _ ++ corners p.plot ++ _ ++ _ ++ _
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hq)))
  have h := shift_containment hc (-p.enclosing.x) (-p.enclosing.y)
  change (shiftRect (-p.enclosing.x) (-p.enclosing.y) p.enclosing).Contained
    (shiftRect (-p.enclosing.x) (-p.enclosing.y) p.plot) at h
  have hx : p.enclosing.x + -p.enclosing.x = 0 := by omega
  have hy : p.enclosing.y + -p.enclosing.y = 0 := by omega
  change (⟨p.enclosing.x + -p.enclosing.x, p.enclosing.y + -p.enclosing.y,
    p.enclosing.w, p.enclosing.h⟩ : Rect).Contained
      (shiftRect (-p.enclosing.x) (-p.enclosing.y) p.plot) at h
  rw [hx, hy] at h
  exact h

theorem radar_hard_of_frame {d : LayoutDump} {b0 : Box} {tail : List Box}
    (hb : d.boxes = b0 :: tail) (hid : b0.id = "plot") (hp : b0.parent = "")
    (hflags : ∀ b ∈ d.boxes, b.exclusive = false ∧ b.role = "node")
    (htail : ∀ b ∈ tail, b.parent = "plot" ∧ b0.rect.Contained b.rect)
    (hroutes : d.routes = []) (hc : (Validator.canvasRect d).Contained b0.rect) :
    HardConstraints d := by
  have hfind : d.box? "plot" = some b0 := by
    unfold LayoutDump.box?
    rw [hb]
    exact List.find?_cons_of_pos (by simp [hid])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb'
    rw [hb] at hb'
    rcases List.mem_cons.mp hb' with rfl | hb''
    · exact hc
    · exact Rect.Contained.trans hc (htail b hb'').2
  · intro b hb' c hc' _ hex _ _
    have := (hflags b hb').1
    rw [this] at hex
    cases hex
  · intro b hb' hne q hq
    rw [hb] at hb'
    rcases List.mem_cons.mp hb' with rfl | hb''
    · exact absurd hp hne
    · have h := htail b hb''
      rw [h.1, hfind] at hq
      cases hq
      exact h.2
  · intro rt hrt; rw [hroutes] at hrt; cases hrt
  · intro rt hrt; rw [hroutes] at hrt; cases hrt
  · intro rt hrt; rw [hroutes] at hrt; cases hrt
  · intro l _ b hb' hex
    have := (hflags b hb').1
    rw [this] at hex
    cases hex
  · constructor
    · intro g hg hrole
      have := (hflags g hg).2
      rw [this] at hrole
      exact absurd hrole (by decide)
    · intro g hg hrole
      have := (hflags g hg).2
      rw [this] at hrole
      exact absurd hrole (by decide)

theorem plan_valid {c : Constants} (hw : 0 ≤ c.width) (hh : 0 ≤ c.height)
    (inp : Input) (hi : Int) (texts : List Caption) (m : Model) :
    HardConstraints ((plan c inp hi texts).scene m).layoutDump := by
  let p := plan c inp hi texts
  let rectAt := shiftRect (-p.enclosing.x) (-p.enclosing.y)
  let root : Box := ⟨"plot", "node", rectAt p.plot, "", false⟩
  let tail : List Box := p.curves.map fun (i, ps) =>
    ⟨"c" ++ toString i, "node", rectAt (bounds ps), "plot", false⟩
  apply radar_hard_of_frame (b0 := root) (tail := tail) rfl rfl rfl
  · intro b hb
    change b ∈ root :: tail at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨rfl, rfl⟩
    · obtain ⟨⟨i, ps⟩, _, rfl⟩ := List.mem_map.mp hb
      exact ⟨rfl, rfl⟩
  · intro b hb
    obtain ⟨⟨i, ps⟩, hcurve, rfl⟩ := List.mem_map.mp hb
    exact ⟨rfl, shift_containment (plan_curve_bounds hw hh hcurve) _ _⟩
  · rfl
  · exact plan_plot_in_canvas c inp hi texts

theorem radar_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem radar_valid {m : Model} {inp : Input} {scene : Scene}
    (h : layout m inp = .ok scene) : HardConstraints scene.layoutDump := by
  unfold layout at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hdimensions
    obtain ⟨_, _, h⟩ := radar_bind_ok h
    split at h
    · cases h
    · obtain ⟨texts, _, h⟩ := radar_bind_ok h
      obtain ⟨_, _, h⟩ := radar_bind_ok h
      obtain ⟨_, _, h⟩ := radar_bind_ok h
      obtain ⟨_, _, h⟩ := radar_bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst scene
      exact plan_valid (by omega) (by omega) inp _ texts m

end Elegant.Chart.Radar
