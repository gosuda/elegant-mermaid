import Elegant.Chart.Venn
import Elegant.Kinds.Venn

set_option autoImplicit false

namespace Elegant.Chart.Venn

theorem bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem measure_nonnegative (width : Int) (l : ModelLabel) (it : Item)
    (h : measure width l = .ok it) : 0 ≤ it.box.w ∧ 0 ≤ it.box.h := by
  have hw : ∀ (ls : List Measure.Line) (w : Int), 0 ≤ w →
      0 ≤ ls.foldl (fun w line => max w line.width) w := by
    intro ls
    induction ls with
    | nil => intro w hw; exact hw
    | cons line ls ih =>
      intro w hw
      exact ih (max w line.width) (Int.le_trans hw (Int.le_max_left _ _))
  unfold measure at h
  split at h <;>
    obtain ⟨metric, _, h⟩ := bind_ok h <;>
    cases he : StyledMeasure.wrap metric width l.text.toList with
    | error e =>
      simp [he, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | ok lines =>
      simp only [he, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      subst it
      exact ⟨hw lines 0 (by decide), by simp only [Measure.Role.lineHeightPx]; omega⟩

theorem mapM_nonnegative (width : Int) (labels : List ModelLabel) (items : List Item)
    (h : labels.mapM (measure width) = .ok items) :
    ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h := by
  induction labels generalizing items with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst items
    simp
  | cons l ls ih =>
    rw [List.mapM_cons] at h
    obtain ⟨it, hm, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst items
    intro item hitem
    rcases List.mem_cons.mp hitem with h | h
    · subst item
      exact measure_nonnegative width l it hm
    · exact ih rest hr item h
theorem mapM_property {α β : Type} (f : α → Except LayoutError β) (P : β → Prop)
    (hf : ∀ a b, f a = .ok b → P b) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst ys
    simp
  | cons x rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨y,hy,h⟩ := bind_ok h
    obtain ⟨tail,ht,h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst ys
    intro y' hy'
    rcases List.mem_cons.mp hy' with he | he
    · subst y'; exact hf x y hy
    · exact ih tail ht y' he

theorem isqrt_greatest (n r k : Int) (hs : Rect.isqrt n = .ok r)
    (hk : 0 ≤ k) (hkn : k*k ≤ n) : k ≤ r := by
  unfold Rect.isqrt at hs
  split at hs
  · rename_i hn
    have he : r = (n.toNat.sqrt : Int) := (Except.ok.inj hs).symm
    subst r
    have hn' : (n.toNat : Int) = n := by omega
    have hs' : n < ((n.toNat.sqrt : Int)+1)*((n.toNat.sqrt : Int)+1) := by
      have hh := Int.ofNat_lt.mpr (Nat.lt_succ_sqrt n.toNat)
      push_cast at hh
      simpa only [hn'] using hh
    by_cases h : k ≤ (n.toNat.sqrt : Int)
    · exact h
    have hk' : (n.toNat.sqrt : Int)+1 ≤ k := by omega
    have hp : 0 ≤ (n.toNat.sqrt : Int)+1 := by omega
    have hm1 := Int.mul_le_mul_of_nonneg_left hk' hp
    have hm2 := Int.mul_le_mul_of_nonneg_right hk' hk
    have hc : ((n.toNat.sqrt : Int)+1)*k = k*((n.toNat.sqrt : Int)+1) :=
      Int.mul_comm _ _
    omega
  · cases hs


theorem square_nonnegative (x : Int) : 0 ≤ x*x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -x := by omega
    have hm := Int.mul_nonneg hn hn
    simpa only [Int.neg_mul_neg] using hm

theorem length_bounds_components (x y length : Int)
    (h : Rect.isqrt (x*x+y*y) = .ok length) :
    -length ≤ x ∧ x ≤ length ∧ -length ≤ y ∧ y ≤ length := by
  have hx := square_nonnegative x
  have hy := square_nonnegative y
  have comp (a b : Int) (_ha : 0 ≤ a*a) (hb : 0 ≤ b*b)
      (hs : Rect.isqrt (a*a+b*b) = .ok length) : -length ≤ a ∧ a ≤ length := by
    by_cases hn : 0 ≤ a
    · have hh := isqrt_greatest _ length a hs hn (by omega)
      have hl := (Rect.isqrt_spec hs).1
      omega
    · have hh := isqrt_greatest _ length (-a) hs (by omega)
        (by simpa only [Int.neg_mul_neg] using (show a*a ≤ a*a+b*b by omega))
      have hl := (Rect.isqrt_spec hs).1
      omega
  have hxy := comp x y hx hy h
  have hyx := comp y x hy hx (by simpa only [Int.add_comm] using h)
  exact ⟨hxy.1,hxy.2,hyx.1,hyx.2⟩

theorem anchor_shift_nonnegative (centre radius delta length : Int)
    (hc : radius ≤ centre) (hr : 0 ≤ radius) (hl : 0 < length)
    (hd : -length ≤ delta) :
    0 ≤ centre + Int.fdiv (delta*radius) (2*length) := by
  have hm := Int.mul_le_mul_of_nonneg_right hd hr
  have hp := Int.mul_nonneg (Int.le_of_lt hl) hr
  have hq : -radius ≤ Int.fdiv (delta*radius) (2*length) := by
    apply le_fdiv_of_mul_le (by omega)
    simp only [Int.neg_mul, Int.mul_neg, Int.mul_assoc] at *
    omega
  omega

def CircleSafe (c : Circle) : Prop := 0 ≤ c.r ∧ c.r ≤ c.x ∧ c.r ≤ c.y

theorem circle_getD_safe (cs : List Circle) (hc : ∀ c ∈ cs, CircleSafe c) (i : Nat) :
    CircleSafe (cs.getD i ⟨0,0,0⟩) := by
  induction cs generalizing i with
  | nil => simp [CircleSafe]
  | cons c cs ih =>
    cases i with
    | zero => exact hc c (by simp)
    | succ i => exact ih (fun c h => hc c (List.mem_cons_of_mem _ h)) i

theorem setAnchor_nonnegative (cs : List Circle) (hc : ∀ c ∈ cs, CircleSafe c)
    (i : Nat) (p : Point) (h : setAnchor cs i = .ok p) : 0 ≤ p.x ∧ 0 ≤ p.y := by
  have hs := circle_getD_safe cs hc i
  let c := cs.getD i ⟨0,0,0⟩
  have hcs : 0 ≤ c.r ∧ c.r ≤ c.x ∧ c.r ≤ c.y := hs
  by_cases hn : cs.length ≤ 1
  · simp only [setAnchor, hn, ite_true, pure, Except.pure, Except.ok.injEq] at h
    subst p
    change 0 ≤ c.x ∧ 0 ≤ c.y
    exact ⟨by omega,by omega⟩
  · simp only [setAnchor, hn, ite_false] at h
    obtain ⟨length, hlength, h⟩ := bind_ok h
    have hl := (Rect.isqrt_spec hlength).1
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst p
      change 0 ≤ c.x ∧ 0 ≤ c.y
      exact ⟨by omega,by omega⟩
    · rename_i hne
      have hd := length_bounds_components _ _ length hlength
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst p
      exact ⟨anchor_shift_nonnegative _ _ _ _ hcs.2.1 hcs.1 (by omega) hd.1,
        anchor_shift_nonnegative _ _ _ _ hcs.2.2 hcs.1 (by omega) hd.2.2.1⟩

theorem fold_add_nonnegative {α : Type} (xs : List α) (f : α → Int)
    (hf : ∀ x ∈ xs, 0 ≤ f x) (initial : Int) (hi : 0 ≤ initial) :
    0 ≤ xs.foldl (fun s x => s+f x) initial := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons x rest ih =>
    apply ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have := hf x (by simp)
    dsimp only
    omega

theorem anchor_nonnegative (m : Model) (cs : List Circle)
    (hc : ∀ c ∈ cs, CircleSafe c) (id : String) (p : Point)
    (h : anchor m cs id = .ok p) : 0 ≤ p.x ∧ 0 ≤ p.y := by
  have hget : ∀ i, 0 ≤ (cs.getD i ⟨0,0,0⟩).x ∧ 0 ≤ (cs.getD i ⟨0,0,0⟩).y := by
    intro i
    have hi := circle_getD_safe cs hc i
    unfold CircleSafe at hi
    omega
  unfold anchor at h
  split at h
  · exact setAnchor_nonnegative cs hc _ p h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst p
    constructor
    · apply Int.fdiv_nonneg
      · exact fold_add_nonnegative _ _ (fun i _ => (hget i).1) 0 (by decide)
      · exact Int.natCast_nonneg _
    · apply Int.fdiv_nonneg
      · exact fold_add_nonnegative _ _ (fun i _ => (hget i).2) 0 (by decide)
      · exact Int.natCast_nonneg _

theorem sqrt_radius_bound (R n r : Int) (hR : 0 ≤ R) (hn : n ≤ R*R)
    (hs : Rect.isqrt n = .ok r) : 0 ≤ r ∧ r ≤ R := by
  have hr := Rect.isqrt_spec hs
  refine ⟨hr.1, ?_⟩
  by_cases h : r ≤ R
  · exact h
  have hlt : R < r := by omega
  have hm1 := Int.mul_le_mul_of_nonneg_left (show R+1 ≤ r by omega) hR
  have hm2 := Int.mul_le_mul_of_nonneg_right (show R+1 ≤ r by omega)
    (show 0 ≤ r by omega)
  have hpos : 0 < r := by omega
  rw [Int.mul_add, Int.mul_one] at hm1
  rw [Int.add_mul, Int.one_mul] at hm2
  have hcomm : R*r = r*R := Int.mul_comm _ _
  omega

theorem scaled_radius_bound (R value largest r : Int) (hR : 0 ≤ R)
    (hl : 0 < largest) (hv : value ≤ largest)
    (hs : Rect.isqrt (Int.fdiv (R*R*max value 0) largest) = .ok r) :
    0 ≤ r ∧ r ≤ R := by
  apply sqrt_radius_bound R _ r hR _ hs
  have hsq : 0 ≤ R*R := Int.mul_nonneg hR hR
  have hv' : max value 0 ≤ largest := by omega
  have hm := Int.mul_le_mul_of_nonneg_left hv' hsq
  apply fdiv_le_of_le_mul hl
  simpa only [Int.mul_comm largest (R*R)] using hm
theorem max_fold_ge (xs : List Int) (initial : Int) : initial ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => exact Int.le_refl _
  | cons x rest ih =>
    exact Int.le_trans (Int.le_max_left initial x) (ih (max initial x))

theorem max_fold_contains (xs : List Int) (initial x : Int) (hx : x ∈ xs) :
    x ≤ xs.foldl max initial := by
  induction xs generalizing initial with
  | nil => simp at hx
  | cons y rest ih =>
    rcases List.mem_cons.mp hx with he | he
    · subst x
      exact Int.le_trans (Int.le_max_right initial y) (max_fold_ge rest (max initial y))
    · exact ih (max initial y) he

theorem mapM_property_on {α β : Type} (f : α → Except LayoutError β) (P : β → Prop)
    (xs : List α) (ys : List β) (hf : ∀ a ∈ xs, ∀ b, f a = .ok b → P b)
    (h : xs.mapM f = .ok ys) : ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil,pure,Except.pure,Except.ok.injEq] at h
    subst ys
    simp
  | cons a rest ih =>
    rw [List.mapM_cons] at h
    obtain ⟨b,hb,h⟩ := bind_ok h
    obtain ⟨tail,ht,h⟩ := bind_ok h
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst ys
    intro y hy
    rcases List.mem_cons.mp hy with he | he
    · subst y; exact hf a (by simp) b hb
    · exact ih tail (fun a ha => hf a (List.mem_cons_of_mem _ ha)) ht y he

theorem measured_radius_bounds (values radii : List Int) (R : Int) (hR : 0 ≤ R)
    (h : values.mapM (fun v => Rect.isqrt (Int.fdiv (R*R*max v 0) (values.foldl max 1))) =
      .ok radii) : ∀ r ∈ radii, 0 ≤ r ∧ r ≤ R := by
  have hl := max_fold_ge values 1
  refine mapM_property_on _ (fun r => 0 ≤ r ∧ r ≤ R) values radii ?_ h
  intro value hv r hs
  exact scaled_radius_bound R value (values.foldl max 1) r hR (by omega)
    (max_fold_contains values 1 value hv) hs

theorem two_centres_nonnegative (R a b d : Int) (_hR : 0 ≤ R)
    (ha : 0 ≤ a ∧ a ≤ R) (hb : 0 ≤ b ∧ b ≤ R)
    (hd : 0 ≤ d ∧ d ≤ a+b) :
    ∀ c ∈ centres [a,b] R d, 0 ≤ c.x-c.r ∧ 0 ≤ c.y-c.r := by
  have hq := fdiv_between d 2 0 R (by decide) (by omega) (by omega)
  intro c hc
  simp only [centres, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h <;> subst c <;> dsimp only <;> omega


theorem scene_nonexclusive (m : Model) (r : Result)
    (hm : ∀ b ∈ m.boxes, b.exclusive = false) :
    ∀ b ∈ (sceneOf m r).boxes, b.exclusive = false := by
  intro b hb
  simp only [sceneOf, List.mem_map] at hb
  obtain ⟨⟨source,i⟩, hs, he⟩ := hb
  subst b
  exact hm source (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hs))

theorem scene_exclusive_clauses (m : Model) (r : Result)
    (hm : ∀ b ∈ m.boxes, b.exclusive = false) :
    Validator.C2 (sceneOf m r).layoutDump ∧
    Validator.C6 (sceneOf m r).layoutDump ∧
    Validator.C7 (sceneOf m r).layoutDump := by
  have hn := scene_nonexclusive m r hm
  refine ⟨?_, ?_, ?_⟩
  · intro b hb c hc _ he
    have hf := hn b hb
    simp [hf] at he
  · intro route hr
    simp [sceneOf, Scene.layoutDump] at hr
  · intro l hl b hb he
    have hf := hn b hb
    simp [hf] at he

theorem extent_fold_ge (xs : List Rect) (initial : Int) :
    initial ≤ xs.foldl (fun n r => max n (r.x+r.w)) initial := by
  induction xs generalizing initial with
  | nil => exact Int.le_refl _
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem extent_fold_contains (xs : List Rect) (initial : Int) (r : Rect) (hr : r ∈ xs) :
    r.x+r.w ≤ xs.foldl (fun n r => max n (r.x+r.w)) initial := by
  induction xs generalizing initial with
  | nil => simp at hr
  | cons a rs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact Int.le_trans (Int.le_max_right _ _) (extent_fold_ge rs _)
    · exact ih _ h

theorem height_fold_ge (xs : List Rect) (initial : Int) :
    initial ≤ xs.foldl (fun n r => max n (r.y+r.h)) initial := by
  induction xs generalizing initial with
  | nil => exact Int.le_refl _
  | cons r rs ih =>
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem height_fold_contains (xs : List Rect) (initial : Int) (r : Rect) (hr : r ∈ xs) :
    r.y+r.h ≤ xs.foldl (fun n r => max n (r.y+r.h)) initial := by
  induction xs generalizing initial with
  | nil => simp at hr
  | cons a rs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact Int.le_trans (Int.le_max_right _ _) (height_fold_ge rs _)
    · exact ih _ h

theorem rect_in_final_extent (xs : List Rect) (width height : Int) (r : Rect)
    (hr : r ∈ xs) (hx : 0 ≤ r.x) (hy : 0 ≤ r.y) :
    Rect.Contained
      ⟨0,0,xs.foldl (fun n r => max n (r.x+r.w)) width,
        xs.foldl (fun n r => max n (r.y+r.h)) height⟩ r := by
  exact ⟨hx,by simpa using extent_fold_contains xs width r hr,
    hy,by simpa using height_fold_contains xs height r hr⟩

theorem getD_nonnegative (xs : List Rect) (h : ∀ r ∈ xs, 0 ≤ r.x ∧ 0 ≤ r.y) (i : Nat) :
    0 ≤ (xs.getD i ⟨0,0,0,0⟩).x ∧ 0 ≤ (xs.getD i ⟨0,0,0,0⟩).y := by
  induction xs generalizing i with
  | nil => simp
  | cons r rs ih =>
    cases i with
    | zero => exact h r (by simp)
    | succ i =>
      exact ih (fun r hr => h r (List.mem_cons_of_mem _ hr)) i

theorem fit_nonnegative (width height : Int) (r : Rect) :
    0 ≤ (fit width height r).x ∧ 0 ≤ (fit width height r).y := by
  simp only [fit, clamp]
  omega

theorem clearEarlier_nonnegative (previous : List Item)
    (hp : ∀ it ∈ previous, 0 ≤ it.rect.y ∧ 0 ≤ it.rect.h)
    (fuel : Nat) (r : Rect) (hr : 0 ≤ r.y) :
    0 ≤ (clearEarlier previous fuel r).y := by
  induction fuel generalizing r with
  | zero => exact hr
  | succ n ih =>
    simp only [clearEarlier]
    split
    · exact hr
    · rename_i it h
      have hmem := List.mem_of_find?_eq_some h
      have hi := hp it hmem
      apply ih
      change 0 ≤ it.rect.y+it.rect.h
      omega

theorem clearEarlier_dimensions (previous : List Item) (fuel : Nat) (r : Rect) :
    (clearEarlier previous fuel r).x = r.x ∧
    (clearEarlier previous fuel r).w = r.w ∧
    (clearEarlier previous fuel r).h = r.h := by
  induction fuel generalizing r with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    simp only [clearEarlier]
    split
    · exact ⟨rfl,rfl,rfl⟩
    · exact ih _

def ItemSafe (it : Item) : Prop :=
  0 ≤ it.rect.x ∧ 0 ≤ it.rect.y ∧ 0 ≤ it.rect.w ∧ 0 ≤ it.rect.h ∧
    0 ≤ it.box.w ∧ 0 ≤ it.box.h

theorem measure_item_safe (width : Int) (l : ModelLabel) (it : Item)
    (h : measure width l = .ok it) : ItemSafe it := by
  have hbox := measure_nonnegative width l it h
  unfold measure at h
  split at h <;>
    obtain ⟨metric,_,h⟩ := bind_ok h <;>
    cases he : StyledMeasure.wrap metric width l.text.toList with
    | error e =>
      simp [he,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
    | ok lines =>
      simp only [he,pure,Except.pure,bind,Except.bind,Except.ok.injEq] at h
      subst it
      exact ⟨by change (0 : Int) ≤ 0; decide,by change (0 : Int) ≤ 0; decide,
        hbox.1,hbox.2,hbox.1,hbox.2⟩

theorem measured_items_safe (width : Int) (labels : List ModelLabel) (items : List Item)
    (h : labels.mapM (measure width) = .ok items) : ∀ it ∈ items, ItemSafe it :=
  mapM_property (measure width) ItemSafe (measure_item_safe width) labels items h

structure StackSafe (s : StackState) : Prop where
  out : ∀ it ∈ s.out, ItemSafe it
  history : ∀ it ∈ s.history, ItemSafe it
  left : 0 ≤ s.left
  low : 0 ≤ s.low
  right : s.left ≤ s.right
  high : s.low ≤ s.high

theorem stackStep_safe (width height band : Int) (a : Point) (s : StackState) (it : Item)
    (hs : StackSafe s) (hw : 0 ≤ it.box.w) (hh : 0 ≤ it.box.h) :
    StackSafe (stackStep width height band a s it) := by
  let initial := fit width height ⟨a.x-Int.fdiv it.box.w 2,s.top,it.box.w,it.box.h⟩
  let index := s.history.findIdx (fun p => p.label.id == it.label.id)
  let r := clearEarlier (s.history.take index) index { initial with y := max initial.y band }
  have hd := clearEarlier_dimensions (s.history.take index) index
    { initial with y := max initial.y band }
  have hxy := fit_nonnegative width height ⟨a.x-Int.fdiv it.box.w 2,s.top,it.box.w,it.box.h⟩
  have hdim : r.x = initial.x ∧ r.w = it.box.w ∧ r.h = it.box.h := by
    exact hd
  have hy : 0 ≤ r.y := by
    apply clearEarlier_nonnegative
    · intro previous hp
      have hi := hs.history previous (List.mem_of_mem_take hp)
      exact ⟨hi.2.1,hi.2.2.2.1⟩
    · change 0 ≤ max initial.y band
      have hiy : 0 ≤ initial.y := hxy.2
      omega
  have hr : 0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h := by
    have hix : 0 ≤ initial.x := hxy.1
    omega
  have hplaced : ItemSafe { it with rect := r } :=
    ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hw,hh⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro previous hp
    change previous ∈ s.out ++ [{ it with rect := r }] at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hs.out previous hp
    · have he := List.mem_singleton.mp hp
      subst previous
      exact hplaced
  · intro previous hp
    change previous ∈ s.history.map
      (fun p => if p.label.id == it.label.id then { it with rect := r } else p) at hp
    obtain ⟨old,ho,he⟩ := List.mem_map.mp hp
    split at he
    · subst previous; exact hplaced
    · subst previous; exact hs.history old ho
  · change 0 ≤ min s.left r.x
    have := hs.left
    omega
  · change 0 ≤ min s.low r.y
    have := hs.low
    omega
  · change min s.left r.x ≤ max s.right (r.x+r.w)
    have := hs.right
    omega
  · change min s.low r.y ≤ max s.high (r.y+r.h)
    have := hs.high
    omega

theorem stackLoop_safe (width height band : Int) (a : Point) (items : List Item)
    (hi : ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h)
    (s : StackState) (hs : StackSafe s) : StackSafe (stackLoop width height band a items s) := by
  induction items generalizing s with
  | nil => exact hs
  | cons it rest ih =>
    apply ih (fun it hit => hi it (List.mem_cons_of_mem _ hit))
    exact stackStep_safe width height band a s it hs
      (hi it (by simp)).1 (hi it (by simp)).2

theorem stack_safe (width height band : Int) (a : Point) (previous items : List Item)
    (ha : 0 ≤ a.x ∧ 0 ≤ a.y)
    (hp : ∀ it ∈ previous, ItemSafe it)
    (hi : ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h) :
    (∀ it ∈ (stack width height band a previous items).1, ItemSafe it) ∧
    0 ≤ (stack width height band a previous items).2.x ∧
    0 ≤ (stack width height band a previous items).2.y ∧
    0 ≤ (stack width height band a previous items).2.w ∧
    0 ≤ (stack width height band a previous items).2.h := by
  let initial : StackState :=
    ⟨a.y-Int.fdiv (items.foldl (fun s i => s+i.box.h) 0) 2, [], previous,a.x,a.x,a.y,a.y⟩
  have hs : StackSafe initial :=
    ⟨by simp [initial],hp,ha.1,ha.2,Int.le_refl _,Int.le_refl _⟩
  have hf := stackLoop_safe width height band a items hi initial hs
  change (∀ it ∈ (stackLoop width height band a items initial).out, ItemSafe it) ∧
    0 ≤ (stackLoop width height band a items initial).left ∧
    0 ≤ (stackLoop width height band a items initial).low ∧
    0 ≤ (stackLoop width height band a items initial).right -
      (stackLoop width height band a items initial).left ∧
    0 ≤ (stackLoop width height band a items initial).high -
      (stackLoop width height band a items initial).low
  exact ⟨hf.out,hf.left,hf.low,by have := hf.right; omega,by have := hf.high; omega⟩

def RectSafe (r : Rect) : Prop := 0 ≤ r.x ∧ 0 ≤ r.y ∧ 0 ≤ r.w ∧ 0 ≤ r.h

structure BoxSafe (s : BoxState) : Prop where
  placed : ∀ it ∈ s.placed, ItemSafe it
  rects : ∀ r ∈ s.rects, RectSafe r

theorem fit_item_safe (width height : Int) (it : Item) (x y : Int)
    (hw : 0 ≤ it.box.w) (hh : 0 ≤ it.box.h) :
    ItemSafe { it with rect := fit width height ⟨x,y,it.box.w,it.box.h⟩ } := by
  have h := fit_nonnegative width height ⟨x,y,it.box.w,it.box.h⟩
  exact ⟨h.1,h.2,hw,hh,hw,hh⟩

theorem placeBox_safe (m : Model) (cs : List Circle) (items : List Item)
    (width height band : Int) (b : ModelBox) (s t : BoxState)
    (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hc : ∀ c ∈ cs, CircleSafe c)
    (hi : ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h)
    (hs : BoxSafe s) (h : placeBox m cs items width height band b s = .ok t) :
    BoxSafe t := by
  unfold placeBox at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst t
    constructor
    · intro it hit
      obtain ⟨old,ho,he⟩ := List.mem_map.mp hit
      have hold := hs.placed old ho
      split at he
      · subst it
        exact fit_item_safe width height old _ _ hold.2.2.2.2.1 hold.2.2.2.2.2
      · subst it; exact hold
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hs.rects r hr
      · have he := List.mem_singleton.mp hr
        subst r
        exact ⟨by change (0 : Int) ≤ 0; decide,by change (0 : Int) ≤ 0; decide,hw,hh⟩
  · obtain ⟨a,ha,h⟩ := bind_ok h
    have ha' := anchor_nonnegative m cs hc b.id a ha
    have hstack := stack_safe width height band a s.placed
      (items.filter (fun it => it.label.owner == b.id)) ha' hs.placed
      (fun it hit => hi it (List.mem_filter.mp hit).1)
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst t
    constructor
    · intro it hit
      obtain ⟨old,ho,he⟩ := List.mem_map.mp hit
      cases hf : (stack width height band a s.placed
          (items.filter (fun it => it.label.owner == b.id))).1.find?
          (fun p => p.label.id == old.label.id) with
      | none =>
        simp only [hf, Option.getD_none] at he
        subst it
        exact hs.placed old ho
      | some placed =>
        simp only [hf, Option.getD_some] at he
        subst it
        exact hstack.1 placed (List.mem_of_find?_eq_some hf)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hs.rects r hr
      · have he := List.mem_singleton.mp hr
        subst r
        split
        · rename_i i _
          have hs' := circle_getD_safe cs hc i
          unfold CircleSafe at hs'
          unfold RectSafe
          dsimp only
          omega
        · exact hstack.2

theorem placeBoxes_safe (m : Model) (cs : List Circle) (items : List Item)
    (width height band : Int) (boxes : List ModelBox) (s t : BoxState)
    (hw : 0 ≤ width) (hh : 0 ≤ height) (hc : ∀ c ∈ cs, CircleSafe c)
    (hi : ∀ it ∈ items, 0 ≤ it.box.w ∧ 0 ≤ it.box.h) (hs : BoxSafe s)
    (h : placeBoxes m cs items width height band boxes s = .ok t) : BoxSafe t := by
  induction boxes generalizing s with
  | nil =>
    simp only [placeBoxes, Except.ok.injEq] at h
    subst t
    exact hs
  | cons b rest ih =>
    simp only [placeBoxes] at h
    obtain ⟨next,hn,h⟩ := bind_ok h
    apply ih next
    · exact placeBox_safe m cs items width height band b s next hw hh hc hi hs hn
    · exact h

theorem placeBox_length (m : Model) (cs : List Circle) (items : List Item)
    (width height band : Int) (b : ModelBox) (s t : BoxState)
    (h : placeBox m cs items width height band b s = .ok t) :
    t.rects.length = s.rects.length+1 := by
  unfold placeBox at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst t
    simp only [List.length_append, List.length_singleton]
  · obtain ⟨_,_,h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst t
    simp only [List.length_append, List.length_singleton]

theorem placeBoxes_length (m : Model) (cs : List Circle) (items : List Item)
    (width height band : Int) (boxes : List ModelBox) (s t : BoxState)
    (h : placeBoxes m cs items width height band boxes s = .ok t) :
    t.rects.length = s.rects.length+boxes.length := by
  induction boxes generalizing s with
  | nil =>
    simp only [placeBoxes, Except.ok.injEq] at h
    subst t
    simp
  | cons b rest ih =>
    simp only [placeBoxes] at h
    obtain ⟨next,hn,h⟩ := bind_ok h
    have hs := placeBox_length m cs items width height band b s next hn
    have ht := ih next h
    simp only [List.length_cons]
    omega

theorem final_root_rect (boxes : List ModelBox) (rects : List Rect) (width height : Int)
    (hlen : boxes.length = rects.length) (i : Nat) (b : ModelBox)
    (hb : boxes[i]? = some b) (hid : b.id = "venn") :
    ((boxes.zip rects).map (fun (b,r) =>
      if b.id == "venn" then (⟨0,0,width,height⟩ : Rect) else r)).getD i ⟨0,0,0,0⟩ =
        ⟨0,0,width,height⟩ := by
  induction boxes generalizing rects i with
  | nil => simp at hb
  | cons head tail ih =>
    cases rects with
    | nil => simp at hlen
    | cons r rs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst b
        simp [hid]
      | succ i =>
        apply ih rs (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen) i
        exact hb

theorem fit_inside_canvas (width height : Int) (r : Rect)
    (hw : r.w ≤ width) (hh : r.h ≤ height) :
    Rect.Contained ⟨0,0,width,height⟩ (fit width height r) := by
  have hx : 0 ≤ width-r.w := by omega
  have hy : 0 ≤ height-r.h := by omega
  simp only [fit, Rect.Contained, clamp]
  omega

theorem venn_bisect_invariant (g : Int → Bool) (fuel : Nat) (lo hi : Int)
    (hl : g lo = true) (hh : g hi = false) :
    g (bisect g fuel lo hi).1 = true ∧ g (bisect g fuel lo hi).2 = false := by
  induction fuel generalizing lo hi with
  | zero => exact ⟨hl,hh⟩
  | succ n ih =>
    simp only [bisect]
    split <;> rename_i h
    · exact ih _ _ h hh
    · exact ih _ _ hl (Bool.eq_false_iff.mpr h)

theorem bisect_bracket (g : Int → Bool) (fuel : Nat) (lo hi : Int) (h : lo ≤ hi) :
    lo ≤ (bisect g fuel lo hi).1 ∧
    (bisect g fuel lo hi).1 ≤ (bisect g fuel lo hi).2 ∧
    (bisect g fuel lo hi).2 ≤ hi := by
  induction fuel generalizing lo hi with
  | zero => exact ⟨Int.le_refl _,h,Int.le_refl _⟩
  | succ n ih =>
    have hm := fdiv_between (lo+hi) 2 lo hi (by decide) (by omega) (by omega)
    simp only [bisect]
    split
    · have hb := ih (Int.fdiv (lo+hi) 2) hi hm.2
      exact ⟨Int.le_trans hm.1 hb.1,hb.2⟩
    · have hb := ih lo (Int.fdiv (lo+hi) 2) hm.1
      exact ⟨hb.1,hb.2.1,Int.le_trans hb.2.2 hm.2⟩

theorem bisect_width_bound (g : Int → Bool) (fuel : Nat) (lo hi : Int)
    (h : hi-lo ≤ (2 : Int)^fuel) :
    (bisect g fuel lo hi).2 - (bisect g fuel lo hi).1 ≤ 1 := by
  induction fuel generalizing lo hi with
  | zero => simpa [bisect] using h
  | succ n ih =>
    have hq := Int.mul_fdiv_add_fmod (lo+hi) 2
    have hr := Int.fmod_nonneg_of_pos (lo+hi) (by decide : (0 : Int) < 2)
    have hr' := Int.fmod_lt_of_pos (lo+hi) (by decide : (0 : Int) < 2)
    have hp : (2 : Int)^(n+1) = 2 * (2 : Int)^n := by
      rw [Int.pow_succ, Int.mul_comm]
    rw [hp] at h
    simp only [bisect]
    split
    · apply ih
      omega
    · apply ih
      omega

theorem venn_bisect_width (g : Int → Bool) (lo hi : Int)
    (h : hi-lo < 4294967296) :
    (bisect g 32 lo hi).2 - (bisect g 32 lo hi).1 ≤ 1 := by
  apply bisect_width_bound
  have hp : (2 : Int)^32 = 4294967296 := by decide
  rw [hp]
  omega
theorem distance_in_bounds (a b target : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ distance a b target ∧ distance a b target ≤ a+b := by
  have hab : ((a-b).natAbs : Int) ≤ a+b := by omega
  have hlo : (0 : Int) ≤ (a-b).natAbs := Int.natCast_nonneg _
  unfold distance
  dsimp only
  split
  · exact ⟨hlo,hab⟩
  · split
    · exact ⟨by omega,Int.le_refl _⟩
    · have hbr := bisect_bracket
        (fun d => decide (lens d a b > target*4294967296))
        (LayoutConst.venn_bisect_iterations.get .vector).toNat
        (a-b).natAbs (a+b) hab
      have hmid := fdiv_between
        ((bisect (fun d => decide (lens d a b > target*4294967296))
          (LayoutConst.venn_bisect_iterations.get .vector).toNat (a-b).natAbs (a+b)).1 +
         (bisect (fun d => decide (lens d a b > target*4294967296))
          (LayoutConst.venn_bisect_iterations.get .vector).toNat (a-b).natAbs (a+b)).2)
        2 0 (a+b) (by decide) (by omega) (by omega)
      exact hmid


theorem centres_safe (rs : List Int) (R target : Int) (hR : 0 ≤ R)
    (hr : ∀ r ∈ rs, 0 ≤ r ∧ r ≤ R) :
    ∀ c ∈ centres rs R (distance (rs.getD 0 0) (rs.getD 1 0) target), CircleSafe c := by
  cases rs with
  | nil => simp [centres]
  | cons a rest =>
    have ha := hr a (by simp)
    cases rest with
    | nil =>
      intro c hc
      simp only [centres, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst c
      unfold CircleSafe
      dsimp only
      omega
    | cons b rest =>
      have hb := hr b (by simp)
      cases rest with
      | nil =>
        have hd := distance_in_bounds a b target ha.1 hb.1
        have hq := fdiv_between (distance a b target) 2 0 R
          (by decide) (by omega) (by omega)
        intro c hc
        simp only [centres, List.getD_cons_zero, List.getD_cons_succ,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc <;> subst c <;> unfold CircleSafe <;> dsimp only <;> omega
      | cons d rest =>
        have hd := hr d (by simp)
        cases rest with
        | nil =>
          have hx := fdiv_between (R*28378) 32768 0 R
            (by decide) (by omega) (by omega)
          have hy := fdiv_between R 2 0 R (by decide) (by omega) (by omega)
          intro c hc
          simp only [centres, LayoutConst.venn_sqrt3_half_q15, LayoutConst.Pair.get,
            List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with hc | hc | hc <;> subst c <;> unfold CircleSafe <;> dsimp only <;> omega
        | cons e rest => simp [centres]

theorem shifted_centres_safe (rs : List Int) (R target band : Int)
    (hR : 0 ≤ R) (hb : 0 ≤ band) (hr : ∀ r ∈ rs, 0 ≤ r ∧ r ≤ R) :
    ∀ c ∈ (centres rs R (distance (rs.getD 0 0) (rs.getD 1 0) target)).map
      (fun c => { c with y := c.y+band }), CircleSafe c := by
  intro c hc
  obtain ⟨old,ho,he⟩ := List.mem_map.mp hc
  subst c
  have hs := centres_safe rs R target hR hr old ho
  unfold CircleSafe at *
  dsimp only
  omega

theorem zip_snd_mem {α β : Type} (xs : List α) (ys : List β) (x : α) (y : β)
    (h : (x,y) ∈ xs.zip ys) : y ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons a rest ih =>
    cases ys with
    | nil => simp at h
    | cons b tail =>
      simp only [List.zip_cons_cons, List.mem_cons] at h
      rcases h with he | he
      · cases he
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih tail he)

theorem getD_property {α : Type} (P : α → Prop) (xs : List α) (fallback : α)
    (hf : P fallback) (hx : ∀ x ∈ xs, P x) (i : Nat) : P (xs.getD i fallback) := by
  induction xs generalizing i with
  | nil => simpa using hf
  | cons x rest ih =>
    cases i with
    | zero => exact hx x (by simp)
    | succ i => exact ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx')) i

def finalWidth (s : BoxState) (width : Int) : Int :=
  s.rects.foldl (fun w r => max w (r.x+r.w))
    (s.placed.foldl (fun w it => max w (it.rect.x+it.rect.w)) width)

def finalHeight (s : BoxState) (height : Int) : Int :=
  s.rects.foldl (fun h r => max h (r.y+r.h))
    (s.placed.foldl (fun h it => max h (it.rect.y+it.rect.h)) height)

def finalRects (m : Model) (s : BoxState) (width height : Int) : List Rect :=
  (m.boxes.zip s.rects).map (fun (b,r) =>
    if b.id == "venn" then ⟨0,0,finalWidth s width,finalHeight s height⟩ else r)

def finished (m : Model) (R : Int) (cs : List Circle) (s : BoxState) (width height : Int) : Result :=
  ⟨R,cs,s.placed,finalRects m s width height,finalWidth s width,finalHeight s height⟩

theorem final_extent_nonnegative (s : BoxState) (width height : Int)
    (hw : 0 ≤ width) (hh : 0 ≤ height) :
    0 ≤ finalWidth s width ∧ 0 ≤ finalHeight s height := by
  have itemFold (items : List Item) (f : Item → Int) (n : Int) (hn : 0 ≤ n) :
      0 ≤ items.foldl (fun n it => max n (f it)) n := by
    induction items generalizing n with
    | nil => exact hn
    | cons it rest ih =>
      exact ih (max n (f it)) (Int.le_trans hn (Int.le_max_left _ _))
  exact ⟨Int.le_trans (itemFold s.placed (fun it => it.rect.x+it.rect.w) width hw)
      (extent_fold_ge s.rects _),
    Int.le_trans (itemFold s.placed (fun it => it.rect.y+it.rect.h) height hh)
      (height_fold_ge s.rects _)⟩

theorem final_rects_contained (m : Model) (s : BoxState) (width height : Int)
    (hs : BoxSafe s) :
    ∀ r ∈ finalRects m s width height,
      Rect.Contained ⟨0,0,finalWidth s width,finalHeight s height⟩ r := by
  intro r hr
  obtain ⟨⟨b,old⟩,hz,he⟩ := List.mem_map.mp hr
  subst r
  change Rect.Contained ⟨0,0,finalWidth s width,finalHeight s height⟩
    (if b.id == "venn" then ⟨0,0,finalWidth s width,finalHeight s height⟩ else old)
  by_cases hid : (b.id == "venn") = true
  · rw [ite_eq_left hid]
    exact Rect.Contained.refl _
  · rw [ite_eq_right hid]
    have hm := zip_snd_mem m.boxes s.rects b old hz
    have hsafe := hs.rects old hm
    exact rect_in_final_extent s.rects _ _ old hm hsafe.1 hsafe.2.1

theorem finished_geometry (m : Model) (R : Int) (cs : List Circle) (s : BoxState)
    (width height : Int) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hs : BoxSafe s) (hlen : s.rects.length = m.boxes.length) :
    Validator.C1 (sceneOf m (finished m R cs s width height)).layoutDump ∧
    (∀ b ∈ (sceneOf m (finished m R cs s width height)).boxes,
      b.id = "venn" → b.rect = ⟨0,0,finalWidth s width,finalHeight s height⟩) := by
  have hdim := final_extent_nonnegative s width height hw hh
  constructor
  · intro b hb
    simp only [sceneOf, List.mem_map, Scene.layoutDump] at hb
    obtain ⟨⟨source,i⟩,_,he⟩ := hb
    subst b
    change Rect.Contained ⟨0,0,finalWidth s width,finalHeight s height⟩
      ((finalRects m s width height).getD i ⟨0,0,0,0⟩)
    refine getD_property
      (fun r : Rect => Rect.Contained ⟨0,0,finalWidth s width,finalHeight s height⟩ r)
      (finalRects m s width height) ⟨0,0,0,0⟩ ?_ ?_ i
    · unfold Rect.Contained
      dsimp only
      omega
    · exact final_rects_contained m s width height hs
  · intro b hb hid
    simp only [sceneOf, List.mem_map] at hb
    obtain ⟨⟨source,i⟩,hi,he⟩ := hb
    subst b
    exact final_root_rect m.boxes s.rects _ _ hlen.symm i source
      (List.mem_zipIdx_iff_getElem?.mp hi) hid

theorem layoutCore_geometry (m : Model) (r : Result)
    (hw : 0 ≤ config m "width" 800) (hh : 0 ≤ config m "height" 450)
    (h : layoutCore m = .ok r) :
    Validator.C1 (sceneOf m r).layoutDump ∧
    (∀ b ∈ (sceneOf m r).boxes, b.id = "venn" →
      b.rect = ⟨0,0,r.width,r.height⟩) := by
  let R := Int.fdiv (min
    (config m "width" (Int.fdiv (LayoutConst.venn_width.get .vector) 64))
    (config m "height" (Int.fdiv (LayoutConst.venn_height.get .vector) 64))) 4 * 64
  have hR : 0 ≤ R := by
    change 0 ≤ Int.fdiv (min (config m "width" 800) (config m "height" 450)) 4 * 64
    exact Int.mul_nonneg (Int.fdiv_nonneg (by omega) (by decide)) (by decide)
  unfold layoutCore at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨items,hitems,h⟩ := bind_ok h
  have hi := mapM_nonnegative (4*R) m.labels items hitems
  have his := measured_items_safe (4*R) m.labels items hitems
  let band := ((items.find? (fun i => i.label.id == "title")).map (·.box.h)).getD 0
  have hb : 0 ≤ band := by
    cases hf : items.find? (fun i => i.label.id == "title") with
    | none => simp [band,hf]
    | some it =>
      have hh' := (hi it (List.mem_of_find?_eq_some hf)).2
      simpa only [band,hf,Option.map_some,Option.getD_some] using hh'
  let width := items.foldl (fun w it => max w it.box.w) (4*R)
  let height := 4*R+band
  have hwidth : 0 ≤ width := by
    have fold_nonnegative (xs : List Item) (n : Int) (hn : 0 ≤ n) :
        0 ≤ xs.foldl (fun w it => max w it.box.w) n := by
      induction xs generalizing n with
      | nil => exact hn
      | cons it rest ih =>
        exact ih (max n it.box.w) (Int.le_trans hn (Int.le_max_left _ _))
    exact fold_nonnegative items (4*R) (by omega)
  have hheight : 0 ≤ height := by dsimp only [height]; omega
  obtain ⟨rs,hrs,h⟩ := bind_ok h
  have hr := measured_radius_bounds (sizes m) rs R hR hrs
  let target := Int.fdiv (R*R*max (overlap m) 0) ((sizes m).foldl max 1)
  let circles := (centres rs R (distance (rs.getD 0 0) (rs.getD 1 0) target)).map
    (fun c => { c with y := c.y+band })
  have hc : ∀ c ∈ circles, CircleSafe c := shifted_centres_safe rs R target band hR hb hr
  obtain ⟨state,hstate,h⟩ := bind_ok h
  have hstate' : placeBoxes m circles items width height band m.boxes ⟨items,[]⟩ = .ok state := hstate
  have hs : BoxSafe state := placeBoxes_safe m circles items width height band m.boxes
    ⟨items,[]⟩ state hwidth hheight hc hi ⟨his,by simp⟩ hstate'
  have hl : state.rects.length = m.boxes.length := by
    simpa only [List.length_nil,Nat.zero_add] using
      placeBoxes_length m circles items width height band m.boxes ⟨items,[]⟩ state hstate'
  obtain ⟨_,_,h⟩ := bind_ok h
  change Except.ok (finished m R circles state width height) = Except.ok r at h
  cases h
  exact finished_geometry m R circles state width height hwidth hheight hs hl

theorem venn_bisect_result_in_bracket (g : Int → Bool) (lo hi : Int)
    (h : lo ≤ hi) (hw : hi-lo < 4294967296)
    (hl : g lo = true) (hh : g hi = false) :
    let b := bisect g 32 lo hi
    let d := Int.fdiv (b.1+b.2) 2
    lo ≤ d ∧ d ≤ hi ∧ b.1 ≤ d ∧ d ≤ b.2 ∧
      b.2-b.1 ≤ 1 ∧ g b.1 = true ∧ g b.2 = false := by
  have hb := bisect_bracket g 32 lo hi h
  have hm := fdiv_between ((bisect g 32 lo hi).1+(bisect g 32 lo hi).2) 2
    (bisect g 32 lo hi).1 (bisect g 32 lo hi).2 (by decide) (by omega) (by omega)
  exact ⟨Int.le_trans hb.1 hm.1, Int.le_trans hm.2 hb.2.2,
    hm.1,hm.2,venn_bisect_width g lo hi hw,venn_bisect_invariant g 32 lo hi hl hh⟩

theorem venn3_inside_canvas (R a b c : Int) (hR : 0 ≤ R)
    (ha : 0 ≤ a ∧ a ≤ R) (hb : 0 ≤ b ∧ b ≤ R) (hc : 0 ≤ c ∧ c ≤ R) :
    ∀ circle ∈ centres [a,b,c] R 0,
      Rect.Contained ⟨0,0,4*R,4*R⟩
        ⟨circle.x-circle.r,circle.y-circle.r,2*circle.r,2*circle.r⟩ := by
  have hx := fdiv_between (R*28378) 32768 0 R (by decide) (by omega) (by omega)
  have hy := fdiv_between R 2 0 R (by decide) (by omega) (by omega)
  intro circle h
  simp only [centres, LayoutConst.venn_sqrt3_half_q15, LayoutConst.Pair.get,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> subst circle <;> simp only [Rect.Contained] <;> omega

theorem venn_too_many_sets (m : Model) (h : (sizes m).length > 3) :
    layout m = .error .domain := by
  simp [layout, h]
theorem venn_no_sets (m : Model) (h : sizes m = []) :
    layout m = .error .domain := by
  simp [layout, h]

theorem venn_exclusive_clauses (m : Model) (s : Layered.FamilyResult)
    (h : Kinds.Venn.layout m = .ok s) :
    Validator.C2 s.scene.layoutDump ∧ Validator.C6 s.scene.layoutDump ∧
      Validator.C7 s.scene.layoutDump := by
  obtain ⟨r, _, hs⟩ := Kinds.Venn.successful_scene m s h
  rw [hs]
  apply scene_exclusive_clauses
  have hn := Kinds.Venn.successful_nonexclusive m s h
  intro b hb
  apply Bool.eq_false_iff.mpr
  intro he
  have ha : m.boxes.any (·.exclusive) = true :=
    List.any_eq_true.mpr ⟨b,hb,he⟩
  rw [hn] at ha
  cases ha

theorem venn_route_clauses (m : Model) (s : Layered.FamilyResult)
    (h : Kinds.Venn.layout m = .ok s) :
    Validator.C4 s.scene.layoutDump ∧ Validator.C5 s.scene.layoutDump := by
  obtain ⟨r, _, hs⟩ := Kinds.Venn.successful_scene m s h
  rw [hs]
  simp [Validator.C4, Validator.C5, sceneOf, Scene.layoutDump]

theorem venn_group_clauses (m : Model) (s : Layered.FamilyResult)
    (h : Kinds.Venn.layout m = .ok s) :
    Validator.C8 s.scene.layoutDump := by
  obtain ⟨r, _, hs⟩ := Kinds.Venn.successful_scene m s h
  have hr := Kinds.Venn.successful_roles m s h
  have hroles : ∀ b ∈ m.boxes, b.role = .node := by
    intro b hb
    by_cases he : b.role = .node
    · exact he
    · have ha : m.boxes.any (fun b => b.role != .node) = true :=
        List.any_eq_true.mpr ⟨b,hb,by simp [he]⟩
      rw [hr] at ha
      cases ha
  have hnodes : ∀ b ∈ (sceneOf m r).boxes, b.role = "node" := by
    intro b hb
    simp only [sceneOf, List.mem_map] at hb
    obtain ⟨⟨source,i⟩, hmem, he⟩ := hb
    subst b
    have hh := hroles source (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hmem))
    simp only [hh, BoxRole.id]
  rw [hs]
  constructor
  · intro b hb he
    have hn := hnodes b hb
    simp [hn] at he
  · intro b hb he
    have hn := hnodes b hb
    simp [hn] at he

theorem venn_valid (m : Model) (_hwell : Elegant.WellFormed m) (_hlimits : WithinLimits m)
    (s : Layered.FamilyResult) (h : Kinds.Venn.layout m = .ok s) :
    HardConstraints s.scene.layoutDump := by
  obtain ⟨r,hr,hs⟩ := Kinds.Venn.successful_scene m s h
  have hd := Kinds.Venn.successful_dimensions m s h
  unfold layout at hr
  split at hr
  · cases hr
  · have hg := layoutCore_geometry m r hd.1 hd.2 hr
    have hc1 : Validator.C1 s.scene.layoutDump := by simpa only [hs] using hg.1
    have hroot : ∀ b ∈ s.scene.boxes, b.id = "venn" →
        b.rect = ⟨0,0,s.scene.canvas.w,s.scene.canvas.h⟩ := by
      simpa only [hs,sceneOf] using hg.2
    have hparents := Kinds.Venn.successful_parents m s h
    have hpinput : ∀ b ∈ m.boxes, b.parent = "" ∨ b.parent = "venn" := by
      intro b hb
      have hp := (List.any_eq_false.mp hparents) b hb
      by_cases hid : b.id = "venn"
      · exact Or.inl (by simpa [hid] using hp)
      · exact Or.inr (by simpa [hid] using hp)
    have hpoutput : ∀ b ∈ s.scene.boxes, b.parent = "" ∨ b.parent = "venn" := by
      rw [hs]
      intro b hb
      simp only [sceneOf,List.mem_map] at hb
      obtain ⟨⟨source,i⟩,hmem,he⟩ := hb
      subst b
      exact hpinput source (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hmem))
    have hc3 : Validator.C3 s.scene.layoutDump := by
      intro b hb hne p hp
      have hpar : b.parent = "venn" := (hpoutput b hb).resolve_left hne
      have hp' : s.scene.layoutDump.boxes.find? (fun b => b.id == "venn") = some p := by
        simpa only [LayoutDump.box?,hpar] using hp
      have hpid : p.id = "venn" := by simpa only [beq_iff_eq] using List.find?_some hp'
      have hpmem : p ∈ s.scene.boxes := List.mem_of_find?_eq_some hp'
      rw [hroot p hpmem hpid]
      exact hc1 b hb
    have he := venn_exclusive_clauses m s h
    have hroute := venn_route_clauses m s h
    have hgroup := venn_group_clauses m s h
    exact ⟨hc1,he.1,hc3,hroute.1,hroute.2,he.2.1,he.2.2,hgroup⟩

end Elegant.Chart.Venn
