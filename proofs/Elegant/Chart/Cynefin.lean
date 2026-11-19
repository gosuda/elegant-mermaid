import Std.Tactic.BVDecide
import Elegant.Chart.XY

set_option autoImplicit false

namespace Elegant.Chart.Cynefin

def integer (o : Options) (key : String) : Option Int :=
  o.config.findSome? fun (k, v) => match v with
    | .integer n => if k == key then some n else none
    | _ => none

structure Consts where
  width : Int
  height : Int
  confusion : Int
  amplitude : Int
  seed : UInt32
  pad : Int
  nameGap : Int
  itemPadX : Int
  itemPadY : Int
  itemGap : Int
  boxPad : Int
  labelGap : Int
  corner : Int
  edge : Int

def constants (m : Model) : Consts :=
  let p := m.profile
  let side := fun (n divisor : Int) => if p == .cell then Int.fdiv (n + divisor - 1) divisor else n * 64
  let width := (integer m.options "width").map (fun n => side n 8) |>.getD (LayoutConst.cynefin_width.get p)
  let height := (integer m.options "height").map (fun n => side n 16) |>.getD (LayoutConst.cynefin_height.get p)
  { width, height, confusion := LayoutConst.cynefin_confusion_permille.get p,
    amplitude := (integer m.options "boundaryAmplitude").map (fun n => side n 8)
      |>.getD (Int.fdiv (width * LayoutConst.cynefin_amplitude_permille.get p) 1000),
    seed := UInt32.ofNat ((integer m.options "seed").getD (LayoutConst.cynefin_default_seed.get p)).toNat,
    pad := LayoutConst.cynefin_pad.get p, nameGap := LayoutConst.cynefin_name_gap.get p,
    itemPadX := LayoutConst.cynefin_item_pad_x.get p, itemPadY := LayoutConst.cynefin_item_pad_y.get p,
    itemGap := LayoutConst.cynefin_item_gap.get p, boxPad := LayoutConst.cynefin_box_pad.get p,
    labelGap := LayoutConst.cynefin_label_gap.get p, corner := LayoutConst.corner_radius.get p,
    edge := if p == .cell then 1 else 0 }

theorem constants_spacing_nonnegative (m : Model) :
    let c := constants m
    0 ≤ c.pad ∧ 0 ≤ c.nameGap ∧ 0 ≤ c.itemPadX ∧ 0 ≤ c.itemPadY ∧
      0 ≤ c.itemGap ∧ 0 ≤ c.boxPad ∧ 0 ≤ c.labelGap := by
  cases h : m.profile <;>
    simp [constants, h, LayoutConst.Pair.get, LayoutConst.cynefin_pad,
      LayoutConst.cynefin_name_gap, LayoutConst.cynefin_item_pad_x,
      LayoutConst.cynefin_item_pad_y, LayoutConst.cynefin_item_gap,
      LayoutConst.cynefin_box_pad, LayoutConst.cynefin_label_gap]

def step (s : UInt32) : UInt32 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 17)
  s ^^^ (s <<< 5)

def draws : Nat → UInt32 → List UInt32
  | 0, _ => []
  | n + 1, s => let t := step s; t :: draws n t

private theorem toNat_ne_zero {x : UInt32} (hx : x ≠ 0) : x.toNat ≠ 0 := by
  intro h
  exact hx (UInt32.toNat_inj.mp (by rw [h]; rfl))

private theorem xor_shiftLeft13_ne_zero (x : UInt32) (hx : x ≠ 0) :
    x ^^^ (x <<< 13) ≠ 0 := by
  intro h
  have he := congrArg UInt32.toNat (UInt32.xor_eq_zero_iff.mp h)
  have hk : (13 : UInt32).toNat % 32 = 13 := rfl
  rw [UInt32.toNat_shiftLeft, hk, Nat.shiftLeft_eq] at he
  have hb := UInt32.toNat_lt x
  have hz := toNat_ne_zero hx
  simp only [Nat.reducePow] at he hb
  omega

private theorem xor_shiftLeft5_ne_zero (x : UInt32) (hx : x ≠ 0) :
    x ^^^ (x <<< 5) ≠ 0 := by
  intro h
  have he := congrArg UInt32.toNat (UInt32.xor_eq_zero_iff.mp h)
  have hk : (5 : UInt32).toNat % 32 = 5 := rfl
  rw [UInt32.toNat_shiftLeft, hk, Nat.shiftLeft_eq] at he
  have hb := UInt32.toNat_lt x
  have hz := toNat_ne_zero hx
  simp only [Nat.reducePow] at he hb
  omega

private theorem xor_shiftRight17_ne_zero (x : UInt32) (hx : x ≠ 0) :
    x ^^^ (x >>> 17) ≠ 0 := by
  intro h
  have he := congrArg UInt32.toNat (UInt32.xor_eq_zero_iff.mp h)
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at he
  have hz := toNat_ne_zero hx
  have h17 : (17 : UInt32).toNat % 32 = 17 := rfl
  rw [h17] at he
  omega

theorem xorshift32_step_nonzero (s : UInt32) (h : s ≠ 0) : step s ≠ 0 :=
  xor_shiftLeft5_ne_zero _ (xor_shiftRight17_ne_zero _ (xor_shiftLeft13_ne_zero s h))

theorem cynefin_draw_count (s : UInt32) : (draws 15 s).length = 15 := by
  have h : ∀ n s, (draws n s).length = n := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih => intro s; simp only [draws, List.length_cons, ih]
  exact h 15 s

def foldPoints (c : Consts) : List Point :=
  let ds := draws 15 c.seed
  (List.range 8).map fun (i : Nat) =>
    ⟨Int.fdiv c.width 2 + Int.fdiv (((ds[i]?.getD 0).toNat : Int) * 2 * c.amplitude) 4294967296 - c.amplitude,
     Int.fdiv ((i : Int) * c.height) 7⟩

theorem cynefin_boundary_inside_frame (c : Consts)
    (hA : 0 ≤ c.amplitude) (hH : 0 ≤ c.height) :
    ∀ p ∈ foldPoints c,
      (if c.amplitude = 0 then p.x = Int.fdiv c.width 2
       else Int.fdiv c.width 2 - c.amplitude ≤ p.x ∧
         p.x < Int.fdiv c.width 2 + c.amplitude) ∧
      0 ≤ p.y ∧ p.y ≤ c.height := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hi8 : i < 8 := List.mem_range.mp hi
  let u := ((draws 15 c.seed)[i]?).getD 0
  have hu0 : 0 ≤ (u.toNat : Int) := Int.natCast_nonneg _
  have hu : (u.toNat : Int) < 4294967296 := by
    have h := u.toNat_lt
    omega
  have hn : 0 ≤ (u.toNat : Int) * 2 * c.amplitude :=
    Int.mul_nonneg (Int.mul_nonneg hu0 (by decide)) hA
  have hq0 := Int.ediv_nonneg hn (show (0 : Int) ≤ 4294967296 by decide)
  have hy0 : 0 ≤ (i : Int) * c.height :=
    Int.mul_nonneg (Int.natCast_nonneg _) hH
  have hy7 : (i : Int) * c.height ≤ c.height * 7 := by
    have h := Int.mul_le_mul_of_nonneg_right (show (i : Int) ≤ 7 by omega) hH
    simpa only [Int.mul_comm] using h
  have hylo := Int.ediv_nonneg hy0 (show (0 : Int) ≤ 7 by decide)
  have hyhi := Int.ediv_le_of_le_mul (show (0 : Int) < 7 by decide) hy7
  simp only
  change (if c.amplitude = 0 then
      Int.fdiv c.width 2 + Int.fdiv ((u.toNat : Int) * 2 * c.amplitude) 4294967296 -
        c.amplitude = Int.fdiv c.width 2
    else Int.fdiv c.width 2 - c.amplitude ≤
      Int.fdiv c.width 2 + Int.fdiv ((u.toNat : Int) * 2 * c.amplitude) 4294967296 -
        c.amplitude ∧
      Int.fdiv c.width 2 + Int.fdiv ((u.toNat : Int) * 2 * c.amplitude) 4294967296 -
        c.amplitude < Int.fdiv c.width 2 + c.amplitude) ∧
    0 ≤ Int.fdiv ((i : Int) * c.height) 7 ∧
      Int.fdiv ((i : Int) * c.height) 7 ≤ c.height
  rw [Measure.fdiv_of_nonneg (b := 4294967296) (by decide),
    Measure.fdiv_of_nonneg (b := 7) (by decide)]
  constructor
  · by_cases hzero : c.amplitude = 0
    · simp [hzero]
    · rw [ite_eq_right hzero]
      have hpositive : 0 < 2 * c.amplitude := by omega
      have hproduct := Int.mul_lt_mul_of_pos_right hu hpositive
      have hqhi : (u.toNat : Int) * 2 * c.amplitude / 4294967296 <
          2 * c.amplitude :=
        (Int.ediv_lt_iff_lt_mul (by decide)).mpr
          (by simpa [Int.mul_assoc, Int.mul_comm] using hproduct)
      omega
  · exact ⟨hylo, hyhi⟩

def foldCommands (cell : Bool) (c : Consts) : List PathCommand :=
  let ps := foldPoints c
  let ds := draws 15 c.seed
  [.M (ps[0]?.getD ⟨0, 0⟩)] ++ (List.range 7).map fun i =>
    let a := ps[i]?.getD ⟨0, 0⟩
    let b := ps[i+1]?.getD ⟨0, 0⟩
    let off := (if i % 2 == 0 then 1 else -1) *
      Int.fdiv (3 * c.amplitude * (ds[i+8]?.getD 0).toNat) 8589934592
    let mid := Int.fdiv (a.y + b.y) 2
    if cell then .L b else .C ⟨a.x + off, mid⟩ ⟨b.x - off, mid⟩ b

def cliffCommands (c : Consts) : List PathCommand :=
  let cx := Int.fdiv c.width 2
  let cy := Int.fdiv c.height 2
  let a := Int.fdiv (c.width * 3) 100
  let pointAt := fun dx percent => Point.mk (cx + dx) (cy + Int.fdiv ((c.height - cy) * percent) 100)
  [.M ⟨cx, cy⟩, .C (pointAt a 20) (pointAt (-Int.fdiv (3*a) 2) 55) (pointAt (Int.fdiv a 2) 75),
   .C (pointAt (-a) 85) (pointAt (Int.fdiv (3*a) 10) 95) ⟨cx, c.height⟩]

def quadrant (c : Consts) (name : String) : Rect :=
  let w := Int.fdiv c.width 2
  let h := Int.fdiv c.height 2
  if name == "complex" then ⟨0, 0, w, h⟩
  else if name == "complicated" then ⟨w, 0, c.width - w, h⟩
  else if name == "clear" then ⟨w, h, c.width - w, c.height - h⟩
  else ⟨0, h, w, c.height - h⟩

def quadrants (c : Consts) : List Rect :=
  ["complex", "complicated", "clear", "chaotic"].map (quadrant c)

theorem cynefin_domains_tile_frame (c : Consts) (hw : 0 ≤ c.width) (hh : 0 ≤ c.height) :
    List.Pairwise Disjoint (quadrants c) ∧
      (∀ r ∈ quadrants c, (Rect.mk 0 0 c.width c.height).Contained r) ∧
      ((quadrants c).map (fun r => r.w * r.h)).sum = c.width * c.height := by
  have hfw := Measure.fdiv_of_nonneg (a := c.width) (b := 2) (by decide)
  have hfh := Measure.fdiv_of_nonneg (a := c.height) (b := 2) (by decide)
  constructor
  · simp [quadrants, quadrant, List.pairwise_cons, Disjoint, Rect.meetsInterior,
      hfw, hfh] <;> omega
  constructor
  · intro r hr
    simp only [quadrants, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp [quadrant, Rect.Contained, hfw, hfh] <;> omega
  · simp [quadrants, quadrant, Int.sub_mul, Int.mul_sub] <;> omega

def right (r : Rect) : Int := r.x + r.w
def bottom (r : Rect) : Int := r.y + r.h

theorem folded_width_ge_initial (lines : List Measure.Line) (initial : Int) :
    initial ≤ lines.foldl (fun w l => max w l.width) initial := by
  induction lines generalizing initial with
  | nil => exact Int.le_refl _
  | cons first rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih (max initial first.width))

theorem measured_text_nonnegative (cell : Bool) (text : String) (role : Measure.Role)
    (box : XY.TextBox) (hout : XY.measureText cell text role role.sizePx = .ok box) :
    0 ≤ box.w ∧ 0 ≤ box.h := by
  cases hm : XY.metricOf cell role role.sizePx with
  | error e => simp [XY.measureText, hm, Bind.bind, Except.bind] at hout
  | ok metric =>
    cases hl : StyledMeasure.wrap metric I32_MAX text.toList with
    | error e =>
      simp [XY.measureText, hm, Bind.bind, Except.bind, hl] at hout
    | ok lines =>
      have he : (XY.TextBox.mk lines
          (lines.foldl (fun w l => max w l.width) 0)
          ((lines.length : Int) * XY.lineHeight cell role role.sizePx)) = box :=
        by simpa [XY.measureText, hm, Bind.bind, Except.bind, hl,
          Pure.pure, Except.pure] using hout
      cases he
      constructor
      · exact folded_width_ge_initial lines 0
      · apply Int.mul_nonneg (Int.natCast_nonneg _)
        cases cell <;> cases role <;>
          decide

structure Placed where
  source : ModelLabel
  box : XY.TextBox
  rect : Rect
  role : Measure.Role
  align : Align := .middle

structure Domain where
  id : String
  cx : Int
  anchorY : Int
  rect : Rect
  badges : List Rect
  labels : List Placed

def Domain.PortBounds (d : Domain) : Prop :=
  0 ≤ d.rect.w ∧ 0 ≤ d.rect.h ∧
  d.rect.x ≤ d.cx ∧ d.cx ≤ right d.rect ∧
  d.rect.y ≤ d.anchorY ∧ d.anchorY ≤ bottom d.rect

theorem domain_left_port (d : Domain) (h : d.PortBounds) :
    Validator.onBoundary ⟨d.rect.x, d.anchorY⟩ d.rect := by
  rcases h with ⟨hw, _hh, _hx0, _hx1, hy0, hy1⟩
  exact ⟨Int.le_refl _, by dsimp [right] at *; omega, hy0, hy1, Or.inl rfl⟩

theorem domain_right_port (d : Domain) (h : d.PortBounds) :
    Validator.onBoundary ⟨right d.rect, d.anchorY⟩ d.rect := by
  rcases h with ⟨hw, _hh, _hx0, _hx1, hy0, hy1⟩
  exact ⟨by dsimp [right] at *; omega, Int.le_refl _, hy0, hy1, Or.inr (Or.inl rfl)⟩

theorem domain_top_port (d : Domain) (h : d.PortBounds) :
    Validator.onBoundary ⟨d.cx, d.rect.y⟩ d.rect := by
  rcases h with ⟨_hw, hh, hx0, hx1, _hy0, _hy1⟩
  exact ⟨hx0, hx1, Int.le_refl _, by dsimp [bottom] at *; omega,
    Or.inr (Or.inr (Or.inl rfl))⟩

theorem domain_bottom_port (d : Domain) (h : d.PortBounds) :
    Validator.onBoundary ⟨d.cx, bottom d.rect⟩ d.rect := by
  rcases h with ⟨_hw, hh, hx0, hx1, _hy0, _hy1⟩
  exact ⟨hx0, hx1, by dsimp [bottom] at *; omega, Int.le_refl _,
    Or.inr (Or.inr (Or.inr rfl))⟩

def boundsOf (initial : Rect) (items : List Rect) : Rect :=
  items.foldl Rect.unionRaw initial

theorem unionRaw_contains_left (a b : Rect) :
    (a.unionRaw b).Contained a := by
  unfold Rect.Contained Rect.unionRaw
  simp only
  omega

theorem unionRaw_contains_right (a b : Rect) :
    (a.unionRaw b).Contained b := by
  unfold Rect.Contained Rect.unionRaw
  simp only
  omega

theorem boundsOf_contains_initial (initial : Rect) (items : List Rect) :
    (boundsOf initial items).Contained initial := by
  induction items generalizing initial with
  | nil => exact Rect.Contained.refl _
  | cons first rest ih =>
    exact Rect.Contained.trans (ih (initial.unionRaw first))
      (unionRaw_contains_left initial first)

theorem boundsOf_contains_member (initial : Rect) (items : List Rect)
    (r : Rect) (hr : r ∈ items) : (boundsOf initial items).Contained r := by
  induction items generalizing initial with
  | nil => simp at hr
  | cons first rest ih =>
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact Rect.Contained.trans
        (boundsOf_contains_initial (initial.unionRaw first) rest)
        (unionRaw_contains_right initial first)
    · exact ih (initial.unionRaw first) hr

theorem inflateRaw_contains_self (r : Rect) (padding : Int) (h : 0 ≤ padding) :
    (r.inflateRaw padding).Contained r := by
  unfold Rect.Contained Rect.inflateRaw
  simp only
  omega

def domainBounds (title : Rect) (badges : List Rect) (padding : Int) : Rect :=
  (boundsOf title badges).inflateRaw padding

theorem domainBounds_contains_title (title : Rect) (badges : List Rect) (padding : Int)
    (h : 0 ≤ padding) : (domainBounds title badges padding).Contained title :=
  Rect.Contained.trans (inflateRaw_contains_self _ padding h)
    (boundsOf_contains_initial title badges)

theorem domainBounds_contains_badge (title : Rect) (badges : List Rect) (padding : Int)
    (h : 0 ≤ padding) (badge : Rect) (hb : badge ∈ badges) :
    (domainBounds title badges padding).Contained badge :=
  Rect.Contained.trans (inflateRaw_contains_self _ padding h)
    (boundsOf_contains_member title badges badge hb)

theorem domainBounds_nonnegative (title : Rect) (badges : List Rect) (padding : Int)
    (hw : 0 ≤ title.w) (hh : 0 ≤ title.h) (hpad : 0 ≤ padding) :
    0 ≤ (domainBounds title badges padding).w ∧
      0 ≤ (domainBounds title badges padding).h := by
  have hc := boundsOf_contains_initial title badges
  unfold Rect.Contained at hc
  unfold domainBounds Rect.inflateRaw
  simp only
  omega

theorem portBounds_of_title_containment (d : Domain) (top width height : Int)
    (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hdw : 0 ≤ d.rect.w) (hdh : 0 ≤ d.rect.h)
    (hy : d.anchorY = top + Int.fdiv height 2)
    (hc : d.rect.Contained ⟨d.cx - Int.fdiv width 2, top, width, height⟩) :
    d.PortBounds := by
  have hfw := Measure.fdiv_of_nonneg (a := width) (b := 2) (by decide)
  have hfh := Measure.fdiv_of_nonneg (a := height) (b := 2) (by decide)
  unfold Rect.Contained at hc
  unfold Domain.PortBounds right bottom
  simp only at hc
  rw [hfw] at hc
  rw [hfh] at hy
  omega

theorem centred_left_nonnegative (width widest padding preferred canvasWidth : Int)
    (hwide : width ≤ widest) :
    0 ≤ max (Int.fdiv widest 2 + padding)
      (min preferred (canvasWidth - (widest - Int.fdiv widest 2 + padding))) -
        Int.fdiv width 2 - padding := by
  have hfw := Measure.fdiv_of_nonneg (a := width) (b := 2) (by decide)
  have hfb := Measure.fdiv_of_nonneg (a := widest) (b := 2) (by decide)
  rw [hfw, hfb]
  omega

def measureDomain (m : Model) (id : String) :
    Except LayoutError (List (ModelLabel × XY.TextBox × Measure.Role)) :=
  (m.labels.filter (fun l => l.owner == id)).mapM fun l => do
    let role := if l.id == id ++ ".label" then Measure.Role.label else .body
    let box ← XY.measureText (m.profile == .cell) l.text role role.sizePx
    pure (l, box, role)

def measuredWidth (c : Consts) (measured : List (ModelLabel × XY.TextBox × Measure.Role)) : Int :=
  (measured.drop 1).foldl (fun w t => max w (t.2.1.w + 2*c.itemPadX))
    (measured.head?.map (fun t => t.2.1.w) |>.getD 0)

def placeDomain (c : Consts) (m : Model) (titleHeight : Int) (id : String) : Except LayoutError Domain := do
  let measured ← measureDomain m id
  let title := measured.head?
  let titleW := title.map (fun x => x.2.1.w) |>.getD 0
  let titleH := title.map (fun x => x.2.1.h) |>.getD 0
  let widest := measuredWidth c measured
  let total := (measured.drop 1).zipIdx.foldl (fun h (t, i) =>
    h + (if i == 0 then c.nameGap else c.itemGap) + t.2.1.h + 2*c.itemPadY) titleH
  let q := quadrant c id
  if m.boxes.any (fun b => b.id == id && b.role == .group) &&
      widest + 2*c.boxPad > q.w then
    throw .domain
  let cx0 := if id == "confusion" then Int.fdiv c.width 2 else q.x + Int.fdiv q.w 2
  let top := if id == "confusion" then max c.boxPad (Int.fdiv c.height 2 - Int.fdiv total 2)
    else q.y + (if q.y == 0 && titleHeight > 0 then 2*c.pad + titleHeight else c.pad)
  let lo := Int.fdiv widest 2 + c.boxPad
  let hi := widest - Int.fdiv widest 2 + c.boxPad
  let cx := max lo (min cx0 (c.width - hi))
  let nameRect : Rect := ⟨cx - Int.fdiv titleW 2, top, titleW, titleH⟩
  let init : List Placed := match title with
    | none => []
    | some (l, b, role) => [⟨l, b, nameRect, role, .middle⟩]
  let (_, badges, labels) := (measured.drop 1).foldl (fun (y, badges, labels) (l, b, role) =>
    let badge : Rect := ⟨cx - Int.fdiv (b.w + 2*c.itemPadX) 2, y,
      b.w + 2*c.itemPadX, b.h + 2*c.itemPadY⟩
    (y + badge.h + c.itemGap, badges ++ [badge], labels ++ [⟨l, b,
      ⟨cx - Int.fdiv b.w 2, y + c.itemPadY, b.w, b.h⟩, role, .middle⟩]))
    (top + titleH + c.nameGap, [], init)
  pure ⟨id, cx, top + Int.fdiv titleH 2,
    domainBounds nameRect badges c.boxPad, badges, labels⟩

theorem placeDomain_rejects_group_overflow (c : Consts) (m : Model) (titleHeight : Int)
    (id : String) (measured : List (ModelLabel × XY.TextBox × Measure.Role))
    (hm : measureDomain m id = .ok measured)
    (hg : m.boxes.any (fun b => b.id == id && b.role == .group) = true)
    (hw : (quadrant c id).w < measuredWidth c measured + 2*c.boxPad) :
    placeDomain c m titleHeight id = .error .domain := by
  simp [placeDomain, hm, hg, hw, Bind.bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

theorem placeDomain_group_width (c : Consts) (m : Model) (titleHeight : Int)
    (id : String) (domain : Domain)
    (measured : List (ModelLabel × XY.TextBox × Measure.Role))
    (hm : measureDomain m id = .ok measured)
    (hg : m.boxes.any (fun b => b.id == id && b.role == .group) = true)
    (h : placeDomain c m titleHeight id = .ok domain) :
    measuredWidth c measured + 2*c.boxPad ≤ (quadrant c id).w := by
  by_cases hn : measuredWidth c measured + 2*c.boxPad ≤ (quadrant c id).w
  · exact hn
  · have hw : (quadrant c id).w < measuredWidth c measured + 2*c.boxPad := by omega
    rw [placeDomain_rejects_group_overflow c m titleHeight id measured hm hg hw] at h
    cases h

theorem successful_group_reservation (c : Consts) (m : Model) (titleHeight : Int)
    (id : String) (domain : Domain)
    (hg : m.boxes.any (fun b => b.id == id && b.role == .group) = true)
    (h : placeDomain c m titleHeight id = .ok domain) :
    ∃ measured, measureDomain m id = .ok measured ∧
      measuredWidth c measured + 2*c.boxPad ≤ (quadrant c id).w := by
  cases hm : measureDomain m id with
  | error e => simp [placeDomain, hm, Bind.bind, Except.bind] at h
  | ok measured =>
    exact ⟨measured, rfl, placeDomain_group_width c m titleHeight id domain measured hm hg h⟩

def groupBudgetWitness (complexHeading otherHeading : String) (otherId : String)
    (otherRole : BoxRole) : Model :=
  { kind := "cynefin", profile := .cell,
    boxes := [
      { id := "frame", exclusive := false },
      { id := "complex", role := .group, parent := "frame", exclusive := false },
      { id := otherId, role := otherRole, parent := "frame", exclusive := false }],
    labels := [
      { id := "complex.label", owner := "complex", text := complexHeading },
      { id := otherId ++ ".label", owner := otherId, text := otherHeading }] }

def heightBudgetWitness : Model :=
  groupBudgetWitness (String.intercalate "\n" (List.replicate 80 "X")) "Y" "chaotic" .group

def forcedBreakHeightBudgetWitness : Model :=
  groupBudgetWitness (String.intercalate "<br/>" (List.replicate 80 "X"))
    "Y" "chaotic" .group

structure Link where
  horizontal : Bool
  a : Point
  b : Point

def links (a b : Domain) : List Link :=
  let h := if right a.rect ≤ b.rect.x then some (Link.mk true ⟨right a.rect, a.anchorY⟩ ⟨b.rect.x, b.anchorY⟩)
    else if right b.rect ≤ a.rect.x then some (Link.mk true ⟨a.rect.x, a.anchorY⟩ ⟨right b.rect, b.anchorY⟩) else none
  let v := if bottom a.rect ≤ b.rect.y then some (Link.mk false ⟨a.cx, bottom a.rect⟩ ⟨b.cx, b.rect.y⟩)
    else if bottom b.rect ≤ a.rect.y then some (Link.mk false ⟨a.cx, a.rect.y⟩ ⟨b.cx, bottom b.rect⟩) else none
  let out := h.toList ++ v.toList
  if out.isEmpty then [if a.cx ≤ b.cx then ⟨true, ⟨right a.rect, a.anchorY⟩, ⟨b.rect.x, b.anchorY⟩⟩
    else ⟨true, ⟨a.rect.x, a.anchorY⟩, ⟨right b.rect, b.anchorY⟩⟩] else out

theorem links_ports (a b : Domain) (ha : a.PortBounds) (hb : b.PortBounds)
    (l : Link) (hl : l ∈ links a b) :
    Validator.onBoundary l.a a.rect ∧ Validator.onBoundary l.b b.rect := by
  by_cases h1 : right a.rect ≤ b.rect.x
  all_goals by_cases h2 : right b.rect ≤ a.rect.x
  all_goals by_cases h3 : bottom a.rect ≤ b.rect.y
  all_goals by_cases h4 : bottom b.rect ≤ a.rect.y
  all_goals by_cases h5 : a.cx ≤ b.cx
  all_goals simp_all [links]
  all_goals first | subst l | rcases hl with rfl | rfl
  all_goals first
    | exact ⟨domain_right_port a ha, domain_left_port b hb⟩
    | exact ⟨domain_left_port a ha, domain_right_port b hb⟩
    | exact ⟨domain_bottom_port a ha, domain_top_port b hb⟩
    | exact ⟨domain_top_port a ha, domain_bottom_port b hb⟩

theorem links_nonempty (a b : Domain) : links a b ≠ [] := by
  by_cases h1 : right a.rect ≤ b.rect.x
  all_goals by_cases h2 : right b.rect ≤ a.rect.x
  all_goals by_cases h3 : bottom a.rect ≤ b.rect.y
  all_goals by_cases h4 : bottom b.rect ≤ a.rect.y
  all_goals by_cases h5 : a.cx ≤ b.cx
  all_goals simp [links, h1, h2, h3, h4, h5]

def rawPath (l : Link) (mid : Int) : List Point :=
  if l.horizontal then [l.a, ⟨mid, l.a.y⟩, ⟨mid, l.b.y⟩, l.b]
    else [l.a, ⟨l.a.x, mid⟩, ⟨l.b.x, mid⟩, l.b]

theorem rawPath_orthogonal (l : Link) (mid : Int) :
    Polyline.isOrthogonal (rawPath l mid) = true := by
  cases l with
  | mk horizontal a b =>
    cases horizontal <;> simp [rawPath, Polyline.isOrthogonal]

theorem rawPath_head (l : Link) (mid : Int) :
    (rawPath l mid).head? = some l.a := by
  cases h : l.horizontal <;> simp [rawPath, h]

theorem rawPath_last (l : Link) (mid : Int) :
    (rawPath l mid).getLast? = some l.b := by
  cases h : l.horizontal <;> simp [rawPath, h]

def dedupeFrom (p : Point) : List Point → List Point
  | [] => [p]
  | q :: rest => if p == q then dedupeFrom p rest else p :: dedupeFrom q rest

theorem dedupeFrom_head (p : Point) (rest : List Point) :
    (dedupeFrom p rest).head? = some p := by
  induction rest generalizing p with
  | nil => rfl
  | cons q rest ih =>
    by_cases h : p = q
    · subst q
      simpa only [dedupeFrom, beq_self_eq_true, ite_true] using ih p
    · have hb : (p == q) = false := by simp [h]
      simp only [dedupeFrom, hb, Bool.false_eq_true, ite_false, List.head?_cons]

theorem dedupeFrom_last (p : Point) (rest : List Point) :
    (dedupeFrom p rest).getLast? = (p :: rest).getLast? := by
  induction rest generalizing p with
  | nil => rfl
  | cons q rest ih =>
    by_cases h : p = q
    · subst q
      simpa only [dedupeFrom, beq_self_eq_true, ite_true, List.getLast?_cons_cons] using ih p
    · have hb : (p == q) = false := by simp [h]
      have hn : dedupeFrom q rest ≠ [] := by
        intro he
        have hf := dedupeFrom_head q rest
        simp only [he, List.head?_nil, reduceCtorEq] at hf
      simp only [dedupeFrom, hb, Bool.false_eq_true, ite_false,
        List.getLast?_cons_of_ne_nil hn, ih, List.getLast?_cons_cons]

theorem dedupeFrom_orthogonal (p : Point) (rest : List Point)
    (h : Polyline.isOrthogonal (p :: rest) = true) :
    Polyline.isOrthogonal (dedupeFrom p rest) = true := by
  induction rest generalizing p with
  | nil => rfl
  | cons q rest ih =>
    simp only [Polyline.isOrthogonal_cons, Bool.and_eq_true] at h
    by_cases heq : p = q
    · subst q
      simpa only [dedupeFrom, beq_self_eq_true, ite_true] using ih p h.2
    · have hb : (p == q) = false := by simp [heq]
      have hf := dedupeFrom_head q rest
      have ht := ih q h.2
      cases hd : dedupeFrom q rest with
      | nil => simp only [hd, List.head?_nil, reduceCtorEq] at hf
      | cons r rs =>
        have hr : r = q := by simpa only [hd, List.head?_cons, Option.some.injEq] using hf
        subst r
        rw [hd] at ht
        simp only [dedupeFrom, hb, Bool.false_eq_true, ite_false, hd,
          Polyline.isOrthogonal_cons, Bool.and_eq_true]
        exact ⟨h.1, ht⟩

def path (l : Link) (mid : Int) : List Point :=
  match rawPath l mid with
  | [] => []
  | p :: rest => dedupeFrom p rest

theorem path_orthogonal (l : Link) (mid : Int) :
    Polyline.isOrthogonal (path l mid) = true := by
  have hraw := rawPath_orthogonal l mid
  cases l with
  | mk horizontal a b =>
    cases horizontal <;> apply dedupeFrom_orthogonal <;> exact hraw

theorem path_head (l : Link) (mid : Int) :
    (path l mid).head? = some l.a := by
  cases h : l.horizontal <;>
    simp only [path, rawPath, h, Bool.false_eq_true, ite_false,
      ite_true, dedupeFrom_head]

theorem path_last (l : Link) (mid : Int) :
    (path l mid).getLast? = some l.b := by
  cases h : l.horizontal <;>
    simp only [path, rawPath, h, Bool.false_eq_true, ite_false,
      ite_true, dedupeFrom_last, List.getLast?_cons_cons, List.getLast?_singleton]

def extent (items : List Rect) (initial : Int) (side : Rect → Int) : Int :=
  items.foldl (fun current r => max current (side r)) initial

theorem extent_ge_initial (items : List Rect) (initial : Int) (side : Rect → Int) :
    initial ≤ extent items initial side := by
  induction items generalizing initial with
  | nil => exact Int.le_refl _
  | cons r rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih (max initial (side r)))

theorem extent_ge_member (items : List Rect) (initial : Int) (side : Rect → Int)
    (r : Rect) (h : r ∈ items) : side r ≤ extent items initial side := by
  induction items generalizing initial with
  | nil => simp at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with h | h
    · subst r
      exact Int.le_trans (Int.le_max_right _ _)
        (extent_ge_initial rest (max initial (side first)) side)
    · exact ih (max initial (side first)) h

def pointExtent (points : List Point) (initial : Int) (axis : Point → Int) : Int :=
  points.foldl (fun current p => max current (axis p)) initial

theorem pointExtent_ge_initial (points : List Point) (initial : Int) (axis : Point → Int) :
    initial ≤ pointExtent points initial axis := by
  induction points generalizing initial with
  | nil => exact Int.le_refl _
  | cons first rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih (max initial (axis first)))

def routeExtent (routes : List Route) (initial : Int) (axis : Point → Int) : Int :=
  routes.foldl (fun current route => pointExtent route.points current axis) initial

theorem routeExtent_ge_initial (routes : List Route) (initial : Int) (axis : Point → Int) :
    initial ≤ routeExtent routes initial axis := by
  induction routes generalizing initial with
  | nil => exact Int.le_refl _
  | cons first rest ih =>
    exact Int.le_trans (pointExtent_ge_initial first.points initial axis)
      (ih (pointExtent first.points initial axis))

theorem extent_contains (items : List Rect) (width height : Int) (r : Rect)
    (h : r ∈ items) (hx : 0 ≤ r.x) (hy : 0 ≤ r.y) :
    Rect.Contained ⟨0, 0, extent items width right, extent items height bottom⟩ r := by
  exact ⟨hx, by simpa only [right, Int.zero_add] using extent_ge_member items width right r h,
    hy, by simpa only [bottom, Int.zero_add] using extent_ge_member items height bottom r h⟩

theorem routeExtent_contains (items : List Rect) (routes : List Route)
    (width height : Int) (r : Rect) (hr : r ∈ items)
    (hx : 0 ≤ r.x) (hy : 0 ≤ r.y) :
    Rect.Contained
      ⟨0, 0, routeExtent routes (extent items width right) Point.x,
        routeExtent routes (extent items height bottom) Point.y⟩ r := by
  have hc := extent_contains items width height r hr hx hy
  have hw := routeExtent_ge_initial routes (extent items width right) Point.x
  have hh := routeExtent_ge_initial routes (extent items height bottom) Point.y
  unfold Rect.Contained at *
  simp only [Int.zero_add] at *
  omega

theorem hardConstraints_of_nonexclusive_nodes (d : LayoutDump)
    (hnodes : ∀ b ∈ d.boxes, b.role = "node" ∧ b.exclusive = false)
    (hcanvas : Validator.C1 d) (hparent : Validator.C3 d)
    (horthogonal : Validator.C4 d) (hports : Validator.C5 d) :
    HardConstraints d := by
  refine ⟨hcanvas, ?_, hparent, horthogonal, hports, ?_, ?_, ?_, ?_⟩
  · intro b hb _c _hc _ hexclusive
    simp [(hnodes b hb).2] at hexclusive
  · intro _r _hr b hb hexclusive
    simp [(hnodes b hb).2] at hexclusive
  · intro _l _hl b hb hexclusive
    simp [(hnodes b hb).2] at hexclusive
  · intro g hg hgroup
    simp [(hnodes g hg).1] at hgroup
  · intro g hg hgroup
    simp [(hnodes g hg).1] at hgroup

theorem hardConstraints_of_nonexclusive (d : LayoutDump)
    (hnonexclusive : ∀ b ∈ d.boxes, b.exclusive = false)
    (hcanvas : Validator.C1 d) (hparent : Validator.C3 d)
    (horthogonal : Validator.C4 d) (hports : Validator.C5 d)
    (hgroups : Validator.C8 d) : HardConstraints d := by
  refine ⟨hcanvas, ?_, hparent, horthogonal, hports, ?_, ?_, hgroups⟩
  · intro b hb _c _hc _ hexclusive
    simp [hnonexclusive b hb] at hexclusive
  · intro _r _hr b hb hexclusive
    simp [hnonexclusive b hb] at hexclusive
  · intro _l _hl b hb hexclusive
    simp [hnonexclusive b hb] at hexclusive

def dumpBoxes (m : Model) (domains : List Domain) (canvas : Size) : List Box :=
  m.boxes.map fun b => Box.mk b.id b.role.id
    (if b.id == "frame" then ⟨0, 0, canvas.w, canvas.h⟩ else
      (domains.find? (fun d => d.id == b.id)).map (·.rect) |>.getD ⟨0, 0, 0, 0⟩)
    b.parent b.exclusive

theorem dumpBoxes_metadata (m : Model) (domains : List Domain) (canvas : Size)
    (b : Box) (hb : b ∈ dumpBoxes m domains canvas) :
    ∃ source ∈ m.boxes, b.id = source.id ∧ b.role = source.role.id ∧
      b.parent = source.parent ∧ b.exclusive = source.exclusive := by
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
  exact ⟨source, hsource, rfl, rfl, rfl, rfl⟩

theorem dumpBoxes_canvas (m : Model) (domains : List Domain) (canvas : Size)
    (hsize : 0 ≤ canvas.w ∧ 0 ≤ canvas.h)
    (hdomains : ∀ d ∈ domains, (Rect.mk 0 0 canvas.w canvas.h).Contained d.rect) :
    ∀ b ∈ dumpBoxes m domains canvas,
      (Rect.mk 0 0 canvas.w canvas.h).Contained b.rect := by
  intro b hb
  obtain ⟨source, _hs, rfl⟩ := List.mem_map.mp hb
  by_cases hf : source.id = "frame"
  · simp only [hf, beq_self_eq_true, ite_true]
    exact Rect.Contained.refl _
  · have hfb : (source.id == "frame") = false := by simp [hf]
    simp only [hfb, Bool.false_eq_true, ite_false]
    cases hd : domains.find? (fun d => d.id == source.id) with
    | none =>
      simp only [Option.map_none, Option.getD_none, Rect.Contained]
      omega
    | some domain =>
      simp only [Option.map_some, Option.getD_some]
      exact hdomains domain (List.mem_of_find?_eq_some hd)

theorem dumpBoxes_frame (m : Model) (domains : List Domain) (canvas : Size)
    (source : ModelBox) (hs : source ∈ m.boxes) (hid : source.id = "frame") :
    ∃ frame ∈ dumpBoxes m domains canvas,
      frame.id = "frame" ∧ frame.rect = ⟨0, 0, canvas.w, canvas.h⟩ := by
  refine ⟨_, List.mem_map.mpr ⟨source, hs, rfl⟩, ?_, ?_⟩
  · exact hid
  · simp only [hid, beq_self_eq_true, ite_true]

theorem dumpBoxes_extent_canvas (m : Model) (domains : List Domain)
    (labels : List Placed) (routes : List Route) (width height : Int)
    (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hdomains : ∀ d ∈ domains, 0 ≤ d.rect.x ∧ 0 ≤ d.rect.y) :
    let items := labels.map (·.rect) ++ domains.map (·.rect)
    let canvas : Size :=
      ⟨routeExtent routes (extent items width right) Point.x,
        routeExtent routes (extent items height bottom) Point.y⟩
    ∀ b ∈ dumpBoxes m domains canvas,
      (Rect.mk 0 0 canvas.w canvas.h).Contained b.rect := by
  dsimp only
  apply dumpBoxes_canvas
  · constructor
    · exact Int.le_trans hw (Int.le_trans (extent_ge_initial _ _ _)
        (routeExtent_ge_initial _ _ _))
    · exact Int.le_trans hh (Int.le_trans (extent_ge_initial _ _ _)
        (routeExtent_ge_initial _ _ _))
  · intro d hd
    exact routeExtent_contains _ routes width height d.rect
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨d, hd, rfl⟩)))
      (hdomains d hd).1 (hdomains d hd).2

theorem dumpBoxes_nonexclusive_nodes (m : Model) (domains : List Domain) (canvas : Size)
    (hmodel : ∀ b ∈ m.boxes, b.role = .node ∧ b.exclusive = false) :
    ∀ b ∈ dumpBoxes m domains canvas, b.role = "node" ∧ b.exclusive = false := by
  intro b hb
  obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hb
  have hs := hmodel source hsource
  exact ⟨by simp only [hs.1, BoxRole.id], hs.2⟩

def segments (ps : List Point) : List (Point × Point) := ps.zip (ps.drop 1)

def crosses (ps : List Point) (r : Rect) : Bool :=
  (segments ps).any fun (a,b) => min a.x b.x ≤ right r && max a.x b.x ≥ r.x &&
    min a.y b.y ≤ bottom r && max a.y b.y ≥ r.y

def lanes (l : Link) (others : List Rect) (gap : Int) : List Int :=
  let a := if l.horizontal then l.a.x else l.a.y
  let b := if l.horizontal then l.b.x else l.b.y
  let mid := Int.fdiv (a+b) 2
  let candidates := others.flatMap fun r => if l.horizontal then [r.x-gap, right r+gap] else [r.y-gap, bottom r+gap]
  let candidates := (candidates.filter fun n => min a b ≤ n && n ≤ max a b && n != mid).eraseDups
  mid :: candidates.mergeSort (fun x y => (x-mid).natAbs < (y-mid).natAbs ||
    ((x-mid).natAbs == (y-mid).natAbs && x ≤ y))

theorem selected_path_property (candidates : List (List Point))
    (accept : List Point → Bool) (P : List Point → Prop)
    (hempty : P []) (hall : ∀ ps ∈ candidates, P ps) :
    P ((candidates.find? accept).getD (candidates.headD [])) := by
  cases hf : candidates.find? accept with
  | none =>
    cases candidates with
    | nil => exact hempty
    | cons first rest =>
      simpa only [hf, Option.getD_none, List.headD_cons] using
        hall first (List.mem_cons_self)
  | some ps =>
    simpa only [hf, Option.getD_some] using hall ps (List.mem_of_find?_eq_some hf)

theorem selected_nonempty_path_property (candidates : List (List Point))
    (accept : List Point → Bool) (P : List Point → Prop)
    (hne : candidates ≠ []) (hall : ∀ ps ∈ candidates, P ps) :
    P ((candidates.find? accept).getD (candidates.headD [])) := by
  cases hf : candidates.find? accept with
  | none =>
    cases candidates with
    | nil => exact False.elim (hne rfl)
    | cons first rest =>
      simpa only [hf, Option.getD_none, List.headD_cons] using
        hall first (List.mem_cons_self)
  | some ps =>
    simpa only [hf, Option.getD_some] using hall ps (List.mem_of_find?_eq_some hf)

theorem route_candidates_nonempty (c : Consts) (others : List Rect) (a b : Domain) :
    ((links a b).flatMap fun l => (lanes l others c.pad).map (path l)) ≠ [] := by
  cases hl : links a b with
  | nil => exact False.elim (links_nonempty a b hl)
  | cons first rest => simp [List.flatMap_cons, lanes]

def elbow (c : Consts) (domains : List Domain) (a b : Domain) : List Point :=
  let others := (domains.filter fun d => d.id != a.id && d.id != b.id).map (·.rect)
  let candidates := (links a b).flatMap fun l => (lanes l others c.pad).map (path l)
  (candidates.find? fun ps => !(others.any (crosses ps))).getD (candidates.headD [])

theorem elbow_orthogonal (c : Consts) (domains : List Domain) (a b : Domain) :
    Polyline.isOrthogonal (elbow c domains a b) = true := by
  let others := (domains.filter fun d => d.id != a.id && d.id != b.id).map (·.rect)
  let candidates := (links a b).flatMap fun l => (lanes l others c.pad).map (path l)
  change Polyline.isOrthogonal
    ((candidates.find? fun ps => !(others.any (crosses ps))).getD (candidates.headD [])) = true
  apply selected_path_property candidates (fun ps => !(others.any (crosses ps)))
    (fun ps => Polyline.isOrthogonal ps = true)
  · rfl
  · intro ps hps
    obtain ⟨l, _hl, hps⟩ := List.mem_flatMap.mp hps
    obtain ⟨mid, _hm, rfl⟩ := List.mem_map.mp hps
    exact path_orthogonal l mid

theorem elbow_ports (c : Consts) (domains : List Domain) (a b : Domain)
    (ha : a.PortBounds) (hb : b.PortBounds) :
    ∃ p q, (elbow c domains a b).head? = some p ∧
      (elbow c domains a b).getLast? = some q ∧
      Validator.onBoundary p a.rect ∧ Validator.onBoundary q b.rect := by
  let others := (domains.filter fun d => d.id != a.id && d.id != b.id).map (·.rect)
  let candidates := (links a b).flatMap fun l => (lanes l others c.pad).map (path l)
  change (fun ps => ∃ p q, ps.head? = some p ∧ ps.getLast? = some q ∧
    Validator.onBoundary p a.rect ∧ Validator.onBoundary q b.rect)
    ((candidates.find? fun ps => !(others.any (crosses ps))).getD (candidates.headD []))
  apply selected_nonempty_path_property candidates (fun ps => !(others.any (crosses ps)))
    (fun ps => ∃ p q, ps.head? = some p ∧ ps.getLast? = some q ∧
      Validator.onBoundary p a.rect ∧ Validator.onBoundary q b.rect)
  · exact route_candidates_nonempty c _ a b
  · intro ps hps
    obtain ⟨l, hl, hps⟩ := List.mem_flatMap.mp hps
    obtain ⟨mid, _hm, rfl⟩ := List.mem_map.mp hps
    exact ⟨l.a, l.b, path_head l mid, path_last l mid, links_ports a b ha hb l hl⟩

theorem successful_routes_orthogonal (c : Consts) (domains : List Domain)
    (sources : List ModelRoute) (routes : List Route)
    (h : (sources.mapM (fun r =>
      match domains.find? (fun d => d.id == r.fromId),
          domains.find? (fun d => d.id == r.toId) with
      | some a, some b =>
        pure (Route.mk r.id r.fromId r.toId r.orthogonal (elbow c domains a b))
      | _, _ => throw .domain) : Except LayoutError (List Route)) = .ok routes) :
    ∀ r ∈ routes, Polyline.isOrthogonal r.points = true := by
  induction sources generalizing routes with
  | nil =>
    have he : routes = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    simp [he]
  | cons source rest ih =>
    rw [List.mapM_cons] at h
    cases ha : domains.find? (fun d => d.id == source.fromId) with
    | none => simp [ha, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some a =>
      cases hb : domains.find? (fun d => d.id == source.toId) with
      | none => simp [ha, hb, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      | some b =>
        cases ht : (rest.mapM (fun r =>
          match domains.find? (fun d => d.id == r.fromId),
              domains.find? (fun d => d.id == r.toId) with
          | some x, some y =>
            pure (Route.mk r.id r.fromId r.toId r.orthogonal (elbow c domains x y))
          | _, _ => throw .domain) : Except LayoutError (List Route)) with
        | error e =>
          have ht' := ht
          simp only [Pure.pure, Except.pure] at ht'
          simp [ha, hb, ht', Bind.bind, Except.bind, Pure.pure, Except.pure] at h
        | ok tail =>
          have ht' := ht
          simp only [Pure.pure, Except.pure] at ht'
          have he : Route.mk source.id source.fromId source.toId source.orthogonal
              (elbow c domains a b) :: tail = routes := by
            simpa [ha, hb, ht', Bind.bind, Except.bind, Pure.pure, Except.pure] using h
          subst routes
          intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact elbow_orthogonal c domains a b
          · exact ih tail ht r hr

def overlaps (a b : Rect) : Bool := a.x < right b && b.x < right a && a.y < bottom b && b.y < bottom a

def hitsLabel (ps : List Point) (r : Rect) (reach : Int) : Bool :=
  (segments ps).any fun (a,b) => min a.x b.x < right r && max a.x b.x + reach > r.x &&
    min a.y b.y < bottom r && max a.y b.y + reach > r.y

def labelSides (c : Consts) (box : XY.TextBox) (ps : List Point) : List (Rect × Align) :=
  let all := ps.zipIdx.map fun (p,i) => (ps[i-1]?.getD p, p)
  let length := fun (pair : Point × Point) =>
    (pair.2.x-pair.1.x).natAbs + (pair.2.y-pair.1.y).natAbs
  (all.mergeSort (fun a b => length a ≥ length b)).flatMap fun (a,b) =>
    let mx := Int.fdiv (a.x+b.x) 2
    let my := Int.fdiv (a.y+b.y) 2
    let sides := if a.y != b.y then
      [(Rect.mk (mx+c.labelGap) (my-Int.fdiv box.h 2) box.w box.h, Align.start),
       (Rect.mk (mx-c.labelGap-box.w) (my-Int.fdiv box.h 2) box.w box.h, Align.start)]
    else [(Rect.mk (mx-Int.fdiv box.w 2) (my+c.labelGap) box.w box.h, Align.middle),
          (Rect.mk (mx-Int.fdiv box.w 2) (my-c.labelGap-box.h) box.w box.h, Align.middle)]
    sides.map fun (r,a) => ({ r with x := max r.x 0, y := max r.y 0 }, a)

def textItem (p : Placed) : Primitive := .text {
  rect := p.rect, role := XY.textRoleOf p.role, size := p.role.sizePx, align := p.align,
  style := "text", lines := XY.runsOf p.box.lines }

def decor (cell : Bool) (c : Consts) : List Primitive :=
  let cx := Int.fdiv c.width 2
  let cy := Int.fdiv c.height 2
  let rx := Int.fdiv (c.width*c.confusion) 1000
  let ry := Int.fdiv (c.height*c.confusion) 1000
  (["complex", "complicated", "clear", "chaotic"].map fun n => .rect (quadrant c n) {style := "band"}) ++
    [.path (foldCommands cell c) {style := "rule"}] ++
    ([(0, cx-rx), (cx+rx, c.width-c.edge)].filterMap fun (a,b) =>
      if a < b then some (.polyline [⟨a,cy⟩,⟨b,cy⟩] 0 {style := "rule"}) else none) ++
    [.path (cliffCommands c) {style := "rule"}, .ellipse cx cy rx ry {style := "group"}]

def axis (a b : Point) : MarkerAxis :=
  if (b.x-a.x).natAbs ≥ (b.y-a.y).natAbs then
    if b.x < a.x then .negativeX else .positiveX
  else if b.y < a.y then .negativeY else .positiveY

def frameConsistent (m : Model) : Bool :=
  m.boxes.all fun b => b.id != "frame" || !b.exclusive

theorem frameConsistent_frame_nonexclusive (m : Model) (h : frameConsistent m = true)
    (b : ModelBox) (hb : b ∈ m.boxes) (hid : b.id = "frame") :
    b.exclusive = false := by
  have hbox := List.all_eq_true.mp h b hb
  simpa [hid] using hbox

def relationsConsistent (m : Model) : Bool :=
  m.boxes.all fun b =>
    !b.exclusive && (if b.id == "frame" then b.parent == "" else b.parent == "frame")

theorem relationsConsistent_box (m : Model) (h : relationsConsistent m = true)
    (b : ModelBox) (hb : b ∈ m.boxes) :
    b.exclusive = false ∧
      (if b.id = "frame" then b.parent = "" else b.parent = "frame") := by
  have hbox := List.all_eq_true.mp h b hb
  by_cases hid : b.id = "frame" <;> simpa [hid] using hbox


def layout (m : Model) : Except LayoutError Scene := do
  if !frameConsistent m then throw .domain
  if !relationsConsistent m then throw .domain
  let c := constants m
  let titleSource := m.labels.find? (fun l => l.id == "title")
  let title ← match titleSource with
    | none => pure ([] : List Placed)
    | some l => do
      let b ← XY.measureText (m.profile == .cell) l.text .title 16
      pure [⟨l,b,⟨max 0 (Int.fdiv c.width 2 - Int.fdiv b.w 2), c.pad,b.w,b.h⟩,.title,.middle⟩]
  let domains ← (m.boxes.filter (fun b => b.id != "frame")).mapM fun b =>
    placeDomain c m ((title.head?).map (·.box.h) |>.getD 0) b.id
  let routes ← m.routes.mapM fun r => do
    match domains.find? (fun d => d.id == r.fromId), domains.find? (fun d => d.id == r.toId) with
    | some a, some b => pure (Route.mk r.id r.fromId r.toId r.orthogonal (elbow c domains a b))
    | _, _ => throw .domain
  let initial := title ++ domains.flatMap (·.labels)
  let labels ← routes.foldlM (fun labels r => do
    match m.labels.find? (fun l => l.owner == r.id) with
    | none => pure labels
    | some l => do
      let box ← XY.measureText (m.profile == .cell) l.text .body 14
      let candidates := labelSides c box r.points
      let blocked := fun rect => domains.any (fun d => overlaps rect d.rect) ||
        routes.any (fun route => hitsLabel route.points rect (if m.profile == .cell then 1 else 0)) ||
        labels.any (fun p => overlaps rect p.rect)
      match (candidates.find? (fun (rect,_) => !blocked rect)).orElse (fun _ => candidates.head?) with
      | none => throw .domain
      | some (rect,align) => pure (labels ++ [⟨l,box,rect,.body,align⟩])) initial
  let extentRects := labels.map (·.rect) ++ domains.map (·.rect)
  let w := extent extentRects c.width right
  let h := extent extentRects c.height bottom
  let w := routeExtent routes w Point.x
  let h := routeExtent routes h Point.y
  let boxes := dumpBoxes m domains ⟨w, h⟩
  let dumpLabels ← m.labels.mapM fun l =>
    match labels.find? (fun p => p.source.id == l.id) with
    | none => throw .domain
    | some p => pure ({
        id := l.id
        owner := l.owner
        text := l.text
        rect := p.rect
        lines := p.box.lines.map (fun line => String.ofList line.text) } : SceneLabel)
  let edgeGroups : List Group := routes.map fun r =>
    let markers := match r.points.reverse with
      | last :: prev :: _ => [Primitive.markerRef "point" last (axis prev last)]
      | _ => []
    {
      role := .edge
      owner := r.id
      items := [.polyline r.points c.corner {style := "edge"}] ++ markers ++
        (labels.filter (fun p => p.source.owner == r.id)).map textItem }
  let nodeGroups : List Group := domains.map fun d =>
    {
      role := .node
      owner := d.id
      items := (if m.profile == .cell then [] else
        d.badges.map fun r => .roundRect r c.corner {style := "node"}) ++
        d.labels.map textItem }
  if !(InI32 w ∧ InI32 h) || boxes.any (fun b => !b.rect.Valid) ||
      dumpLabels.any (fun l => !l.rect.Valid) || routes.any (fun r =>
        r.points.any (fun p => !(InI32 p.x ∧ InI32 p.y))) then throw .overflow
  pure {
    kind := "cynefin"
    profile := m.profile
    options := {m.options with direction := .TB}
    canvas := ⟨w,h⟩
    boxes := boxes
    routes := routes
    labels := dumpLabels
    items := [{role := .decor, owner := "", items := decor (m.profile == .cell) c}] ++
      edgeGroups ++ [{role := .node, owner := "frame", items := title.map textItem}] ++ nodeGroups }

theorem layout_frame_consistent (m : Model) (scene : Scene)
    (h : layout m = .ok scene) : frameConsistent m = true := by
  by_cases hc : frameConsistent m = true
  · exact hc
  · simp [layout, hc, Bind.bind, Except.bind] at h

theorem layout_boxes_nonexclusive (m : Model) (scene : Scene)
    (h : layout m = .ok scene) :
    ∀ b ∈ m.boxes, b.exclusive = false := by
  have hc : relationsConsistent m = true := by
    by_cases hr : relationsConsistent m = true
    · exact hr
    · by_cases hf : frameConsistent m = true <;>
        simp [layout, hr, hf, Bind.bind, Except.bind] at h
  intro b hb
  exact (relationsConsistent_box m hc b hb).1

theorem layout_relations_consistent (m : Model) (scene : Scene)
    (h : layout m = .ok scene) : relationsConsistent m = true := by
  by_cases hc : relationsConsistent m = true
  · exact hc
  · by_cases hf : frameConsistent m = true <;>
      simp [layout, hc, hf, Bind.bind, Except.bind] at h

theorem layout_dumpBoxes_nonexclusive (m : Model) (scene : Scene)
    (h : layout m = .ok scene) (domains : List Domain) (canvas : Size) :
    ∀ b ∈ dumpBoxes m domains canvas, b.exclusive = false := by
  intro b hb
  obtain ⟨source, hs, _hid, _hrole, _hparent, hexclusive⟩ :=
    dumpBoxes_metadata m domains canvas b hb
  rw [hexclusive]
  exact layout_boxes_nonexclusive m scene h source hs

theorem layout_dumpBoxes_parents (m : Model) (scene : Scene)
    (h : layout m = .ok scene) (domains : List Domain) (canvas : Size) :
    ∀ b ∈ dumpBoxes m domains canvas,
      if b.id = "frame" then b.parent = "" else b.parent = "frame" := by
  intro b hb
  obtain ⟨source, hs, hid, _hrole, hparent, _hexclusive⟩ :=
    dumpBoxes_metadata m domains canvas b hb
  rw [hid, hparent]
  exact (relationsConsistent_box m (layout_relations_consistent m scene h) source hs).2

theorem layout_exclusive_clearance (m : Model) (scene : Scene)
    (h : layout m = .ok scene) (domains : List Domain) (canvas : Size)
    (routes : List Route) (labels : List Label) :
    let d : LayoutDump := ⟨canvas, dumpBoxes m domains canvas, routes, labels⟩
    Validator.C2 d ∧ Validator.C6 d ∧ Validator.C7 d := by
  have hn := layout_dumpBoxes_nonexclusive m scene h domains canvas
  constructor
  · intro b hb _c _hc _ hexclusive
    simp [hn b hb] at hexclusive
  constructor
  · intro _r _hr b hb hexclusive
    simp [hn b hb] at hexclusive
  · intro _l _hl b hb hexclusive
    simp [hn b hb] at hexclusive

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem mapM_success_property {α β : Type}
    (f : α → Except LayoutError β) (P : β → Prop)
    (hf : ∀ a b, f a = .ok b → P b) :
    ∀ (sources : List α) (results : List β),
      sources.mapM f = .ok results → ∀ b ∈ results, P b := by
  intro sources
  induction sources with
  | nil =>
    intro results h b hb
    have he : results = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    simp [he] at hb
  | cons source rest ih =>
    intro results h b hb
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨tail, htail, h⟩ := bind_ok h
    have he : first :: tail = results := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst results
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      exact hf source first hfirst
    · exact ih tail htail b hb

theorem measureDomain_nonnegative (m : Model) (id : String)
    (measured : List (ModelLabel × XY.TextBox × Measure.Role))
    (h : measureDomain m id = .ok measured) :
    ∀ t ∈ measured, 0 ≤ t.2.1.w ∧ 0 ≤ t.2.1.h := by
  apply mapM_success_property _
    (fun t : ModelLabel × XY.TextBox × Measure.Role => 0 ≤ t.2.1.w ∧ 0 ≤ t.2.1.h)
    ?_ _ measured h
  intro l t ht
  let role := if l.id == id ++ ".label" then Measure.Role.label else .body
  change (do
    let box ← XY.measureText (m.profile == Profile.cell) l.text role role.sizePx
    pure (l, box, role)) = .ok t at ht
  obtain ⟨box, hbox, ht⟩ := bind_ok ht
  have he : (l, box, role) = t := by
    simpa only [Pure.pure, Except.pure, Except.ok.injEq] using ht
  subst t
  exact measured_text_nonnegative _ _ _ _ hbox


private theorem checked_domain_ok {α : Type} (condition : Bool) (value result : α)
    (h : (do
      if condition then throw .domain
      pure value : Except LayoutError α) = .ok result) : value = result := by
  by_cases hc : condition = true
  · simp [hc, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simpa [hc, Bind.bind, Except.bind, Pure.pure, Except.pure] using h

theorem placeDomain_id (c : Consts) (m : Model) (titleHeight : Int) (id : String)
    (domain : Domain) (h : placeDomain c m titleHeight id = .ok domain) :
    domain.id = id := by
  unfold placeDomain at h
  obtain ⟨_measured, _hm, h⟩ := bind_ok h
  have he := checked_domain_ok _ _ domain h
  cases he
  rfl

private theorem mapM_success_origin {α β : Type}
    (f : α → Except LayoutError β) :
    ∀ (sources : List α) (results : List β),
      sources.mapM f = .ok results →
      ∀ b ∈ results, ∃ a ∈ sources, f a = .ok b := by
  intro sources
  induction sources with
  | nil =>
    intro results h b hb
    have he : results = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    simp [he] at hb
  | cons source rest ih =>
    intro results h b hb
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨tail, htail, h⟩ := bind_ok h
    have he : first :: tail = results := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst results
    rcases List.mem_cons.mp hb with hb | hb
    · subst b
      exact ⟨source, List.mem_cons_self, hfirst⟩
    · obtain ⟨a, ha, hfa⟩ := ih tail htail b hb
      exact ⟨a, List.mem_cons_of_mem source ha, hfa⟩


private theorem foldl_property {α β : Type} (f : β → α → β) (P : β → Prop)
    (items : List α) (hf : ∀ a ∈ items, ∀ s, P s → P (f s a))
    (initial : β) (hi : P initial) : P (items.foldl f initial) := by
  induction items generalizing initial with
  | nil => exact hi
  | cons a rest ih =>
    exact ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
      (f initial a) (hf a List.mem_cons_self initial hi)

private theorem foldMax_initial {α : Type} (items : List α) (f : α → Int)
    (initial : Int) :
    initial ≤ items.foldl (fun current item => max current (f item)) initial := by
  induction items generalizing initial with
  | nil => exact Int.le_refl _
  | cons a rest ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih (max initial (f a)))

private theorem foldMax_member {α : Type} (items : List α) (f : α → Int)
    (initial : Int) (a : α) (ha : a ∈ items) :
    f a ≤ items.foldl (fun current item => max current (f item)) initial := by
  induction items generalizing initial with
  | nil => simp at ha
  | cons first rest ih =>
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      exact Int.le_trans (Int.le_max_right _ _)
        (foldMax_initial rest f (max initial (f first)))
    · exact ih (max initial (f first)) ha

theorem domainBounds_origins (title : Rect) (badges : List Rect) (padding : Int)
    (ht : padding ≤ title.x ∧ padding ≤ title.y)
    (hb : ∀ b ∈ badges, padding ≤ b.x ∧ padding ≤ b.y) :
    0 ≤ (domainBounds title badges padding).x ∧
      0 ≤ (domainBounds title badges padding).y := by
  have hbounds : padding ≤ (boundsOf title badges).x ∧
      padding ≤ (boundsOf title badges).y := by
    apply foldl_property Rect.unionRaw
      (fun r => padding ≤ r.x ∧ padding ≤ r.y) badges ?_ title ht
    intro b hmem r hr
    have hbadge := hb b hmem
    simp only [Rect.unionRaw]
    omega
  unfold domainBounds Rect.inflateRaw
  simp only
  omega
private theorem find?_exists_of_mem {α : Type} (predicate : α → Bool)
    (items : List α) (a : α) (ha : a ∈ items) (hp : predicate a = true) :
    ∃ b, items.find? predicate = some b := by
  cases hf : items.find? predicate with
  | none =>
    have hn := List.find?_eq_none.mp hf a ha
    exact False.elim (hn hp)
  | some b => exact ⟨b, rfl⟩

theorem successful_domains_same_id (m : Model) (title : List Placed)
    (domains : List Domain)
    (h : ((m.boxes.filter (fun b => b.id != "frame")).mapM (fun b =>
      placeDomain (constants m) m ((title.head?).map (·.box.h) |>.getD 0) b.id) :
        Except LayoutError (List Domain)) = .ok domains)
    (a b : Domain) (ha : a ∈ domains) (hb : b ∈ domains) (hid : a.id = b.id) :
    a = b := by
  obtain ⟨sa, _hsa, hca⟩ := mapM_success_origin _ _ domains h a ha
  obtain ⟨sb, _hsb, hcb⟩ := mapM_success_origin _ _ domains h b hb
  have hida := placeDomain_id _ _ _ _ _ hca
  have hidb := placeDomain_id _ _ _ _ _ hcb
  have hsource : sa.id = sb.id := hida.symm.trans (hid.trans hidb)
  rw [hsource] at hca
  exact Except.ok.inj (hca.symm.trans hcb)

theorem successful_domain_box_lookup (m : Model) (title : List Placed)
    (domains : List Domain) (canvas : Size)
    (h : ((m.boxes.filter (fun b => b.id != "frame")).mapM (fun b =>
      placeDomain (constants m) m ((title.head?).map (·.box.h) |>.getD 0) b.id) :
        Except LayoutError (List Domain)) = .ok domains)
    (a : Domain) (ha : a ∈ domains) :
    ∃ box, (dumpBoxes m domains canvas).find? (fun b => b.id == a.id) = some box ∧
      box.rect = a.rect := by
  obtain ⟨source, hsource, hcall⟩ := mapM_success_origin _ _ domains h a ha
  have hid := placeDomain_id _ _ _ _ _ hcall
  have hs := List.mem_filter.mp hsource
  have hnotframe : a.id ≠ "frame" := by
    simpa only [← hid, bne_iff_ne] using hs.2
  obtain ⟨chosen, hchosen⟩ := find?_exists_of_mem (fun d : Domain => d.id == a.id)
    domains a ha (by simp)
  have hchosenid : chosen.id = a.id := by
    simpa only [beq_iff_eq] using List.find?_some hchosen
  have hchoseneq := successful_domains_same_id m title domains h chosen a
    (List.mem_of_find?_eq_some hchosen) ha hchosenid
  subst chosen
  let sourceBox : Box := Box.mk source.id source.role.id
    (if source.id == "frame" then ⟨0, 0, canvas.w, canvas.h⟩ else
      (domains.find? (fun d => d.id == source.id)).map (·.rect) |>.getD ⟨0, 0, 0, 0⟩)
    source.parent source.exclusive
  have hboxmem : sourceBox ∈ dumpBoxes m domains canvas :=
    List.mem_map.mpr ⟨source, hs.1, rfl⟩
  obtain ⟨box, hbox⟩ := find?_exists_of_mem (fun b : Box => b.id == a.id)
    (dumpBoxes m domains canvas) sourceBox hboxmem (by
      change (source.id == a.id) = true
      simp only [← hid, beq_self_eq_true])
  refine ⟨box, hbox, ?_⟩
  have hboxid : box.id = a.id := by
    simpa only [beq_iff_eq] using List.find?_some hbox
  obtain ⟨s, _hs, he⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hbox)
  have hsid : s.id = a.id := (congrArg Box.id he).trans hboxid
  rw [← he]
  simp only [hsid, beq_iff_eq, hnotframe, ite_false, hchosen,
    Option.map_some, Option.getD_some]

theorem placeDomain_ports (m : Model) (titleHeight : Int) (id : String)
    (domain : Domain)
    (h : placeDomain (constants m) m titleHeight id = .ok domain) :
    domain.PortBounds := by
  unfold placeDomain at h
  obtain ⟨measured, hm, h⟩ := bind_ok h
  have hmeasured := measureDomain_nonnegative m id measured hm
  have htitle :
      0 ≤ (measured.head?.map (fun t => t.2.1.w) |>.getD 0) ∧
      0 ≤ (measured.head?.map (fun t => t.2.1.h) |>.getD 0) := by
    cases measured with
    | nil => simp
    | cons first rest =>
      simpa only [List.head?_cons, Option.map_some, Option.getD_some] using
        hmeasured first List.mem_cons_self
  have hpad := (constants_spacing_nonnegative m).2.2.2.2.2.1
  have he := checked_domain_ok _ _ domain h
  cases he
  apply portBounds_of_title_containment _
    _ (measured.head?.map (fun t => t.2.1.w) |>.getD 0)
    (measured.head?.map (fun t => t.2.1.h) |>.getD 0)
    htitle.1 htitle.2
  · exact (domainBounds_nonnegative _ _ _ htitle.1 htitle.2 hpad).1
  · exact (domainBounds_nonnegative _ _ _ htitle.1 htitle.2 hpad).2
  · rfl
  · exact domainBounds_contains_title _ _ _ hpad

theorem successful_domain_ports (m : Model) (title : List Placed)
    (domains : List Domain)
    (h : ((m.boxes.filter (fun b => b.id != "frame")).mapM (fun b =>
      placeDomain (constants m) m ((title.head?).map (·.box.h) |>.getD 0) b.id) :
        Except LayoutError (List Domain)) = .ok domains) :
    ∀ d ∈ domains, d.PortBounds := by
  exact mapM_success_property _ Domain.PortBounds
    (fun source d hd => placeDomain_ports m _ source.id d hd) _ domains h

theorem placeDomain_origins (m : Model) (titleHeight : Int) (id : String)
    (domain : Domain) (hh : 0 ≤ (constants m).height)
    (h : placeDomain (constants m) m titleHeight id = .ok domain) :
    0 ≤ domain.rect.x ∧ 0 ≤ domain.rect.y := by
  unfold placeDomain at h
  obtain ⟨measured, hm, h⟩ := bind_ok h
  let c := constants m
  let titleW := measured.head?.map (fun t => t.2.1.w) |>.getD 0
  let titleH := measured.head?.map (fun t => t.2.1.h) |>.getD 0
  let widest := measuredWidth c measured
  let total := (measured.drop 1).zipIdx.foldl (fun height (t, i) =>
    height + (if i == 0 then c.nameGap else c.itemGap) + t.2.1.h + 2*c.itemPadY) titleH
  let q := quadrant c id
  let preferred := if id == "confusion" then Int.fdiv c.width 2 else q.x + Int.fdiv q.w 2
  let top := if id == "confusion" then max c.boxPad (Int.fdiv c.height 2 - Int.fdiv total 2)
    else q.y + (if q.y == 0 && titleHeight > 0 then 2*c.pad + titleHeight else c.pad)
  let cx := max (Int.fdiv widest 2 + c.boxPad)
    (min preferred (c.width - (widest - Int.fdiv widest 2 + c.boxPad)))
  let nameRect : Rect := ⟨cx - Int.fdiv titleW 2, top, titleW, titleH⟩
  let initial : List Placed := match measured.head? with
    | none => []
    | some (l, b, role) => [⟨l, b, nameRect, role, .middle⟩]
  let step := fun (state : Int × List Rect × List Placed)
      (t : ModelLabel × XY.TextBox × Measure.Role) =>
    let badge : Rect := ⟨cx - Int.fdiv (t.2.1.w + 2*c.itemPadX) 2, state.1,
      t.2.1.w + 2*c.itemPadX, t.2.1.h + 2*c.itemPadY⟩
    (state.1 + badge.h + c.itemGap, state.2.1 ++ [badge],
      state.2.2 ++ [⟨t.1, t.2.1,
        ⟨cx - Int.fdiv t.2.1.w 2, state.1 + c.itemPadY, t.2.1.w, t.2.1.h⟩,
        t.2.2, .middle⟩])
  let state := (measured.drop 1).foldl step (top + titleH + c.nameGap, [], initial)
  have hmeasured := measureDomain_nonnegative m id measured hm
  have htitleH : 0 ≤ titleH := by
    cases measured with
    | nil => exact Int.le_refl _
    | cons first rest =>
      exact (hmeasured first List.mem_cons_self).2
  have hspacing := constants_spacing_nonnegative m
  change 0 ≤ c.pad ∧ 0 ≤ c.nameGap ∧ 0 ≤ c.itemPadX ∧ 0 ≤ c.itemPadY ∧
    0 ≤ c.itemGap ∧ 0 ≤ c.boxPad ∧ 0 ≤ c.labelGap at hspacing
  change 0 ≤ c.height at hh
  have hpad : c.boxPad ≤ c.pad := by
    cases hp : m.profile <;>
      simp [c, constants, hp, LayoutConst.Pair.get, LayoutConst.cynefin_box_pad,
        LayoutConst.cynefin_pad]
  have hqy : 0 ≤ q.y := by
    have hdiv := Measure.fdiv_of_nonneg (a := c.height) (b := 2) (by decide)
    have hed : 0 ≤ c.height / 2 := Int.ediv_nonneg hh (by decide)
    dsimp only [q, quadrant]
    split <;> (try split) <;> (try split) <;> simp only <;> omega
  have htop : c.boxPad ≤ top := by
    dsimp only [top]
    split
    · exact Int.le_max_left _ _
    · split
      · rename_i hbranch
        have hpositive : 0 < titleHeight := by
          exact of_decide_eq_true (Bool.and_eq_true_iff.mp hbranch).2
        have hpadzero := hspacing.1
        omega
      · omega
  have hleft (width : Int) (hwidth : width ≤ widest) :
      c.boxPad ≤ cx - Int.fdiv width 2 := by
    have hx := centred_left_nonnegative width widest c.boxPad preferred c.width hwidth
    change 0 ≤ cx - Int.fdiv width 2 - c.boxPad at hx
    omega
  have htitleW : titleW ≤ widest :=
    foldMax_initial (measured.drop 1) (fun t => t.2.1.w + 2*c.itemPadX) titleW
  have hstate : c.boxPad ≤ state.1 ∧
      ∀ badge ∈ state.2.1, c.boxPad ≤ badge.x ∧ c.boxPad ≤ badge.y := by
    apply foldl_property step
      (fun s => c.boxPad ≤ s.1 ∧
        ∀ badge ∈ s.2.1, c.boxPad ≤ badge.x ∧ c.boxPad ≤ badge.y)
      (measured.drop 1) ?_ _ ?_
    · intro t ht s hs
      have hsize := hmeasured t (List.mem_of_mem_drop ht)
      have hwidth : t.2.1.w + 2*c.itemPadX ≤ widest :=
        foldMax_member (measured.drop 1) (fun t => t.2.1.w + 2*c.itemPadX) titleW t ht
      have hx := hleft _ hwidth
      constructor
      · dsimp only [step]
        have hpy := hspacing.2.2.2.1
        have hgap := hspacing.2.2.2.2.1
        omega
      · intro badge hbadge
        change badge ∈ s.2.1 ++ [_] at hbadge
        rcases List.mem_append.mp hbadge with hbadge | hbadge
        · exact hs.2 badge hbadge
        · have he := List.mem_singleton.mp hbadge
          subst badge
          exact ⟨hx, hs.1⟩
    · constructor
      · have hgap := hspacing.2.1
        dsimp only
        omega
      · simp
  have he : (⟨id, cx, top + Int.fdiv titleH 2,
      domainBounds nameRect state.2.1 c.boxPad, state.2.1, state.2.2⟩ : Domain) = domain :=
    checked_domain_ok _ _ domain h
  rw [← he]
  exact domainBounds_origins nameRect state.2.1 c.boxPad
    ⟨hleft titleW htitleW, htop⟩ hstate.2

theorem successful_routes_endpoints (c : Consts) (domains : List Domain)
    (sources : List ModelRoute) (routes : List Route)
    (h : (sources.mapM (fun r =>
      match domains.find? (fun d => d.id == r.fromId),
          domains.find? (fun d => d.id == r.toId) with
      | some a, some b =>
        pure (Route.mk r.id r.fromId r.toId r.orthogonal (elbow c domains a b))
      | _, _ => throw .domain) : Except LayoutError (List Route)) = .ok routes) :
    ∀ r ∈ routes, ∃ a ∈ domains, ∃ b ∈ domains,
      a.id = r.fromId ∧ b.id = r.toId ∧ r.points = elbow c domains a b := by
  apply mapM_success_property _
    (fun r : Route => ∃ a ∈ domains, ∃ b ∈ domains,
      a.id = r.fromId ∧ b.id = r.toId ∧ r.points = elbow c domains a b)
    ?_ sources routes h
  intro source route hs
  cases ha : domains.find? (fun d => d.id == source.fromId) with
  | none =>
    simp [ha, throw, throwThe, MonadExceptOf.throw] at hs
  | some a =>
    cases hb : domains.find? (fun d => d.id == source.toId) with
    | none =>
      simp [ha, hb, throw, throwThe, MonadExceptOf.throw] at hs
    | some b =>
      have he : Route.mk source.id source.fromId source.toId source.orthogonal
          (elbow c domains a b) = route := by
        simpa [ha, hb, Pure.pure, Except.pure] using hs
      subst route
      exact ⟨a, List.mem_of_find?_eq_some ha, b, List.mem_of_find?_eq_some hb,
        by simpa only [beq_iff_eq] using List.find?_some ha,
        by simpa only [beq_iff_eq] using List.find?_some hb, rfl⟩

theorem successful_routes_boundary (c : Consts) (domains : List Domain)
    (sources : List ModelRoute) (routes : List Route)
    (hdomains : ∀ d ∈ domains, d.PortBounds)
    (h : (sources.mapM (fun r =>
      match domains.find? (fun d => d.id == r.fromId),
          domains.find? (fun d => d.id == r.toId) with
      | some a, some b =>
        pure (Route.mk r.id r.fromId r.toId r.orthogonal (elbow c domains a b))
      | _, _ => throw .domain) : Except LayoutError (List Route)) = .ok routes) :
    ∀ r ∈ routes, ∃ a ∈ domains, ∃ b ∈ domains, ∃ p q,
      a.id = r.fromId ∧ b.id = r.toId ∧
      r.points.head? = some p ∧ r.points.getLast? = some q ∧
      Validator.onBoundary p a.rect ∧ Validator.onBoundary q b.rect := by
  intro r hr
  obtain ⟨a, ha, b, hb, hidA, hidB, hpoints⟩ :=
    successful_routes_endpoints c domains sources routes h r hr
  obtain ⟨p, q, hp, hq, hpa, hqb⟩ :=
    elbow_ports c domains a b (hdomains a ha) (hdomains b hb)
  refine ⟨a, ha, b, hb, p, q, hidA, hidB, ?_, ?_, hpa, hqb⟩
  · simpa only [hpoints] using hp
  · simpa only [hpoints] using hq

private theorem checked_ok {α : Type} (condition : Bool) (value : α) (result : α)
    (h : (do
      if condition then throw .overflow
      pure value : Except LayoutError α) = .ok result) : value = result := by
  by_cases hc : condition = true
  · simp [hc, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simpa [hc, Bind.bind, Except.bind, Pure.pure, Except.pure] using h

theorem successful_layout_decompose (m : Model) (scene : Scene)
    (h : layout m = .ok scene) :
    ∃ (title : List Placed) (domains : List Domain) (routes : List Route)
      (labels : List Placed) (dumpLabels : List SceneLabel),
      ((m.boxes.filter (fun b => b.id != "frame")).mapM (fun b =>
        placeDomain (constants m) m ((title.head?).map (·.box.h) |>.getD 0) b.id) :
          Except LayoutError (List Domain)) = .ok domains ∧
      (m.routes.mapM (fun r =>
        match domains.find? (fun d => d.id == r.fromId),
            domains.find? (fun d => d.id == r.toId) with
        | some a, some b =>
          pure (Route.mk r.id r.fromId r.toId r.orthogonal
            (elbow (constants m) domains a b))
        | _, _ => throw .domain) : Except LayoutError (List Route)) = .ok routes ∧
      scene.canvas = ⟨
        routeExtent routes (extent (labels.map (·.rect) ++ domains.map (·.rect))
          (constants m).width right) Point.x,
        routeExtent routes (extent (labels.map (·.rect) ++ domains.map (·.rect))
          (constants m).height bottom) Point.y⟩ ∧
      scene.boxes = dumpBoxes m domains scene.canvas ∧
      scene.routes = routes ∧ scene.labels = dumpLabels := by
  have hf := layout_frame_consistent m scene h
  have hr := layout_relations_consistent m scene h
  unfold layout at h
  simp only [hf, hr] at h
  cases htitleFind : m.labels.find? (fun l => l.id == "title") with
  | none =>
    simp only [htitleFind, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨domains, hdomains, h⟩ := bind_ok h
    obtain ⟨routes, hroutes, h⟩ := bind_ok h
    obtain ⟨labels, _hlabels, h⟩ := bind_ok h
    obtain ⟨dumpLabels, _hdumpLabels, h⟩ := bind_ok h
    have he := checked_ok _ _ scene h
    cases he
    exact ⟨[], domains, routes, labels, dumpLabels, hdomains, hroutes,
      rfl, rfl, rfl, rfl⟩
  | some l =>
    simp only [htitleFind] at h
    obtain ⟨tbox, _htbox, h⟩ := bind_ok h
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    obtain ⟨domains, hdomains, h⟩ := bind_ok h
    obtain ⟨routes, hroutes, h⟩ := bind_ok h
    obtain ⟨labels, _hlabels, h⟩ := bind_ok h
    obtain ⟨dumpLabels, _hdumpLabels, h⟩ := bind_ok h
    have he := checked_ok _ _ scene h
    cases he
    exact ⟨[⟨l, tbox,
      ⟨max 0 (Int.fdiv (constants m).width 2 - Int.fdiv tbox.w 2),
        (constants m).pad, tbox.w, tbox.h⟩, .title, .middle⟩],
      domains, routes, labels, dumpLabels, hdomains, hroutes,
      rfl, rfl, rfl, rfl⟩

theorem successful_scene_nonexclusive (m : Model) (scene : Scene)
    (h : layout m = .ok scene) :
    ∀ b ∈ scene.boxes, b.exclusive = false := by
  obtain ⟨_title, domains, _routes, _labels, _dumpLabels, _hd, _hroutes, _hc, hb, _hr, _hl⟩ :=
    successful_layout_decompose m scene h
  rw [hb]
  exact layout_dumpBoxes_nonexclusive m scene h domains scene.canvas

theorem successful_scene_orthogonal (m : Model) (scene : Scene)
    (h : layout m = .ok scene) :
    ∀ r ∈ scene.routes, Polyline.isOrthogonal r.points = true := by
  obtain ⟨_title, domains, routes, _labels, _dumpLabels, _hd, hroutes, _hc, _hb, hr, _hl⟩ :=
    successful_layout_decompose m scene h
  rw [hr]
  exact successful_routes_orthogonal (constants m) domains m.routes routes hroutes

theorem successful_scene_canvas_of_domain_origins (m : Model) (scene : Scene)
    (h : layout m = .ok scene)
    (hw : 0 ≤ (constants m).width) (hh : 0 ≤ (constants m).height)
    (horigins : ∀ (title : List Placed) (domains : List Domain),
      ((m.boxes.filter (fun b => b.id != "frame")).mapM (fun b =>
        placeDomain (constants m) m ((title.head?).map (·.box.h) |>.getD 0) b.id) :
          Except LayoutError (List Domain)) = .ok domains →
      ∀ d ∈ domains, 0 ≤ d.rect.x ∧ 0 ≤ d.rect.y) :
    Validator.C1 scene.layoutDump := by
  obtain ⟨title, domains, routes, labels, _dumpLabels, hd, _hroutes, hc, hb,
    _hr, _hl⟩ := successful_layout_decompose m scene h
  change ∀ b ∈ scene.boxes,
    (Rect.mk 0 0 scene.canvas.w scene.canvas.h).Contained b.rect
  rw [hb, hc]
  exact dumpBoxes_extent_canvas m domains labels routes
    (constants m).width (constants m).height hw hh (horigins title domains hd)

theorem successful_scene_parent_containment (m : Model) (scene : Scene)
    (h : layout m = .ok scene) (hcanvas : Validator.C1 scene.layoutDump) :
    Validator.C3 scene.layoutDump := by
  obtain ⟨_title, domains, _routes, _labels, _dumpLabels, _hd, _hroutes, _hc,
    hb, _hr, _hl⟩ := successful_layout_decompose m scene h
  intro b hmem hparent p hp
  have hmem' : b ∈ dumpBoxes m domains scene.canvas := by
    change b ∈ scene.boxes at hmem
    rwa [hb] at hmem
  have hrel := layout_dumpBoxes_parents m scene h domains scene.canvas b hmem'
  have hnotframe : b.id ≠ "frame" := by
    intro hid
    simp only [hid, ↓reduceIte] at hrel
    exact hparent hrel
  have hparentframe : b.parent = "frame" := by
    simpa only [hnotframe, ↓reduceIte] using hrel
  have hpfind : scene.boxes.find? (fun box => box.id == b.parent) = some p := hp
  have hpmem : p ∈ scene.boxes := List.mem_of_find?_eq_some hpfind
  have hpid : p.id = "frame" := by
    have hid := List.find?_some hpfind
    simpa only [hparentframe, beq_iff_eq] using hid
  have hprect : p.rect = ⟨0, 0, scene.canvas.w, scene.canvas.h⟩ := by
    rw [hb] at hpmem
    obtain ⟨source, _hs, he⟩ := List.mem_map.mp hpmem
    have hsource : source.id = "frame" := by
      have hid : source.id = p.id := congrArg Box.id he
      exact hid.trans hpid
    rw [← he]
    simp only [hsource, beq_self_eq_true, ite_true]
  rw [hprect]
  exact hcanvas b hmem

theorem successful_scene_ports (m : Model) (scene : Scene)
    (h : layout m = .ok scene) : Validator.C5 scene.layoutDump := by
  obtain ⟨title, domains, routes, _labels, _dumpLabels, hd, hroutes, _hc, hb,
    hr, _hl⟩ := successful_layout_decompose m scene h
  intro r hmem
  have hmem' : r ∈ routes := by
    change r ∈ scene.routes at hmem
    rwa [hr] at hmem
  obtain ⟨a, ha, b, hbm, p, q, hida, hidb, hp, hq, hpa, hqb⟩ :=
    successful_routes_boundary (constants m) domains m.routes routes
      (successful_domain_ports m title domains hd) hroutes r hmem'
  obtain ⟨fromBox, hfrom, hfromrect⟩ :=
    successful_domain_box_lookup m title domains scene.canvas hd a ha
  obtain ⟨toBox, hto, htorect⟩ :=
    successful_domain_box_lookup m title domains scene.canvas hd b hbm
  refine ⟨p, q, fromBox, toBox, hp, hq, ?_, ?_, ?_, ?_⟩
  · change scene.boxes.find? (fun box => box.id == r.fromId) = some fromBox
    rw [hb, ← hida]
    exact hfrom
  · change scene.boxes.find? (fun box => box.id == r.toId) = some toBox
    rw [hb, ← hidb]
    exact hto
  · rwa [hfromrect]
  · rwa [htorect]

theorem cynefin_c1_of_nonneg_dims (m : Model) (scene : Scene)
    (hdims : 0 ≤ (constants m).width ∧ 0 ≤ (constants m).height)
    (h : layout m = .ok scene) : Validator.C1 scene.layoutDump := by
  apply successful_scene_canvas_of_domain_origins m scene h hdims.1 hdims.2
  intro title domains hd
  exact mapM_success_property _ (fun d => 0 ≤ d.rect.x ∧ 0 ≤ d.rect.y)
    (fun source d hcall => placeDomain_origins m _ source.id d hdims.2 hcall)
    _ domains hd

theorem cynefin_c3_of_nonneg_dims (m : Model) (scene : Scene)
    (hdims : 0 ≤ (constants m).width ∧ 0 ≤ (constants m).height)
    (h : layout m = .ok scene) : Validator.C3 scene.layoutDump :=
  successful_scene_parent_containment m scene h
    (cynefin_c1_of_nonneg_dims m scene hdims h)

def negativeHeightWitness : Model :=
  { kind := "cynefin", profile := .cell,
    options := { config := [("height", .integer (-1600))] },
    boxes := [
      { id := "frame", exclusive := false },
      { id := "complex", parent := "frame", exclusive := false },
      { id := "chaotic", parent := "frame", exclusive := false }] }

theorem negativeHeightWitness_wellFormed : WellFormed negativeHeightWitness := by
  decide

theorem negativeHeightWitness_withinLimits : WithinLimits negativeHeightWitness := by
  decide

theorem negativeHeightWitness_counterexample :
    ∃ scene, layout negativeHeightWitness = .ok scene ∧
      ¬ Validator.C1 scene.layoutDump := by
  refine ⟨_, rfl, ?_⟩
  decide

end Elegant.Chart.Cynefin
