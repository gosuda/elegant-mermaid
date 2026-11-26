import ElegantGeometry.Basic
import Elegant.Gen.Advances
import Elegant.Gen.Advancesupem
import Elegant.Gen.Graphemes
import Elegant.Gen.Ideographic
import Elegant.Gen.Incb
import Elegant.Gen.Unicodewidth

set_option autoImplicit false

/-! Text measurement of the Lean reference: font advances, cell widths, extended grapheme
clusters (UAX #29, GB1 to GB999 with GB9c, GB11, GB12, GB13), and greedy wrapping.

Strings are lists of Unicode scalar values (`List Char`); a cluster is a nonempty scalar list.
Widths are integers. Rounding is `Int.fdiv`. The generated tables are read through binary search
and the theorems below never inspect table contents: a font advance is a `Nat`, so every sum of
advances is non-negative by type, and a width is a monotone function of such a sum once the units
per em are positive and the size is not negative.

The Go twin is `internal/measure`: `Segment`, `ClusterWidth`, `VectorWidth`, `Wrap`. -/

namespace Elegant.Measure

/-! ### Integer helpers -/

/-- `Int.fdiv` agrees with `/` for a non-negative divisor. -/
theorem fdiv_of_nonneg {a b : Int} (hb : 0 ≤ b) : Int.fdiv a b = a / b := by
  rw [Int.fdiv_eq_ediv]
  simp [hb]

/-- `ceil_div(a, b) = floor_div(a + b - 1, b)`, for `b > 0`. -/
def ceilDiv (a b : Int) : Int := Int.fdiv (a + b - 1) b

theorem ceilDiv_eq {a b : Int} (hb : 0 < b) : ceilDiv a b = (a + b - 1) / b :=
  fdiv_of_nonneg (Int.le_of_lt hb)

theorem ceilDiv_mono {a a' b : Int} (hb : 0 < b) (h : a ≤ a') : ceilDiv a b ≤ ceilDiv a' b := by
  rw [ceilDiv_eq hb, ceilDiv_eq hb]
  exact Int.ediv_le_ediv hb (by omega)

theorem ceilDiv_nonneg {a b : Int} (hb : 0 < b) (ha : 0 ≤ a) : 0 ≤ ceilDiv a b := by
  rw [ceilDiv_eq hb]
  exact Int.ediv_nonneg (by omega) (Int.le_of_lt hb)

theorem le_ceilDiv_mul {a b : Int} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  rw [ceilDiv_eq hb]
  have h1 := Int.mul_ediv_add_emod (a + b - 1) b
  have h2 := Int.emod_lt_of_pos (a + b - 1) hb
  have h3 := Int.emod_nonneg (a + b - 1) (Int.ne_of_gt hb)
  rw [Int.mul_comm]
  omega

theorem ceilDiv_le_of_le_mul {a b c : Int} (hb : 0 < b) (h : a ≤ c * b) : ceilDiv a b ≤ c := by
  rw [ceilDiv_eq hb]
  have : (a + b - 1) / b < c + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hb]
    have : (c + 1) * b = c * b + b := by rw [Int.add_mul, Int.one_mul]
    omega
  omega

theorem ceilDiv_add_le {x y b : Int} (hb : 0 < b) :
    ceilDiv (x + y) b ≤ ceilDiv x b + ceilDiv y b := by
  apply ceilDiv_le_of_le_mul hb
  have hx := le_ceilDiv_mul (a := x) hb
  have hy := le_ceilDiv_mul (a := y) hb
  rw [Int.add_mul]
  omega

/-- The extra width of a non-default `fontFamily`: `floor_div(w * 108, 100)`. -/
def fontFamilyFactor (w : Int) : Int := Int.fdiv (w * 108) 100

theorem fontFamilyFactor_eq (w : Int) : fontFamilyFactor w = (w * 108) / 100 :=
  fdiv_of_nonneg (by decide)

theorem fontFamilyFactor_mono {a b : Int} (h : a ≤ b) :
    fontFamilyFactor a ≤ fontFamilyFactor b := by
  rw [fontFamilyFactor_eq, fontFamilyFactor_eq]
  omega

theorem fontFamilyFactor_nonneg {a : Int} (h : 0 ≤ a) : 0 ≤ fontFamilyFactor a := by
  rw [fontFamilyFactor_eq]
  omega

theorem fontFamilyFactor_add_le (a b : Int) :
    fontFamilyFactor (a + b) ≤ fontFamilyFactor a + fontFamilyFactor b + 1 := by
  rw [fontFamilyFactor_eq, fontFamilyFactor_eq, fontFamilyFactor_eq]
  omega

/-- The largest int64 value and the smallest. -/
def I64_MAX : Int := 9223372036854775807
def I64_MIN : Int := -9223372036854775808

/-- A value that must be an int32 result; otherwise the kernel's overflow error. -/
def checkedI32 (v : Int) : Except LayoutError Int :=
  if I32_MIN ≤ v ∧ v ≤ I32_MAX then .ok v else .error .overflow

/-- A product that must be an int64 intermediate; otherwise the kernel's overflow error. -/
def checkedI64 (v : Int) : Except LayoutError Int :=
  if I64_MIN ≤ v ∧ v ≤ I64_MAX then .ok v else .error .overflow

/-! ### Table lookups

Every generated range table is sorted and disjoint (`tools/specgen`), so the lookup is a binary
search for the first range whose upper bound reaches the code point. -/

/-- The least index below `n` where the monotone predicate `p` holds, or `n`. At most 64
halvings, which covers every array. -/
def partitionPoint (n : Nat) (p : Nat → Bool) : Nat :=
  go 64 0 n
where
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if p mid then go fuel lo mid else go fuel (mid + 1) hi
      else lo

def graphemeProp (cp : Nat) : Nat :=
  let i := partitionPoint graphemes.size fun i =>
    match graphemes[i]? with
    | some r => decide (cp ≤ r.hi)
    | none => true
  match graphemes[i]? with
  | some r => if r.lo ≤ cp then r.prop else 0
  | none => 0

def incbProp (cp : Nat) : Nat :=
  let i := partitionPoint incb.size fun i =>
    match incb[i]? with
    | some r => decide (cp ≤ r.hi)
    | none => true
  match incb[i]? with
  | some r => if r.lo ≤ cp then r.prop else 0
  | none => 0

/-- East Asian width class of a scalar: 0, 1, or 2. Unlisted scalars have width 1. -/
def scalarWidth (cp : Nat) : Nat :=
  let i := partitionPoint unicodewidth.size fun i =>
    match unicodewidth[i]? with
    | some r => decide (cp ≤ r.hi)
    | none => true
  match unicodewidth[i]? with
  | some r => if r.lo ≤ cp then r.value else 1
  | none => 1

/-- `Ideographic` from `PropList.txt`. -/
def isIdeographic (cp : Nat) : Bool :=
  let i := partitionPoint ideographic.size fun i =>
    match ideographic[i]? with
    | some r => decide (cp ≤ r.hi)
    | none => true
  match ideographic[i]? with
  | some r => decide (r.lo ≤ cp)
  | none => false

def advanceKey (weight cp : Nat) : Nat := weight * 4294967296 + cp

/-- The advance of a code point in font units, when the font has the glyph. Weight 0 is Regular,
1 is SemiBold. -/
def advanceUnits? (weight cp : Nat) : Option Nat :=
  let key := advanceKey weight cp
  let i := partitionPoint advances.size fun i =>
    match advances[i]? with
    | some r => decide (key ≤ advanceKey r.weight r.cp)
    | none => true
  match advances[i]? with
  | some r => if advanceKey r.weight r.cp == key then some r.units else none
  | none => none

/-! ### Grapheme cluster segmentation (UAX #29, Unicode 18.0.0)

`Grapheme_Cluster_Break` values of `tools/specgen`: 1 CR, 2 LF, 3 Control, 4 Extend, 5 ZWJ,
6 Regional_Indicator, 7 Prepend, 8 SpacingMark, 9 L, 10 V, 11 T, 12 LV, 13 LVT,
14 Extended_Pictographic, 0 Other. `InCB`: 1 Linker, 2 Consonant, 3 Extend. -/

def propCR : Nat := 1
def propLF : Nat := 2
def propControl : Nat := 3
def propExtend : Nat := 4
def propZWJ : Nat := 5
def propRegionalIndicator : Nat := 6
def propPrepend : Nat := 7
def propSpacingMark : Nat := 8
def propL : Nat := 9
def propV : Nat := 10
def propT : Nat := 11
def propLV : Nat := 12
def propLVT : Nat := 13
def propExtendedPictographic : Nat := 14

def incbLinker : Nat := 1
def incbConsonant : Nat := 2
def incbExtend : Nat := 3

/-- U+FE0F. -/
def presentationSelector : Nat := 0xFE0F
/-- U+20E3. -/
def combiningKeycap : Nat := 0x20E3

def isControl (prop : Nat) : Bool :=
  prop == propCR || prop == propLF || prop == propControl

/-- GB6, GB7, GB8. -/
def hangulJoins (prev next : Nat) : Bool :=
  if prev == propL then
    next == propL || next == propV || next == propLV || next == propLVT
  else if prev == propLV || prev == propV then
    next == propV || next == propT
  else if prev == propLVT || prev == propT then
    next == propT
  else false

/-- GB9, GB9a. -/
def attachesToPrevious (next : Nat) : Bool :=
  next == propExtend || next == propZWJ || next == propSpacingMark

/-- The state of the left-to-right pass: the previous scalar's class, and the run state that
GB9c (`linkerRun`), GB11 (`pictRun`, `gb11Pending`), and GB12 and GB13 (`riRun`) need. -/
structure BreakState where
  prev : Nat := 0
  pictRun : Bool := false
  gb11Pending : Bool := false
  linkerRun : Bool := false
  riRun : Nat := 0
deriving Repr

def BreakState.advance (st : BreakState) (prop incb : Nat) : BreakState where
  prev := prop
  pictRun := prop == propExtendedPictographic || (prop == propExtend && st.pictRun)
  gb11Pending := prop == propZWJ && st.pictRun
  linkerRun :=
    if incb == incbLinker then true
    else if incb == incbExtend then st.linkerRun
    else false
  riRun := if prop == propRegionalIndicator then st.riRun + 1 else 0

/-- The state after the first scalar of a cluster run. -/
def stateAt (cp : Nat) : BreakState :=
  BreakState.advance {} (graphemeProp cp) (incbProp cp)

/-- GB12 and GB13: break between two regional indicators after an even run of them. -/
def BreakState.regionalJoins (st : BreakState) (next : Nat) : Bool :=
  if st.prev != propRegionalIndicator || next != propRegionalIndicator then true
  else st.riRun % 2 == 0

/-- Is there a break before a scalar of class `next` and `InCB` class `nextIncb`?
GB3 to GB5, GB6 to GB9b, GB9c, GB11, then GB12, GB13, GB999. -/
def BreakState.breaksBefore (st : BreakState) (next nextIncb : Nat) : Bool :=
  if st.prev == propCR && next == propLF then false
  else if isControl st.prev || isControl next then true
  else if hangulJoins st.prev next || attachesToPrevious next then false
  else if st.prev == propPrepend then false
  else if st.linkerRun && nextIncb == incbConsonant then false
  else if st.gb11Pending && next == propExtendedPictographic then false
  else st.regionalJoins next

/-- A grapheme cluster: a nonempty list of scalars. -/
abbrev Cluster := List Char

/-- One pass over the scalars after the first. `cur` is the open cluster, reversed. `out` holds
the closed clusters, last first. -/
def segGo (st : BreakState) (cur : List Char) (out : List Cluster) : List Char → List Cluster
  | [] => (cur.reverse :: out).reverse
  | c :: rest =>
    let p := graphemeProp c.toNat
    let i := incbProp c.toNat
    if st.breaksBefore p i then segGo (st.advance p i) [c] (cur.reverse :: out) rest
    else segGo (st.advance p i) (c :: cur) out rest

/-- The extended grapheme clusters of a scalar list, in order. -/
def segment : List Char → List Cluster
  | [] => []
  | c :: rest => segGo (stateAt c.toNat) [c] [] rest

/-- The scalars of a cluster list. -/
def joinClusters (cs : List Cluster) : List Char := cs.flatten

theorem segGo_join (rest : List Char) :
    ∀ (st : BreakState) (cur : List Char) (out : List Cluster),
      joinClusters (segGo st cur out rest) = joinClusters out.reverse ++ cur.reverse ++ rest := by
  induction rest with
  | nil =>
    intro st cur out
    simp [segGo, joinClusters, List.flatten_append]
  | cons c rest ih =>
    intro st cur out
    simp only [segGo]
    split
    · rw [ih]
      simp [joinClusters, List.flatten_append]
    · rw [ih]
      simp [joinClusters]

/-- Clusters concatenate back to the scalars. -/
theorem segment_concat (s : List Char) : joinClusters (segment s) = s := by
  cases s with
  | nil => rfl
  | cons c rest =>
    simp only [segment]
    rw [segGo_join]
    simp [joinClusters]

/-! ### Cluster width and cell width -/

/-- The cell width of a grapheme cluster: 0 for a cluster that starts with an `Extend` or `ZWJ`
scalar, 2 for a wide first scalar, for U+20E3, and for U+FE0F after an `Extended_Pictographic`
scalar, else 1. -/
def clusterWidthLoop (pict : Bool) : List Char → Nat
  | [] => 1
  | c :: rest =>
    if c.toNat == combiningKeycap then 2
    else if c.toNat == presentationSelector && pict then 2
    else clusterWidthLoop (pict || graphemeProp c.toNat == propExtendedPictographic) rest

def clusterWidth : Cluster → Nat
  | [] => 1
  | c :: rest =>
    let prop := graphemeProp c.toNat
    if prop == propExtend || prop == propZWJ then 0
    else if scalarWidth c.toNat == 2 then 2
    else clusterWidthLoop false (c :: rest)

/-- The cell width of a cluster list: the sum of the cluster widths. -/
def cw (cs : List Cluster) : Nat := (cs.map clusterWidth).sum

/-- The cell width of a string: the width of its clusters. -/
def cellWidth (s : List Char) : Nat := cw (segment s)

/-! ### Vector width -/

inductive Profile where
  | vector
  | cell
deriving DecidableEq, Repr

/-- Text roles: size, line height, and font weight. -/
inductive Role where
  | body
  | label
  | title
deriving DecidableEq, Repr

def Role.sizePx : Role → Int
  | .title => 16
  | _ => 14

def Role.lineHeightPx : Role → Int
  | .title => 24
  | _ => 20

/-- 0 is Regular (400), 1 is SemiBold (600). -/
def Role.weight : Role → Nat
  | .body => 0
  | _ => 1

/-- A resolved metric. `upem` is the units per em of the font of `weight`; `sizePx` is in px. -/
structure Metric where
  profile : Profile
  sizePx : Int
  weight : Nat
  upem : Nat
  fontFamily : Bool
deriving Repr

/-- A metric whose vector fields are usable: a size that is not negative and a positive em. -/
def Metric.WF (m : Metric) : Prop :=
  m.profile = .cell ∨ (0 ≤ m.sizePx ∧ 0 < m.upem)

instance (m : Metric) : Decidable m.WF := by
  unfold Metric.WF; exact inferInstance

/-- Units per em of a font weight; a domain error for an unknown weight or an empty em. -/
def upemOf (w : Nat) : Except LayoutError Nat :=
  match advancesUpem[w]? with
  | some u => if 0 < u then .ok u.toNat else .error .domain
  | none => .error .domain

def Role.metric (r : Role) (fontFamily : Bool := false) : Except LayoutError Metric := do
  let u ← upemOf r.weight
  pure { profile := .vector, sizePx := r.sizePx, weight := r.weight, upem := u, fontFamily }

def Metric.cell : Metric :=
  { profile := .cell, sizePx := 0, weight := 0, upem := 1, fontFamily := false }

/-- The advance of one scalar in font units: the table value, else one em for a wide scalar,
else `floor_div(6 * upem + 5, 10)`. -/
def advanceOf (upem weight cp : Nat) : Nat :=
  match advanceUnits? weight cp with
  | some x => x
  | none => if scalarWidth cp == 2 then upem else (6 * upem + 5) / 10

/-- The sum of the advances of a scalar list, in font units. -/
def advanceSum (upem weight : Nat) (s : List Char) : Nat :=
  (s.map fun c => advanceOf upem weight c.toNat).sum

theorem advanceSum_append (upem weight : Nat) (a b : List Char) :
    advanceSum upem weight (a ++ b) = advanceSum upem weight a + advanceSum upem weight b := by
  simp [advanceSum, List.map_append, List.sum_append]

/-- The vector width of an advance sum, unchecked: `ceil_div(sum * size * 64, upem)`, then the
`fontFamily` factor. -/
def vecSpanWidth (m : Metric) (span : Nat) : Int :=
  let w := ceilDiv ((span : Int) * (m.sizePx * 64)) (m.upem : Int)
  if m.fontFamily then fontFamilyFactor w else w

/-- The vector width `w ff s` of a string, unchecked. -/
def vw (m : Metric) (s : List Char) : Int := vecSpanWidth m (advanceSum m.upem m.weight s)

/-- The vector width, as the checked kernel computes it: a domain error for a negative size or an
empty em, an overflow when the product leaves int64 or a width leaves int32. -/
def checkedVecSpanWidth (m : Metric) (span : Nat) : Except LayoutError Int :=
  if m.sizePx < 0 ∨ m.upem = 0 then .error .domain
  else do
    let product ← checkedI64 ((span : Int) * (m.sizePx * 64))
    let w ← checkedI32 (ceilDiv product (m.upem : Int))
    if m.fontFamily then checkedI32 (fontFamilyFactor w) else pure w

/-- The width of a string under a metric: the cell width, or the checked vector width. -/
def textWidth (m : Metric) (s : List Char) : Except LayoutError Int :=
  match m.profile with
  | .cell => checkedI32 (cellWidth s)
  | .vector => checkedVecSpanWidth m (advanceSum m.upem m.weight s)

/-- The wrap target: the kind's own, else `maxWidth`, else the default (12800 units, 32 cells). -/
def wrapTarget (profile : Profile) (kindTarget maxWidth : Int) : Int :=
  if 0 < kindTarget then kindTarget
  else if 0 < maxWidth then maxWidth
  else match profile with
    | .cell => 32
    | .vector => 12800


/-! ### Metric well-formedness and width theorems -/

/-- The vector fields of a metric are usable: a size that is not negative and a positive em. -/
def Metric.VecWF (m : Metric) : Prop := 0 ≤ m.sizePx ∧ 0 < m.upem

theorem Metric.WF_of_vec {m : Metric} (h : m.VecWF) : m.WF := Or.inr h

/-- The width of a span of advance sums or cell widths under a metric, unchecked. -/
def spanWidth (m : Metric) (span : Nat) : Int :=
  match m.profile with
  | .cell => (span : Int)
  | .vector => vecSpanWidth m span

theorem vecSpanWidth_mono {m : Metric} (hm : m.VecWF) {a b : Nat} (h : a ≤ b) :
    vecSpanWidth m a ≤ vecSpanWidth m b := by
  obtain ⟨hs, hu⟩ := hm
  have hu' : (0 : Int) < (m.upem : Int) := by exact_mod_cast hu
  have h1 : (a : Int) * (m.sizePx * 64) ≤ (b : Int) * (m.sizePx * 64) :=
    Int.mul_le_mul_of_nonneg_right (by exact_mod_cast h) (by omega)
  have h2 := ceilDiv_mono (b := (m.upem : Int)) hu' h1
  unfold vecSpanWidth
  by_cases hf : m.fontFamily
  · simp only [hf, ↓reduceIte]
    exact fontFamilyFactor_mono h2
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact h2

theorem vecSpanWidth_nonneg {m : Metric} (hm : m.VecWF) (a : Nat) : 0 ≤ vecSpanWidth m a := by
  obtain ⟨hs, hu⟩ := hm
  have hu' : (0 : Int) < (m.upem : Int) := by exact_mod_cast hu
  have h1 : 0 ≤ (a : Int) * (m.sizePx * 64) :=
    Int.mul_nonneg (Int.natCast_nonneg a) (by omega)
  have h2 := ceilDiv_nonneg hu' h1
  unfold vecSpanWidth
  by_cases hf : m.fontFamily
  · simp only [hf, ↓reduceIte]
    exact fontFamilyFactor_nonneg h2
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact h2

theorem vecSpanWidth_add_le {m : Metric} (hm : m.VecWF) (x y : Nat) :
    vecSpanWidth m (x + y) ≤
      vecSpanWidth m x + vecSpanWidth m y + (if m.fontFamily then 1 else 0) := by
  obtain ⟨hs, hu⟩ := hm
  have hu' : (0 : Int) < (m.upem : Int) := by exact_mod_cast hu
  have h1 : ((x + y : Nat) : Int) * (m.sizePx * 64) =
      (x : Int) * (m.sizePx * 64) + (y : Int) * (m.sizePx * 64) := by
    rw [Int.natCast_add, Int.add_mul]
  have h2 := ceilDiv_add_le (x := (x : Int) * (m.sizePx * 64)) (y := (y : Int) * (m.sizePx * 64))
    hu'
  unfold vecSpanWidth
  by_cases hf : m.fontFamily
  · simp only [hf, ↓reduceIte]
    rw [h1]
    have h3 := fontFamilyFactor_mono h2
    have h4 := fontFamilyFactor_add_le
      (ceilDiv ((x : Int) * (m.sizePx * 64)) (m.upem : Int))
      (ceilDiv ((y : Int) * (m.sizePx * 64)) (m.upem : Int))
    exact Int.le_trans h3 h4
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [h1]
    omega

theorem spanWidth_mono {m : Metric} (hm : m.WF) {a b : Nat} (h : a ≤ b) :
    spanWidth m a ≤ spanWidth m b := by
  unfold spanWidth
  cases hp : m.profile with
  | cell => exact Int.ofNat_le.mpr h
  | vector =>
    rcases hm with hm | hm
    · rw [hp] at hm; cases hm
    · exact vecSpanWidth_mono hm h

/-- A width is not negative. Vector: the vector fields are usable. Cell: always. -/
theorem width_nonneg :
    (∀ (m : Metric) (s : List Char), m.VecWF → 0 ≤ vw m s) ∧
    (∀ cs : List Cluster, 0 ≤ (cw cs : Int)) :=
  ⟨fun _ _ hm => vecSpanWidth_nonneg hm _, fun _ => Int.natCast_nonneg _⟩

/-- Width is subadditive. Vector: `w (a ++ b) ≤ w a + w b`, plus 1 under `fontFamily` (the
factor `floor_div(x * 108, 100)` adds at most 1). Cell: exactly additive over a concatenation of
cluster lists. No bound on scalar strings is claimed for the cell width: `segment (a ++ b)`
can merge the last cluster of `a` with the first of `b`. -/
theorem width_append_le :
    (∀ (m : Metric) (a b : List Char), m.VecWF →
      vw m (a ++ b) ≤ vw m a + vw m b + (if m.fontFamily then 1 else 0)) ∧
    (∀ ca cb : List Cluster, cw (ca ++ cb) = cw ca + cw cb) := by
  refine ⟨?_, ?_⟩
  · intro m a b hm
    unfold vw
    rw [advanceSum_append]
    exact vecSpanWidth_add_le hm _ _
  · intro ca cb
    simp [cw, List.map_append, List.sum_append]

theorem checkedI32_ok {v x : Int} (h : checkedI32 v = .ok x) : x = v := by
  unfold checkedI32 at h
  split at h
  · injection h with h; exact h.symm
  · cases h

theorem checkedI64_ok {v x : Int} (h : checkedI64 v = .ok x) : x = v := by
  unfold checkedI64 at h
  split at h
  · injection h with h; exact h.symm
  · cases h

/-- A checked vector width is the unchecked one, and its metric is usable. -/
theorem checkedVecSpanWidth_ok {m : Metric} {span : Nat} {x : Int}
    (h : checkedVecSpanWidth m span = .ok x) : m.VecWF ∧ x = vecSpanWidth m span := by
  unfold checkedVecSpanWidth at h
  by_cases hs : m.sizePx < 0 ∨ m.upem = 0
  · simp only [hs, ↓reduceIte] at h; cases h
  · simp only [hs, ↓reduceIte] at h
    have hs' := not_or.mp hs
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    cases h1 : checkedI64 ((span : Int) * (m.sizePx * 64)) with
    | error e => rw [h1] at h; cases h
    | ok p =>
      rw [h1] at h
      have hp := checkedI64_ok h1
      simp only [bind, Except.bind] at h
      cases h2 : checkedI32 (ceilDiv p (m.upem : Int)) with
      | error e => rw [h2] at h; cases h
      | ok w =>
        rw [h2] at h
        have hw := checkedI32_ok h2
        unfold vecSpanWidth
        subst hp hw
        by_cases hf : m.fontFamily
        · simp only [hf, ↓reduceIte] at h ⊢
          cases h3 : checkedI32
              (fontFamilyFactor (ceilDiv ((span : Int) * (m.sizePx * 64)) (m.upem : Int))) with
          | error e => rw [h3] at h; cases h
          | ok y =>
            rw [h3] at h
            injection h with h
            rw [← h]
            exact checkedI32_ok h3
        · simp only [hf, Bool.false_eq_true, ↓reduceIte] at h ⊢
          injection h with h
          exact h.symm

/-- A checked cell width is the cell width of the clusters. -/
theorem textWidth_cell {m : Metric} {s : List Char} {x : Int} (hp : m.profile = .cell)
    (h : textWidth m s = .ok x) : x = (cellWidth s : Int) := by
  unfold textWidth at h
  rw [hp] at h
  exact checkedI32_ok h

/-- A checked vector width is the vector width `vw`, for a usable metric. -/
theorem textWidth_vector {m : Metric} {s : List Char} {x : Int} (hp : m.profile = .vector)
    (h : textWidth m s = .ok x) : m.VecWF ∧ x = vw m s := by
  unfold textWidth at h
  rw [hp] at h
  exact checkedVecSpanWidth_ok h

/-- A checked width, in either profile, is not negative. -/
theorem textWidth_nonneg {m : Metric} {s : List Char} {x : Int}
    (h : textWidth m s = .ok x) : 0 ≤ x := by
  cases hp : m.profile with
  | cell => rw [textWidth_cell hp h]; exact Int.natCast_nonneg _
  | vector =>
    obtain ⟨hm, hx⟩ := textWidth_vector hp h
    rw [hx]
    exact width_nonneg.1 m s hm

/-! ### Wrapping -/

/-- The sublist `[a, b)`; empty when `b ≤ a`. -/
def slice {α : Type} (l : List α) (a b : Nat) : List α := (l.drop a).take (b - a)

theorem slice_self {α : Type} (l : List α) (a : Nat) : slice l a a = [] := by
  simp [slice]

theorem drop_eq_slice_append {α : Type} (l : List α) {a b : Nat} (h : a ≤ b) :
    l.drop a = slice l a b ++ l.drop b := by
  unfold slice
  have h2 : l.drop b = (l.drop a).drop (b - a) := by
    rw [List.drop_drop, Nat.add_sub_of_le h]
  rw [h2, List.take_append_drop]

theorem take_sum_mono (x : List Nat) {a b : Nat} (h : a ≤ b) :
    (x.take a).sum ≤ (x.take b).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  exact Nat.le_add_right _ _

theorem slice_sum_mono (x : List Nat) (i : Nat) {e j : Nat} (h : e ≤ j) :
    (slice x i e).sum ≤ (slice x i j).sum :=
  take_sum_mono _ (by omega)

/-- A wrapped line: its text, the separator that follows it, and the width of its text. -/
structure Line where
  text : List Char
  sep : List Char
  width : Int
deriving Repr

/-- Each line's text followed by its separator, in order. -/
def joinLines (ls : List Line) : List Char := (ls.map fun l => l.text ++ l.sep).flatten

/-- A space cluster is exactly U+0020. -/
def isSp (c : Cluster) : Bool := c == [' ']

/-- The length of the leading run of space clusters. -/
def spaceRun : List Cluster → Nat
  | [] => 0
  | c :: rest => if isSp c then spaceRun rest + 1 else 0

theorem spaceRun_le : ∀ l : List Cluster, spaceRun l ≤ l.length
  | [] => by simp [spaceRun]
  | c :: rest => by
    have ih := spaceRun_le rest
    unfold spaceRun
    split
    · simp; omega
    · simp

def isAsciiAlnum (cp : Nat) : Bool :=
  (48 ≤ cp && cp ≤ 57) || (97 ≤ cp && cp ≤ 122) || (65 ≤ cp && cp ≤ 90)

/-- Break opportunity of kind `H` or `I` between two clusters: after U+002D before an ASCII
letter or digit, or between two `Ideographic` scalars. -/
def breakAt (prev cur : Cluster) : Bool :=
  match prev.getLast?, cur.head? with
  | some p, some n =>
    (p == '-' && isAsciiAlnum n.toNat) || (isIdeographic p.toNat && isIdeographic n.toNat)
  | _, _ => false

/-- A break opportunity: the text ends at cluster index `pos`, and the next line starts at
`next`. The separator is `[pos, next)`: a space run, or empty. -/
structure Opp where
  pos : Nat
  next : Nat

/-- The opportunities of a cluster list, by increasing `pos`. `oppsGo i prev l` scans the
clusters `l` that start at index `i`, after the cluster `prev`. A maximal space run that starts
after index 0 and does not reach the end is an opportunity `S`; a trailing run is not. -/
def oppsGo : Nat → Cluster → List Cluster → List Opp
  | _, _, [] => []
  | i, prev, c :: rest =>
    if isSp c then
      if isSp prev then oppsGo (i + 1) c rest
      else if spaceRun (c :: rest) = (c :: rest).length then []
      else ⟨i, i + spaceRun (c :: rest)⟩ :: oppsGo (i + 1) c rest
    else
      (if breakAt prev c then [⟨i, i⟩] else []) ++ oppsGo (i + 1) c rest

def opps : List Cluster → List Opp
  | [] => []
  | c :: rest => oppsGo 1 c rest

theorem oppsGo_wf : ∀ (l : List Cluster) (i : Nat) (prev : Cluster) (o : Opp),
    o ∈ oppsGo i prev l → i ≤ o.pos ∧ o.pos ≤ o.next ∧ o.next < i + l.length
  | [], i, prev, o, h => by simp [oppsGo] at h
  | c :: rest, i, prev, o, h => by
    have ih := oppsGo_wf rest (i + 1) c
    have hr := spaceRun_le (c :: rest)
    unfold oppsGo at h
    by_cases hc : isSp c
    · simp only [hc, ↓reduceIte] at h
      by_cases hp : isSp prev
      · simp only [hp, ↓reduceIte] at h
        have := ih o h
        simp only [List.length_cons] at *
        omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
        by_cases he : spaceRun (c :: rest) = (c :: rest).length
        · simp only [he, ↓reduceIte] at h; simp at h
        · simp only [he, ↓reduceIte] at h
          simp only [List.mem_cons] at h
          rcases h with h | h
          · subst h
            simp only [List.length_cons] at *
            omega
          · have := ih o h
            simp only [List.length_cons] at *
            omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      simp only [List.mem_append] at h
      rcases h with h | h
      · by_cases hb : breakAt prev c
        · simp only [hb, ↓reduceIte] at h
          simp only [List.mem_singleton] at h
          subst h
          simp only [List.length_cons]
          omega
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h; simp at h
      · have := ih o h
        simp only [List.length_cons] at *
        omega

theorem opps_wf (cs : List Cluster) :
    ∀ o ∈ opps cs, o.pos ≤ o.next ∧ o.next < cs.length := by
  intro o h
  cases cs with
  | nil => simp [opps] at h
  | cons c rest =>
    have := oppsGo_wf rest 1 c o h
    simp only [List.length_cons] at *
    omega

/-- The opportunity with the largest `pos` in `(i, j]`; the list is ordered by increasing
`pos`, so this is the last match. -/
def lastOpp (i j : Nat) : List Opp → Option Opp
  | [] => none
  | o :: os =>
    match lastOpp i j os with
    | some r => some r
    | none => if i < o.pos ∧ o.pos ≤ j then some o else none

theorem lastOpp_spec (i j : Nat) : ∀ (os : List Opp) (o : Opp),
    lastOpp i j os = some o → o ∈ os ∧ i < o.pos ∧ o.pos ≤ j
  | [], o, h => by simp [lastOpp] at h
  | p :: os, o, h => by
    unfold lastOpp at h
    split at h
    · rename_i r hr
      have := lastOpp_spec i j os r hr
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · split at h
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_self, hp⟩
      · simp at h

/-- The span of one cluster: the cell width, or the advance sum in font units. -/
def clusterSpan (m : Metric) (c : Cluster) : Nat :=
  match m.profile with
  | .cell => clusterWidth c
  | .vector => advanceSum m.upem m.weight c

/-- Scan the spans of the clusters from a line start; the count of leading clusters whose total
width stays within `L`. The width is monotone in the total, so this is the largest `j - i` with
`W(i, j) ≤ L`. -/
def fitScan (m : Metric) (L : Int) : Nat → Nat → List Nat → Nat
  | _, k, [] => k
  | acc, k, s :: rest =>
    if spanWidth m (acc + s) ≤ L then fitScan m L (acc + s) (k + 1) rest else k

theorem fitScan_spec (m : Metric) (L : Int) : ∀ (ss : List Nat) (acc k : Nat),
    ∃ t, fitScan m L acc k ss = k + t ∧ t ≤ ss.length ∧
      (t = 0 ∨ spanWidth m (acc + (ss.take t).sum) ≤ L)
  | [], acc, k => ⟨0, by simp [fitScan], by simp, Or.inl rfl⟩
  | s :: rest, acc, k => by
    unfold fitScan
    by_cases h : spanWidth m (acc + s) ≤ L
    · simp only [h, ↓reduceIte]
      obtain ⟨t', ht1, ht2, ht3⟩ := fitScan_spec m L rest (acc + s) (k + 1)
      refine ⟨t' + 1, by omega, by simp; omega, Or.inr ?_⟩
      rw [List.take_succ_cons, List.sum_cons]
      rcases ht3 with ht3 | ht3
      · subst ht3
        simpa [Nat.add_assoc] using h
      · rw [← Nat.add_assoc]; exact ht3
    · simp only [h, ↓reduceIte]
      exact ⟨0, by simp, by simp, Or.inl rfl⟩

/-- `j - i` of rule 8, step 1: the length of the longest prefix that fits, at least 1. -/
def lineLen (m : Metric) (L : Int) (ss : List Nat) : Nat := max 1 (fitScan m L 0 0 ss)

theorem lineLen_spec (m : Metric) (L : Int) (ss : List Nat) (hss : ss ≠ []) :
    1 ≤ lineLen m L ss ∧ lineLen m L ss ≤ ss.length ∧
      (lineLen m L ss = 1 ∨ spanWidth m (ss.take (lineLen m L ss)).sum ≤ L) := by
  obtain ⟨t, ht1, ht2, ht3⟩ := fitScan_spec m L ss 0 0
  have hlen : 0 < ss.length := List.length_pos_iff.mpr hss
  unfold lineLen
  rw [ht1]
  by_cases h0 : t = 0
  · subst h0
    simp only [Nat.zero_add, Nat.max_def]
    refine ⟨by simp, by simp; omega, Or.inl (by simp)⟩
  · have : max 1 (0 + t) = t := by omega
    rw [this]
    refine ⟨by omega, ht2, Or.inr ?_⟩
    rcases ht3 with h | h
    · exact absurd h h0
    · simpa using h

/-- A line over cluster slices: text `[a, b)`, separator `[c, d)`. -/
def mkLine (m : Metric) (cs : List Cluster) (ss : List Nat) (a b c d : Nat) : Line where
  text := joinClusters (slice cs a b)
  sep := joinClusters (slice cs c d)
  width := spanWidth m (slice ss a b).sum

/-- The final line from `i`: a trailing space run that starts after `i` is its separator. -/
def finalLine (m : Metric) (cs : List Cluster) (ss : List Nat) (n i : Nat) : Line :=
  let t := spaceRun (cs.drop i).reverse
  let r := if i < n - t then n - t else n
  mkLine m cs ss i r r n

/-- Rule 8, iterated with `fuel` steps from line start `i`. -/
def wrapLoop (m : Metric) (L : Int) (cs : List Cluster) (ss : List Nat) (opps : List Opp)
    (n : Nat) : Nat → Nat → List Line
  | 0, _ => []
  | fuel + 1, i =>
    if i < n then
      let j := i + lineLen m L (ss.drop i)
      if j = n then [finalLine m cs ss n i]
      else
        match lastOpp i j opps with
        | some o => mkLine m cs ss i o.pos o.pos o.next :: wrapLoop m L cs ss opps n fuel o.next
        | none => mkLine m cs ss i j j j :: wrapLoop m L cs ss opps n fuel j
    else []

/-- Wrap a cluster list: fuel equal to the cluster count. -/
def wrapClusters (m : Metric) (L : Int) (cs : List Cluster) : List Line :=
  wrapLoop m L cs (cs.map (clusterSpan m)) (opps cs) cs.length cs.length 0

/-- Wrap a scalar list at width `L` (rule 8), unchecked. -/
def wrapCore (m : Metric) (L : Int) (s : List Char) : List Line :=
  wrapClusters m L (segment s)

/-- Wrap a scalar list at width `L`. A domain error for an unusable metric; an overflow when a
line width leaves int32. -/
def wrap (m : Metric) (L : Int) (s : List Char) : Except LayoutError (List Line) :=
  if ¬ m.WF then .error .domain
  else if (wrapCore m L s).all (fun l => decide (I32_MIN ≤ l.width ∧ l.width ≤ I32_MAX)) then
    .ok (wrapCore m L s)
  else .error .overflow

theorem wrap_ok {m : Metric} {L : Int} {s : List Char} {ls : List Line}
    (h : wrap m L s = .ok ls) : m.WF ∧ ls = wrapCore m L s := by
  unfold wrap at h
  split at h
  · simp at h
  · rename_i hwf
    split at h
    · simp only [Except.ok.injEq] at h
      exact ⟨Classical.byContradiction hwf, h.symm⟩
    · simp at h

theorem join_chain (cs : List Cluster) {i a b : Nat} (h1 : i ≤ a) (h2 : a ≤ b) :
    joinClusters (slice cs i a) ++ joinClusters (slice cs a b) ++ joinClusters (cs.drop b) =
      joinClusters (cs.drop i) := by
  have e1 := drop_eq_slice_append cs h1
  have e2 := drop_eq_slice_append cs h2
  unfold joinClusters
  rw [e1, e2, List.flatten_append, List.flatten_append, List.append_assoc]

theorem drop_length_eq_nil {α : Type} (l : List α) {n i : Nat} (hn : l.length = n) (h : n ≤ i) :
    l.drop i = [] := List.drop_eq_nil_of_le (by omega)

theorem wrapLoop_join (m : Metric) (L : Int) (cs : List Cluster) (ss : List Nat)
    (os : List Opp) (n : Nat) (hn : cs.length = n) (hss : ss.length = n)
    (hos : ∀ o ∈ os, o.pos ≤ o.next ∧ o.next ≤ n) :
    ∀ (fuel i : Nat), n - i ≤ fuel →
      joinLines (wrapLoop m L cs ss os n fuel i) = joinClusters (cs.drop i) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i hi
    simp only [wrapLoop, joinLines, List.map_nil, List.flatten_nil]
    rw [drop_length_eq_nil cs hn (by omega)]
    rfl
  | succ fuel ih =>
    intro i hi
    unfold wrapLoop
    by_cases hin : i < n
    · simp only [hin, ↓reduceIte]
      have hne : ss.drop i ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        omega
      obtain ⟨hk1, hk2, _⟩ := lineLen_spec m L (ss.drop i) hne
      have hlen : (ss.drop i).length = n - i := by simp [hss]
      by_cases hj : i + lineLen m L (ss.drop i) = n
      · simp only [hj, ↓reduceIte]
        simp only [joinLines, finalLine, mkLine, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil]
        have ht := spaceRun_le (cs.drop i).reverse
        simp only [List.length_reverse, List.length_drop, hn] at ht
        split
        · rename_i hr
          have := join_chain cs (i := i) (a := n - spaceRun (cs.drop i).reverse) (b := n)
            (by omega) (by omega)
          rw [← this, drop_length_eq_nil cs hn (Nat.le_refl n)]
          simp [joinClusters]
        · have := join_chain cs (i := i) (a := n) (b := n) (by omega) (by omega)
          rw [← this, drop_length_eq_nil cs hn (Nat.le_refl n)]
          simp [joinClusters, slice_self]
      · simp only [hj, ↓reduceIte]
        split
        · rename_i o ho
          obtain ⟨hom, hoi, hoj⟩ := lastOpp_spec i _ os o ho
          obtain ⟨hp, hq⟩ := hos o hom
          simp only [joinLines, mkLine, List.map_cons, List.flatten_cons]
          have hrec := ih o.next (by omega)
          unfold joinLines at hrec
          rw [hrec]
          have := join_chain cs (i := i) (a := o.pos) (b := o.next) (by omega) hp
          rw [← this, List.append_assoc]
        · simp only [joinLines, mkLine, List.map_cons, List.flatten_cons]
          have hrec := ih (i + lineLen m L (ss.drop i)) (by omega)
          unfold joinLines at hrec
          rw [hrec]
          have := join_chain cs (i := i) (a := i + lineLen m L (ss.drop i))
            (b := i + lineLen m L (ss.drop i)) (by omega) (by omega)
          rw [← this]
    · simp only [hin, ↓reduceIte]
      rw [drop_length_eq_nil cs hn (by omega)]
      rfl

/-- The text of a wrapped line is the text of its lines and separators, in order. -/
theorem wrapCore_preserves_text (m : Metric) (L : Int) (s : List Char) :
    joinLines (wrapCore m L s) = s := by
  unfold wrapCore wrapClusters
  rw [wrapLoop_join m L (segment s) _ _ _ rfl (by simp) (fun o ho => ?_) _ _ (by omega)]
  · simpa using segment_concat s
  · have := opps_wf (segment s) o ho
    exact ⟨this.1, Nat.le_of_lt this.2⟩

theorem wrap_preserves_text {m : Metric} {L : Int} {s : List Char} {ls : List Line}
    (h : wrap m L s = .ok ls) : joinLines ls = s := by
  rw [(wrap_ok h).2]
  exact wrapCore_preserves_text m L s

theorem wrapLoop_mkLine (m : Metric) (L : Int) (cs : List Cluster) (ss : List Nat)
    (os : List Opp) (n : Nat) :
    ∀ (fuel i : Nat) (l : Line), l ∈ wrapLoop m L cs ss os n fuel i →
      ∃ a b c d, l = mkLine m cs ss a b c d := by
  intro fuel
  induction fuel with
  | zero => intro i l hl; simp [wrapLoop] at hl
  | succ fuel ih =>
    intro i l hl
    unfold wrapLoop at hl
    by_cases hin : i < n
    · simp only [hin, ↓reduceIte] at hl
      by_cases hj : i + lineLen m L (ss.drop i) = n
      · simp only [hj, ↓reduceIte, List.mem_singleton] at hl
        subst hl
        exact ⟨_, _, _, _, rfl⟩
      · simp only [hj, ↓reduceIte] at hl
        split at hl
        · simp only [List.mem_cons] at hl
          rcases hl with hl | hl
          · exact ⟨_, _, _, _, hl⟩
          · exact ih _ l hl
        · simp only [List.mem_cons] at hl
          rcases hl with hl | hl
          · exact ⟨_, _, _, _, hl⟩
          · exact ih _ l hl
    · simp only [hin, ↓reduceIte] at hl
      simp at hl

theorem mkLine_fit {m : Metric} (hm : m.WF) {L : Int} (cs : List Cluster) (ss : List Nat)
    {n i e k : Nat} (hn : cs.length = n) (hik : i + k ≤ n) (hie : i < e) (hek : e ≤ i + k)
    (hk : k = 1 ∨ spanWidth m ((ss.drop i).take k).sum ≤ L) (a b : Nat) :
    (mkLine m cs ss i e a b).width ≤ L ∨
      ∃ x, x + 1 ≤ cs.length ∧
        (mkLine m cs ss i e a b).text = joinClusters (slice cs x (x + 1)) := by
  rcases hk with hk | hk
  · subst hk
    right
    refine ⟨i, by omega, ?_⟩
    have : e = i + 1 := by omega
    subst this
    rfl
  · left
    show spanWidth m (slice ss i e).sum ≤ L
    have h1 := slice_sum_mono ss i hek
    have h2 : slice ss i (i + k) = (ss.drop i).take k := by simp [slice]
    rw [h2] at h1
    exact Int.le_trans (spanWidth_mono hm h1) hk

theorem wrapLoop_fit {m : Metric} (hm : m.WF) (L : Int) (cs : List Cluster) (ss : List Nat)
    (os : List Opp) (n : Nat) (hn : cs.length = n) (hss : ss.length = n) :
    ∀ (fuel i : Nat) (l : Line), l ∈ wrapLoop m L cs ss os n fuel i →
      l.width ≤ L ∨ ∃ x, x + 1 ≤ cs.length ∧ l.text = joinClusters (slice cs x (x + 1)) := by
  intro fuel
  induction fuel with
  | zero => intro i l hl; simp [wrapLoop] at hl
  | succ fuel ih =>
    intro i l hl
    unfold wrapLoop at hl
    by_cases hin : i < n
    · simp only [hin, ↓reduceIte] at hl
      have hne : ss.drop i ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        omega
      obtain ⟨hk1, hk2, hk3⟩ := lineLen_spec m L (ss.drop i) hne
      have hlen : (ss.drop i).length = n - i := by simp [hss]
      by_cases hj : i + lineLen m L (ss.drop i) = n
      · simp only [hj, ↓reduceIte, List.mem_singleton] at hl
        subst hl
        have ht := spaceRun_le (cs.drop i).reverse
        simp only [List.length_reverse, List.length_drop, hn] at ht
        dsimp only [finalLine]
        refine mkLine_fit hm cs ss hn (k := lineLen m L (ss.drop i)) (by omega) ?_ ?_ hk3 _ _
        · split <;> omega
        · split <;> omega
      · simp only [hj, ↓reduceIte] at hl
        split at hl
        · rename_i o ho
          obtain ⟨hom, hoi, hoj⟩ := lastOpp_spec i _ os o ho
          simp only [List.mem_cons] at hl
          rcases hl with hl | hl
          · subst hl
            exact mkLine_fit hm cs ss hn (by omega) hoi hoj hk3 _ _
          · exact ih _ l hl
        · simp only [List.mem_cons] at hl
          rcases hl with hl | hl
          · subst hl
            exact mkLine_fit hm cs ss hn (by omega) (by omega) (Nat.le_refl _) hk3 _ _
          · exact ih _ l hl
    · simp only [hin, ↓reduceIte] at hl
      simp at hl

/-- Every line and every separator is the concatenation of a contiguous slice of the clusters. -/
theorem wrap_no_cluster_split {m : Metric} {L : Int} {s : List Char} {ls : List Line}
    (h : wrap m L s = .ok ls) :
    ∀ l ∈ ls, (∃ a b, l.text = joinClusters (slice (segment s) a b)) ∧
      (∃ c d, l.sep = joinClusters (slice (segment s) c d)) := by
  intro l hl
  rw [(wrap_ok h).2] at hl
  unfold wrapCore wrapClusters at hl
  obtain ⟨a, b, c, d, hl⟩ := wrapLoop_mkLine m L _ _ _ _ _ _ l hl
  subst hl
  exact ⟨⟨a, b, rfl⟩, ⟨c, d, rfl⟩⟩

/-- Every line has width at most `L`, or consists of exactly one cluster. -/
theorem wrap_lines_fit {m : Metric} {L : Int} {s : List Char} {ls : List Line}
    (h : wrap m L s = .ok ls) :
    ∀ l ∈ ls, l.width ≤ L ∨
      ∃ x, x + 1 ≤ (segment s).length ∧ l.text = joinClusters (slice (segment s) x (x + 1)) := by
  intro l hl
  obtain ⟨hm, h⟩ := wrap_ok h
  rw [h] at hl
  unfold wrapCore wrapClusters at hl
  exact wrapLoop_fit hm L (segment s) _ _ _ rfl (by simp) _ _ l hl

/-! ### Reference values

Checked when the module is built; each equals the value of the Go twin `internal/measure`. -/

#guard (do let m ← Role.metric .label; textWidth m "Start".toList).toOption == some 2086
#guard (do let m ← Role.metric .label; textWidth m "Choice".toList).toOption == some 3041
#guard (do let m ← Role.metric .label; textWidth m "yes".toList).toOption == some 1550
#guard cellWidth "alpha beta-gamma 日本語テキスト".toList == 31
#guard (segment [Char.ofNat 0x1F1E6, Char.ofNat 0x1F1E7, Char.ofNat 0x1F1E8, Char.ofNat 0x1F1E9,
    Char.ofNat 0x1F1EA]).map (·.map Char.toNat) ==
  [[0x1F1E6, 0x1F1E7], [0x1F1E8, 0x1F1E9], [0x1F1EA]]
#guard ((wrap Metric.cell 8 "alpha beta-gamma 日本語テキスト".toList).toOption.map
    fun ls => ls.map fun l => (String.ofList l.text, String.ofList l.sep, l.width)) ==
  some [("alpha", " ", 5), ("beta-", "", 5), ("gamma 日", "", 8), ("本", "", 2),
    ("語テキス", "", 8), ("ト", "", 2)]

end Elegant.Measure
