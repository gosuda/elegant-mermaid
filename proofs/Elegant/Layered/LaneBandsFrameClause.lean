import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsCoverage
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands
/- Falsity witness for the planned `pinPairGeometry_of_cover` replacement
(`history://PinPairGeometryFinishT`): it is FALSE as stated because the loose
band's shift overflows its band by `clear`, so a lane member and a loose box
in different bands have neither the same shift nor ordered containment in
both band bounds, while C8a still holds through member-interval ordering.

Executed witness (`proofs/wip/Probe/PinC8aFalsityProbe.lean`, model
`[lane "A", node "a1" in "A", loose "l1"]`, route `a1 -> l1`):
`bands = [A@[1024, 11390] shift 3072, ""@[11390, 13540] shift 5120]`,
`title = 1280`, `clear = 1792`; box shifts `A -> 3072`, `a1 -> 3072`,
`l1 -> 5120` (different shifts, so the common-translation disjunct fails);
shifted `l1 = [13182, 15332]` starts at/after `11390` (lower holds) but ends
past `13540` by exactly `clear` (upper fails), and no other band contains it
(lane `A` ends at `11390`). Hence the two-disjunct `pinPairGeometry`
conclusion fails for the unrelated lane/loose pair, while the C8a clause
holds via lane-upper ordering plus the loose lower bound. The restated
`pinBands_c8a` below concludes `Disjoint` directly from the member intervals
and never uses the second disjunct of `pinPairGeometry`. -/

/-- Scene parents mirror model parents, and every band frame present in the
scene is an ancestor-or-self of its member scene boxes along scene parents.
The first conjunct ties each scene box to the model parent chain that
`inLane`/`lanesOf` read; the second puts every present frame into the scope
of routes between its members. The guard is occurrence in `s.boxes`, not
`band.id ≠ ""`: the loose band (`id = ""`) is vacuously exempt exactly when
no scene box is named `""` (the executed case), while a scene containing a
box named `""` must still satisfy the ancestor clause for the loose band,
since `replaceFrame` would stretch that box. Statement is identical to
`PinSceneParents` in `LaneBandsApplyPinKeptClearProof.lean` so one executed
proof serves both. -/
def PinSceneParents (boxes : List ModelBox) (s : Scene) (bands : List Band) : Prop :=
  (∀ mb ∈ boxes, mb.parent ≠ "" → ∀ sb ∈ s.boxes, sb.id = mb.id → sb.parent = mb.parent) ∧
  (∀ band ∈ bands, (∃ b ∈ s.boxes, b.id = band.id) →
    ∀ mid ∈ band.members, mid = band.id ∨ band.id ∈ s.layoutDump.ancestors mid)


/-- Equal `(id, parent)` box sequences give equal parent lookups. -/
private theorem boxParent_eq_of_pairs {l₁ l₂ : List Box} (id : String)
    (h : l₁.map (fun b => (b.id, b.parent)) = l₂.map (fun b => (b.id, b.parent))) :
    (l₁.find? (fun b => b.id == id)).map (fun b => b.parent) =
      (l₂.find? (fun b => b.id == id)).map (fun b => b.parent) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a₁ t₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons a₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hp, hrest⟩ := h
      injection hp with hid hpar
      by_cases hc : (a₁.id == id) = true
      · have hc2 : (a₂.id == id) = true := by rw [← hid]; exact hc
        simp only [List.find?, hc, hc2, Option.map_some, hpar]
      · have hc2 : ¬((a₂.id == id) = true) := by rw [← hid]; exact hc
        simp only [List.find?, hc, hc2]
        exact ih hrest

/-- Ancestor lists agree when the `(id, parent)` sequences of the box lists
agree (the fuel is the common length). -/
private theorem ancestors_eq_of_pairs {d₁ d₂ : LayoutDump} (x : String)
    (h : d₁.boxes.map (fun b => (b.id, b.parent)) =
      d₂.boxes.map (fun b => (b.id, b.parent))) :
    d₁.ancestors x = d₂.ancestors x := by
  have hgo : ∀ fuel : Nat, ∀ y : String,
      LayoutDump.ancestors.go d₁ fuel y = LayoutDump.ancestors.go d₂ fuel y := by
    intro fuel
    induction fuel with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      have hpar := boxParent_eq_of_pairs (l₁ := d₁.boxes) (l₂ := d₂.boxes) y h
      simp only [LayoutDump.ancestors.go, LayoutDump.box?]
      cases h1 : d₁.boxes.find? (fun b => b.id == y) with
      | none =>
        have hm : (d₁.boxes.find? (fun b => b.id == y)).map (fun b => b.parent) = none := by
          rw [h1]; rfl
        rw [hm] at hpar
        cases h2 : d₂.boxes.find? (fun b => b.id == y) with
        | none => rfl
        | some _b₂ => rw [h2] at hpar; simp at hpar
      | some b₁ =>
        have hm : (d₁.boxes.find? (fun b => b.id == y)).map (fun b => b.parent) =
            some b₁.parent := by
          rw [h1]; rfl
        rw [hm] at hpar
        cases h2 : d₂.boxes.find? (fun b => b.id == y) with
        | none => rw [h2] at hpar; simp at hpar
        | some b₂ =>
          rw [h2] at hpar
          simp only [Option.map_some, Option.some.injEq] at hpar
          dsimp only
          by_cases hp : b₁.parent = ""
          · have hp2 : b₂.parent = "" := by rw [← hpar]; exact hp
            simp [hp, hp2]
          · have hp2 : b₂.parent ≠ "" := by rw [← hpar]; exact hp
            simp only [hp, hp2, ↓reduceIte]
            rw [hpar]
            exact congrArg (fun t => b₂.parent :: t) (ih b₂.parent)
  have hlen : d₁.boxes.length = d₂.boxes.length := by
    simpa only [List.length_map] using congrArg List.length h
  unfold LayoutDump.ancestors
  rw [hlen]
  exact hgo _ x

/-- Shifting two rectangles by the same amount along one axis preserves
disjointness. -/
private theorem disjoint_withStart {axis : Axis} {a b : Rect} {da db : Int}
    (h : da = db) (hD : Disjoint a b) :
    Disjoint (axis.withStart a (axis.start a + da))
      (axis.withStart b (axis.start b + db)) := by
  subst h
  cases axis with
  | x =>
    unfold Disjoint Rect.meetsInterior at hD ⊢
    simp only [Axis.withStart, Axis.start]
    omega
  | y =>
    unfold Disjoint Rect.meetsInterior at hD ⊢
    simp only [Axis.withStart, Axis.start]
    omega

/-- Two rectangles whose axis intervals lie in ordered band intervals are
disjoint. -/
private theorem disjoint_of_bands {axis : Axis} {a b : Rect} {lg hg lb hb : Int}
    (h1 : lg ≤ axis.start a) (h2 : axis.start a + axis.length a ≤ hg)
    (h3 : lb ≤ axis.start b) (h4 : axis.start b + axis.length b ≤ hb)
    (hord : hg ≤ lb ∨ hb ≤ lg) : Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  cases axis with
  | x =>
    simp only [Axis.start, Axis.length] at *
    rcases hord with h | h <;> omega
  | y =>
    simp only [Axis.start, Axis.length] at *
    rcases hord with h | h <;> omega

/-- The clause reads only the box list, so equal box lists give equal `C8a`. -/
private theorem c8a_of_boxes_eq {A B : Scene}
    (hboxes : B.boxes = A.boxes) (h : Validator.C8a A.layoutDump) :
    Validator.C8a B.layoutDump := by
  have hanc : ∀ x : String, B.layoutDump.ancestors x = A.layoutDump.ancestors x := by
    intro x
    refine ancestors_eq_of_pairs x ?_
    show B.boxes.map (fun b => (b.id, b.parent)) =
      A.boxes.map (fun b => (b.id, b.parent))
    rw [hboxes]
  intro g hg hrole b hb hne hnot1 hnot2
  have hgB : g ∈ B.boxes := hg
  have hbB : b ∈ B.boxes := hb
  rw [hboxes] at hgB hbB
  have h1 : g.id ∉ A.layoutDump.ancestors b.id := by
    rw [← hanc b.id]; exact hnot1
  have h2 : b.id ∉ A.layoutDump.ancestors g.id := by
    rw [← hanc g.id]; exact hnot2
  exact h g hgB hrole b hbB hne h1 h2

/-- `spacingOf` titles and clearances are non-negative on both profiles. -/
theorem spacing_of_nonneg {profile : Profile} {sp : Spacing}
    (h : spacingOf profile = .ok sp) : 0 ≤ sp.title ∧ 0 ≤ sp.clear := by
  cases profile with
  | vector =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h
      LayoutConst.cluster_pad LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩
  | cell =>
    unfold spacingOf LayoutConst.slot LayoutConst.line_h
      LayoutConst.cluster_pad LayoutConst.Pair.get at h
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by decide, by decide⟩

/-- The loose band is never negative: empty content gives thickness zero,
otherwise the bounds are ordered. -/
theorem looseBand_thickness_nonneg (boxes : List ModelBox) (s : Scene)
    (axis : Axis) (sp : Spacing) (loose : List String) (start : Int) :
    0 ≤ (looseBand boxes s axis sp loose start).thickness := by
  unfold looseBand
  cases h : bounds (contentValues boxes s axis "" loose) with
  | none => simp
  | some p =>
    cases p with
    | mk lo hi =>
      have hle : lo ≤ hi := bounds_le (by simpa using h)
      simp only
      omega

/-- Every lane band in a `layLanes` fold is non-negative when the spacing is. -/
theorem layLanes_thickness_nonneg (boxes : List ModelBox) (s : Scene)
    (axis : Axis) (sp : Spacing) (lanes : List String) (start : Int)
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear) :
    ∀ b ∈ layLanes boxes s axis sp lanes start, 0 ≤ b.thickness := by
  induction lanes generalizing start with
  | nil =>
    intro b hb
    simp [layLanes] at hb
  | cons lane rest ih =>
    intro b hb
    simp only [layLanes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · have h := laneBand_thickness_nonneg boxes s axis sp lane start ht hc
      simpa [laneBand] using h
    · exact ih (start + (laneBand boxes s axis sp lane start).thickness) b hb

/-- Every band of `layBands` is non-negative when the spacing is. -/
theorem layBands_thickness_nonneg (boxes : List ModelBox) (s : Scene)
    (axis : Axis) (sp : Spacing) (lanes : List String)
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear) :
    ∀ b ∈ layBands boxes s axis sp lanes, 0 ≤ b.thickness := by
  unfold layBands
  simp only
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact layLanes_thickness_nonneg boxes s axis sp lanes _ ht hc
  · simp only [hl, ↓reduceIte, Bool.false_eq_true]
    intro b hb
    rw [List.mem_append] at hb
    rcases hb with hb | hb
    · exact layLanes_thickness_nonneg boxes s axis sp lanes _ ht hc b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact looseBand_thickness_nonneg boxes s axis sp _ _

/-- Every band of a tiling starts at or after the tiling start. -/
theorem tiled_all_start_ge {start : Int} {bands : List Band}
    (h : Tiled start bands) (hnonneg : ∀ b ∈ bands, 0 ≤ b.thickness)
    {c : Band} (hmem : c ∈ bands) : start ≤ c.start := by
  induction bands generalizing start with
  | nil => simp at hmem
  | cons b bs ih =>
    obtain ⟨hstart, htail⟩ := h
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · omega
    · have hbpos : 0 ≤ b.thickness := hnonneg b (List.mem_cons.mpr (Or.inl rfl))
      have htailNonneg : ∀ x ∈ bs, 0 ≤ x.thickness := by
        intro x hx
        exact hnonneg x (List.mem_cons.mpr (Or.inr hx))
      have hle := ih (start := start + b.thickness) htail htailNonneg hmem
      omega

/-- A later band starts at or after the end of the head band. -/
theorem tiled_head_le {start : Int} {b : Band} {bs : List Band} {c : Band}
    (h : Tiled start (b :: bs))
    (hnonneg : ∀ x ∈ b :: bs, 0 ≤ x.thickness) (hmem : c ∈ bs) :
    b.start + b.thickness ≤ c.start := by
  obtain ⟨hstart, htail⟩ := h
  have htailNonneg : ∀ x ∈ bs, 0 ≤ x.thickness := by
    intro x hx
    exact hnonneg x (List.mem_cons.mpr (Or.inr hx))
  have hge := tiled_all_start_ge (start := start + b.thickness) htail htailNonneg hmem
  omega

/-- Distinct bands of a non-negative tiling have ordered cross intervals. -/
theorem tiled_ordered {start : Int} {bands : List Band}
    (h : Tiled start bands) (hnonneg : ∀ b ∈ bands, 0 ≤ b.thickness)
    {dg db : Band} (hg : dg ∈ bands) (hb : db ∈ bands) (hne : dg ≠ db) :
    dg.start + dg.thickness ≤ db.start ∨
      db.start + db.thickness ≤ dg.start := by
  induction bands generalizing start with
  | nil =>
    simp at hg
  | cons b bs ih =>
    obtain ⟨hstart, htail⟩ := h
    rw [List.mem_cons] at hg hb
    rcases hg with rfl | hg <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · exact Or.inl (tiled_head_le ⟨hstart, htail⟩ hnonneg hb)
    · exact Or.inr (tiled_head_le ⟨hstart, htail⟩ hnonneg hg)
    · have htailNonneg : ∀ x ∈ bs, 0 ≤ x.thickness := by
        intro x hx
        exact hnonneg x (List.mem_cons.mpr (Or.inr hx))
      exact ih (start := start + b.thickness) htail htailNonneg hg hb

/-- A `foldl min` is below every element of the folded list. -/
theorem foldl_min_le_mem {l : List Int} {init x : Int}
    (hmem : x ∈ l) : l.foldl min init ≤ x := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons a rest ih =>
    rw [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with hEq | hmem
    · rw [hEq]
      have hle : rest.foldl min (min init a) ≤ min init a :=
        foldl_min_le rest (min init a)
      omega
    · exact ih (init := min init a) hmem

/-- A `foldl max` is above every element of the folded list. -/
theorem foldl_max_ge_mem {l : List Int} {init x : Int}
    (hmem : x ∈ l) : x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at hmem
  | cons a rest ih =>
    rw [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with hEq | hmem
    · rw [hEq]
      have hle : max init a ≤ rest.foldl max (max init a) :=
        le_foldl_max rest (max init a)
      omega
    · exact ih (init := max init a) hmem

/-- Every element of a bounded list lies between its bounds. -/
theorem bounds_mem {vs : List Int} {lo hi x : Int}
    (h : bounds vs = some (lo, hi)) (hmem : x ∈ vs) : lo ≤ x ∧ x ≤ hi := by
  cases vs with
  | nil => simp [bounds] at h
  | cons v rest =>
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨foldl_min_le _ _, le_foldl_max _ _⟩
    · exact ⟨foldl_min_le_mem hmem, foldl_max_ge_mem hmem⟩

/-- Two lanes containing the same box coincide: `laneOf` returns one root. -/
theorem inLane_unique {boxes : List ModelBox} {id lane1 lane2 : String}
    (h1 : inLane boxes id lane1 = true) (h2 : inLane boxes id lane2 = true) :
    lane1 = lane2 := by
  unfold inLane at h1 h2
  cases h : laneOf boxes id with
  | none => simp [h] at h1
  | some p =>
    cases p with
    | mk found isGroup =>
      simp only [h, Bool.and_eq_true, beq_iff_eq] at h1 h2
      obtain ⟨hg1, e1⟩ := h1
      obtain ⟨hg2, e2⟩ := h2
      rw [← e1, ← e2]

/-- `find?` over a nodup model-id list returns the unique box with that id. -/
theorem modelFind?_eq_self {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup)
    {x : ModelBox} (hx : x ∈ boxes) : boxes.find? (fun b => b.id == x.id) = some x := by
  induction boxes with
  | nil => simp at hx
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, hrest⟩ := hn
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne : first.id ≠ x.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      have hfind : (first.id == x.id) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.find?, hfind, ih hrest hx]

/-- A loose node is in no lane: its root is itself with `isGroup = false`. -/
theorem loose_not_inLane {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup)
    {id lane : String} (hmem : id ∈ looseNodes boxes) :
    inLane boxes id lane = false := by
  unfold looseNodes at hmem
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
  obtain ⟨hmbmem, hpred⟩ := List.mem_filter.mp hmb
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hpar', hrole'⟩ := hpred
  have hpar : mb.parent = "" := beq_iff_eq.mp hpar'
  have hrole : mb.role = .node := beq_iff_eq.mp hrole'
  have heq : mb.id = id := hid
  have hfind : boxes.find? (fun b => b.id == id) = some mb := by
    have hx : mb ∈ boxes := hmbmem
    rw [← heq]
    exact modelFind?_eq_self hn hx
  simp [inLane, laneOf, laneOfAux, hfind, hpar, hrole]

/-- Membership in a lane band means `inLane` holds for that lane. -/
theorem laneBand_mem_inLane {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane id : String} {start : Int}
    (hmem : id ∈ (laneBand boxes s axis sp lane start).members) :
    inLane boxes id lane = true := by
  unfold laneBand at hmem
  simp only at hmem
  obtain ⟨mb, hmb, hid⟩ := List.mem_map.mp hmem
  obtain ⟨hmbmem, hpred⟩ := List.mem_filter.mp hmb
  have htrue : inLane boxes mb.id lane = true := by
    simpa using hpred
  rw [hid] at htrue
  exact htrue



/-- A lane band member in another lane's band forces the lanes equal. -/
theorem laneBand_mem_unique {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane1 lane2 : String} {start1 start2 : Int} {id : String}
    (h1 : id ∈ (laneBand boxes s axis sp lane1 start1).members)
    (h2 : id ∈ (laneBand boxes s axis sp lane2 start2).members) :
    lane1 = lane2 := by
  exact inLane_unique (laneBand_mem_inLane h1) (laneBand_mem_inLane h2)

/-- Loose members are in no lane band. -/
theorem loose_lane_members_disjoint {boxes : List ModelBox} (hn : (boxes.map (fun b => b.id)).Nodup)
    {s : Scene} {axis : Axis} {sp : Spacing} {lane : String} {start : Int} {id : String}
    (hloose : id ∈ looseNodes boxes)
    (hlane : id ∈ (laneBand boxes s axis sp lane start).members) : False := by
  have hfalse : inLane boxes id lane = false := loose_not_inLane hn hloose
  have htrue : inLane boxes id lane = true := laneBand_mem_inLane hlane
  rw [hfalse] at htrue
  cases htrue


/-- Lane ids inherit nodup from model ids. -/
theorem lanesOf_nodup {boxes : List ModelBox} :
    (boxes.map (fun b => b.id)).Nodup → (lanesOf boxes).Nodup := by
  induction boxes with
  | nil => intro _; simp [lanesOf]
  | cons b rest ih =>
    intro h
    have htail : (rest.map (fun b => b.id)).Nodup := (List.nodup_cons.mp h).2
    have hrest := ih htail
    have hnot : b.id ∉ rest.map (fun b => b.id) := (List.nodup_cons.mp h).1
    by_cases hp : (b.role == .group && b.parent == "") = true
    · have hne : b.id ∉ ((rest.filter fun b => b.role == .group && b.parent == "").map
          (fun b => b.id)) := by
        intro hmem
        obtain ⟨x, hxm, hidx⟩ := List.mem_map.mp hmem
        obtain ⟨hx, _⟩ := List.mem_filter.mp hxm
        have hmem' : x.id ∈ rest.map (fun b => b.id) := List.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hidx] at hmem'
        exact hnot hmem'
      have heq : lanesOf (b :: rest) = b.id ::
          ((rest.filter fun b => b.role == .group && b.parent == "").map (fun b => b.id)) := by
        simp [lanesOf, hp]
      rw [heq]
      exact List.nodup_cons.mpr ⟨hne, hrest⟩
    · have hpF : (b.role == .group && b.parent == "") = false := by
        cases he : (b.role == .group && b.parent == "") with
        | true => exact absurd he hp
        | false => rfl
      have heq : lanesOf (b :: rest) =
          ((rest.filter fun b => b.role == .group && b.parent == "").map (fun b => b.id)) := by
        simp [lanesOf, hpF]
      rw [heq]
      exact hrest



/-- Every `layLanes` band is a `laneBand` for its lane. -/
theorem layLanes_mem_lane {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {start : Int} {band : Band}
    (hmem : band ∈ layLanes boxes s axis sp lanes start) :
    ∃ lane ∈ lanes, ∃ st : Int, band = laneBand boxes s axis sp lane st := by
  induction lanes generalizing start with
  | nil => simp [layLanes] at hmem
  | cons lane rest ih =>
    simp only [layLanes] at hmem
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ⟨lane, List.mem_cons.mpr (Or.inl rfl), start, rfl⟩
    · obtain ⟨l, hl, st, rfl⟩ := ih hmem
      exact ⟨l, List.mem_cons.mpr (Or.inr hl), st, rfl⟩

/-- Every `layLanes` band id is a lane. -/
theorem layLanes_id_mem {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {start : Int} {band : Band}
    (hmem : band ∈ layLanes boxes s axis sp lanes start) : band.id ∈ lanes := by
  obtain ⟨lane, hl, st, rfl⟩ := layLanes_mem_lane hmem
  exact hl

/-- `find?` over a nodup band-id list returns the unique band with that id. -/
theorem bandFind?_eq_self {bands : List Band} (hn : (bands.map (fun b => b.id)).Nodup)
    {x : Band} (hx : x ∈ bands) : bands.find? (fun b => b.id == x.id) = some x := by
  induction bands with
  | nil => simp at hx
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, hrest⟩ := hn
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne : first.id ≠ x.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      have hfind : (first.id == x.id) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.find?, hfind, ih hrest hx]

/-- A band covering predicate as a proposition. -/
def bandCovers (band : Band) (id : String) : Prop :=
  band.id = id ∨ id ∈ band.members

/-- The `bandShift` predicate is true exactly for covering bands. -/
theorem bandShift_pred_true {band : Band} {id : String}
    (h : bandCovers band id) : (band.id == id || band.members.contains id) = true := by
  rcases h with hEq | hmem
  · simp [hEq]
  · simp [List.contains_eq_mem, hmem]

/-- The `bandShift` predicate is false for non-covering bands. -/
theorem bandShift_pred_false {band : Band} {id : String}
    (h : ¬ bandCovers band id) :
    (band.id == id || band.members.contains id) = false := by
  have h1 : band.id ≠ id := by
    intro heq
    exact h (Or.inl heq)
  have h2 : id ∉ band.members := by
    intro hmem
    exact h (Or.inr hmem)
  simp [beq_eq_false_iff_ne.mpr h1, List.contains_eq_mem, h2]






/-- `find?` over a nodup scene-id list returns the unique box with that id. -/
theorem sceneFind?_eq_self {boxes : List Box} (hn : (boxes.map (fun b => b.id)).Nodup)
    {x : Box} (hx : x ∈ boxes) : boxes.find? (fun b => b.id == x.id) = some x := by
  induction boxes with
  | nil => simp at hx
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    obtain ⟨hfresh, hrest⟩ := hn
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have hne : first.id ≠ x.id := by
        intro heq
        exact hfresh (List.mem_map.mpr ⟨x, hx, heq.symm⟩)
      have hfind : (first.id == x.id) = false := beq_eq_false_iff_ne.mpr hne
      simp [List.find?, hfind, ih hrest hx]

/-- A member's cross endpoints appear in `contentValues`. -/
theorem contentValues_mem_start {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {lane : String} {members : List String} {b : Box}
    (hmem : b.id ∈ members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    axis.start b.rect ∈ contentValues boxes s axis lane members ∧
      axis.start b.rect + axis.length b.rect ∈ contentValues boxes s axis lane members := by
  unfold contentValues
  have hmemMap : axis.start b.rect ∈ members.flatMap (fun id =>
      match s.boxes.find? (fun b' => b'.id == id) with
      | none => ([] : List Int)
      | some bb => [axis.start bb.rect, axis.start bb.rect + axis.length bb.rect]) := by
    rw [List.mem_flatMap]
    exact ⟨b.id, hmem, by simp [hfind]⟩
  have hmemMap2 : axis.start b.rect + axis.length b.rect ∈ members.flatMap (fun id =>
      match s.boxes.find? (fun b' => b'.id == id) with
      | none => ([] : List Int)
      | some bb => [axis.start bb.rect, axis.start bb.rect + axis.length bb.rect]) := by
    rw [List.mem_flatMap]
    exact ⟨b.id, hmem, by simp [hfind]⟩
  constructor
  · exact List.mem_append.mpr (Or.inl hmemMap)
  · exact List.mem_append.mpr (Or.inl hmemMap2)

/-- `layBands` splits into lane bands or the trailing loose band. -/

theorem layBands_mem_cases {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lanes : List String} {band : Band}
    (hmem : band ∈ layBands boxes s axis sp lanes) :
    band ∈ layLanes boxes s axis sp lanes (firstLaneStart s lanes axis) ∨
      band = looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s lanes axis + ((layLanes boxes s axis sp lanes
          (firstLaneStart s lanes axis)).map (fun b => b.thickness)).sum) := by
  unfold layBands at hmem
  simp only at hmem
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte] at hmem
    exact Or.inl hmem
  · simp only [hl, ↓reduceIte, Bool.false_eq_true] at hmem
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact Or.inl hmem
    · rw [List.mem_singleton] at hmem
      exact Or.inr hmem

/-- A lane member's cross interval lies within its band's content extent. -/
theorem laneMember_bounds {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {start : Int} {b : Box}
    (hmem : b.id ∈ (laneBand boxes s axis sp lane start).members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    ∃ lo hi : Int,
      bounds (contentValues boxes s axis lane
        ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id)) =
        some (lo, hi) ∧
      lo ≤ axis.start b.rect ∧ axis.start b.rect + axis.length b.rect ≤ hi := by
  have hmem' : b.id ∈ (boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id := by
    unfold laneBand at hmem
    simpa using hmem
  obtain ⟨hstart, hend⟩ := contentValues_mem_start hmem' hfind
  cases hc : contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) with
  | nil =>
    rw [hc] at hstart
    simp at hstart
  | cons v rest =>
    have hEq : bounds (v :: rest) = some (rest.foldl min v, rest.foldl max v) := rfl
    have hstart' : axis.start b.rect ∈ v :: rest := by rw [← hc]; exact hstart
    have hend' : axis.start b.rect + axis.length b.rect ∈ v :: rest := by
      rw [← hc]; exact hend
    obtain ⟨hlo1, _⟩ := bounds_mem (h := hEq) hstart'
    obtain ⟨_, hhi2⟩ := bounds_mem (h := hEq) hend'
    exact ⟨_, _, hEq, hlo1, hhi2⟩




/-- A lane member shifted by its band stays inside the band. -/
theorem laneMember_within {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {lane : String} {start : Int} {b : Box}
    (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    (hmem : b.id ∈ (laneBand boxes s axis sp lane start).members)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    let band := laneBand boxes s axis sp lane start
    let d := band.shift
    band.start ≤ axis.start b.rect + d ∧
      axis.start b.rect + axis.length b.rect + d ≤ band.start + band.thickness := by
  obtain ⟨lo, hi, hEq, hlo1, hhi2⟩ := laneMember_bounds (hmem := hmem) (hfind := hfind)
  unfold laneBand
  simp only
  have hExt : (bounds (contentValues boxes s axis lane
      ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id))).getD
      (start, start) = (lo, hi) := by
    simp [hEq]
  rw [hExt]
  simp only
  omega

/-- A loose member's endpoints lie within its content bounds. -/
theorem looseMember_bounds {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {loose : List String} {b : Box}
    (hmem : b.id ∈ loose)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    ∃ lo hi : Int,
      bounds (contentValues boxes s axis "" loose) = some (lo, hi) ∧
      lo ≤ axis.start b.rect ∧ axis.start b.rect + axis.length b.rect ≤ hi := by
  obtain ⟨hstart, hend⟩ := contentValues_mem_start (lane := "") (members := loose)
    (b := b) hmem hfind
  cases hc : contentValues boxes s axis "" loose with
  | nil =>
    rw [hc] at hstart
    simp at hstart
  | cons v rest =>
    have hEq : bounds (v :: rest) = some (rest.foldl min v, rest.foldl max v) := rfl
    have hstart' : axis.start b.rect ∈ v :: rest := by rw [← hc]; exact hstart
    have hend' : axis.start b.rect + axis.length b.rect ∈ v :: rest := by
      rw [← hc]; exact hend
    obtain ⟨hlo1, _⟩ := bounds_mem (h := hEq) hstart'
    obtain ⟨_, hhi2⟩ := bounds_mem (h := hEq) hend'
    exact ⟨_, _, hEq, hlo1, hhi2⟩

/-- A loose member shifted by its band starts at or after the band start. -/
theorem looseMember_lower {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {loose : List String} {start : Int} {b : Box}
    (hc : 0 ≤ sp.clear)
    (hmem : b.id ∈ loose)
    (hfind : s.boxes.find? (fun b' => b'.id == b.id) = some b) :
    let band := looseBand boxes s axis sp loose start
    band.start ≤ axis.start b.rect + band.shift := by
  obtain ⟨lo, hi, hEq, hlo1, _⟩ := looseMember_bounds (hmem := hmem) (hfind := hfind)
  unfold looseBand
  rw [hEq]
  simp only
  omega


/-- `bandShift` returns the unique covering band's shift. -/
theorem bandShift_eq {bands : List Band} {id : String} {band : Band}
    (hmem : band ∈ bands) (hcov : bandCovers band id)
    (hUniq : ∀ b1 ∈ bands, ∀ b2 ∈ bands,
      bandCovers b1 id → bandCovers b2 id → b1 = b2) :
    bandShift bands id = band.shift := by
  induction bands with
  | nil => simp at hmem
  | cons hd bs ih =>
    rw [List.mem_cons] at hmem
    rcases hmem with hEq | hmem
    · have hcovHd : bandCovers hd id := hEq ▸ hcov
      have hfind : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
          some hd := by simp only [List.find?_cons, bandShift_pred_true hcovHd]
      have hShiftEq : hd.shift = band.shift := by
        have h := congrArg Band.shift hEq
        exact h.symm
      unfold bandShift
      rw [hfind]
      simp [hShiftEq]
    · by_cases hc : bandCovers hd id
      · have heq : hd = band := hUniq hd (List.mem_cons.mpr (Or.inl rfl)) band
          (List.mem_cons.mpr (Or.inr hmem)) hc hcov
        have hfind : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
            some hd := by simp only [List.find?_cons, bandShift_pred_true hc]
        have hShiftEq : hd.shift = band.shift := by rw [heq]
        unfold bandShift
        rw [hfind]
        simp [hShiftEq]
      · have hfindFalse : (hd.id == id || hd.members.contains id) = false :=
          bandShift_pred_false hc
        have hfindEq : (hd :: bs).find? (fun b => b.id == id || b.members.contains id) =
            bs.find? (fun b => b.id == id || b.members.contains id) := by
          simp only [List.find?_cons, hfindFalse]
        have hUniqTail : ∀ b1 ∈ bs, ∀ b2 ∈ bs,
            bandCovers b1 id → bandCovers b2 id → b1 = b2 := by
          intro b1 hb1 b2 hb2 hc1 hc2
          exact hUniq b1 (List.mem_cons.mpr (Or.inr hb1)) b2
            (List.mem_cons.mpr (Or.inr hb2)) hc1 hc2
        have ih' := ih hmem hUniqTail
        unfold bandShift
        rw [hfindEq]
        exact ih'



/-- The per-pair geometry of the `applyPin` stage. For every pair of pinned
boxes there are source boxes with the same ids, parents, and roles; the
ancestor exclusions reflect down to the source scene; and for a pair of
distinct, unrelated boxes either it is a common translation along the pinning
axis, or each box's pinning-axis interval lies in a band interval, with the two
band intervals ordered. This names the
geometry of the pinning phase alone and concludes no disjointness of output
boxes. -/
def pinPairGeometry {pin : Pin} {bands : List Band} {s pinned : Scene} : Prop :=
  applyPin pin bands s = .ok pinned →
    ∀ g' ∈ pinned.boxes, ∀ b' ∈ pinned.boxes,
      ∃ gb ∈ s.boxes, ∃ bb ∈ s.boxes,
        g'.id = gb.id ∧ b'.id = bb.id ∧ g'.parent = gb.parent ∧
        b'.parent = bb.parent ∧ g'.role = gb.role ∧ b'.role = bb.role ∧
        (g'.id ∉ pinned.layoutDump.ancestors b'.id →
          gb.id ∉ s.layoutDump.ancestors bb.id) ∧
        (b'.id ∉ pinned.layoutDump.ancestors g'.id →
          bb.id ∉ s.layoutDump.ancestors gb.id) ∧
        (g'.id ∉ pinned.layoutDump.ancestors b'.id →
          b'.id ∉ pinned.layoutDump.ancestors g'.id → b'.id ≠ g'.id →
          (∃ d : Int,
            g'.rect = pin.axis.withStart gb.rect (pin.axis.start gb.rect + d) ∧
            b'.rect = pin.axis.withStart bb.rect (pin.axis.start bb.rect + d)) ∨
          (∃ dg ∈ bands, ∃ db ∈ bands,
            (dg.start + dg.thickness ≤ db.start ∨
              db.start + db.thickness ≤ dg.start) ∧
            dg.start ≤ pin.axis.start g'.rect ∧
            pin.axis.start g'.rect + pin.axis.length g'.rect ≤
              dg.start + dg.thickness ∧
            db.start ≤ pin.axis.start b'.rect ∧
            pin.axis.start b'.rect + pin.axis.length b'.rect ≤
              db.start + db.thickness))

/-- Splitting an `Except` bind at its `ok` value. -/
private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Two box lists with equal id and parent maps have equal `(id, parent)` maps. -/
private theorem map_pairs_of_two {l₁ l₂ : List Box}
    (hi : l₁.map (fun b => b.id) = l₂.map (fun b => b.id))
    (hp : l₁.map (fun b => b.parent) = l₂.map (fun b => b.parent)) :
    l₁.map (fun b => (b.id, b.parent)) = l₂.map (fun b => (b.id, b.parent)) := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at hi
  | cons a₁ t₁ ih =>
    cases l₂ with
    | nil => simp at hi
    | cons a₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at hi hp
      obtain ⟨hid, hi'⟩ := hi
      obtain ⟨hpar, hp'⟩ := hp
      simp only [List.map_cons, hid, hpar, ih hi' hp']

/-- The box stage of a successful uniform shift, as a `mapM` equation, and the
result's box list. -/
private theorem shiftAll_mapM_boxes {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    ∃ boxes, s.boxes.mapM (fun b : Box =>
      (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } :
        Except LayoutError Box)) = .ok boxes ∧ s'.boxes = boxes := by
  unfold shiftAll at h
  obtain ⟨boxes, hboxes, h⟩ := bind_ok h
  obtain ⟨labels, _hlabels, h⟩ := bind_ok h
  obtain ⟨routes, _hroutes, h⟩ := bind_ok h
  obtain ⟨items, _hitems, h⟩ := bind_ok h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨boxes, hboxes, rfl⟩

/-- Every box of a successful `mapM` shift keeps id, parent, and role and moves
by the exact checked sum. -/
private theorem shiftBoxesM_mem {axis : Axis} {delta : Int} :
    ∀ (l : List Box) (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant delta).rect axis b.rect } :
      Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + delta) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + delta := by
  intro l
  induction l with
  | nil =>
    intro l' h b' hb'
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    simp at hb'
  | cons head tail ih =>
    intro l' h b' hb'
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    rw [List.mem_cons] at hb'
    rcases hb' with hhead | hmem
    · subst hhead
      obtain ⟨hid, hpar, hrole, _hexcl, w, hw, heq, hval⟩ :=
        shiftBox_ok (axis := axis) (delta := delta) hfirst
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid, hpar, hrole, w, hw, heq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, hrole, w, hw, heq, hval⟩ := ih rest hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, w, hw, heq, hval⟩

/-- The box effect of the `restoreOrigin` stage: the `(id, parent)` sequence is
kept, and either the scene is unchanged or one uniform delta shifts every box
along the axis, keeping ids and roles. -/
theorem restoreOriginShift {axis : Axis} {routed origin : Scene}
    (h : restoreOrigin axis routed = .ok origin) :
    (origin.boxes.map (fun b => (b.id, b.parent)) =
      routed.boxes.map (fun b => (b.id, b.parent))) ∧
    (origin = routed ∨
      ∃ d : Int, ∀ b' ∈ origin.boxes, ∃ b ∈ routed.boxes,
        b'.id = b.id ∧ b'.role = b.role ∧
        b'.rect = axis.withStart b.rect (axis.start b.rect + d)) := by
  rcases restoreOrigin_cases h with heq | ⟨d, _hd, hshift⟩
  · refine ⟨?_, Or.inl heq⟩
    rw [heq]
  · obtain ⟨boxes, hboxes, hdest⟩ := shiftAll_mapM_boxes hshift
    have hids := shiftBoxes_maps routed.boxes axis d boxes hboxes
    obtain ⟨_hlen, hid, hpar, hrole, _hexcl⟩ := hids
    refine ⟨?_, Or.inr ⟨d, ?_⟩⟩
    · rw [hdest]
      exact map_pairs_of_two hid hpar
    · intro b' hb'
      rw [hdest] at hb'
      obtain ⟨b, hb, hidb, _hparb, hroleb, w, hw, heq, hval⟩ :=
        shiftBoxesM_mem routed.boxes boxes hboxes b' hb'
      exact ⟨b, hb, hidb, hroleb, by rw [heq, hval]⟩

/-- Transporting the clause through the origin restore: the routed scene has
the pinned boxes, the restore keeps the parent sequence, and a uniform shift
preserves every disjointness. -/
private theorem c8a_of_restore {axis : Axis} {routed origin pinned : Scene}
    (hbox : routed.boxes = pinned.boxes)
    (hpairs : origin.boxes.map (fun b => (b.id, b.parent)) =
      routed.boxes.map (fun b => (b.id, b.parent)))
    (hmove : origin = routed ∨
      ∃ d : Int, ∀ b' ∈ origin.boxes, ∃ b ∈ routed.boxes,
        b'.id = b.id ∧ b'.role = b.role ∧
        b'.rect = axis.withStart b.rect (axis.start b.rect + d))
    (h : Validator.C8a pinned.layoutDump) : Validator.C8a origin.layoutDump := by
  have hanc : ∀ x : String, origin.layoutDump.ancestors x = pinned.layoutDump.ancestors x := by
    intro x
    refine ancestors_eq_of_pairs x ?_
    show origin.boxes.map (fun b => (b.id, b.parent)) =
      pinned.boxes.map (fun b => (b.id, b.parent))
    rw [hpairs, hbox]
  rcases hmove with heq | ⟨d, hmem⟩
  · have hb : origin.boxes = pinned.boxes := by rw [heq]; exact hbox
    exact c8a_of_boxes_eq hb h
  · intro g' hg' hrole b' hb' hne hnot1 hnot2
    obtain ⟨gp, hgp, hidg, hroleg, hG⟩ := hmem g' hg'
    obtain ⟨bp, hbp, hidb, _hroleb, hB⟩ := hmem b' hb'
    have hgpP : gp ∈ pinned.boxes := by rw [← hbox]; exact hgp
    have hbpP : bp ∈ pinned.boxes := by rw [← hbox]; exact hbp
    have hgGroup : gp.role = "group" := by rw [← hroleg]; exact hrole
    have hneP : bp.id ≠ gp.id := by
      intro hEq
      apply hne
      rw [hidb, hidg]
      exact hEq
    have h1 : gp.id ∉ pinned.layoutDump.ancestors bp.id := by
      rw [← hidg, ← hidb, ← hanc b'.id]
      exact hnot1
    have h2 : bp.id ∉ pinned.layoutDump.ancestors gp.id := by
      rw [← hidb, ← hidg, ← hanc g'.id]
      exact hnot2
    have hDisj : Disjoint gp.rect bp.rect := h gp hgpP hgGroup bp hbpP hneP h1 h2
    rw [hG, hB]
    exact disjoint_withStart (axis := axis) (a := gp.rect) (b := bp.rect)
      (da := d) (db := d) rfl hDisj

/-- Chunk membership keeps the shift: any entry of a band chunk carries its shift. -/
private theorem ppg_chunk_mem_snd (bid : String) (bshift : Int) (members : List String)
    (e : String × Int)
    (h : e ∈ ((bid, bshift) :: members.map fun m => (m, bshift))) : e.2 = bshift := by
  simp only [List.mem_cons, List.mem_map] at h
  rcases h with rfl | ⟨m, _, rfl⟩
  · rfl
  · rfl

/-- A band chunk lookup is the band predicate: it finds `shift` exactly for covering ids. -/
private theorem ppg_chunk_find_map (bid : String) (bshift : Int) (members : List String)
    (id : String) :
    ((((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id)).map (·.2)) =
      if bid == id || members.contains id then some bshift else none := by
  by_cases hbid : (bid == id) = true
  · have hfind : ((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id) =
        some (bid, bshift) := by
      simp only [List.find?_cons, hbid]
    simp only [hfind, Option.map_some]
    have hcond : (bid == id || members.contains id) = true := by
      simp only [hbid, Bool.true_or]
    simp only [hcond, ite_true]
  · have hbidF : (bid == id) = false := by
      cases hb : (bid == id) with
      | true => exact absurd hb hbid
      | false => rfl
    by_cases hmem : members.contains id = true
    · have hcond : (bid == id || members.contains id) = true := by
        simp only [hbidF, hmem, Bool.or_true]
      simp only [hcond, ite_true]
      have hmem' : id ∈ members := List.contains_iff_mem.mp hmem
      have hin : (id, bshift) ∈ ((bid, bshift) :: members.map fun m => (m, bshift)) :=
        List.mem_cons_of_mem _ (List.mem_map.mpr ⟨id, hmem', rfl⟩)
      have hmeq : (((id, bshift)).1 == id) = true := beq_self_eq_true id
      have hne : (((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id)) ≠
          none := by
        intro hnone
        have hcon := List.find?_eq_none.mp hnone _ hin
        exact hcon hmeq
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp hne
      have hmemE : e ∈ ((bid, bshift) :: members.map fun m => (m, bshift)) :=
        List.mem_of_find?_eq_some he
      have hsnd := ppg_chunk_mem_snd bid bshift members e hmemE
      rw [he]
      simp only [Option.map_some, hsnd]
    · have hmemF : members.contains id = false := by
        cases hb : members.contains id with
        | true => exact absurd hb hmem
        | false => rfl
      have hcond : (bid == id || members.contains id) = false := by
        simp only [hbidF, hmemF, Bool.or_self]
      simp only [hcond]
      have hnone : ((bid, bshift) :: members.map fun m => (m, bshift)).find? (fun e => e.1 == id) =
          none := by
        rw [List.find?_eq_none]
        intro e he
        simp only [List.mem_cons, List.mem_map] at he
        rcases he with rfl | ⟨m, hm, rfl⟩
        · show ¬ (((bid, bshift).1 == id) = true)
          simp only [hbidF]
          exact Bool.false_ne_true
        · show ¬ (((m, bshift).1 == id) = true)
          have hme : m ≠ id := by
            intro hme
            subst hme
            have ht : members.contains m = true :=
              List.contains_iff_mem.mpr hm
            rw [ht] at hmemF
            exact Bool.noConfusion hmemF
          have hfalse : (m == id) = false := by
            cases hb : (m == id) with
            | true => exact absurd (beq_iff_eq.mp hb) hme
            | false => rfl
          simp only [hfalse]
          exact Bool.false_ne_true
      simp [hnone]

/-- The pin delta of an id is the band shift of its covering band. -/
private theorem ppg_pinBoxDelta_eq (axis : Axis) (bands : List Band) (s : Scene)
    (id : String) :
    (buildPin axis bands s).boxDelta id = bandShift bands id := by
  unfold buildPin Pin.boxDelta bandShift
  simp only
  induction bands with
  | nil => rfl
  | cons b rest ih =>
    rw [List.flatMap_cons, List.find?_append, Option.map_or]
    by_cases hcond : (b.id == id || b.members.contains id) = true
    · have hchunk : (((b.id, b.shift) :: b.members.map fun m => (m, b.shift)).find?
          (fun e => e.1 == id)).map (·.2) = some b.shift := by
        have hmap := ppg_chunk_find_map b.id b.shift b.members id
        simp only [hcond] at hmap
        exact hmap
      rw [hchunk, Option.some_or]
      have hfind : (b :: rest).find? (fun b => b.id == id || b.members.contains id) = some b := by
        simp only [List.find?_cons, hcond]
      simp only [hfind, Option.map_some, Option.getD_some]
    · have hcondF : (b.id == id || b.members.contains id) = false := by
        cases hb : (b.id == id || b.members.contains id) with
        | true => exact absurd hb hcond
        | false => rfl
      have hchunk : (((b.id, b.shift) :: b.members.map fun m => (m, b.shift)).find?
          (fun e => e.1 == id)).map (·.2) = none := by
        have hmap := ppg_chunk_find_map b.id b.shift b.members id
        simp only [hcondF] at hmap
        exact hmap
      rw [hchunk, Option.none_or]
      have hfind : (b :: rest).find? (fun b => b.id == id || b.members.contains id) =
          rest.find? (fun b => b.id == id || b.members.contains id) := by
        simp only [List.find?_cons, hcondF]
      rw [hfind]
      exact ih

private theorem ppg_placeRect_idem (axis : Axis) (s1 t1 s2 t2 : Int) (r : Rect) :
    placeRect axis s2 t2 (placeRect axis s1 t1 r) = placeRect axis s2 t2 r := by
  cases axis <;> rfl

private theorem ppg_start_withStart (axis : Axis) (r : Rect) (w : Int) :
    Axis.start axis (Axis.withStart axis r w) = w := by
  cases axis <;> rfl

private theorem ppg_length_withStart (axis : Axis) (r : Rect) (w : Int) :
    Axis.length axis (Axis.withStart axis r w) = Axis.length axis r := by
  cases axis <;> rfl

private theorem ppg_placeRect_start (axis : Axis) (s t : Int) (r : Rect) :
    Axis.start axis (placeRect axis s t r) = s := by
  unfold placeRect
  cases axis <;> rfl

private theorem ppg_placeRect_other_x {start thickness : Int} {r : Rect} :
    (placeRect Axis.x start thickness r).y = r.y ∧
    (placeRect Axis.x start thickness r).h = r.h :=
  ⟨rfl, rfl⟩

private theorem ppg_placeRect_other_y {start thickness : Int} {r : Rect} :
    (placeRect Axis.y start thickness r).x = r.x ∧
    (placeRect Axis.y start thickness r).w = r.w :=
  ⟨rfl, rfl⟩

private theorem ppg_placeRect_length (axis : Axis) (s t : Int) (r : Rect) :
    Axis.length axis (placeRect axis s t r) = t := by
  unfold placeRect
  cases axis <;> rfl

private theorem ppg_replaceFrame_full {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((b.id = band.id ∧ b'.rect = placeRect axis band.start band.thickness b.rect) ∨
        b'.rect = b.rect) := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    intro b' hb'
    exact ⟨b', hb', rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩
  | some idx =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error _e => simp [hstart, Bind.bind, Except.bind] at h
    | ok _s =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error _e => simp [hthick] at h
      | ok _t =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        intro b' hb'
        have hboxes : s'.boxes = s.boxes.mapIdx (fun j b =>
            if j = idx then ({ b with rect := placeRect axis _s _t b.rect } : Box) else b) := by
          rw [← h]
        rw [hboxes] at hb'
        obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hb'
        rw [List.getElem_mapIdx] at heq
        have hj' : j < s.boxes.length := by
          have hlen : (s.boxes.mapIdx (fun j b =>
              if j = idx then ({ b with rect := placeRect axis _s _t b.rect } : Box)
              else b)).length = s.boxes.length :=
            List.length_mapIdx
          rw [hlen] at hj
          exact hj
        have hmem : (s.boxes[j]'hj') ∈ s.boxes := List.getElem_mem hj'
        have hs' : _s = band.start := checkedI32_ok hstart
        have ht' : _t = band.thickness := checkedI32_ok hthick
        have hpbeta : (((s.boxes[idx]'hi).id == band.id)) = true := hp
        by_cases hcond : j = idx
        · subst j
          have heqb : (if idx = idx then Box.mk (s.boxes[idx]'hj').id
              (s.boxes[idx]'hj').role
              (placeRect axis _s _t (s.boxes[idx]'hj').rect)
              (s.boxes[idx]'hj').parent (s.boxes[idx]'hj').exclusive
              else (s.boxes[idx]'hj')) = b' := heq
          rw [ite_eq_left rfl] at heqb
          subst heqb
          have hbid : (s.boxes[idx]'hj').id = band.id := beq_iff_eq.mp hpbeta
          refine ⟨(s.boxes[idx]'hj'), hmem, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
          · intro hAx
            rw [hAx]
            exact ppg_placeRect_other_x
          · intro hAx
            rw [hAx]
            exact ppg_placeRect_other_y
          · left
            refine ⟨hbid, ?_⟩
            rw [hs', ht']
        · have heqb : (if j = idx then Box.mk (s.boxes[j]'hj').id
              (s.boxes[j]'hj').role
              (placeRect axis _s _t (s.boxes[j]'hj').rect)
              (s.boxes[j]'hj').parent (s.boxes[j]'hj').exclusive
              else (s.boxes[j]'hj')) = b' := heq
          rw [ite_eq_right hcond] at heqb
          subst heqb
          exact ⟨(s.boxes[j]'hj'), hmem, rfl, rfl, rfl, rfl,
            fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩

private theorem ppg_foldPlace_full (bands : List Band) (axis : Axis) (s : Scene)
    (hUniq : ∀ id : String, ∀ b1 ∈ bands, ∀ b2 ∈ bands,
      bandCovers b1 id → bandCovers b2 id → b1 = b2) :
    ∀ (s' : Scene),
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    ∀ b' ∈ s'.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((∃ band ∈ bands, b.id = band.id ∧
        b'.rect = placeRect axis band.start band.thickness b.rect) ∨ b'.rect = b.rect) := by
  induction bands generalizing s with
  | nil =>
    intro s' h b' hb'
    have he : s' = s := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure,
        Except.ok.injEq] using h.symm
    subst he
    exact ⟨b', hb', rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, Or.inr rfl⟩
  | cons band rest ih =>
    intro s' h b' hb'
    have hUniqRest : ∀ id : String, ∀ b1 ∈ rest, ∀ b2 ∈ rest,
        bandCovers b1 id → bandCovers b2 id → b1 = b2 := by
      intro id b1 hb1 b2 hb2 hc1 hc2
      exact hUniq id b1 (List.mem_cons.mpr (Or.inr hb1)) b2
        (List.mem_cons.mpr (Or.inr hb2)) hc1 hc2
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := bind_ok h
    obtain ⟨m, hmin, hid1, hpar1, hrole1, hexcl1, hx1, hy1, hrect1⟩ :=
      ih mid hUniqRest s' h _ hb'
    obtain ⟨m0, hmin0, hid0, hpar0, hrole0, hexcl0, hx0, hy0, hrect0⟩ :=
      ppg_replaceFrame_full (axis := axis) (band := band) hmid _ hmin
    refine ⟨m0, hmin0, hid1.trans hid0, hpar1.trans hpar0, hrole1.trans hrole0,
      hexcl1.trans hexcl0, ?_, ?_, ?_⟩
    · intro hAx
      obtain ⟨hyM, hhM⟩ := hx1 hAx
      obtain ⟨hyB, hhB⟩ := hx0 hAx
      exact ⟨hyM.trans hyB, hhM.trans hhB⟩
    · intro hAx
      obtain ⟨hxM, hwM⟩ := hy1 hAx
      obtain ⟨hxB, hwB⟩ := hy0 hAx
      exact ⟨hxM.trans hxB, hwM.trans hwB⟩
    · rcases hrect1 with ⟨B, hBmem, hBid, hBrect⟩ | hsame
      · rcases hrect0 with ⟨hm0id, hm0rect⟩ | hsame0
        · have hBeq : B = band := by
            have hcovB : bandCovers B B.id := Or.inl rfl
            have hcovBand : bandCovers band B.id := by
              have heq : B.id = band.id := hBid.symm.trans (hid0.trans hm0id)
              exact Or.inl heq.symm
            exact hUniq B.id B (List.mem_cons.mpr (Or.inr hBmem)) band
              (List.mem_cons.mpr (Or.inl rfl)) hcovB hcovBand
          subst B
          rw [hm0rect] at hBrect
          rw [ppg_placeRect_idem] at hBrect
          exact Or.inl ⟨band, List.mem_cons.mpr (Or.inl rfl), hm0id, hBrect⟩
        · rw [hsame0] at hBrect
          exact Or.inl ⟨B, List.mem_cons.mpr (Or.inr hBmem),
            hid0.symm.trans hBid, hBrect⟩
      · rcases hrect0 with ⟨hm0id, hm0rect⟩ | hsame0
        · rw [hsame]
          exact Or.inl ⟨band, List.mem_cons.mpr (Or.inl rfl), hm0id, hm0rect⟩
        · exact Or.inr (hsame.trans hsame0)

private theorem ppg_pinShift_mem (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Box),
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    ∀ b' ∈ l', ∃ b ∈ l, b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧
      b'.exclusive = b.exclusive ∧
      ∃ w, Measure.checkedI32 (axis.start b.rect + pin.boxDelta b.id) = .ok w ∧
        b'.rect = axis.withStart b.rect w ∧ w = axis.start b.rect + pin.boxDelta b.id := by
  induction l with
  | nil =>
    intro l' h b' hb'
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    simp at hb'
  | cons head tail ih =>
    intro l' h b' hb'
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hmem
    · obtain ⟨hid1, hpar1, hrole1, hexcl1, w, hw, heq, hval⟩ :=
        shiftBox_ok hfirst
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid1, hpar1, hrole1, hexcl1, w, hw,
        heq, hval⟩
    · obtain ⟨b, hbin, hid, hpar, hrole, hexcl, w, hw, heq, hval⟩ := ih _ hrest _ hmem
      exact ⟨b, List.mem_cons.mpr (Or.inr hbin), hid, hpar, hrole, hexcl, w, hw, heq, hval⟩

private theorem ppg_pinned_full {pin : Pin} {bands : List Band} {s pinned : Scene}
    (hUniq : ∀ id : String, ∀ b1 ∈ bands, ∀ b2 ∈ bands,
      bandCovers b1 id → bandCovers b2 id → b1 = b2)
    (h : applyPin pin bands s = .ok pinned) :
    ∀ b' ∈ pinned.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent ∧ b'.role = b.role ∧ b'.exclusive = b.exclusive ∧
      (pin.axis = Axis.x → b'.rect.y = b.rect.y ∧ b'.rect.h = b.rect.h) ∧
      (pin.axis = Axis.y → b'.rect.x = b.rect.x ∧ b'.rect.w = b.rect.w) ∧
      ((∃ band ∈ bands, b.id = band.id ∧
        Axis.start pin.axis b'.rect = band.start ∧
        Axis.length pin.axis b'.rect = band.thickness) ∨
        (∃ D, Axis.start pin.axis b'.rect = Axis.start pin.axis b.rect + D ∧
          Axis.length pin.axis b'.rect = Axis.length pin.axis b.rect ∧
          D = pin.boxDelta b.id)) := by
  obtain ⟨shiftedBoxes, _shiftedLabels, _shiftedRoutes, _shiftedItems,
    hboxes, _hlabels, _hroutes, _hitems, hfold⟩ := applyPin_shifted h
  intro b' hb'
  obtain ⟨m, hmin, hid1, hpar1, hrole1, hexcl1, hx1, hy1, hrect1⟩ :=
    ppg_foldPlace_full bands pin.axis _ hUniq _ hfold _ hb'
  have hmin' : m ∈ shiftedBoxes := hmin
  obtain ⟨b, hbin, hid0, hpar0, hrole0, hexcl0, w, _hw, heq0, hval⟩ :=
    ppg_pinShift_mem s.boxes pin pin.axis _ hboxes _ hmin'
  have hOtherM : (pin.axis = Axis.x → m.rect.y = b.rect.y ∧ m.rect.h = b.rect.h) ∧
      (pin.axis = Axis.y → m.rect.x = b.rect.x ∧ m.rect.w = b.rect.w) := by
    constructor
    · intro hAx
      have e := heq0
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
    · intro hAx
      have e := heq0
      rw [hAx] at e
      rw [e]
      exact ⟨rfl, rfl⟩
  refine ⟨b, hbin, hid1.trans hid0, hpar1.trans hpar0, hrole1.trans hrole0,
    hexcl1.trans hexcl0, ?_, ?_, ?_⟩
  · intro hAx
    obtain ⟨hyM, hhM⟩ := hx1 hAx
    obtain ⟨hyB, hhB⟩ := hOtherM.1 hAx
    exact ⟨hyM.trans hyB, hhM.trans hhB⟩
  · intro hAx
    obtain ⟨hxM, hwM⟩ := hy1 hAx
    obtain ⟨hxB, hwB⟩ := hOtherM.2 hAx
    exact ⟨hxM.trans hxB, hwM.trans hwB⟩
  · rcases hrect1 with ⟨B, hBmem, hBid, hBrect⟩ | hsame
    · left
      refine ⟨B, hBmem, hid0.symm.trans hBid, ?_, ?_⟩
      · have hs := ppg_placeRect_start pin.axis B.start B.thickness m.rect
        rw [hBrect]
        exact hs
      · have hl := ppg_placeRect_length pin.axis B.start B.thickness m.rect
        rw [hBrect]
        exact hl
    · right
      have hstartM : Axis.start pin.axis m.rect =
          Axis.start pin.axis b.rect + pin.boxDelta b.id := by
        rw [heq0, ppg_start_withStart]
        exact hval
      have hlenM : Axis.length pin.axis m.rect = Axis.length pin.axis b.rect := by
        rw [heq0, ppg_length_withStart]
      refine ⟨pin.boxDelta b.id, ?_, ?_, rfl⟩
      · rw [hsame]
        exact hstartM
      · rw [hsame]
        exact hlenM

private theorem ppg_mapIdx_pairs_general (l : List Box) (f : Nat → Box → Box)
    (hf : ∀ j b, ((f j b).id, (f j b).parent) = (b.id, b.parent)) :
    (l.mapIdx f).map (fun b => (b.id, b.parent)) = l.map (fun b => (b.id, b.parent)) := by
  induction l generalizing f with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.mapIdx_cons]
    have hhead : ((f 0 hd).id, (f 0 hd).parent) = (hd.id, hd.parent) := hf 0 hd
    simp only [List.map_cons, hhead]
    have htail := ih (fun j b => f (j + 1) b) (fun j b => hf (j + 1) b)
    simp only [htail]


private theorem ppg_shiftPairs (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ l' : List Box,
    l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' →
    l.map (fun b => (b.id, b.parent)) = l'.map (fun b => (b.id, b.parent)) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    rfl
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hid, hpar, _, _, _, _, _, _⟩ := shiftBox_ok hfirst
    have hhead : ((head.id, head.parent) : String × String) = ((first.id, first.parent) : String × String) := by
      rw [hid, hpar]
    simp only [List.map_cons, hhead]
    rw [ih _ hrest]

private theorem ppg_replacePairs {axis : Axis} {band : Band} {s s' : Scene}
    (h : replaceFrame axis band s = .ok s') :
    s.boxes.map (fun b => (b.id, b.parent)) = s'.boxes.map (fun b => (b.id, b.parent)) := by
  unfold replaceFrame at h
  cases hfind : s.boxes.findIdx? (fun b => b.id == band.id) with
  | none =>
    simp only [hfind, Pure.pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  | some idx =>
    simp only [hfind] at h
    cases hstart : Measure.checkedI32 band.start with
    | error _e => simp [hstart, Bind.bind, Except.bind] at h
    | ok _s =>
      simp only [hstart, Bind.bind, Except.bind] at h
      cases hthick : Measure.checkedI32 band.thickness with
      | error _e => simp [hthick] at h
      | ok _t =>
        simp only [hthick, Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only
        have hmap : (s.boxes.mapIdx (fun j b =>
            if j = idx then ({ b with rect := placeRect axis _s _t b.rect } : Box) else b)).map
            (fun b => (b.id, b.parent)) = s.boxes.map (fun b => (b.id, b.parent)) := by
          apply ppg_mapIdx_pairs_general
          intro j b
          by_cases hcond : j = idx
          · simp only [hcond, ite_true]
          · simp only [hcond, ite_false]
        exact hmap.symm

private theorem ppg_foldPairs (bands : List Band) (axis : Axis) (s : Scene) :
    ∀ s' : Scene,
    bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' →
    s.boxes.map (fun b => (b.id, b.parent)) = s'.boxes.map (fun b => (b.id, b.parent)) := by
  induction bands generalizing s with
  | nil =>
    intro s' h
    have he : s' = s := by
      simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    rfl
  | cons band rest ih =>
    intro s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := bind_ok h
    have h1 := ppg_replacePairs hmid
    have h2 := ih mid _ h
    rw [h1, h2]

private theorem ppg_pinnedPairs {pin : Pin} {bands : List Band} {s pinned : Scene}
    (h : applyPin pin bands s = .ok pinned) :
    s.boxes.map (fun b => (b.id, b.parent)) =
      pinned.boxes.map (fun b => (b.id, b.parent)) := by
  obtain ⟨shiftedBoxes, shiftedLabels, shiftedRoutes, shiftedItems, hboxes, _hlabels, _hroutes, _hitems, hfold⟩ := applyPin_shifted h
  have hshift := ppg_shiftPairs s.boxes pin pin.axis _ hboxes
  have hshiftScene : s.boxes.map (fun b => (b.id, b.parent)) = ({ s with boxes := shiftedBoxes, labels := shiftedLabels, routes := shiftedRoutes, items := shiftedItems } : Scene).boxes.map (fun b => (b.id, b.parent)) := by simpa only using hshift
  have hfoldPairs := ppg_foldPairs bands pin.axis ({ s with boxes := shiftedBoxes, labels := shiftedLabels, routes := shiftedRoutes, items := shiftedItems } : Scene) _ hfold
  rw [hshiftScene, hfoldPairs]

private theorem ppg_mem_eq_of_id_eq (l : List Box) : (l.map (fun b => b.id)).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.id = b.id → a = b := by
  induction l with
  | nil =>
    intro _ a ha _ _ _
    simp at ha
  | cons hd tl ih =>
    intro hnd a ha b hb hid
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hfresh, hrest⟩ := hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exfalso
      have hmem : b.id ∈ tl.map (fun b => b.id) := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [← hid] at hmem
      exact hfresh hmem
    · exfalso
      have hmem : a.id ∈ tl.map (fun b => b.id) := List.mem_map.mpr ⟨a, ha, rfl⟩
      rw [hid] at hmem
      exact hfresh hmem
    · exact ih hrest _ ha _ hb hid

private theorem ppg_mapIdx_ids_general (l : List Box) (f : Nat → Box → Box)
    (hf : ∀ j b, (f j b).id = b.id) :
    (l.mapIdx f).map (fun b => b.id) = l.map (fun b => b.id) := by
  induction l generalizing f with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.mapIdx_cons]
    have hhead : (f 0 hd).id = hd.id := hf 0 hd
    simp only [List.map_cons, hhead]
    have htail := ih (fun j b => f (j + 1) b) (fun j b => hf (j + 1) b)
    simp only [htail]

private theorem ppg_shiftIds (l : List Box) (pin : Pin) (axis : Axis) :
    ∀ l' : List Box, l.mapM (fun b : Box => (do pure { b with rect := ← (Move.constant (pin.boxDelta b.id)).rect axis b.rect } : Except LayoutError Box)) = .ok l' → l.map (fun b => b.id) = l'.map (fun b => b.id) := by
  induction l with
  | nil =>
    intro l' h
    have he : l' = [] := by simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    rfl
  | cons head tail ih =>
    intro l' h
    rw [List.mapM_cons] at h
    obtain ⟨first, hfirst, h⟩ := bind_ok h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    have he : first :: rest = l' := by simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    obtain ⟨hid, _, _, _, _, _, _, _⟩ := shiftBox_ok hfirst
    simp only [List.map_cons, hid]
    rw [ih _ hrest]

private theorem ppg_replaceIds {axis : Axis} {band : Band} {s s' : Scene} (h : replaceFrame axis band s = .ok s') : s.boxes.map (fun b => b.id) = s'.boxes.map (fun b => b.id) := by
  have hPairs := ppg_replacePairs h
  have hfst := congrArg (List.map Prod.fst) hPairs
  have hfun : (Prod.fst ∘ fun b : Box => (b.id, b.parent)) = fun b : Box => b.id := rfl
  rw [List.map_map, List.map_map, hfun] at hfst
  exact hfst

private theorem ppg_foldIds (bands : List Band) (axis : Axis) (s : Scene) : ∀ s' : Scene, bands.foldlM (fun scene band => replaceFrame axis band scene) s = .ok s' → s.boxes.map (fun b => b.id) = s'.boxes.map (fun b => b.id) := by
  induction bands generalizing s with
  | nil =>
    intro s' h
    have he : s' = s := by simpa only [List.foldlM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    rfl
  | cons band rest ih =>
    intro s' h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := bind_ok h
    have h1 := ppg_replaceIds hmid
    have h2 := ih mid _ h
    rw [h1, h2]

private theorem ppg_lanesOf_mem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

private theorem ppg_inLane_self_of_nodup {boxes : List ModelBox} {lane : String}
    (hNodup : (boxes.map (fun b => b.id)).Nodup)
    (hlane : lane ∈ lanesOf boxes) : inLane boxes lane lane = true := by
  obtain ⟨mb, hmbMem, hmbRole, hmbPar, hmbId⟩ := ppg_lanesOf_mem hlane
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have hEq : (fun b : ModelBox => b.id == lane) = (fun b : ModelBox => b.id == mb.id) := by
      funext b
      rw [hmbId]
    rw [hEq]
    exact modelFind?_eq_self hNodup hmbMem
  unfold inLane laneOf laneOfAux
  rw [hfind]
  simp [hmbPar, hmbRole]

private theorem ppg_id_mem_of_nodup {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {bands : List Band} {band : Band} {b : Box}
    (hModelNodup : (boxes.map (fun b => b.id)).Nodup)
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hbandMem : band ∈ bands) (hbandNe : band.id ≠ "")
    (hbid : b.id = band.id) : b.id ∈ band.members := by
  have hCases := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis) (sp := sp)
    (lanes := lanesOf boxes) (band := band) (by rw [← hbands]; exact hbandMem)
  rcases hCases with hLane | hLoose
  · obtain ⟨lane, hlaneMem, st, rfl⟩ := layLanes_mem_lane hLane
    have hIn : inLane boxes lane lane = true := ppg_inLane_self_of_nodup hModelNodup hlaneMem
    have hMemMap : lane ∈ ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := by
      obtain ⟨mb, hmbMem, _, _, hmbId⟩ := ppg_lanesOf_mem hlaneMem
      have hFilt : mb ∈ (boxes.filter fun b => inLane boxes b.id lane) := by
        rw [List.mem_filter]
        refine ⟨hmbMem, ?_⟩
        have hEq : inLane boxes mb.id lane = inLane boxes lane lane := by rw [hmbId]
        rw [hEq, hIn]
      exact List.mem_map.mpr ⟨mb, hFilt, hmbId⟩
    have hEqMem : (laneBand boxes s axis sp lane st).members =
        ((boxes.filter fun b => inLane boxes b.id lane).map fun b => b.id) := rfl
    have hMemMap2 : lane ∈ (laneBand boxes s axis sp lane st).members := by
      rw [hEqMem]
      exact hMemMap
    have hBandId : (laneBand boxes s axis sp lane st).id = lane := rfl
    have hBidLane : b.id = lane := by rw [hbid, hBandId]
    rw [hBidLane]
    exact hMemMap2
  · exfalso
    have hId : (looseBand boxes s axis sp (looseNodes boxes)
        (firstLaneStart s (lanesOf boxes) axis +
          (List.map (fun b => b.thickness)
            (layLanes boxes s axis sp (lanesOf boxes)
              (firstLaneStart s (lanesOf boxes) axis))).sum)).id = "" := by
      unfold looseBand
      cases hb : bounds (contentValues boxes s axis "" (looseNodes boxes)) with
      | none => rfl
      | some p =>
        cases p with
        | mk lo hi => rfl
    exact hbandNe (by rw [hLoose, hId])



/-- Lane ids are nonempty model ids. -/
private theorem ppg_lanes_ne_empty {boxes : List ModelBox}
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") {lane : String}
    (h : lane ∈ lanesOf boxes) : lane ≠ "" := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, _⟩ := List.mem_filter.mp hx
  exact hModelNoEmpty x hxb

/-- `layLanes` ids are exactly the lane list. -/
private theorem ppg_layLanes_ids (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (lanes : List String) (start : Int) :
    (layLanes boxes s axis sp lanes start).map (fun b => b.id) = lanes := by
  induction lanes generalizing start with
  | nil => rfl
  | cons lane rest ih =>
    have hhead : (laneBand boxes s axis sp lane start).id = lane := rfl
    simp only [layLanes, List.map_cons, hhead, ih]

/-- The loose band id is always `""`. -/
private theorem ppg_looseBand_id (boxes : List ModelBox) (s : Scene) (axis : Axis)
    (sp : Spacing) (loose : List String) (start : Int) :
    (looseBand boxes s axis sp loose start).id = "" := by
  unfold looseBand
  cases hb : bounds (contentValues boxes s axis "" loose) with
  | none => rfl
  | some p =>
    cases p with
    | mk lo hi => rfl

/-- `layBands` ids are nodup when model ids are nodup and nonempty: lane ids
are the nodup lane list and the trailing loose id `""` is fresh. -/
private theorem ppg_layBands_ids_nodup (boxes : List ModelBox) (s : Scene)
    (axis : Axis) (sp : Spacing)
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "") :
    ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup := by
  have hLaneIds : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id) =
      lanesOf boxes :=
    ppg_layLanes_ids _ _ _ _ _ _
  have hLaneNodup : ((layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.id).Nodup := by
    rw [hLaneIds]
    exact lanesOf_nodup hModelNodup
  have hfresh : "" ∉ lanesOf boxes :=
    fun hmem => ppg_lanes_ne_empty hModelNoEmpty hmem rfl
  unfold layBands
  by_cases hl : (looseNodes boxes).isEmpty = true
  · simp only [hl, ↓reduceIte]
    exact hLaneNodup
  · simp only [hl, ↓reduceIte, Bool.false_eq_true, List.map_append, hLaneIds]
    have hsing : ∀ S : Int, (([looseBand boxes s axis sp (looseNodes boxes) S].map
        fun b => b.id) = [""]) := by
      intro S
      simp only [List.map_cons, List.map_nil, ppg_looseBand_id]
    simp only [hsing]
    rw [List.nodup_append]
    refine ⟨?_, (by simp : ([""] : List String).Nodup), ?_⟩
    · exact lanesOf_nodup hModelNodup
    · intro a ha b hb hEq
      rw [List.mem_singleton] at hb
      subst hb
      exact ppg_lanes_ne_empty hModelNoEmpty ha hEq

/-- Bands with equal ids coincide, from id nodup. -/
private theorem ppg_bands_mem_eq_of_id_eq (l : List Band)
    (hnd : (l.map fun b => b.id).Nodup) :
    ∀ a ∈ l, ∀ b ∈ l, a.id = b.id → a = b := by
  induction l with
  | nil =>
    intro a ha _ _ _
    simp at ha
  | cons hd tl ih =>
    intro a ha b hb hid
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hfresh, hrest⟩ := hnd
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exfalso
      have hmem : b.id ∈ tl.map (fun b => b.id) := List.mem_map.mpr ⟨b, hb, rfl⟩
      rw [← hid] at hmem
      exact hfresh hmem
    · exfalso
      have hmem : a.id ∈ tl.map (fun b => b.id) := List.mem_map.mpr ⟨a, ha, rfl⟩
      rw [hid] at hmem
      exact hfresh hmem
    · exact ih hrest _ ha _ hb hid

/-- Loose band members are exactly the loose list. -/
private theorem ppg_looseBand_mem {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} {loose : List String} {start : Int} {id : String}
    (h : id ∈ (looseBand boxes s axis sp loose start).members) : id ∈ loose := by
  have heq : (looseBand boxes s axis sp loose start).members = loose := by
    unfold looseBand
    cases hb : bounds (contentValues boxes s axis "" loose) with
    | none => rfl
    | some p =>
      cases p with
      | mk lo hi => rfl
  rw [heq] at h
  exact h

/-- Band members are nonempty model ids. -/
private theorem ppg_mem_ne_empty {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing} (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    {band : Band} (hmem : band ∈ layBands boxes s axis sp (lanesOf boxes))
    {m : String} (h : m ∈ band.members) : m ≠ "" := by
  have hCases := layBands_mem_cases hmem
  rcases hCases with hLane | hLoose
  · obtain ⟨lane, _, _, rfl⟩ := layLanes_mem_lane hLane
    obtain ⟨mb, hmb, rfl⟩ := List.mem_map.mp h
    obtain ⟨hmbmem, _⟩ := List.mem_filter.mp hmb
    exact hModelNoEmpty mb hmbmem
  · rw [hLoose] at h
    have hmem2 : m ∈ looseNodes boxes := ppg_looseBand_mem h
    unfold looseNodes at hmem2
    obtain ⟨mb, hmb, rfl⟩ := List.mem_map.mp hmem2
    obtain ⟨hmbmem, _⟩ := List.mem_filter.mp hmb
    exact hModelNoEmpty mb hmbmem

/-- Bands covering the empty id coincide: members are nonempty, so both cover
by id equality, and both are the trailing loose band. -/
private theorem ppg_cover_unique_empty {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 "")
    {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 "") : b1 = b2 := by
  have hNe1 : "" ∉ b1.members := by
    intro hcon
    exact ppg_mem_ne_empty hModelNoEmpty (hbands ▸ hm1) hcon rfl
  have hNe2 : "" ∉ b2.members := by
    intro hcon
    exact ppg_mem_ne_empty hModelNoEmpty (hbands ▸ hm2) hcon rfl
  have hid1 : b1.id = "" := by
    rcases hc1 with hEq | hMem
    · exact hEq
    · exact absurd hMem hNe1
  have hid2 : b2.id = "" := by
    rcases hc2 with hEq | hMem
    · exact hEq
    · exact absurd hMem hNe2
  have hC1 := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis)
    (sp := sp) (lanes := lanesOf boxes) (band := b1) (hbands ▸ hm1)
  have hC2 := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis)
    (sp := sp) (lanes := lanesOf boxes) (band := b2) (hbands ▸ hm2)
  rcases hC1 with hL1 | hO1 <;> rcases hC2 with hL2 | hO2
  · exfalso
    have hmem : b1.id ∈ lanesOf boxes := layLanes_id_mem hL1
    exact ppg_lanes_ne_empty hModelNoEmpty hmem hid1
  · exfalso
    have hmem : b1.id ∈ lanesOf boxes := layLanes_id_mem hL1
    exact ppg_lanes_ne_empty hModelNoEmpty hmem hid1
  · exfalso
    have hmem : b2.id ∈ lanesOf boxes := layLanes_id_mem hL2
    exact ppg_lanes_ne_empty hModelNoEmpty hmem hid2
  · rw [hO1, hO2]

/-- A covering band of a nonempty id is unique: lane membership decides the
lane, loose membership contradicts lane membership, and equal ids give equal
bands by id nodup. -/
private theorem ppg_cover_unique {boxes : List ModelBox} {s : Scene} {axis : Axis}
    {sp : Spacing}
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (_hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map fun b => b.id).Nodup)
    {bands : List Band} (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    {id : String} (hidNe : id ≠ "")
    {b1 : Band} (hm1 : b1 ∈ bands) (hc1 : bandCovers b1 id)
    {b2 : Band} (hm2 : b2 ∈ bands) (hc2 : bandCovers b2 id) : b1 = b2 := by
  have hIdsNodupB : ((bands.map fun b => b.id)).Nodup := by
    rw [hbands]
    exact hIdsNodup
  have hmem : ∀ b ∈ bands, ∀ c ∈ bands, b.id = c.id → b = c :=
    ppg_bands_mem_eq_of_id_eq bands hIdsNodupB
  have hCases1 := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis)
    (sp := sp) (lanes := lanesOf boxes) (band := b1) (hbands ▸ hm1)
  have hCases2 := layBands_mem_cases (boxes := boxes) (s := s) (axis := axis)
    (sp := sp) (lanes := lanesOf boxes) (band := b2) (hbands ▸ hm2)
  have hid1 : b1.id = id ∨ id ∈ b1.members := hc1
  have hid2 : b2.id = id ∨ id ∈ b2.members := hc2
  rcases hCases1 with hLane1 | hLoose1 <;>
    rcases hCases2 with hLane2 | hLoose2
  · obtain ⟨lane1, _, st1, rfl⟩ := layLanes_mem_lane hLane1
    obtain ⟨lane2, _, st2, rfl⟩ := layLanes_mem_lane hLane2
    have e1 : (laneBand boxes s axis sp lane1 st1).id = lane1 := rfl
    have e2 : (laneBand boxes s axis sp lane2 st2).id = lane2 := rfl
    rcases hid1 with hEq1 | hMem1 <;> rcases hid2 with hEq2 | hMem2
    · exact hmem _ hm1 _ hm2 (hEq1.trans hEq2.symm)
    · have hIn2 : inLane boxes id lane2 = true := laneBand_mem_inLane hMem2
      have hLaneMem : id ∈ lanesOf boxes := by
        have h1 := layLanes_id_mem hLane1
        rw [hEq1] at h1
        exact h1
      have hSelf := ppg_inLane_self_of_nodup hModelNodup hLaneMem
      have hEq : lane2 = id := inLane_unique hIn2 hSelf
      exact hmem _ hm1 _ hm2 (hEq1.trans (e2.trans hEq).symm)
    · have hIn1 : inLane boxes id lane1 = true := laneBand_mem_inLane hMem1
      have hLaneMem : id ∈ lanesOf boxes := by
        have h2 := layLanes_id_mem hLane2
        rw [hEq2] at h2
        exact h2
      have hSelf := ppg_inLane_self_of_nodup hModelNodup hLaneMem
      have hEq : lane1 = id := inLane_unique hIn1 hSelf
      exact hmem _ hm1 _ hm2 ((e1.trans hEq).trans hEq2.symm)
    · have hIn1 : inLane boxes id lane1 = true := laneBand_mem_inLane hMem1
      have hIn2 : inLane boxes id lane2 = true := laneBand_mem_inLane hMem2
      have hEq : lane1 = lane2 := inLane_unique hIn1 hIn2
      exact hmem _ hm1 _ hm2 ((e1.trans hEq).trans e2.symm)
  · obtain ⟨lane1, _, st1, rfl⟩ := layLanes_mem_lane hLane1
    rw [hLoose2] at hid2
    rcases hid1 with hEq1 | hMem1
    · have hLaneMem : id ∈ lanesOf boxes := by
        have h1 := layLanes_id_mem hLane1
        rw [hEq1] at h1
        exact h1
      have hSelf := ppg_inLane_self_of_nodup hModelNodup hLaneMem
      rcases hid2 with hEq2 | hMem2
      · rw [ppg_looseBand_id] at hEq2
        exact absurd hEq2.symm hidNe
      · exfalso
        have hContra := loose_not_inLane hModelNodup
          (ppg_looseBand_mem hMem2) (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
    · have hIn1 : inLane boxes id lane1 = true := laneBand_mem_inLane hMem1
      rcases hid2 with hEq2 | hMem2
      · rw [ppg_looseBand_id] at hEq2
        exact absurd hEq2.symm hidNe
      · exfalso
        exact loose_lane_members_disjoint hModelNodup (ppg_looseBand_mem hMem2) hMem1
  · obtain ⟨lane2, _, st2, rfl⟩ := layLanes_mem_lane hLane2
    rw [hLoose1] at hid1
    rcases hid2 with hEq2 | hMem2
    · have hLaneMem : id ∈ lanesOf boxes := by
        have h2 := layLanes_id_mem hLane2
        rw [hEq2] at h2
        exact h2
      have hSelf := ppg_inLane_self_of_nodup hModelNodup hLaneMem
      rcases hid1 with hEq1 | hMem1
      · rw [ppg_looseBand_id] at hEq1
        exact absurd hEq1.symm hidNe
      · exfalso
        have hContra := loose_not_inLane hModelNodup
          (ppg_looseBand_mem hMem1) (lane := id)
        rw [hSelf] at hContra
        exact Bool.noConfusion hContra
    · have hIn2 : inLane boxes id lane2 = true := laneBand_mem_inLane hMem2
      rcases hid1 with hEq1 | hMem1
      · rw [ppg_looseBand_id] at hEq1
        exact absurd hEq1.symm hidNe
      · exfalso
        exact loose_lane_members_disjoint hModelNodup (ppg_looseBand_mem hMem1) hMem2
  · rw [hLoose1, hLoose2]

/-- Thickness sums are non-negative. -/
private theorem ppg_sum_thickness_nonneg (bands : List Band)
    (h : ∀ b ∈ bands, 0 ≤ b.thickness) : 0 ≤ (bands.map fun b => b.thickness).sum := by
  induction bands with
  | nil => simp
  | cons hd tl ih =>
    have hhd : 0 ≤ hd.thickness := h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ b ∈ tl, 0 ≤ b.thickness := by
      intro b hb
      exact h b (List.mem_cons.mpr (Or.inr hb))
    simp only [List.map_cons, List.sum_cons]
    have := ih htl
    omega

/-- Every band of a non-negative tiling ends at or before the tiling end:
`start + total thickness`. -/
private theorem ppg_tiled_end_le {start : Int} {bands : List Band}
    (h : Tiled start bands) (hnonneg : ∀ b ∈ bands, 0 ≤ b.thickness)
    {c : Band} (hmem : c ∈ bands) :
    c.start + c.thickness ≤ start + (bands.map fun b => b.thickness).sum := by
  induction bands generalizing start with
  | nil => simp at hmem
  | cons b bs ih =>
    obtain ⟨hstart, htail⟩ := h
    rw [List.mem_cons] at hmem
    have hbpos : 0 ≤ b.thickness := hnonneg b (List.mem_cons.mpr (Or.inl rfl))
    have htailNonneg : ∀ x ∈ bs, 0 ≤ x.thickness := by
      intro x hx
      exact hnonneg x (List.mem_cons.mpr (Or.inr hx))
    have hsumNonneg := ppg_sum_thickness_nonneg bs htailNonneg
    rcases hmem with rfl | hmem
    · simp only [List.map_cons, List.sum_cons]
      omega
    · have hle := ih (start := start + b.thickness) htail htailNonneg hmem
      simp only [List.map_cons, List.sum_cons] at hle ⊢
      omega

/-- Every lane band ends at or before the loose band start. -/
private theorem ppg_lane_end_le_loose {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    {L : Band}
    (hmem : L ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)) :
    L.start + L.thickness ≤ firstLaneStart s (lanesOf boxes) axis +
      (((layLanes boxes s axis sp (lanesOf boxes)
        (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.thickness)).sum := by
  exact ppg_tiled_end_le (layLanes_tiled boxes s axis sp (lanesOf boxes) _)
    (layLanes_thickness_nonneg boxes s axis sp (lanesOf boxes) _ ht hc) hmem

/-- Ordered cross-axis intervals are disjoint: the end of one is at or before
the start of the other along the pinning axis. -/
private theorem ppg_disjoint_of_axis_le {axis : Axis} {a b : Rect}
    (h : Axis.start axis a + Axis.length axis a ≤ Axis.start axis b) :
    Disjoint a b := by
  unfold Disjoint Rect.meetsInterior
  cases axis with
  | x =>
    simp only [Axis.start, Axis.length] at h ⊢
    omega
  | y =>
    simp only [Axis.start, Axis.length] at h ⊢
    omega

/-- A same-shift transfer of disjointness along the pinning axis: the shifted
rects keep their cross-axis lengths and move by one shared delta, while the
other axis is unchanged, so disjointness transfers from the source pair. -/
private theorem ppg_transfer_disjoint {axis : Axis} {g' gb b' bb : Rect} {D : Int}
    (hGs : Axis.start axis g' = Axis.start axis gb + D)
    (hGl : Axis.length axis g' = Axis.length axis gb)
    (hBs : Axis.start axis b' = Axis.start axis bb + D)
    (hBl : Axis.length axis b' = Axis.length axis bb)
    (hxg : axis = Axis.x → g'.y = gb.y ∧ g'.h = gb.h)
    (hyg : axis = Axis.y → g'.x = gb.x ∧ g'.w = gb.w)
    (hxb : axis = Axis.x → b'.y = bb.y ∧ b'.h = bb.h)
    (hyb : axis = Axis.y → b'.x = bb.x ∧ b'.w = bb.w)
    (hD : Disjoint gb bb) : Disjoint g' b' := by
  cases axis with
  | x =>
    obtain ⟨hy1, hh1⟩ := hxg rfl
    obtain ⟨hy2, hh2⟩ := hxb rfl
    unfold Disjoint Rect.meetsInterior at hD ⊢
    simp only [Axis.start, Axis.length] at hGs hGl hBs hBl
    omega
  | y =>
    obtain ⟨hx1, hw1⟩ := hyg rfl
    obtain ⟨hx2, hw2⟩ := hyb rfl
    unfold Disjoint Rect.meetsInterior at hD ⊢
    simp only [Axis.start, Axis.length] at hGs hGl hBs hBl
    omega


/-- Pinning keeps clause C8a: a group frame is disjoint from every box that is
neither its ancestor nor its descendant. Lane frames become band rectangles,
bands tile the pinning axis, a pair inside one band moves by that band's single
shift, the origin restore is one uniform shift, and label relocation and canvas
growth leave boxes untouched. The loose band's shift overflows its band by
`clear`, so the proof concludes disjointness directly from the member
intervals (lane members stay within their band, loose members stay at or
beyond the loose band's lower bound) and never uses the second disjunct of
`pinPairGeometry`. -/
theorem pinBands_c8a {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC8a : Validator.C8a s.layoutDump)
    (hModelNodup : (boxes.map fun b => b.id).Nodup)
    (hModelNoEmpty : ∀ b ∈ boxes, b.id ≠ "")
    (hNodupS : (s.boxes.map fun b => b.id).Nodup)
    (hNoEmpty : ∀ b ∈ s.boxes, b.id ≠ "")
    (hcover : ∀ sp : Spacing, spacingOf o.profile = .ok sp →
      PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hParents : ∀ sp : Spacing, ∀ bands : List Band, spacingOf o.profile = .ok sp →
      bands = layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes) →
      PinSceneParents boxes s bands)
    (h : pinBands boxes o s = .ok r) : Validator.C8a r.layoutDump := by
  cases hLanes : lanesOf boxes with
  | nil =>
    have hNo : pinBands boxes o s = .ok s := pinBands_no_lanes hLanes
    rw [hNo] at h
    cases h
    exact hC8a
  | cons lane rest =>
    have hlanes : lanesOf boxes ≠ [] := by
      rw [hLanes]
      intro hnil
      cases hnil
    obtain ⟨sp, axis, bands, pinned, routed, origin, strip, stripScene,
      hsp, haxis, hbands, happ, hroute, horig, _hstrip, hstripEq, hgrow⟩ :=
      pinBands_spec (boxes := boxes) (o := o) (s := s) (r := r) hlanes h
    have hcovAx : PinBoxCoverage boxes s axis sp := by
      rw [haxis]
      exact hcover sp hsp
    have hbandsDir : bands = layBands boxes s (Axis.ofDirection o.direction) sp
        (lanesOf boxes) := by
      rw [← haxis]
      exact hbands
    have hparAx := hParents sp bands hsp hbandsDir
    obtain ⟨ht, hc⟩ := spacing_of_nonneg hsp
    obtain ⟨hroutedBoxes, _hroutedLabels, _hroutedCanvas⟩ := rerouteBands_frame hroute

    obtain ⟨hgrowBoxes, _hgrowRoutes, _hgrowLabels⟩ := growCanvas_frame hgrow
    have hstripBoxes : stripScene.boxes = origin.boxes := by
      rw [hstripEq]
      exact relocateLabels_boxes axis strip origin
    have hrBoxes : r.boxes = origin.boxes := by rw [hgrowBoxes, hstripBoxes]
    have hPinned : Validator.C8a pinned.layoutDump := by
      have hTiled : Tiled (firstLaneStart s (lanesOf boxes) axis) bands := by
        rw [hbands]
        exact layBands_tiled boxes s axis sp (lanesOf boxes)
      have hnonnegB : ∀ b ∈ bands, 0 ≤ b.thickness := by
        rw [hbands]
        exact layBands_thickness_nonneg boxes s axis sp (lanesOf boxes) ht hc
      have hIdsNodup : ((layBands boxes s axis sp (lanesOf boxes)).map
          fun b => b.id).Nodup :=
        ppg_layBands_ids_nodup boxes s axis sp hModelNodup hModelNoEmpty
      have hUniq : ∀ id : String, ∀ b1 ∈ bands, ∀ b2 ∈ bands,
          bandCovers b1 id → bandCovers b2 id → b1 = b2 := by
        intro id b1 hb1 b2 hb2 hc1 hc2
        by_cases hidEq : id = ""
        · subst hidEq
          exact ppg_cover_unique_empty hModelNoEmpty hbands hb1 hc1 hb2 hc2
        · exact ppg_cover_unique hModelNodup hModelNoEmpty hIdsNodup hbands
            hidEq hb1 hc1 hb2 hc2
      have hPairs := ppg_pinnedPairs happ
      have hancEq : ∀ x : String,
          pinned.layoutDump.ancestors x = s.layoutDump.ancestors x :=
        fun x => ancestors_eq_of_pairs x hPairs.symm
      obtain ⟨_hparMir, hparAnc⟩ := hparAx
      intro g' hg' hrole b' hb' hne hnot1 hnot2
      obtain ⟨gb, hgb, hidg, _hparg, hroleg, _hexclg, hxg, hyg, hrectg⟩ :=
        ppg_pinned_full hUniq happ g' hg'
      obtain ⟨bb, hbb, hidb, _hparb, _hroleb, _hexclb, hxb, hyb, hrectb⟩ :=
        ppg_pinned_full hUniq happ b' hb'
      have hgbGroup : gb.role = "group" := by rw [← hroleg]; exact hrole
      have hAnc1 : gb.id ∉ s.layoutDump.ancestors bb.id := by
        have h := hnot1
        rw [hidg, hidb, hancEq bb.id] at h
        exact h
      have hAnc2 : bb.id ∉ s.layoutDump.ancestors gb.id := by
        have h := hnot2
        rw [hidb, hancEq g'.id, hidg] at h
        exact h
      have hneBB : bb.id ≠ gb.id := by
        intro hEq
        apply hne
        rw [hidb, hidg]
        exact hEq
      have hgbNe : gb.id ≠ "" := hNoEmpty gb hgb
      have hbbNe : bb.id ≠ "" := hNoEmpty bb hbb
      obtain ⟨Cg, hCgMemL, hCgCov⟩ := hcovAx gb hgb
      obtain ⟨Cb, hCbMemL, hCbCov⟩ := hcovAx bb hbb
      have hCgMemB : Cg ∈ bands := by rw [hbands]; exact hCgMemL
      have hCbMemB : Cb ∈ bands := by rw [hbands]; exact hCbMemL
      have hDisjBase : Disjoint gb.rect bb.rect :=
        hC8a gb hgb hgbGroup bb hbb hneBB hAnc1 hAnc2
      rcases hrectg with ⟨Fg, hFgMemB, hFgId, hFgStart, hFgLen⟩ | ⟨Dg, hGs, hGl, hGv⟩
      · -- g' is a lane frame over Fg
        have hFgCg : Fg = Cg :=
          hUniq gb.id Fg hFgMemB Cg hCgMemB (Or.inl hFgId.symm) hCgCov
        have hFs : Axis.start axis g'.rect = Cg.start := by
          rw [← hFgCg]; exact hFgStart
        have hFl : Axis.length axis g'.rect = Cg.thickness := by
          rw [← hFgCg]; exact hFgLen
        rcases hrectb with ⟨Fb, hFbMemB, hFbId, hFbStart, hFbLen⟩ | ⟨Db, hBs, hBl, hBv⟩
        · -- both frames
          have hFbCb : Fb = Cb :=
            hUniq bb.id Fb hFbMemB Cb hCbMemB (Or.inl hFbId.symm) hCbCov
          have hBs' : Axis.start axis b'.rect = Cb.start := by
            rw [← hFbCb]; exact hFbStart
          have hBl' : Axis.length axis b'.rect = Cb.thickness := by
            rw [← hFbCb]; exact hFbLen
          by_cases hSame : Cg = Cb
          · exfalso
            apply hneBB
            rw [hFbId, hFbCb, ← hSame, ← hFgCg, ← hFgId]
          · have hord := tiled_ordered hTiled hnonnegB hCgMemB hCbMemB hSame
            have h1 : Cg.start ≤ Axis.start axis g'.rect := by omega
            have h2 : Axis.start axis g'.rect + Axis.length axis g'.rect ≤
                Cg.start + Cg.thickness := by omega
            have h3 : Cb.start ≤ Axis.start axis b'.rect := by omega
            have h4 : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                Cb.start + Cb.thickness := by omega
            exact disjoint_of_bands (axis := axis) h1 h2 h3 h4 hord
        · -- g' frame, b' shifted
          have hDbShift : Db = Cb.shift := by
            have h2 : (buildPin axis bands s).boxDelta bb.id =
                bandShift bands bb.id :=
              ppg_pinBoxDelta_eq axis bands s bb.id
            have h3 : bandShift bands bb.id = Cb.shift :=
              bandShift_eq hCbMemB hCbCov (hUniq bb.id)
            rw [hBv, h2, h3]
          have hBs' : Axis.start axis b'.rect =
              Axis.start axis bb.rect + Db := hBs
          have hCbMemBB : bb.id ∈ Cb.members := by
            rcases hCbCov with hEq | hMem
            · exact ppg_id_mem_of_nodup hModelNodup hbands hCbMemB
                (by intro hcon; exact hbbNe (hEq.symm.trans hcon)) hEq.symm
            · exact hMem
          have hfindB : s.boxes.find? (fun b' => b'.id == bb.id) = some bb :=
            sceneFind?_eq_self hNodupS hbb
          have hCbCases := layBands_mem_cases (band := Cb) (hbands ▸ hCbMemB)
          rcases hCbCases with hCbLane | hCbLoose
          · obtain ⟨blane, _, bst, rfl⟩ := layLanes_mem_lane hCbLane
            have hwithinB : (laneBand boxes s axis sp blane bst).start ≤
                Axis.start axis bb.rect +
                  (laneBand boxes s axis sp blane bst).shift ∧
                Axis.start axis bb.rect + Axis.length axis bb.rect +
                  (laneBand boxes s axis sp blane bst).shift ≤
                (laneBand boxes s axis sp blane bst).start +
                  (laneBand boxes s axis sp blane bst).thickness :=
              laneMember_within ht hc hCbMemBB hfindB
            have hBl' : Axis.length axis b'.rect =
                Axis.length axis bb.rect := hBl
            have hBsLo : (laneBand boxes s axis sp blane bst).start ≤
                Axis.start axis b'.rect := by
              rw [hBs', hDbShift]
              exact hwithinB.1
            have hBsHi : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                (laneBand boxes s axis sp blane bst).start +
                  (laneBand boxes s axis sp blane bst).thickness := by
              omega
            by_cases hSame : Cg = (laneBand boxes s axis sp blane bst)
            · exfalso
              have hFgCb : Fg = (laneBand boxes s axis sp blane bst) :=
                hFgCg.trans hSame
              have hgbCb : gb.id = (laneBand boxes s axis sp blane bst).id :=
                hFgId.trans (congrArg Band.id hFgCb)
              have hpar := hparAnc (laneBand boxes s axis sp blane bst) hCbMemB
                ⟨gb, hgb, hgbCb⟩ bb.id hCbMemBB
              rcases hpar with hEq | hmem
              · exact hneBB (hEq.trans hgbCb.symm)
              · exact hAnc1 (by rw [hgbCb]; exact hmem)
            · have hord := tiled_ordered hTiled hnonnegB hCgMemB hCbMemB hSame
              have h1 : Cg.start ≤ Axis.start axis g'.rect := by omega
              have h2 : Axis.start axis g'.rect + Axis.length axis g'.rect ≤
                  Cg.start + Cg.thickness := by omega
              exact disjoint_of_bands (axis := axis) h1 h2 hBsLo hBsHi hord
          · -- Cb loose: frame end below loose start
            have hmemL : bb.id ∈ looseNodes boxes := by
              have h2 := hCbMemBB
              rw [hCbLoose] at h2
              exact ppg_looseBand_mem h2
            have hlowerB : Cb.start ≤ Axis.start axis bb.rect + Cb.shift := by
              rw [hCbLoose]
              exact looseMember_lower hc hmemL hfindB
            have hFgLay : Fg ∈ layLanes boxes s axis sp (lanesOf boxes)
                (firstLaneStart s (lanesOf boxes) axis) := by
              have hC := layBands_mem_cases (band := Fg) (hbands ▸ hFgMemB)
              rcases hC with hL | hO
              · exact hL
              · exfalso
                have hId : Fg.id = "" := by
                  rw [hO]; exact ppg_looseBand_id _ _ _ _ _ _
                exact hNoEmpty gb hgb (hFgId.trans hId)
            have hFsC : Axis.start axis g'.rect = Fg.start := hFgStart
            have hFlC : Axis.length axis g'.rect = Fg.thickness := hFgLen
            have hle : Fg.start + Fg.thickness ≤ Cb.start := by
              have hLend := ppg_lane_end_le_loose ht hc hFgLay
              rw [hCbLoose, looseBand_start]
              exact hLend
            have hBle : Axis.start axis g'.rect + Axis.length axis g'.rect ≤
                Axis.start axis b'.rect := by
              have h1g : Axis.start axis g'.rect + Axis.length axis g'.rect =
                  Fg.start + Fg.thickness := by rw [hFsC, hFlC]
              have h2 : Cb.start ≤ Axis.start axis b'.rect := by
                rw [hBs', hDbShift]
                exact hlowerB
              omega
            exact ppg_disjoint_of_axis_le hBle
      · -- g' shifted
        have hDgShift : Dg = Cg.shift := by
          have h2 : (buildPin axis bands s).boxDelta gb.id =
              bandShift bands gb.id :=
            ppg_pinBoxDelta_eq axis bands s gb.id
          have h3 : bandShift bands gb.id = Cg.shift :=
            bandShift_eq hCgMemB hCgCov (hUniq gb.id)
          rw [hGv, h2, h3]
        have hGs' : Axis.start axis g'.rect =
            Axis.start axis gb.rect + Dg := hGs
        have hfindG : s.boxes.find? (fun b' => b'.id == gb.id) = some gb :=
          sceneFind?_eq_self hNodupS hgb
        have hCgMemBB : gb.id ∈ Cg.members := by
          rcases hCgCov with hEq | hMem
          · exact ppg_id_mem_of_nodup hModelNodup hbands hCgMemB
              (by intro hcon; exact hgbNe (hEq.symm.trans hcon)) hEq.symm
          · exact hMem
        have hCgCases := layBands_mem_cases (band := Cg) (hbands ▸ hCgMemB)
        rcases hCgCases with hCgLane | hCgLoose
        · obtain ⟨glane, _, gst, rfl⟩ := layLanes_mem_lane hCgLane
          have hwithinG : (laneBand boxes s axis sp glane gst).start ≤
              Axis.start axis gb.rect +
                (laneBand boxes s axis sp glane gst).shift ∧
              Axis.start axis gb.rect + Axis.length axis gb.rect +
                (laneBand boxes s axis sp glane gst).shift ≤
              (laneBand boxes s axis sp glane gst).start +
                (laneBand boxes s axis sp glane gst).thickness :=
            laneMember_within ht hc hCgMemBB hfindG
          have hGl' : Axis.length axis g'.rect =
              Axis.length axis gb.rect := hGl
          have hGsLo : (laneBand boxes s axis sp glane gst).start ≤
              Axis.start axis g'.rect := by
            rw [hGs', hDgShift]
            exact hwithinG.1
          have hGsHi : Axis.start axis g'.rect + Axis.length axis g'.rect ≤
              (laneBand boxes s axis sp glane gst).start +
                (laneBand boxes s axis sp glane gst).thickness := by
            omega
          rcases hrectb with ⟨Fb, hFbMemB, hFbId, hFbStart, hFbLen⟩ | ⟨Db, hBs, hBl, hBv⟩
          · -- b' frame
            have hFbCb : Fb = Cb :=
              hUniq bb.id Fb hFbMemB Cb hCbMemB (Or.inl hFbId.symm) hCbCov
            have hBsB : Axis.start axis b'.rect = Cb.start := by
              rw [← hFbCb]; exact hFbStart
            have hBlB : Axis.length axis b'.rect = Cb.thickness := by
              rw [← hFbCb]; exact hFbLen
            by_cases hSame : (laneBand boxes s axis sp glane gst) = Cb
            · exfalso
              have hmem : gb.id ∈ Cb.members := by
                rw [← hSame]; exact hCgMemBB
              have hCbFb : Cb.id = Fb.id := by rw [hFbCb]
              have hCbBb : Cb.id = bb.id := hCbFb.trans hFbId.symm
              have hpar := hparAnc Cb hCbMemB ⟨bb, hbb, hCbBb.symm⟩ gb.id hmem
              rcases hpar with hEq | hmem2
              · exact hneBB (hCbBb.symm.trans hEq.symm)
              · exact hAnc2 (by rw [hCbBb] at hmem2; exact hmem2)
            · have hord := tiled_ordered hTiled hnonnegB hCgMemB hCbMemB hSame
              have h3 : Cb.start ≤ Axis.start axis b'.rect := by omega
              have h4 : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                  Cb.start + Cb.thickness := by omega
              exact disjoint_of_bands (axis := axis) hGsLo hGsHi h3 h4 hord
          · -- b' shifted, Cg lane
            have hDbShift : Db = Cb.shift := by
              have h2 : (buildPin axis bands s).boxDelta bb.id =
                  bandShift bands bb.id :=
                ppg_pinBoxDelta_eq axis bands s bb.id
              have h3 : bandShift bands bb.id = Cb.shift :=
                bandShift_eq hCbMemB hCbCov (hUniq bb.id)
              rw [hBv, h2, h3]
            have hBs' : Axis.start axis b'.rect =
                Axis.start axis bb.rect + Db := hBs
            have hCbMemBB : bb.id ∈ Cb.members := by
              rcases hCbCov with hEq | hMem
              · exact ppg_id_mem_of_nodup hModelNodup hbands hCbMemB
                  (by intro hcon; exact hbbNe (hEq.symm.trans hcon)) hEq.symm
              · exact hMem
            have hfindB : s.boxes.find? (fun b' => b'.id == bb.id) = some bb :=
              sceneFind?_eq_self hNodupS hbb
            have hCbCases := layBands_mem_cases (band := Cb) (hbands ▸ hCbMemB)
            rcases hCbCases with hCbLane | hCbLoose
            · obtain ⟨blane, _, bst, rfl⟩ := layLanes_mem_lane hCbLane
              have hwithinB : (laneBand boxes s axis sp blane bst).start ≤
                  Axis.start axis bb.rect +
                    (laneBand boxes s axis sp blane bst).shift ∧
                  Axis.start axis bb.rect + Axis.length axis bb.rect +
                    (laneBand boxes s axis sp blane bst).shift ≤
                  (laneBand boxes s axis sp blane bst).start +
                    (laneBand boxes s axis sp blane bst).thickness :=
                laneMember_within ht hc hCbMemBB hfindB
              have hBl' : Axis.length axis b'.rect =
                  Axis.length axis bb.rect := hBl
              have hBsLo : (laneBand boxes s axis sp blane bst).start ≤
                  Axis.start axis b'.rect := by
                rw [hBs', hDbShift]
                exact hwithinB.1
              have hBsHi : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                  (laneBand boxes s axis sp blane bst).start +
                    (laneBand boxes s axis sp blane bst).thickness := by
                omega
              by_cases hSame : (laneBand boxes s axis sp glane gst) =
                  (laneBand boxes s axis sp blane bst)
              · -- same band: same shift, base transfers
                have hDbShift' : Db =
                    (laneBand boxes s axis sp glane gst).shift := by
                  rw [hSame]; exact hDbShift
                have hDD : Dg = Db := hDgShift.trans hDbShift'.symm
                have hBsD : Axis.start axis b'.rect =
                    Axis.start axis bb.rect + Dg := by
                  rw [hDD]; exact hBs'
                exact ppg_transfer_disjoint hGs' hGl' hBsD hBl' hxg hyg hxb hyb
                  hDisjBase
              · have hord := tiled_ordered hTiled hnonnegB hCgMemB hCbMemB hSame
                exact disjoint_of_bands (axis := axis) hGsLo hGsHi hBsLo hBsHi
                  hord
            · -- Cb loose: lane end below loose shifted start
              have hmemL : bb.id ∈ looseNodes boxes := by
                have h2 := hCbMemBB
                rw [hCbLoose] at h2
                exact ppg_looseBand_mem h2
              have hlowerB : Cb.start ≤ Axis.start axis bb.rect + Cb.shift := by
                rw [hCbLoose]
                exact looseMember_lower hc hmemL hfindB
              have hle : (laneBand boxes s axis sp glane gst).start +
                  (laneBand boxes s axis sp glane gst).thickness ≤ Cb.start := by
                have hLend := ppg_lane_end_le_loose ht hc hCgLane
                rw [hCbLoose, looseBand_start]
                exact hLend
              have hBle : Axis.start axis g'.rect + Axis.length axis g'.rect ≤
                  Axis.start axis b'.rect := by
                have h2 : Cb.start ≤ Axis.start axis b'.rect := by
                  rw [hBs', hDbShift]
                  exact hlowerB
                omega
              exact ppg_disjoint_of_axis_le hBle
        · -- Cg loose
          have hmemL : gb.id ∈ looseNodes boxes := by
            have h2 := hCgMemBB
            rw [hCgLoose] at h2
            exact ppg_looseBand_mem h2
          have hlowerG : Cg.start ≤ Axis.start axis gb.rect + Cg.shift := by
            rw [hCgLoose]
            exact looseMember_lower hc hmemL hfindG
          have hGsLo : Cg.start ≤ Axis.start axis g'.rect := by
            rw [hGs', hDgShift]
            exact hlowerG
          rcases hrectb with ⟨Fb, hFbMemB, hFbId, hFbStart, hFbLen⟩ | ⟨Db, hBs, hBl, hBv⟩
          · -- b' frame, Cg loose
            have hFbCb : Fb = Cb :=
              hUniq bb.id Fb hFbMemB Cb hCbMemB (Or.inl hFbId.symm) hCbCov
            have hBsB : Axis.start axis b'.rect = Cb.start := by
              rw [← hFbCb]; exact hFbStart
            have hBlB : Axis.length axis b'.rect = Cb.thickness := by
              rw [← hFbCb]; exact hFbLen
            by_cases hSame : Cg = Cb
            · exfalso
              have hmem : gb.id ∈ Cb.members := by
                rw [← hSame]; exact hCgMemBB
              have hCbFb : Cb.id = Fb.id := by rw [hFbCb]
              have hCbBb : Cb.id = bb.id := hCbFb.trans hFbId.symm
              have hpar := hparAnc Cb hCbMemB ⟨bb, hbb, hCbBb.symm⟩ gb.id hmem
              rcases hpar with hEq | hmem2
              · exact hneBB (hCbBb.symm.trans hEq.symm)
              · exact hAnc2 (by rw [hCbBb] at hmem2; exact hmem2)
            · have hFbLay : Fb ∈ layLanes boxes s axis sp (lanesOf boxes)
                  (firstLaneStart s (lanesOf boxes) axis) := by
                have hC := layBands_mem_cases (band := Fb) (hbands ▸ hFbMemB)
                rcases hC with hL | hO
                · exact hL
                · exfalso
                  have hId : Fb.id = "" := by
                    rw [hO]; exact ppg_looseBand_id _ _ _ _ _ _
                  exact hNoEmpty bb hbb (hFbId.trans hId)
              have hle : Fb.start + Fb.thickness ≤ Cg.start := by
                have hLend := ppg_lane_end_le_loose ht hc hFbLay
                rw [hCgLoose, looseBand_start]
                exact hLend
              have hBle : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                  Axis.start axis g'.rect := by
                have hFbS : Axis.start axis b'.rect = Fb.start := hFbStart
                have hFbL : Axis.length axis b'.rect = Fb.thickness := hFbLen
                have h1b : Axis.start axis b'.rect + Axis.length axis b'.rect =
                    Fb.start + Fb.thickness := by rw [hFbS, hFbL]
                omega
              exact (Disjoint.comm _ _).mpr (ppg_disjoint_of_axis_le hBle)
          · -- b' shifted, Cg loose
            have hDbShift : Db = Cb.shift := by
              have h2 : (buildPin axis bands s).boxDelta bb.id =
                  bandShift bands bb.id :=
                ppg_pinBoxDelta_eq axis bands s bb.id
              have h3 : bandShift bands bb.id = Cb.shift :=
                bandShift_eq hCbMemB hCbCov (hUniq bb.id)
              rw [hBv, h2, h3]
            have hBs' : Axis.start axis b'.rect =
                Axis.start axis bb.rect + Db := hBs
            have hCbMemBB : bb.id ∈ Cb.members := by
              rcases hCbCov with hEq | hMem
              · exact ppg_id_mem_of_nodup hModelNodup hbands hCbMemB
                  (by intro hcon; exact hbbNe (hEq.symm.trans hcon)) hEq.symm
              · exact hMem
            have hfindB : s.boxes.find? (fun b' => b'.id == bb.id) = some bb :=
              sceneFind?_eq_self hNodupS hbb
            have hCbCases := layBands_mem_cases (band := Cb) (hbands ▸ hCbMemB)
            rcases hCbCases with hCbLane | hCbLoose
            · obtain ⟨blane, _, bst, rfl⟩ := layLanes_mem_lane hCbLane
              have hwithinB : (laneBand boxes s axis sp blane bst).start ≤
                  Axis.start axis bb.rect +
                    (laneBand boxes s axis sp blane bst).shift ∧
                  Axis.start axis bb.rect + Axis.length axis bb.rect +
                    (laneBand boxes s axis sp blane bst).shift ≤
                  (laneBand boxes s axis sp blane bst).start +
                    (laneBand boxes s axis sp blane bst).thickness :=
                laneMember_within ht hc hCbMemBB hfindB
              have hBl' : Axis.length axis b'.rect =
                  Axis.length axis bb.rect := hBl
              have hBsHi : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                  (laneBand boxes s axis sp blane bst).start +
                    (laneBand boxes s axis sp blane bst).thickness := by
                omega
              have hle : (laneBand boxes s axis sp blane bst).start +
                  (laneBand boxes s axis sp blane bst).thickness ≤ Cg.start := by
                have hLend := ppg_lane_end_le_loose ht hc hCbLane
                rw [hCgLoose, looseBand_start]
                exact hLend
              have hBle : Axis.start axis b'.rect + Axis.length axis b'.rect ≤
                  Axis.start axis g'.rect := by
                omega
              exact (Disjoint.comm _ _).mpr (ppg_disjoint_of_axis_le hBle)
            · -- both loose: same band, same shift, base transfers
              have hSameLL : Cg = Cb := hCgLoose.trans hCbLoose.symm
              have hDbShift' : Db = Cg.shift := by
                rw [hSameLL]; exact hDbShift
              have hDD : Dg = Db := hDgShift.trans hDbShift'.symm
              have hBsD : Axis.start axis b'.rect =
                  Axis.start axis bb.rect + Dg := by
                rw [hDD]; exact hBs'
              have hBl' : Axis.length axis b'.rect =
                  Axis.length axis bb.rect := hBl
              have hGl' : Axis.length axis g'.rect =
                  Axis.length axis gb.rect := hGl
              exact ppg_transfer_disjoint hGs' hGl' hBsD hBl' hxg hyg hxb hyb
                hDisjBase
    have hOrigin : Validator.C8a origin.layoutDump := by
      rcases restoreOriginShift horig with ⟨hpairs, hmove⟩
      exact c8a_of_restore hroutedBoxes hpairs hmove hPinned
    exact c8a_of_boxes_eq hrBoxes hOrigin

end LaneBands
end Layered
end Elegant
