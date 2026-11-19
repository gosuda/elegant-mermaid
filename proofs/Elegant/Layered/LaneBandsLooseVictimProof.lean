import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsFrameClause
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-! # Loose-band route against lane-band box after the swimlane pin.

Verdict on full pin-axis containment of kept loose-band routes: FALSE.
`wip/Probe/LaneBandsLooseVictimProofProbe.lean` evaluates executed
layouts: on `mCross` the loose self-loop `e4` has base pin-axis points
`[22012, 22780, 22780, 22012]` while its loose band covers `[19930, 22012]`
(`lower=true`, `upper=false`; the overshoot is one routing slot, `768`).
The same shape recurs on `mLooseBetween`, `mLooseSelf`, `mNested` and
`mEmptyLane` (e.g. `mLooseSelf e0`: points `[3106, 3874, 3874, 3106]` over
`[1024, 3106]`). Full containment would need `contentValues` to cover
routes, but loose content covers boxes only (`inLane boxes id ""` is always
false), so no strip bound applies to a kept loose route.

The true form the consumer needs is one-sided: every loose-covered route
point sits at or above the loose content minimum (`lower=true` on all
seven executed probes: `mCross`, `mTwoLoose`, `mLooseBetween`,
`mLaneLoose`, `mLooseSelf`, `mNested`, `mEmptyLane`; the ill-formed `mIll`
is rejected by `layoutFamily`). Lane boxes sit inside lane slots, lane
slots precede the loose slot, and the loose slot starts at or below the
lower bound, so a lower-bounded loose route misses every lane-band box
along the pin axis. The Bool mirror `looseResidB` of
`PinLooseRouteLaneVictimClear` over actual scene pairs is `true` on the
same probes, and pinned `C6` holds throughout.

`PinLooseRouteLower` is the narrowed lemma on the way (one public named
def over executed runs, true on the probes). `pinLooseVictimMissOfLower`
proves the loose-vs-lane sub-case from bundle facts plus the lower bound,
staying name-free of the tracked file's private shift helpers so both
modules resolve. The bridge `pinLooseRouteLaneVictimClear_of_lower` and
the closed `pinBands_c6_executed_closed` live at the end of the tracked
`LaneBandsKeptClearExecutedProof.lean`, which imports this module. -/

/-- Pin-axis shift of a point by one band delta (public copy of the tracked
kept-route shift, so the narrowed fact stays name-free). -/
def lvShiftPoint (axis : Axis) (delta : Int) (p : Point) : Point :=
  axis.withPoint p (axis.point p + delta)

/-- Pin-axis shift of a rect by one band delta (public copy of the tracked
kept-box shift, so the narrowed fact stays name-free). -/
def lvShiftRect (axis : Axis) (delta : Int) (r : Rect) : Rect :=
  axis.withStart r (axis.start r + delta)

/-- The narrowed loose-pair lemma on the way: every route whose ends both
lie in the loose band has all base pin-axis points at or above the loose
content minimum (shifted: inside-or-above the loose slot start). True on
every executed probe (`lower=true`); false in general for arbitrary
scenes, so it travels as the single residual. -/
def PinLooseRouteLower (axis : Axis) (bands : List Band) (s : Scene)
    (sp : Spacing) : Prop :=
  ∀ (old : Route), old ∈ s.routes →
    ∀ (j1 : Nat), (hj1 : j1 < bands.length) →
      (bands[j1]'hj1).id = "" →
      bands.findIdx? (fun b_ => b_.id == old.fromId ||
        decide (old.fromId ∈ b_.members)) = some j1 →
      bands.findIdx? (fun b_ => b_.id == old.toId ||
        decide (old.toId ∈ b_.members)) = some j1 →
      ∀ p ∈ old.points,
        (bands[j1]'hj1).start + sp.clear ≤
          axis.point p + (bands[j1]'hj1).shift

/-- `findIdx?` success gives the index and the predicate there. -/
private theorem lvFindIdx_pred {α : Type} {p : α → Bool} {l : List α} {i : Nat}
    (h : l.findIdx? p = some i) : ∃ hlt : i < l.length, p (l[i]'hlt) = true := by
  obtain ⟨hlt, hpred, _⟩ := (List.findIdx?_eq_some_iff_getElem).mp h
  exact ⟨hlt, hpred⟩

/-- Thickness sums are non-negative (prefixed copy). -/
private theorem lvSumNonneg (bands : List Band)
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

/-- Every band of a non-negative tiling ends at or before the tiling end
(prefixed copy). -/
private theorem lvTiledEndLe {start : Int} {bands : List Band}
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
    have hsumNonneg := lvSumNonneg bs htailNonneg
    rcases hmem with rfl | hmem
    · simp only [List.map_cons, List.sum_cons]
      omega
    · have hle := ih (start := start + b.thickness) htail htailNonneg hmem
      simp only [List.map_cons, List.sum_cons] at hle ⊢
      omega

/-- Every lane band ends at or before the loose band start. -/
private theorem lvLaneEndLe {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} (ht : 0 ≤ sp.title) (hc : 0 ≤ sp.clear)
    {L : Band}
    (hmem : L ∈ layLanes boxes s axis sp (lanesOf boxes)
      (firstLaneStart s (lanesOf boxes) axis)) :
    L.start + L.thickness ≤ firstLaneStart s (lanesOf boxes) axis +
      (((layLanes boxes s axis sp (lanesOf boxes)
        (firstLaneStart s (lanesOf boxes) axis)).map fun b => b.thickness)).sum := by
  exact lvTiledEndLe (layLanes_tiled boxes s axis sp (lanesOf boxes) _)
    (layLanes_thickness_nonneg boxes s axis sp (lanesOf boxes) _ ht hc) hmem
/-- Pin-axis coordinate of a shifted point. -/
private theorem lvShiftPoint_point (axis : Axis) (delta : Int) (p : Point) :
    axis.point (lvShiftPoint axis delta p) = axis.point p + delta := by
  cases axis <;> rfl

/-- Pin-axis start of a shifted rect. -/
private theorem lvShiftRect_start (axis : Axis) (delta : Int) (r : Rect) :
    axis.start (lvShiftRect axis delta r) = axis.start r + delta := by
  cases axis <;> rfl

/-- Cross-axis length is unchanged by a pin-axis shift. -/
private theorem lvShiftRect_length (axis : Axis) (delta : Int) (r : Rect) :
    axis.length (lvShiftRect axis delta r) = axis.length r := by
  cases axis <;> rfl

/-- One-sided strip miss: a polyline entirely at or above `Rlo` misses a
rect ending at or below `Rlo` along the pin axis. -/
private theorem lvStripMiss {axis : Axis} {pts : List Point} {r : Rect} {Rlo : Int}
    (hroute : ∀ q ∈ pts, Rlo ≤ axis.point q)
    (hbox : axis.start r + axis.length r ≤ Rlo) : ¬ Polyline.hitsRect pts r := by
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
        have hp := hroute p hpm
        have hq := hroute q hqm
        refine ⟨?_, ih (fun p' hp' => hroute p' (List.mem_cons_of_mem _ hp'))⟩
        cases axis with
        | x =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox ⊢
          exact Or.inr (Or.inl (by omega))
        | y =>
          simp only [Axis.point, Axis.start, Axis.length] at hp hq hbox ⊢
          exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  intro hhit
  obtain ⟨_, _, hmiss⟩ := hhit
  exact hmiss hall

/-- A lane id comes from a root group model box (prefixed copy). -/
private theorem lvLanesOfMem {boxes : List ModelBox} {lane : String}
    (h : lane ∈ lanesOf boxes) :
    ∃ mb ∈ boxes, mb.role = .group ∧ mb.parent = "" ∧ mb.id = lane := by
  unfold lanesOf at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  obtain ⟨hxb, hpred⟩ := List.mem_filter.mp hx
  simp only [Bool.and_eq_true] at hpred
  obtain ⟨hrole, hpar⟩ := hpred
  exact ⟨x, hxb, beq_iff_eq.mp hrole, beq_iff_eq.mp hpar, rfl⟩

/-- A lane is in its own lane (prefixed copy). -/
private theorem lvInLaneSelf {boxes : List ModelBox} {lane : String}
    (hlane : lane ∈ lanesOf boxes) (hnodup : (boxes.map (·.id)).Nodup) :
    inLane boxes lane lane = true := by
  obtain ⟨mb, hmb, hrole, hpar, hid⟩ := lvLanesOfMem hlane
  have hfind : boxes.find? (fun b => b.id == lane) = some mb := by
    have h0 := modelFind?_eq_self hnodup hmb
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

/-- A lane-covered victim box stays inside its lane slot (shifted). -/
private theorem lvLaneBoxSlot {axis : Axis} {bands : List Band} {s : Scene}
    {boxes : List ModelBox} {sp : Spacing} {b_old : Box} {j : Nat}
    {lane : String} {st : Int}
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear)
    (hnodupS : (s.boxes.map (·.id)).Nodup)
    (hnodupM : (boxes.map (·.id)).Nodup)
    (hbmem : b_old ∈ s.boxes)
    (hj : j < bands.length)
    (hgeq : (bands[j]'hj) = laneBand boxes s axis sp lane st)
    (hlane : lane ∈ lanesOf boxes)
    (hjcov : bands.findIdx? (fun b_ => b_.id == b_old.id ||
      decide (b_old.id ∈ b_.members)) = some j) :
    (bands[j]'hj).start ≤ axis.start b_old.rect + (bands[j]'hj).shift ∧
      axis.start b_old.rect + axis.length b_old.rect + (bands[j]'hj).shift ≤
        (bands[j]'hj).start + (bands[j]'hj).thickness := by
  obtain ⟨hj_lt, hpred⟩ := lvFindIdx_pred hjcov
  have heqjj : (bands[j]'hj_lt) = (bands[j]'hj) := rfl
  have hpred' : ((bands[j]'hj_lt).id == b_old.id ||
      decide (b_old.id ∈ (bands[j]'hj_lt).members)) = true := hpred
  rw [Bool.or_eq_true] at hpred'
  have hmem : b_old.id ∈ (laneBand boxes s axis sp lane st).members := by
    rcases hpred' with h | h
    · have heq : (bands[j]'hj_lt).id = b_old.id := beq_iff_eq.mp h
      have hlaneid : (bands[j]'hj).id = lane := by rw [hgeq]; rfl
      rw [heqjj] at heq
      rw [hlaneid] at heq
      have heq' : b_old.id = lane := heq.symm
      obtain ⟨mb, hmb, _, _, hid⟩ := lvLanesOfMem hlane
      have hself : inLane boxes lane lane = true := lvInLaneSelf hlane hnodupM
      have hmemF : mb ∈ boxes.filter fun b_ => inLane boxes b_.id lane := by
        rw [List.mem_filter]
        refine ⟨hmb, ?_⟩
        rw [hid]
        exact hself
      have hmemL : (bands[j]'hj).members =
          (boxes.filter fun b => inLane boxes b.id lane).map (·.id) := by
        rw [hgeq]; rfl
      have hmap : lane ∈ (boxes.filter fun b_ =>
          inLane boxes b_.id lane).map (·.id) :=
        List.mem_map.mpr ⟨mb, hmemF, hid⟩
      have hB2mem : lane ∈ (bands[j]'hj).members := by
        rw [hmemL]; exact hmap
      have hgoal : b_old.id ∈ (laneBand boxes s axis sp lane st).members := by
        rw [← hgeq, heq']
        exact hB2mem
      exact hgoal
    · have hm : b_old.id ∈ (bands[j]'hj_lt).members := of_decide_eq_true h
      rw [heqjj] at hm
      have hmem' : b_old.id ∈ (laneBand boxes s axis sp lane st).members := by
        rw [← hgeq]
        exact hm
      exact hmem'
  have hfind : s.boxes.find? (fun b' => b'.id == b_old.id) = some b_old :=
    sceneFind?_eq_self hnodupS hbmem
  obtain ⟨hs1, hs2⟩ := laneMember_within hnn.1 hnn.2 hmem hfind
  have hs1' : (laneBand boxes s axis sp lane st).start ≤
      axis.start b_old.rect + (laneBand boxes s axis sp lane st).shift := hs1
  have hs2' : axis.start b_old.rect + axis.length b_old.rect +
      (laneBand boxes s axis sp lane st).shift ≤
      (laneBand boxes s axis sp lane st).start +
        (laneBand boxes s axis sp lane st).thickness := hs2
  have hsh : (laneBand boxes s axis sp lane st).shift =
      (bands[j]'hj).shift := by
    rw [← hgeq]
  have hst : (laneBand boxes s axis sp lane st).start =
      (bands[j]'hj).start := by
    rw [← hgeq]
  have hth : (laneBand boxes s axis sp lane st).thickness =
      (bands[j]'hj).thickness := by
    rw [← hgeq]
  rw [hsh] at hs1' hs2'
  rw [hst] at hs1' hs2'
  rw [hth] at hs2'
  exact ⟨hs1', hs2'⟩
/-- The true form: a lower-bounded loose-band route misses a lane-band box.
Sub-case of `PinLooseRouteLaneVictimClear` for actual shifted pairs: the
route stays at or above the loose slot start while the lane box sits inside
its lane slot, and lane slots precede the loose slot. Proved from executed
bundle facts plus the narrowed lower bound. -/
theorem pinLooseVictimMissOfLower {axis : Axis} {bands : List Band}
    {s : Scene} {boxes : List ModelBox} {sp : Spacing}
    {r old : Route} {b b_old : Box} {j1 j : Nat}
    (hbands : bands = layBands boxes s axis sp (lanesOf boxes))
    (hnn : 0 ≤ sp.title ∧ 0 ≤ sp.clear)
    (hnodupS : (s.boxes.map (·.id)).Nodup)
    (hnodupM : (boxes.map (·.id)).Nodup)
    (hneM : ∀ b ∈ boxes, b.id ≠ "")
    (hbmem : b_old ∈ s.boxes)
    (hj1 : j1 < bands.length) (hfiL : (bands[j1]'hj1).id = "")
    (hj : j < bands.length) (hjL : (bands[j]'hj).id ≠ "")
    (hjcov : bands.findIdx? (fun b_ => b_.id == b_old.id ||
      decide (b_old.id ∈ b_.members)) = some j)
    (hrPts : r.points =
      old.points.map (lvShiftPoint axis (bands[j1]'hj1).shift))
    (hbRect : b.rect = lvShiftRect axis (bands[j]'hj).shift b_old.rect)
    (hlower : ∀ p ∈ old.points, (bands[j1]'hj1).start + sp.clear ≤
      axis.point p + (bands[j1]'hj1).shift) :
    ¬ Polyline.hitsRect r.points b.rect := by
  have hgjL : bands[j]'hj ∈ layBands boxes s axis sp (lanesOf boxes) := by
    rw [← hbands]
    exact List.getElem_mem hj
  have hgj1 : bands[j1]'hj1 ∈ layBands boxes s axis sp (lanesOf boxes) := by
    rw [← hbands]
    exact List.getElem_mem hj1
  rcases layBands_mem_cases hgjL with hlay | hloose
  · obtain ⟨lane, hlane, st, hgeq⟩ := layLanes_mem_lane hlay
    obtain ⟨hs1, hs2⟩ :=
      lvLaneBoxSlot hnn hnodupS hnodupM hbmem hj hgeq hlane hjcov
    have hle := lvLaneEndLe hnn.1 hnn.2 hlay
    rcases layBands_mem_cases hgj1 with hc1lay | hc1loose
    · obtain ⟨lane1, hlane1, _, hgeq1⟩ := layLanes_mem_lane hc1lay
      have hid1 : (bands[j1]'hj1).id = lane1 := by rw [hgeq1]; rfl
      rw [hid1] at hfiL
      obtain ⟨mb1, hmb1, _, _, hidmb1⟩ := lvLanesOfMem hlane1
      have hne1 : lane1 ≠ "" := by
        rw [← hidmb1]
        exact hneM mb1 hmb1
      exact absurd hfiL hne1
    · have hB1start : (bands[j1]'hj1).start =
          firstLaneStart s (lanesOf boxes) axis +
          (((layLanes boxes s axis sp (lanesOf boxes)
            (firstLaneStart s (lanesOf boxes) axis)).map
            fun b => b.thickness)).sum := by
        rw [hc1loose]
        exact looseBand_start _ _ _ _ _ _
      have hroute : ∀ q ∈ r.points,
          (bands[j1]'hj1).start + sp.clear ≤ axis.point q := by
        rw [hrPts]
        intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
        rw [lvShiftPoint_point]
        exact hlower p hp
      have hbox : axis.start b.rect + axis.length b.rect ≤
          (bands[j1]'hj1).start + sp.clear := by
        rw [hbRect, lvShiftRect_start, lvShiftRect_length]
        omega
      exact lvStripMiss hroute hbox
  · have hid2 : (bands[j]'hj).id = "" := by
      rw [hloose]
      unfold looseBand
      split <;> rfl
    exact absurd hid2 hjL

end LaneBands
end Layered
end Elegant
