import Elegant.Kinds.Swimlane
import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsBoxClausesExecuted
import Elegant.Layered.LaneBandsFindRouteFactsProof
import Elegant.Layered.LaneEnds
import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneEndsPinExec
import Elegant.Layered.LaneEndsPinRerouteBoundary
import Elegant.Layered.LaneEndsPinFrameTransport
import ElegantGeometry.Validator

set_option autoImplicit false

/-! The former same-band-or-kink premise fails on the two successful layouts
in SwimlaneEndsAboveProof. The reroute step rebuilds those routes and sets
fresh endpoints. A kept route with equal band shifts moves rigidly. -/

namespace Elegant
namespace Kinds

open Elegant.Layered.LaneBands
open Elegant.Layered

/-- The reroute-shape disjunct of the replacement seam: the route joins two
different bands with at least two points and both endpoints band-covered,
which is exactly when `rerouteBands` rebuilds it. -/
def SwimlaneEndsRerouted (m : Model) (base : Layered.FamilyResult) (sp : Spacing)
    (rt : Route) : Prop :=
  ∃ fi ti : Nat,
    (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes)).findIdx?
        (fun b => b.id == rt.fromId || b.members.contains rt.fromId) = some fi ∧
    (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
      (lanesOf m.boxes)).findIdx?
        (fun b => b.id == rt.toId || b.members.contains rt.toId) = some ti ∧
    fi ≠ ti ∧ 1 < rt.points.length

/-- Replacement for the refuted `endsSplit` seam: on every executed run, each
base route is either rerouted-shaped or has equal endpoint band shifts. -/
def SwimlaneEndsPremise (m : Model) : Prop :=
  ∀ base : Layered.FamilyResult,
    Layered.layoutFamily (Swimlane.input m) m.options = .ok base →
    ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
    ∀ rt ∈ base.scene.routes,
      SwimlaneEndsRerouted m base sp rt ∨
        bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) rt.fromId =
        bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)) rt.toId

namespace SwimlaneEndsCutover

/-! ### Bool mirror of the premise and its exact equivalence -/

/-- Bool mirror of the reroute-shape disjunct (same definition as
`SwimlaneEndsSplitCutoverProbe.reroutedShapeB`). -/
def reroutedShapeB (bands : List Band) (r : Route) : Bool :=
  match bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId),
        bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) with
  | some fi, some ti => fi != ti && 1 < r.points.length
  | _, _ => false

/-- Bool mirror of the whole replacement premise over an executed run
(same definition as `SwimlaneEndsSplitCutoverProbe.endsShiftB`). -/
def endsShiftB (m : Model) (base : Layered.FamilyResult)
    (axis : LaneBands.Axis) (sp : Spacing) : Bool :=
  let bands := layBands m.boxes base.scene axis sp (lanesOf m.boxes)
  base.scene.routes.all fun r =>
    reroutedShapeB bands r || bandShift bands r.fromId == bandShift bands r.toId

/-- The reroute-shape Bool mirror is exactly the reroute-shape disjunct. -/
theorem reroutedShapeB_iff (bands : List Band) (r : Route) :
    reroutedShapeB bands r = true ↔
      ∃ fi ti : Nat,
        bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) = some fi ∧
        bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) = some ti ∧
        fi ≠ ti ∧ 1 < r.points.length := by
  simp only [reroutedShapeB]
  cases hf : bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) with
  | none => simp
  | some fi =>
    cases ht : bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) with
    | none => simp
    | some ti =>
      constructor
      · intro hbool
        rcases Bool.and_eq_true_iff.mp hbool with ⟨hne, hlen⟩
        exact ⟨fi, ti, rfl, rfl, bne_iff_ne.mp hne, of_decide_eq_true hlen⟩
      · rintro ⟨_fi', _ti', hfi, hti, hne, hlen⟩
        cases Option.some.inj hfi
        cases Option.some.inj hti
        exact Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr hne, decide_eq_true hlen⟩

/-- The checked Bool equals the per-run premise body in the axis-form it is
elaborated at: on any executed run (fixed `base`, `axis`, `sp`),
`endsShiftB = true` is exactly the disjunction the ends consumer needs.
The probe prints `endsShift=true` for the two refuting models; this
theorem lifts that evaluation to the proposition. -/
theorem endsShiftB_eq (m : Model) (base : Layered.FamilyResult)
    (axis : LaneBands.Axis) (sp : Spacing) :
    endsShiftB m base axis sp = true ↔
      ∀ rt ∈ base.scene.routes,
        (∃ fi ti : Nat,
            (layBands m.boxes base.scene axis sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == rt.fromId || b.members.contains rt.fromId) = some fi ∧
            (layBands m.boxes base.scene axis sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == rt.toId || b.members.contains rt.toId) = some ti ∧
            fi ≠ ti ∧ 1 < rt.points.length) ∨
          bandShift (layBands m.boxes base.scene axis sp (lanesOf m.boxes)) rt.fromId =
          bandShift (layBands m.boxes base.scene axis sp (lanesOf m.boxes)) rt.toId := by
  unfold endsShiftB
  constructor
  · intro h rt hrt
    have hr := List.all_eq_true.mp h rt hrt
    rcases Bool.or_eq_true_iff.mp hr with hbool | hbool
    · exact Or.inl ((reroutedShapeB_iff _ rt).mp hbool)
    · exact Or.inr (beq_iff_eq.mp hbool)
  · intro h
    apply List.all_eq_true.mpr
    intro rt hrt
    apply Bool.or_eq_true_iff.mpr
    rcases h rt hrt with hrer | hshift
    · exact Or.inl ((reroutedShapeB_iff _ rt).mpr hrer)
    · exact Or.inr (beq_iff_eq.mpr hshift)

/-- Instantiated form at the executed axis: the probe's `endsShift=true`
verdict on a model and a successful run lifts to the premise body that
`swimlane_endsOld_of_premise` consumes. -/
theorem endsShiftB_premise {m : Model} {base : Layered.FamilyResult} {sp : Spacing}
    (hbool : endsShiftB m base (Axis.ofDirection m.options.direction) sp = true) :
    ∀ rt ∈ base.scene.routes,
      SwimlaneEndsRerouted m base sp rt ∨
        bandShift (layBands m.boxes base.scene
          (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.fromId =
        bandShift (layBands m.boxes base.scene
          (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.toId := by
  have h := (endsShiftB_eq m base (Axis.ofDirection m.options.direction) sp).mp hbool
  intro rt hrt
  rcases h rt hrt with hex | hshift
  · exact Or.inl hex
  · exact Or.inr hshift

private theorem se_bind {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem se_nodup_map_inj {α β : Type} [BEq β] [LawfulBEq β] (g : α → β)
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

private theorem se_mapM_point_head {m : Move} {axis : LaneBands.Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs → ∀ p,
      ps.head? = some p → ∃ q, qs.head? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x xs ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := se_bind h
    obtain ⟨rest', hrest, hrfl⟩ := se_bind h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
    subst hrfl
    have hpx : x = p := by simpa using hp
    subst hpx
    exact ⟨x', rfl, hx'⟩

private theorem se_mapM_point_getLast {m : Move} {axis : LaneBands.Axis} :
    ∀ (ps qs : List Point), ps.mapM (m.point axis) = .ok qs → ∀ p,
      ps.getLast? = some p → ∃ q, qs.getLast? = some q ∧ m.point axis p = .ok q := by
  intro ps
  induction ps with
  | nil => intro qs _ p hp; simp at hp
  | cons x rest ih =>
    intro qs h p hp
    rw [List.mapM_cons] at h
    obtain ⟨x', hx', h⟩ := se_bind h
    obtain ⟨rest', hrest, hrfl⟩ := se_bind h
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
      obtain ⟨q, hq, hfun⟩ := ih _ hrest p hp
      refine ⟨q, ?_, hfun⟩
      rw [List.getLast?_cons, hq]
      rfl

/-- Head of a constant-move `mapM` in general head form: the first point
shifts by exactly delta. -/
private theorem se_const_head' {axis : LaneBands.Axis} {delta : Int} {p : Point}
    {ps qs : List Point}
    (h : ps.mapM ((Move.constant delta).point axis) = .ok qs)
    (hp : ps.head? = some p) :
    ∃ qP, qs.head? = some qP ∧ qP = axis.withPoint p (axis.point p + delta) := by
  obtain ⟨qP, hhead, hfun⟩ := se_mapM_point_head _ _ h p hp
  unfold Move.point at hfun
  obtain ⟨w, hw, hrfl⟩ := se_bind hfun
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have happEq : (Move.constant delta).apply (axis.point p) =
      Measure.checkedI32 (axis.point p + delta) := by
    simp [Move.apply, Move.offset]
  rw [happEq] at hw
  have hwEq : w = axis.point p + delta := checked_value hw
  refine ⟨_, hhead, ?_⟩
  rw [hwEq]

/-- Last of a constant-move `mapM` in general last form: the last point
shifts by exactly delta. -/
private theorem se_const_last' {axis : LaneBands.Axis} {delta : Int} {q : Point}
    {ps qs : List Point}
    (h : ps.mapM ((Move.constant delta).point axis) = .ok qs)
    (hq : ps.getLast? = some q) :
    ∃ qQ, qs.getLast? = some qQ ∧ qQ = axis.withPoint q (axis.point q + delta) := by
  obtain ⟨qQ, hlast, hfun⟩ := se_mapM_point_getLast _ _ h q hq
  unfold Move.point at hfun
  obtain ⟨w, hw, hrfl⟩ := se_bind hfun
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
  subst hrfl
  have happEq : (Move.constant delta).apply (axis.point q) =
      Measure.checkedI32 (axis.point q + delta) := by
    simp [Move.apply, Move.offset]
  rw [happEq] at hw
  have hwEq : w = axis.point q + delta := checked_value hw
  refine ⟨_, hlast, ?_⟩
  rw [hwEq]

private theorem se_frame_mem {axis : LaneBands.Axis} {bands : List Band} {s : Scene}
    {f : LaneFrame} (hf : f ∈ laneFrames axis bands s) :
    ∃ band ∈ bands, ∃ b ∈ s.boxes, band.id = f.id ∧
      f.near = axis.start b.rect + band.shift - band.start ∧
      f.length = axis.length b.rect ∧
      s.boxes.find? (fun b => b.id == band.id) = some b := by
  unfold laneFrames at hf
  obtain ⟨band, hband, hfb⟩ := List.mem_filterMap.mp hf
  cases hfind : s.boxes.find? (fun b => b.id == band.id) with
  | none => simp [hfind] at hfb
  | some b =>
    simp [hfind] at hfb
    subst hfb
    exact ⟨band, hband, b, List.mem_of_find?_eq_some hfind, rfl, rfl, rfl, hfind⟩

/-- End-rect of a pinned endpoint box equals the base box shifted by its
band shift, in both the lane-frame and non-frame cases. -/
private theorem se_endRect_shift {m : Model} {base : Layered.FamilyResult}
    {pinned : Scene} {sp : Spacing} {delta : Int}
    {eid : String} {fb0 bp : Box}
    (hModelClean : (m.boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ m.boxes, b.id ≠ "")
    (hnodupB : (base.scene.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "")
    (hsp : spacingOf m.options.profile = .ok sp)
    (happ : applyPin (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
      base.scene) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene = .ok pinned)
    (hb0 : fb0 ∈ base.scene.boxes) (hid0 : fb0.id = eid)
    (hbp : bp ∈ pinned.boxes) (hpid : bp.id = eid)
    (hdelta : delta = bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) eid) :
    endRect (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) bp =
      (Axis.ofDirection m.options.direction).withStart fb0.rect
        ((Axis.ofDirection m.options.direction).start fb0.rect + delta) := by
  have haxis : (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
      base.scene).axis = Axis.ofDirection m.options.direction := rfl
  have hfindS0 : base.scene.boxes.find? (fun b => b.id == fb0.id) = some fb0 := by
    cases hf : base.scene.boxes.find? (fun b => b.id == fb0.id) with
    | none =>
      exact (List.find?_eq_none.mp hf fb0 hb0 (beq_self_eq_true _)).elim
    | some b =>
      have hbmem := List.mem_of_find?_eq_some hf
      have hbid : b.id = fb0.id := by
        have h := List.find?_some hf
        simpa using h
      have hbEq : b = fb0 :=
        se_nodup_map_inj (fun x : Box => x.id) hnodupB hbmem hb0 hbid
      subst hbEq
      rfl
  cases hfind : (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
      base.scene).find? (fun b_ => b_.id == bp.id) with
  | some f =>
    obtain ⟨band, hband, _bS, _hbmem, hidband, _hneF, _hlenF, _hfindS⟩ :=
      se_frame_mem (List.mem_of_find?_eq_some hfind)
    have hfid : f.id = bp.id := by
      have h := List.find?_some hfind
      simpa using h
    have hbandid : band.id = eid := hidband.trans (hfid.trans hpid)
    have hne' : eid ≠ "" := by
      rw [← hid0]
      exact hNoEmpty fb0 hb0
    have hne : band.id ≠ "" := by rw [hbandid]; exact hne'
    have hb0id : fb0.id = band.id := hid0.trans hbandid.symm
    have hbpid : bp.id = band.id := hpid.trans hbandid.symm
    obtain ⟨_, _, hend⟩ :=
      lppaFrameTransportResidual_holds sp hsp hModelClean hnodupB happ hband hne
        hb0 hb0id hbp hbpid
    rw [hend]
    have hshiftEq : bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) eid = band.shift := by
      apply exec_bandShift_eq hband
      · exact Or.inl hbandid
      · intro b1 hb1 b2 hb2 hc1 hc2
        exact exec_cover_unique hModelClean.1 hModelClean.2
          (by exact hne') hb1 hb2 hc1 hc2
    rw [hdelta, hshiftEq]
  | none =>
    have hnf : ∀ band ∈ (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)), band.id ≠ bp.id := by
      intro band hmem heq
      have hfid : band.id = eid := heq.trans hpid
      have hfb0' : fb0.id = band.id := hid0.trans hfid.symm
      have hfindB : base.scene.boxes.find? (fun b => b.id == band.id) = some fb0 := by
        have hEq : (fun b : Box => b.id == band.id) = (fun b : Box => b.id == fb0.id) := by
          funext x
          rw [hfb0']
        rw [hEq]
        exact hfindS0
      exfalso
      let hframe : LaneFrame :=
        { id := band.id,
          near := (Axis.ofDirection m.options.direction).start fb0.rect
            + band.shift - band.start,
          length := (Axis.ofDirection m.options.direction).length fb0.rect }
      have hfmem : hframe ∈ laneFrames
          (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene := by
        unfold laneFrames
        exact List.mem_filterMap.mpr ⟨band, hmem, by rw [hfindB]; try rfl⟩
      have hfidF : hframe.id = band.id := rfl

      have hpredF : (hframe.id == bp.id) = true := by
        rw [hfidF, hfid, hpid]
        exact beq_self_eq_true _
      exact absurd hpredF (List.find?_eq_none.mp hfind hframe hfmem)
    obtain ⟨b, hbmem, w, hidb, _hw, hrectb, hval⟩ := applyPin_c5_box happ bp hbp hnf
    have hbEq : b = fb0 :=
      se_nodup_map_inj (fun x : Box => x.id) hnodupB hbmem hb0
        (hidb.symm.trans (hpid.trans hid0.symm))
    have hboxDelta : (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
        base.scene).boxDelta b.id = bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) b.id := buildPin_boxDelta b.id
    have hbid : b.id = eid := hidb.symm.trans hpid
    have hwEq : w = (Axis.ofDirection m.options.direction).start fb0.rect + delta := by
      rw [haxis] at hval
      rw [hbEq] at hval hboxDelta hbid
      rw [hval, hboxDelta, hbid, ← hdelta]
    have hbpEq : bp.rect = (Axis.ofDirection m.options.direction).withStart fb0.rect
        ((Axis.ofDirection m.options.direction).start fb0.rect + delta) := by
      rw [haxis] at hrectb
      rw [hbEq] at hrectb
      rw [hrectb, hwEq]
    have hend : endRect (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) bp =
        bp.rect := by
      unfold endRect
      rw [hfind]
    rw [hend, hbpEq]

/-- A satisfying member gives a `find?` witness (local copy; the original is
private to `LaneEndsPinExec`). -/
private theorem se_find?_ex {α : Type} (p : α → Bool) :
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

/-- Ends for the routed scene of an executed `pinBands` run: kept routes
ride a rigid constant shift, rebuilt routes get fresh `findRoute` ends on
the old frames. Consumed by `pinBands_ends_of_routed`. -/
theorem swimlane_endsRouted_of_premise {m : Model} {base : Layered.FamilyResult}
    {sp : Spacing} {pinned routed : Scene}
    (hC5 : Validator.C5 base.scene.layoutDump)
    (hrouteNodup : (base.scene.routes.map (·.id)).Nodup)
    (hnodupB : (base.scene.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "")
    (hPrem : ∀ rt ∈ base.scene.routes,
      SwimlaneEndsRerouted m base sp rt ∨
        bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.fromId =
        bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.toId)
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (m.boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ m.boxes, b.id ≠ "")
    (hsp : spacingOf m.options.profile = .ok sp)
    (happ : applyPin (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene = .ok pinned)
    (hroute : rerouteBands (Axis.ofDirection m.options.direction) sp (LayoutConst.rank_gap.get m.options.profile) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
      (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) base.scene.routes pinned = .ok routed) :
    EndsOnOld (Axis.ofDirection m.options.direction) (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) routed.layoutDump := by
  have haxPin : (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene).axis = (Axis.ofDirection m.options.direction) := rfl
  have hErouted : EndsOnOld (Axis.ofDirection m.options.direction) (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) routed.layoutDump := by
    intro r' hr'
    obtain ⟨rp, _hrpm, old, holdmem, hpair, hid, hfrom, hto, _horthEq, hcase⟩ :=
      c4c5_reroute_mem (Axis.ofDirection m.options.direction) sp (LayoutConst.rank_gap.get m.options.profile) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
        (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) base.scene.routes pinned routed hroute r' hr'
    rcases hcase with ⟨hptsEq, hkept⟩
      | ⟨_fi, _ti, fb, tb, ends, obs, pts, _hfi, _hti, hfb, htb, hends, _hobs, hfindR, hptsPts⟩
    · -- kept route: its pinned image is a rigid constant shift of the base route
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpair
      obtain ⟨hkR, hkO⟩ := getElem?_zip_iff.mp hk
      change pinned.routes[k]? = some rp at hkR
      change base.scene.routes[k]? = some old at hkO
      have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
      have hkOL : k < base.scene.routes.length := (List.getElem?_eq_some_iff.mp hkO).1
      obtain ⟨hidC, hfromC, htoC, _horthC, hmapOr⟩ := applyPin_c4_map happ hkRL hkOL hkR hkO
      obtain ⟨p, q, fb0, tb0, hp, hq, hfb0, htb0, hb1, hb2⟩ := hC5 old holdmem
      have hfb0M : fb0 ∈ base.scene.boxes := List.mem_of_find?_eq_some hfb0
      have htb0M : tb0 ∈ base.scene.boxes := List.mem_of_find?_eq_some htb0
      have hfb0id : fb0.id = old.fromId := by
        have hx := List.find?_some hfb0
        simpa using hx
      have htb0id : tb0.id = old.toId := by
        have hx := List.find?_some htb0
        simpa using hx
      have hbpFex : ∃ bx ∈ base.scene.boxes, bx.id = rp.fromId :=
        ⟨fb0, hfb0M, by rw [hfb0id, ← hfromC]⟩
      have hbpTex : ∃ bx ∈ base.scene.boxes, bx.id = rp.toId :=
        ⟨tb0, htb0M, by rw [htb0id, ← htoC]⟩
      have hsomeF := c4c5_pinned_box_some happ rp.fromId hbpFex
      have hsomeT := c4c5_pinned_box_some happ rp.toId hbpTex
      obtain ⟨bpF, hbpF⟩ := Option.isSome_iff_exists.mp hsomeF
      obtain ⟨bpT, hbpT⟩ := Option.isSome_iff_exists.mp hsomeT
      have hbpFM : bpF ∈ pinned.boxes := List.mem_of_find?_eq_some hbpF
      have hbpTM : bpT ∈ pinned.boxes := List.mem_of_find?_eq_some hbpT
      have hbpFid : bpF.id = rp.fromId := by
        have hx := List.find?_some hbpF
        simpa using hx
      have hbpTid : bpT.id = rp.toId := by
        have hx := List.find?_some hbpT
        simpa using hx
      have hgd0 : old.points.head?.getD ⟨0, 0⟩ = p := by simp only [hp, Option.getD_some]
      have hgd1 : old.points.getLast?.getD ⟨0, 0⟩ = q := by simp only [hq, Option.getD_some]
      have hnre : ¬ SwimlaneEndsRerouted m base sp old := by
        rintro ⟨fiR, tiR, hfiR, htiR, hneR, hlenR⟩
        have hpredeq : (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == rp.fromId || b.members.contains rp.fromId) =
            (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == old.fromId || b.members.contains old.fromId) := by
          rw [hfromC]
        have hpredeq2 : (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == rp.toId || b.members.contains rp.toId) =
            (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)).findIdx?
              (fun b => b.id == old.toId || b.members.contains old.toId) := by
          rw [htoC]
        rcases hkept with ⟨fiK, tiK, hfiK, htiK, hor⟩ | hnfF | hnfT | hbfF | hbfT
        · have e1 : fiK = fiR :=
            Option.some.inj (hfiK.symm.trans (hpredeq.trans hfiR))
          have e2 : tiK = tiR :=
            Option.some.inj (htiK.symm.trans (hpredeq2.trans htiR))
          rcases hor with heq | hlt
          · exact hneR (e1.symm.trans (heq.trans e2))
          · omega
        · have h := hnfF.symm.trans (hpredeq.trans hfiR)
          cases h
        · have h := hnfT.symm.trans (hpredeq2.trans htiR)
          cases h
        · exact absurd (by rw [hbpFid]; simp) (List.find?_eq_none.mp hbfF bpF hbpFM)
        · exact absurd (by rw [hbpTid]; simp) (List.find?_eq_none.mp hbfT bpT hbpTM)
      rcases hPrem old holdmem with hrer | hshiftEq
      · exact absurd hrer hnre
      · rcases hmapOr with ⟨hnone, _⟩ | ⟨d, hd, hmap⟩
        · -- no pin entry would mean empty base points, contradicting C5
          exfalso
          have hmem : (⟨old.id, bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) old.fromId, bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) old.toId,
              (Axis.ofDirection m.options.direction).point p, (Axis.ofDirection m.options.direction).point q⟩ : RouteDelta) ∈
              base.scene.routes.filterMap (fun rr =>
                match rr.points.head?, rr.points.getLast? with
                | some f, some l => some ⟨rr.id, bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rr.fromId,
                    bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rr.toId, (Axis.ofDirection m.options.direction).point f, (Axis.ofDirection m.options.direction).point l⟩
                | _, _ => none) := by
            apply List.mem_filterMap.mpr
            exact ⟨old, holdmem, by simp only [hp, hq]⟩
          obtain ⟨dd, hdd⟩ := se_find?_ex (fun d : RouteDelta => d.id == old.id) _
            ⟨_, hmem, beq_self_eq_true _⟩
          have hdd' : (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene).route old.id = some dd := hdd
          rw [hidC] at hnone
          rw [hdd'] at hnone
          cases hnone
        · have hd' : (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene).route old.id = some d := hidC ▸ hd
          obtain ⟨hfd, htd, _hfirst, _hlast⟩ := c4c5_route_deltas holdmem hrouteNodup hd'
          have heqd : d.fromDelta = d.toDelta := hfd.trans (hshiftEq.trans htd.symm)
          have hmove : routeMove d = Move.constant d.fromDelta := by
            simp [routeMove, heqd]
          rw [hmove] at hmap
          rw [haxPin] at hmap
          obtain ⟨qP, hqPhead, hqPEq⟩ := se_const_head' hmap hp
          obtain ⟨qQ, hqQlast, hqQEq⟩ := se_const_last' hmap hq
          have hfromId : fb0.id = rp.fromId := by rw [hfb0id, ← hfromC]
          have htoId : tb0.id = rp.toId := by rw [htb0id, ← htoC]
          have hdeltaF : d.fromDelta = bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) fb0.id := by
            rw [hfb0id]
            exact hfd
          have hdeltaT : d.toDelta = bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) tb0.id := by
            rw [htb0id]
            exact htd
          have hendF := se_endRect_shift (eid := fb0.id) hModelClean hnodupB hNoEmpty hsp happ
            hfb0M rfl hbpFM (hbpFid.trans hfromId.symm) hdeltaF
          have hendT := se_endRect_shift (eid := tb0.id) hModelClean hnodupB hNoEmpty hsp happ
            htb0M rfl hbpTM (hbpTid.trans htoId.symm) hdeltaT
          have hbP : Validator.onBoundary qP
              (endRect (Axis.ofDirection m.options.direction) (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) bpF) := by
            rw [hqPEq, hendF]
            exact onBoundary_crossShift.mpr hb1
          have hbQ : Validator.onBoundary qQ
              (endRect (Axis.ofDirection m.options.direction) (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) bpT) := by
            rw [hqQEq, hendT, heqd]
            exact onBoundary_crossShift.mpr hb2
          have hfindF : pinned.layoutDump.box? rp.fromId = some bpF := by
            unfold LayoutDump.box?
            exact hbpF
          have hfindT : pinned.layoutDump.box? rp.toId = some bpT := by
            unfold LayoutDump.box?
            exact hbpT
          have hdumpEq : routed.layoutDump.boxes = pinned.layoutDump.boxes :=
            (rerouteBands_frame hroute).1
          refine ⟨qP, qQ, bpF, bpT, ?_, ?_, ?_, ?_, hbP, hbQ⟩
          · rw [hptsEq]; exact hqPhead
          · rw [hptsEq]; exact hqQlast
          · unfold LayoutDump.box?
            rw [hdumpEq, hfrom]; exact hfindF
          · unfold LayoutDump.box?
            rw [hdumpEq, hto]; exact hfindT
    · -- rebuilt route: fresh findRoute ends on the old frames
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpair
      obtain ⟨hkR, hkO⟩ := getElem?_zip_iff.mp hk
      change pinned.routes[k]? = some rp at hkR
      change base.scene.routes[k]? = some old at hkO
      have hkRL : k < pinned.routes.length := (List.getElem?_eq_some_iff.mp hkR).1
      have hkOL : k < base.scene.routes.length := (List.getElem?_eq_some_iff.mp hkO).1
      obtain ⟨_, hfrEq, htoEq, _, _⟩ := applyPin_c4_map happ hkRL hkOL hkR hkO
      obtain ⟨fbp, tbp, hfbp, htbp, hbs, hbt⟩ :=
        lepeRerouteEndsBdryPairedExec_holds (boxes := m.boxes) (o := m.options)
          (s := base.scene) sp hsp hnodupB hModelClean hNoEmpty happ hC5 holdmem
          ⟨hfrEq, htoEq⟩ hfb htb hends
      obtain ⟨hhead, hlast⟩ :=
        hEndsPin (Axis.ofDirection m.options.direction) sp (buildPin (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene) fb tb old.points ends obs
          (LayoutConst.rank_gap.get m.options.profile) pts hends hfindR
      have hdumpEq : routed.layoutDump.boxes = pinned.layoutDump.boxes :=
        (rerouteBands_frame hroute).1
      refine ⟨ends.source, ends.target, fbp, tbp, ?_, ?_, ?_, ?_, hbs, hbt⟩
      · rw [hptsPts]; exact hhead
      · rw [hptsPts]; exact hlast
      · unfold LayoutDump.box?
        rw [hdumpEq, hfrom]; exact hfbp
      · unfold LayoutDump.box?
        rw [hdumpEq, hto]; exact htbp

  exact hErouted

/-- The `pinBands` result satisfies `EndsOnOld` from the replacement
premise. Replaces `pinBands_ends_exec_final`, whose old premise was
refuted by `SwimlaneEndsAboveProof`. -/
theorem swimlane_endsOld_of_premise {m : Model} {base : Layered.FamilyResult}
    {r : Scene}
    (hC5 : Validator.C5 base.scene.layoutDump)
    (hlanes : lanesOf m.boxes ≠ [])
    (hrouteNodup : (base.scene.routes.map (·.id)).Nodup)
    (hnodupB : (base.scene.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "")
    (hPrem : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ rt ∈ base.scene.routes,
        SwimlaneEndsRerouted m base sp rt ∨
          bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.fromId =
          bandShift (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) rt.toId)
    (hEndsPin : FindRouteEndsPin)
    (hModelClean : (m.boxes.map fun b => b.id).Nodup ∧ ∀ b ∈ m.boxes, b.id ≠ "")
    (h : pinBands m.boxes m.options base.scene = .ok r) :
    ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      EndsOnOld (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction) (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes)) base.scene)
        r.layoutDump := by
  refine pinBands_ends_of_routed hlanes hnodupB h ?_
  intro sp hsp pinned routed happ hroute
  exact swimlane_endsRouted_of_premise hC5 hrouteNodup hnodupB hNoEmpty
    (hPrem sp hsp) hEndsPin hModelClean hsp happ hroute

end SwimlaneEndsCutover
end Kinds
end Elegant
