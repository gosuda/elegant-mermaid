import Elegant.Layered.LaneBands
import Elegant.Layered.LaneBandsBoxClauses
import Elegant.Layered.LaneBandsBoxClausesProof
import Elegant.Layered.LaneBandsRouteClauses
import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsCoverage
import Elegant.Layered.LaneBandsClearance
import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsLabelClauses
import Elegant.Layered.LaneBandsFindRouteClearProof
import Elegant.Layered.LaneBandsFrameClause
import Elegant.Layered.LaneEnds
import Elegant.Layered.LaneEndsClauses
import Elegant.Layered.LaneEndsRouteClauses
import Elegant.Kinds.Swimlane
import ElegantGeometry.Validator

set_option autoImplicit false

/-! Clause transport for the composed lane pinning `pinLanes = pinBands >>= attachLaneEnds`.

Each clause is proved by unfolding `pinLanes` with `pinLanes_spec` into the
`pinBands` result and the `attachLaneEnds` result, applying the tracked
`pinBands_cK` theorem on the pinned scene, then carrying the clause over the
lane-end step with the tracked `attachLaneEnds_cK` theorem. C5 comes from
`attachLaneEnds_c5` (not from `pinBands_c5`); C6 additionally needs
orthogonality of the pinned routes, which follows from `pinBands_c4` once
every pinned route is shown to keep its orthogonal flag. -/

namespace Elegant
namespace Layered
namespace LaneBands

/-- Binding step of an `Except` computation (local copy; other copies stay private). -/
private theorem pinLanes_bindOk {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A uniform shift keeps every route orthogonal flag. -/
private theorem pinLanes_shiftAll_ortho {axis : Axis} {delta : Int} {s s' : Scene}
    (hAll : ∀ rt ∈ s.routes, rt.orthogonal = true)
    (h : shiftAll axis delta s = .ok s') :
    ∀ r ∈ s'.routes, r.orthogonal = true := by
  unfold shiftAll at h
  obtain ⟨_boxes, _hboxes, h⟩ := pinLanes_bindOk h
  obtain ⟨_labels, _hlabels, h⟩ := pinLanes_bindOk h
  obtain ⟨routes, hroutes, h⟩ := pinLanes_bindOk h
  obtain ⟨_items, _hitems, h⟩ := pinLanes_bindOk h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  show ∀ r ∈ routes, r.orthogonal = true
  have hspec := mapM_except_spec
    (fun r : Route => (do pure { r with points := ← r.points.mapM ((Move.constant delta).point axis) } : Except LayoutError Route))
    s.routes routes hroutes
  have hlen : routes.length = s.routes.length := hspec.1
  intro r hr
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
  have hkR : k < routes.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkS : k < s.routes.length := by omega
  obtain ⟨a, b, ha, hb, hfab⟩ := hspec.2 k hkS hkR
  have hbeq : b = r := Option.some.inj (by rw [← hb]; exact hk)
  have hamem : a ∈ s.routes := List.mem_of_getElem? ha
  have hflag : a.orthogonal = true := hAll a hamem
  cases hinner : a.points.mapM ((Move.constant delta).point axis) with
  | error e =>
    simp only [hinner, Bind.bind, Except.bind] at hfab
    exact absurd hfab (by simp)
  | ok pts =>
    simp only [hinner, Bind.bind, Except.bind, Pure.pure, Except.pure,
      Except.ok.injEq] at hfab
    subst hbeq
    rw [← hfab]
    exact hflag

/-- `pinBands` keeps every route orthogonal flag. -/
private theorem pinLanes_allOrtho {boxes : List ModelBox} {o : Options} {s pinned : Scene}
    (hAll : ∀ rt ∈ s.routes, rt.orthogonal = true)
    (hpin : pinBands boxes o s = .ok pinned) :
    ∀ r ∈ pinned.routes, r.orthogonal = true := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinBands boxes o s = .ok s := pinBands_no_lanes hlanes
    have heq : pinned = s := Except.ok.inj (hpin.symm.trans hno)
    subst heq
    exact hAll
  · obtain ⟨_sp, axis, bands, p0, routed, origin, _strip, stripScene, _hsp, _haxis,
        _hbands, happ, hroute, horig, _hstrip, hrelocEq, hgrow⟩ :=
      pinBands_spec hlanes hpin
    obtain ⟨_shiftedBoxes, _shiftedLabels, shiftedRoutes, _shiftedItems,
        _hboxes, _hlabels, hroutes, _hitems, hfold⟩ := applyPin_shifted happ
    have hlenS : shiftedRoutes.length = s.routes.length :=
      (mapM_except_spec _ s.routes shiftedRoutes hroutes).1
    have hrr : p0.routes = shiftedRoutes :=
      (foldReplaceFrame_all bands (buildPin axis bands s).axis _ p0 hfold).2.2.2.2.2.2.1
    have hlenP : p0.routes.length = s.routes.length := by rw [hrr, hlenS]
    have h0 : ∀ r ∈ p0.routes, r.orthogonal = true := by
      intro rP hrP
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrP
      have hkP : k < p0.routes.length := (List.getElem?_eq_some_iff.mp hk).1
      have hkS : k < s.routes.length := by omega
      have hkO : s.routes[k]? = some s.routes[k] :=
        List.getElem?_eq_some_iff.mpr ⟨hkS, rfl⟩
      have hkSh : k < shiftedRoutes.length := by omega
      obtain ⟨_a, _b, _ha, _hb, _hfab⟩ := (mapM_except_spec _ s.routes shiftedRoutes hroutes).2 k hkS hkSh
      obtain ⟨_hid, _hfrom, _hto, horth, _hmap⟩ :=
        applyPin_c4_map happ hkP hkS hk hkO
      have hmem : s.routes[k] ∈ s.routes := List.mem_of_getElem? hkO
      have hflag : (s.routes[k]).orthogonal = true := hAll _ hmem
      rw [horth]
      exact hflag
    have h1 : ∀ r ∈ routed.routes, r.orthogonal = true := by
      intro r' hr'
      obtain ⟨r, hr, _old, _hold, _hpair, _hid, _hfrom, _hto, horthEq, _hcase⟩ :=
        c4c5_reroute_mem _ _ _ _ _ _ _ _ hroute r' hr'
      rw [horthEq]
      exact h0 r hr
    have h2 : ∀ r ∈ origin.routes, r.orthogonal = true := by
      rcases restoreOrigin_cases horig with heq | ⟨delta, _hpos, hshift⟩
      · subst heq
        exact h1
      · exact pinLanes_shiftAll_ortho h1 hshift
    have hstripR : stripScene.routes = origin.routes := by
      rw [hrelocEq]
      exact relocateLabels_routes axis _ origin
    have hgrowR : pinned.routes = stripScene.routes := (growCanvas_frame hgrow).2.1
    intro r hr
    rw [hgrowR, hstripR] at hr
    exact h2 r hr

theorem pinLanes_c1 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC1 : Validator.C1 s.layoutDump)
    (h : pinLanes boxes o s = .ok r) :
    Validator.C1 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC1
  · obtain ⟨_sp, _pinned, _hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c1 (pinBands_c1 hC1 hpin) hatt

theorem pinLanes_c2 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hcover : ∀ sp : Spacing, spacingOf o.profile = .ok sp →
      PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hsetup : ∀ sp : Spacing, spacingOf o.profile = .ok sp →
      PinSetup s (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)))
    (hC2 : Validator.C2 s.layoutDump)
    (h : pinLanes boxes o s = .ok r) :
    Validator.C2 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC2
  · obtain ⟨sp, _pinned, hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    have hRes : PinC2Sep o s _pinned :=
      pinC2Sep_of_pin (hcover sp hsp) hBoxesNodup hNe (hsetup sp hsp) rfl hsp hpin
    exact attachLaneEnds_c2 (pinBands_c2 hC2 hRes hpin) hatt

theorem pinLanes_c3 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hcover : ∀ sp : Spacing, spacingOf o.profile = .ok sp →
      PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hsNodup : (s.boxes.map (·.id)).Nodup)
    (hBoxesNodup : (boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ boxes, b.id ≠ "")
    (hC3 : Validator.C3 s.layoutDump)
    (hsetup : ∀ sp : Spacing, spacingOf o.profile = .ok sp →
      PinSetup s (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)))
    (h : pinLanes boxes o s = .ok r) :
    Validator.C3 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC3
  · obtain ⟨sp, _pinned, hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    have hRes : PinC3Cross o s _pinned :=
      pinC3Cross_of_pin (hcover sp hsp) hsNodup hBoxesNodup hNe hC3 (hsetup sp hsp)
        rfl hsp hpin
    exact attachLaneEnds_c3 (pinBands_c3 hC3 hRes hpin) hatt

theorem pinLanes_c4 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC4 : Validator.C4 s.layoutDump)
    (hrouteNodup : (s.routes.map (·.id)).Nodup)
    (hcov : ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      PinBoxCoverage boxes s (Axis.ofDirection o.direction) sp)
    (hEndsBox : ∀ rt ∈ s.routes,
      (s.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
      (s.boxes.find? (fun b => b.id == rt.toId)).isSome = true)
    (hOrthoPin : FindRouteOrthoPin)
    (h : pinLanes boxes o s = .ok r) :
    Validator.C4 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC4
  · obtain ⟨_sp, _pinned, _hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c4
      (pinBands_c4 hC4 hlanes hrouteNodup hcov hEndsBox hOrthoPin hpin) hatt

theorem pinLanes_c5 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (hC5 : Validator.C5 s.layoutDump)
    (hEndsOld : ∀ (pinned : Scene), pinBands boxes o s = .ok pinned →
      ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      EndsOnOld (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        pinned.layoutDump)
    (hFit : ∀ (pinned : Scene), pinBands boxes o s = .ok pinned →
      ∀ (sp : Spacing), spacingOf o.profile = .ok sp →
      FramesFit (Axis.ofDirection o.direction)
        (laneFrames (Axis.ofDirection o.direction)
          (layBands boxes s (Axis.ofDirection o.direction) sp (lanesOf boxes)) s)
        pinned.layoutDump)
    (h : pinLanes boxes o s = .ok r) :
    Validator.C5 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC5
  · obtain ⟨sp, _pinned, hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c5 (hEndsOld _ hpin sp hsp) (hFit _ hpin sp hsp) hatt

theorem pinLanes_c6 {m : Model} {base : FamilyResult} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hbase : HardConstraints base.scene.layoutDump)
    (happly : pinBandsApplyPinKeptClear)
    (hrouteNodup : (base.scene.routes.map (·.id)).Nodup)
    (hcov : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction) sp)
    (hEndsBox : ∀ rt ∈ base.scene.routes,
      (base.scene.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
      (base.scene.boxes.find? (fun b => b.id == rt.toId)).isSome = true)
    (hOrthoPin : FindRouteOrthoPin)
    (hGap : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      GapClear (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes))
          base.scene)
        pinned.layoutDump)
    (hPos : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ExclusivePositive pinned.layoutDump)
    (hFit : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      FramesFit (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes))
          base.scene)
        pinned.layoutDump)
    (hLen : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ f ∈ laneFrames (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes))
        base.scene, 0 ≤ f.length)
    (hOrthoAll : ∀ rt ∈ base.scene.routes, rt.orthogonal = true)
    (h : pinLanes m.boxes m.options base.scene = .ok r) :
    Validator.C6 r.layoutDump := by
  by_cases hlanes : lanesOf m.boxes = []
  · have hno : pinLanes m.boxes m.options base.scene = .ok base.scene :=
      pinLanes_no_lanes hlanes
    have hr : base.scene = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hbase.2.2.2.2.2.1
  · obtain ⟨sp, _pinned, hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    have hC6pin : Validator.C6 _pinned.layoutDump :=
      pinBands_c6 hfam hpin hbase happly
    have hC4pin : Validator.C4 _pinned.layoutDump :=
      pinBands_c4 hbase.2.2.2.1 hlanes hrouteNodup hcov hEndsBox hOrthoPin hpin
    have hAllPin : ∀ rt ∈ _pinned.routes, rt.orthogonal = true :=
      pinLanes_allOrtho hOrthoAll hpin
    have hOrtho : ∀ rt ∈ _pinned.layoutDump.routes,
        Polyline.isOrthogonal rt.points = true := by
      have hdeq : _pinned.layoutDump.routes = _pinned.routes :=
        (pinBands_layoutDump).2.1
      rw [hdeq]
      intro rt hrt
      exact hC4pin rt hrt (hAllPin rt hrt)
    exact attachLaneEnds_c6 hC6pin hOrtho (hGap _ hpin sp hsp) (hPos _ hpin)
      (hFit _ hpin sp hsp) (hLen _ hpin sp hsp) hatt

theorem pinLanes_c7 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (h : pinLanes boxes o s = .ok r) (hin : Validator.C7 s.layoutDump)
    (hclean : LaneInputIdsClean s) (hshape : LaneSceneShape s) :
    Validator.C7 r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hin
  · obtain ⟨_sp, _pinned, _hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c7 (pinBands_c7 hpin hin hclean hshape) hatt

theorem pinLanes_c8a {boxes : List ModelBox} {o : Options} {s r : Scene}
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
    (h : pinLanes boxes o s = .ok r) :
    Validator.C8a r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hC8a
  · obtain ⟨sp, _pinned, hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c8a
      (pinBands_c8a hC8a hModelNodup hModelNoEmpty hNodupS hNoEmpty hcover hParents
        hpin) hatt

theorem pinLanes_c8b {boxes : List ModelBox} {o : Options} {s r : Scene}
    (h : pinLanes boxes o s = .ok r) (hin : Validator.C8b s.layoutDump) :
    Validator.C8b r.layoutDump := by
  by_cases hlanes : lanesOf boxes = []
  · have hno : pinLanes boxes o s = .ok s := pinLanes_no_lanes hlanes
    have hr : s = r := Except.ok.inj (hno.symm.trans h)
    subst hr
    exact hin
  · obtain ⟨_sp, _pinned, _hsp, hpin, hatt⟩ := pinLanes_spec hlanes h
    exact attachLaneEnds_c8b (pinBands_c8b hpin hin) hatt

theorem pinLanes_hardConstraints {m : Model} {base : FamilyResult} {r : Scene}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hbase : HardConstraints base.scene.layoutDump)
    (happly : pinBandsApplyPinKeptClear)
    (hrouteNodup : (base.scene.routes.map (·.id)).Nodup)
    (hcov : ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      PinBoxCoverage m.boxes base.scene (Axis.ofDirection m.options.direction) sp)
    (hEndsBox : ∀ rt ∈ base.scene.routes,
      (base.scene.boxes.find? (fun b => b.id == rt.fromId)).isSome = true ∧
      (base.scene.boxes.find? (fun b => b.id == rt.toId)).isSome = true)
    (hOrthoPin : FindRouteOrthoPin)
    (hBoxesNodup : (m.boxes.map (·.id)).Nodup)
    (hNe : ∀ b ∈ m.boxes, b.id ≠ "")
    (hsetup : ∀ sp : Spacing, spacingOf m.options.profile = .ok sp →
      PinSetup base.scene
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes)))
    (hsNodup : (base.scene.boxes.map (·.id)).Nodup)
    (hNoEmpty : ∀ b ∈ base.scene.boxes, b.id ≠ "")
    (hModelNoEmpty : ∀ b ∈ m.boxes, b.id ≠ "")
    (hParents : ∀ sp : Spacing, ∀ bands : List Band,
      spacingOf m.options.profile = .ok sp →
      bands = layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
        (lanesOf m.boxes) →
      PinSceneParents m.boxes base.scene bands)
    (hclean : LaneInputIdsClean base.scene)
    (hshape : LaneSceneShape base.scene)
    (hEndsOld : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      EndsOnOld (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes))
          base.scene)
        pinned.layoutDump)
    (hFit : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      FramesFit (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes))
          base.scene)
        pinned.layoutDump)
    (hGap : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      GapClear (Axis.ofDirection m.options.direction)
        (laneFrames (Axis.ofDirection m.options.direction)
          (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
            (lanesOf m.boxes))
          base.scene)
        pinned.layoutDump)
    (hPos : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ExclusivePositive pinned.layoutDump)
    (hLen : ∀ (pinned : Scene), pinBands m.boxes m.options base.scene = .ok pinned →
      ∀ (sp : Spacing), spacingOf m.options.profile = .ok sp →
      ∀ f ∈ laneFrames (Axis.ofDirection m.options.direction)
        (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp
          (lanesOf m.boxes))
        base.scene, 0 ≤ f.length)
    (hOrthoAll : ∀ rt ∈ base.scene.routes, rt.orthogonal = true)
    (h : pinLanes m.boxes m.options base.scene = .ok r) :
    HardConstraints r.layoutDump :=
  ⟨pinLanes_c1 hbase.1 h,
    pinLanes_c2 hcov hBoxesNodup hNe hsetup hbase.2.1 h,
    pinLanes_c3 hcov hsNodup hBoxesNodup hNe hbase.2.2.1 hsetup h,
    pinLanes_c4 hbase.2.2.2.1 hrouteNodup hcov hEndsBox hOrthoPin h,
    pinLanes_c5 hbase.2.2.2.2.1 hEndsOld hFit h,
    pinLanes_c6 hfam hbase happly hrouteNodup hcov hEndsBox hOrthoPin hGap hPos
      hFit hLen hOrthoAll h,
    pinLanes_c7 h hbase.2.2.2.2.2.2.1 hclean hshape,
    pinLanes_c8a hbase.2.2.2.2.2.2.2.1 hBoxesNodup hModelNoEmpty hsNodup hNoEmpty
      hcov hParents h,
    pinLanes_c8b h hbase.2.2.2.2.2.2.2.2⟩

end LaneBands
end Layered
end Elegant
