import Elegant.Layered.LaneBandsLooseLowerProof
import Elegant.Layered.LaneBandsBoxClausesExecuted
import Elegant.Layered.LaneBandsRouteClauses

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

/-- A loose route's shifted point lies in the measured content interval, which
starts one clearance beyond the loose band's nominal start. -/
theorem looseBand_route_point_within {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} {members : List String} {start : Int}
    {r : Route} {p : Point} (hr : r ∈ s.routes) (hp : p ∈ r.points)
    (hfrom : r.fromId ∈ members) (hto : r.toId ∈ members) :
    let band := looseBand boxes s axis sp members start
    band.start + sp.clear ≤ axis.point p + band.shift ∧
      axis.point p + band.shift ≤ band.start + sp.clear + band.thickness := by
  have hmem := contentValues_mem_loose_route_point (boxes := boxes) (axis := axis)
    hr hp hfrom hto
  cases hvalues : contentValues boxes s axis "" members with
  | nil => rw [hvalues] at hmem; simp at hmem
  | cons first rest =>
    have hBounds : bounds (contentValues boxes s axis "" members) =
        some (rest.foldl min first, rest.foldl max first) := by
      simp only [hvalues, bounds]
    obtain ⟨hlo, hhi⟩ := bounds_mem hBounds hmem
    simp only [looseBand, hBounds]
    omega

private theorem cover_of_findIdx {bs : List Band} {id : String} {i : Nat}
    (hi : i < bs.length)
    (hfind : bs.findIdx? (fun b => b.id == id || decide (id ∈ b.members)) = some i) :
    bandCovers (bs[i]'hi) id := by
  obtain ⟨_, hpred, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  have hcover : ((bs[i]'hi).id == id || decide (id ∈ (bs[i]'hi).members)) = true := hpred
  rw [Bool.or_eq_true] at hcover
  rcases hcover with heq | hmem
  · exact Or.inl (beq_iff_eq.mp heq)
  · exact Or.inr (of_decide_eq_true hmem)

private theorem tiled_end_le_last {start : Int} {named : List Band} {loose b : Band}
    (ht : Tiled start (named ++ [loose]))
    (hnn : ∀ g ∈ named ++ [loose], 0 ≤ g.thickness)
    (hb : b ∈ named) : b.start + b.thickness ≤ loose.start := by
  induction named generalizing start with
  | nil => simp at hb
  | cons first rest ih =>
    change Tiled start (first :: (rest ++ [loose])) at ht
    change (∀ g ∈ first :: (rest ++ [loose]), 0 ≤ g.thickness) at hnn
    rcases List.mem_cons.mp hb with rfl | hb
    · exact tiled_head_le ht hnn (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
    · exact ih ht.2 (fun g hg => hnn g (List.mem_cons_of_mem _ hg)) hb

private theorem bandShift_at_index {bands : List Band} {id : String} {i : Nat}
    (hi : i < bands.length)
    (h : bands.findIdx? (fun b => b.id == id || decide (id ∈ b.members)) = some i) :
    bandShift bands id = (bands[i]'hi).shift := by
  simp only [bandShift, List.contains_eq_mem, List.find?_eq_bind_findIdx?_getElem?, h,
    Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-- Both endpoint indices give the same checked `buildPin` translation.
Point success already accounts for the integer range check. -/
theorem buildPin_same_band_point_cross {axis : Axis} {bands : List Band} {s : Scene}
    {r : Route} {p shifted : Point} {d : RouteDelta} {i : Nat} (hi : i < bands.length)
    (hRoutes : (s.routes.map (·.id)).Nodup) (hr : r ∈ s.routes)
    (hfrom : bands.findIdx? (fun b => b.id == r.fromId || decide (r.fromId ∈ b.members)) =
      some i)
    (hto : bands.findIdx? (fun b => b.id == r.toId || decide (r.toId ∈ b.members)) = some i)
    (hentry : (buildPin axis bands s).route r.id = some d)
    (hpoint : (routeMove d).point axis p = .ok shifted) :
    axis.point shifted = axis.point p + (bands[i]'hi).shift := by
  obtain ⟨hf, ht, _, _⟩ := buildPin_route_find hRoutes hr hentry
  rw [bandShift_at_index hi hfrom] at hf
  rw [bandShift_at_index hi hto] at ht
  have hmove : routeMove d = .constant (bands[i]'hi).shift := by simp [routeMove, hf, ht]
  rw [hmove] at hpoint
  obtain ⟨w, hw, hshifted, _⟩ := movePoint_ok hpoint
  rw [hshifted, moveConstant_value hw]
  cases axis <;> rfl

/-- The loose-route clearance seam for the bands actually constructed from
this scene, with unique box IDs and no empty endpoint or lane IDs. -/
theorem pinLooseRouteAboveLaneBox_layBands {boxes : List ModelBox} {s : Scene}
    {axis : Axis} {sp : Spacing} (hModelIds : (boxes.map (·.id)).Nodup)
    (hNonempty : ∀ b ∈ boxes, b.id ≠ "") (hSceneIds : (s.boxes.map (·.id)).Nodup)
    (hEndpoints : ∀ r ∈ s.routes, r.fromId ≠ "" ∧ r.toId ≠ "")
    (hSpacing : 0 ≤ sp.title ∧ 0 ≤ sp.clear) :
    PinLooseRouteAboveLaneBox axis (layBands boxes s axis sp (lanesOf boxes)) s := by
  let bands := layBands boxes s axis sp (lanesOf boxes)
  let start := firstLaneStart s (lanesOf boxes) axis
  let named := layLanes boxes s axis sp (lanesOf boxes) start
  let looseStart := start + (named.map (·.thickness)).sum
  let loose := looseBand boxes s axis sp (looseNodes boxes) looseStart
  change PinLooseRouteAboveLaneBox axis bands s
  intro r hr b hb _ _ i hi hiId hfrom hto j hj hjId hfind p hp
  have hTrailing : (bands[i]'hi) = loose := by
    rcases layBands_mem_cases (List.getElem_mem hi) with hNamed | hLoose
    · obtain ⟨mb, hmb, _, _, hId⟩ := exec_lanesOf_mem (layLanes_id_mem hNamed)
      exact (hNonempty mb hmb (hId.trans hiId)).elim
    · exact hLoose
  have hNamed : (bands[j]'hj) ∈ named := by
    rcases layBands_mem_cases (List.getElem_mem hj) with hNamed | hLoose
    · exact hNamed
    · exfalso
      apply hjId
      rw [hLoose]
      exact exec_looseBand_id _ _ _ _ _ _
  have looseMember (id : String) (hId : id ≠ "")
      (h : bands.findIdx? (fun g => g.id == id || decide (id ∈ g.members)) = some i) :
      id ∈ looseNodes boxes := by
    rcases cover_of_findIdx hi h with heq | hmem
    · exact (hId (heq.symm.trans hiId)).elim
    · rw [hTrailing, looseBand_members] at hmem
      exact hmem
  obtain ⟨hf, ht⟩ := hEndpoints r hr
  have hLower : loose.start + sp.clear ≤ axis.point p + loose.shift :=
    (looseBand_route_point_within (boxes := boxes) (sp := sp) (start := looseStart)
      hr hp (looseMember r.fromId hf hfrom) (looseMember r.toId ht hto)).1
  have hUpper : axis.start b.rect + axis.length b.rect + (bands[j]'hj).shift ≤
      (bands[j]'hj).start + (bands[j]'hj).thickness := by
    have hcover := cover_of_findIdx hj hfind
    obtain ⟨lane, hLane, st, hBand⟩ := layLanes_mem_lane hNamed
    rw [hBand] at hcover ⊢
    have hmem : b.id ∈ (laneBand boxes s axis sp lane st).members := by
      rcases hcover with heq | hmem
      · have heq' : lane = b.id := heq
        rw [← heq']
        exact exec_lane_self_mem hModelIds hLane st
      · exact hmem
    exact (laneMember_within hSpacing.1 hSpacing.2 hmem (sceneFind?_eq_self hSceneIds hb)).2
  have hTiled : Tiled start (named ++ [loose]) :=
    tiled_snoc (layLanes_tiled boxes s axis sp (lanesOf boxes) start)
      (looseBand_start boxes s axis sp (looseNodes boxes) looseStart)
  have hNonneg : ∀ band ∈ named ++ [loose], 0 ≤ band.thickness := by
    intro band hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact layLanes_thickness_nonneg boxes s axis sp (lanesOf boxes) start
        hSpacing.1 hSpacing.2 band hmem
    · rw [List.mem_singleton.mp hmem]
      exact looseBand_thickness_nonneg boxes s axis sp (looseNodes boxes) looseStart
  have hOrder := tiled_end_le_last hTiled hNonneg hNamed
  have hClear := hSpacing.2
  rw [hTrailing]
  omega

/-- Discharge the loose-route seam on a successful swimlane base layout.
Layered admission supplies `hNonempty`; base C5 supplies endpoint lookup.
No hypothesis about the result of `applyPin` is needed for this bound. -/
theorem swimlane_pinLooseRouteAboveLaneBox {m : Model} {base : FamilyResult} {sp : Spacing}
    (hfam : layoutFamily (Kinds.Swimlane.input m) m.options = .ok base)
    (hNonempty : ∀ b ∈ m.boxes, b.id ≠ "")
    (hC5 : Validator.C5 base.scene.layoutDump) (hsp : spacingOf m.options.profile = .ok sp) :
    PinLooseRouteAboveLaneBox (Axis.ofDirection m.options.direction)
      (layBands m.boxes base.scene (Axis.ofDirection m.options.direction) sp (lanesOf m.boxes))
      base.scene := by
  have hIds : base.scene.boxes.map (·.id) = m.boxes.map (·.id) := (layoutFamily_ids hfam).1
  have hModelIds : (m.boxes.map (·.id)).Nodup := Model.boxIds_nodup (layoutFamily_wellFormed hfam)
  have hSceneIds : (base.scene.boxes.map (·.id)).Nodup := by
    rw [hIds]
    exact hModelIds
  have endpointNe {id : String} {b : Box} (h : base.scene.layoutDump.box? id = some b) :
      id ≠ "" := by
    change base.scene.boxes.find? (fun b => b.id == id) = some b at h
    have hId : b.id = id :=
      beq_iff_eq.mp (List.find?_some (p := fun box : Box => box.id == id) h)
    have hmem : id ∈ base.scene.boxes.map (·.id) :=
      List.mem_map.mpr ⟨b, List.mem_of_find?_eq_some h, hId⟩
    rw [hIds] at hmem
    obtain ⟨mb, hmb, rfl⟩ := List.mem_map.mp hmem
    exact hNonempty mb hmb
  refine pinLooseRouteAboveLaneBox_layBands hModelIds hNonempty hSceneIds ?_ (spacing_of_nonneg hsp)
  intro r hr
  obtain ⟨_, _, _, _, _, _, hfrom, hto, _, _⟩ := hC5 r hr
  exact ⟨endpointNe hfrom, endpointNe hto⟩

end LaneBands
end Layered
end Elegant
