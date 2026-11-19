import Elegant.Kinds.Ishikawa
import Elegant.Kinds.IshikawaValid
import Elegant.Kinds.IshikawaSeparationFacts
import Elegant.Kinds.IshikawaOrthogonalityFacts
import Elegant.IshikawaClearanceHardBClose

/-!
# Final Ishikawa validity assembly

Combines the eight proved validator clauses (C1-C8) of the actual Ishikawa adapter.
C1-C5, C7, C8a and C8b are proved in the imported clause modules. The route-clearance
clause C6 is reduced, by `ishikawa_c6_of_raw`, to the raw tree-layout pairwise
clearance `IshikawaRawForeignRouteClearance`, the one open premise of
`ishikawa_valid_of_raw_clearance`.  The raw-level rib assembly must still discharge it;
its HARD B part rests on `HardBDeeperEarlierReal` and the conditional branch-5 placement.
-/

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-- Residual raw-level executed fact: for the actual decode/layout execution of `m`,
whenever the raw tree layout assigns distinct node indices a route and a box, the
route misses the box. This is stronger than validator clause C6 and lives at a
different level (no exclusivity or route-scope side condition, raw pre-normalization
tree layout, all distinct index pairs). It is what remains after the scene and
normalization transport of `ishikawa_c6_of_raw`; discharging it needs the rib assembly
(`layout_origin`, `assemblePairs_box_origin`, `assemblePairs_piece_route_origin`) and
the per-rib clearance chain: `ishikawa_hard_b_real` for odd-depth routes, the even and
cause-box cases from `Elegant.IshikawaClearanceFacts`
(`placed_foreign_entry_even_route_clearance`, `placed_empty_entries_routes_miss_right_box`)
and cross-rib separation of `assemblePairs` shifts. -/
def IshikawaRawForeignRouteClearance (m : Model) : Prop :=
  ∀ (input : Elegant.Kinds.Ishikawa.Input) (raw : Tree.Layout),
    Elegant.Kinds.Ishikawa.decode m = .ok input →
    Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw →
    ∀ (targetIndex boxIndex : Nat) (pts : List Point) (rect : Rect),
      raw.routes[targetIndex]? = some pts →
      raw.boxes[boxIndex]? = some rect →
      targetIndex ≠ boxIndex →
      ¬ Polyline.hitsRect pts rect

/-- Clause C6 of the actual Ishikawa adapter, reduced to the raw tree-layout pairwise
route/box clearance `IshikawaRawForeignRouteClearance`. The proof is the scene and
normalization transport: a successful scene route and a foreign positive-size box
correspond to distinct node indices of the normalized layout
(`successful_scene_foreign_native_indices`), normalization translates both by one
common vector (`Tree.normalize_records`), and `hitsRect_translate` transports the
miss back. Zero-area boxes are never hit. -/
theorem ishikawa_c6_of_raw (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result)
    (hraw : IshikawaRawForeignRouteClearance m) :
    Validator.C6 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := Elegant.Kinds.Ishikawa.layout_success_scene m result h
  rw [hdump]
  intro route hroute box hbox _hexclusive hscope
  by_cases hsize : 0 < box.rect.w ∧ 0 < box.rect.h
  · obtain ⟨hw, hh⟩ := hsize
    obtain ⟨input, raw, normalized, canvas, hdecode, hlayoutRaw, hnormal, hclear⟩ :=
      successful_scene_foreign_native_indices m s hwf hs
    obtain ⟨targetIndex, boxIndex, target, source, _htargetBound, _hboxBound, htarget,
      htargetId, hroutePoints, hsource, hid, hrect, hne, _, _⟩ :=
      hclear route hroute box hbox hw hh hscope
    obtain ⟨dx, dy, hboxesMap, hroutesMap⟩ := Tree.normalize_records hnormal
    rw [hroutesMap, List.getElem?_map] at hroutePoints
    rw [Option.map_eq_some_iff] at hroutePoints
    obtain ⟨pts, hptsRaw, hptsSome⟩ := hroutePoints
    have hptsEq : pts.map (fun p => ⟨p.x + dx, p.y + dy⟩) = route.points :=
      hptsSome
    rw [hboxesMap, List.getElem?_map] at hrect
    rw [Option.map_eq_some_iff] at hrect
    obtain ⟨rect0, hrectRaw, hrectSome⟩ := hrect
    have hrectEq : rect0.translateRaw dx dy = box.rect := hrectSome
    have hmiss := hraw input raw hdecode hlayoutRaw targetIndex boxIndex pts rect0
      hptsRaw hrectRaw (Ne.symm hne)
    have htrans : ¬ Polyline.hitsRect (pts.map (fun p => ⟨p.x + dx, p.y + dy⟩))
        (rect0.translateRaw dx dy) :=
      fun hA => hmiss ((hitsRect_translate dx dy pts rect0).mp hA)
    rw [hptsEq, hrectEq] at htrans
    exact htrans
  · intro habs
    obtain ⟨hw', hh', _⟩ := habs
    exact hsize ⟨hw', hh'⟩

/-- The eight validator clauses of a successful Ishikawa layout, given the one
OPEN fact `IshikawaRawForeignRouteClearance`.  C1-C5, C7, C8a, C8b are proved
for the actual adapter in the imported clause modules; C6 comes from
`ishikawa_c6_of_raw`.  The raw clearance is still owed by the rib assembly:
per-rib odd-depth routes through `ishikawa_hard_b_real` (whose open premises
are `HardBDeeperEarlierReal` and the conditional branch-5 placement), the even
and cause-box cases, cross-rib separation of the `assemblePairs` shifts, and
the piece-to-index correspondence. -/
theorem ishikawa_valid_of_raw_clearance (m : Model) (result : Layered.FamilyResult)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (h : Elegant.Kinds.Ishikawa.layout m = .ok result)
    (hraw : IshikawaRawForeignRouteClearance m) :
    HardConstraints result.scene.layoutDump :=
  ⟨Elegant.Kinds.IshikawaValid.ishikawa_c1 m result hwf hlimits h,
    Elegant.Kinds.IshikawaSeparation.ishikawa_c2 m result hwf hlimits h,
    Elegant.Kinds.Ishikawa.ishikawa_c3 m result hwf hlimits h,
    Elegant.Kinds.IshikawaOrthogonalityFacts.ishikawa_c4 m result hwf hlimits h,
    Elegant.Kinds.IshikawaValid.ishikawa_c5 m result hwf hlimits h,
    ishikawa_c6_of_raw m result hwf h hraw,
    Elegant.Kinds.Ishikawa.ishikawa_c7 m result hwf hlimits h,
    ⟨Elegant.Kinds.IshikawaSeparation.ishikawa_c8a m result hwf hlimits h,
      Elegant.Kinds.IshikawaValid.ishikawa_c8b m result hwf hlimits h⟩⟩

end Elegant.Kinds.IshikawaFinal
