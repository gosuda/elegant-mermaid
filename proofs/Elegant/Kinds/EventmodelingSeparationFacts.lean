import Elegant.Kinds.EventmodelingValid

namespace Elegant.Kinds.Eventmodeling

private def bandStep (offset : Int) (st : List Int × List Int × List Int)
    (band : Nat × Rect) : List Int × List Int × List Int :=
  (st.1.set band.1 band.2.y, st.2.1.set band.1 band.2.h,
    st.2.2 ++ [band.2.y + band.2.h + offset])

private theorem bandFold_preserves (offset : Int) (bands : List (Nat × Rect))
    (state : List Int × List Int × List Int) (i : Nat)
    (habsent : i ∉ bands.map Prod.fst) :
    (bands.foldl (bandStep offset) state).1.getD i 0 = state.1.getD i 0 ∧
    (bands.foldl (bandStep offset) state).2.1.getD i 0 = state.2.1.getD i 0 := by
  induction bands generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons band bands ih =>
    have hn : i ≠ band.1 := by
      intro he
      exact habsent (by simp [he])
    have ht : i ∉ bands.map Prod.fst := by
      intro hm
      exact habsent (by simp [hm])
    obtain ⟨hy, hh⟩ := ih (bandStep offset state band) ht
    rw [List.foldl_cons]
    constructor
    · rw [hy]
      simp only [bandStep, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (fun he => hn he.symm)]
    · rw [hh]
      simp only [bandStep, List.getD_eq_getElem?_getD,
        List.getElem?_set_ne (fun he => hn he.symm)]

private theorem bandFold_lengths (offset : Int) (bands : List (Nat × Rect))
    (state : List Int × List Int × List Int) :
    (bands.foldl (bandStep offset) state).1.length = state.1.length ∧
    (bands.foldl (bandStep offset) state).2.1.length = state.2.1.length := by
  induction bands generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons band bands ih =>
    simpa only [List.foldl_cons, bandStep, List.length_set] using
      ih (bandStep offset state band)

private theorem bandFold_member (offset : Int) (bands : List (Nat × Rect))
    (hn : (bands.map Prod.fst).Nodup)
    (state : List Int × List Int × List Int) (band : Nat × Rect)
    (hm : band ∈ bands) (hy : band.1 < state.1.length)
    (hh : band.1 < state.2.1.length) :
    (bands.foldl (bandStep offset) state).1.getD band.1 0 = band.2.y ∧
    (bands.foldl (bandStep offset) state).2.1.getD band.1 0 = band.2.h := by
  induction bands generalizing state with
  | nil => cases hm
  | cons first bands ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst band
      rw [List.foldl_cons]
      obtain ⟨hfy, hfh⟩ := bandFold_preserves offset bands
        (bandStep offset state first) first.1 hn'.1
      constructor
      · rw [hfy]
        simp only [bandStep, List.getD_eq_getElem?_getD,
          List.getElem?_set_self hy, Option.getD_some]
      · rw [hfh]
        simp only [bandStep, List.getD_eq_getElem?_getD,
          List.getElem?_set_self hh, Option.getD_some]
    · rw [List.foldl_cons]
      exact ih hn'.2 (bandStep offset state first) hm
        (by simpa only [bandStep, List.length_set] using hy)
        (by simpa only [bandStep, List.length_set] using hh)

private theorem bandWalk_keys (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) :
    (Lanes.Eventmodeling.bandWalk height gap width top indices).map Prod.fst = indices := by
  induction indices generalizing top with
  | nil => rfl
  | cons i indices ih =>
    simp only [Lanes.Eventmodeling.bandWalk, List.map_cons]
    rw [ih]

theorem rows_band_coordinates (g : Family) (c : Lanes.EventConsts)
    (frames : List Rect) {i : Nat} {band : Rect}
    (hm : (i, band) ∈ Lanes.Eventmodeling.laneBands g c frames) :
    (Lanes.Eventmodeling.rows g c frames).laneY.getD i 0 = band.y ∧
    (Lanes.Eventmodeling.rows g c frames).laneH.getD i 0 = band.h := by
  have hkeys : (Lanes.Eventmodeling.laneBands g c frames).map Prod.fst =
      Lanes.Eventmodeling.order g := bandWalk_keys _ _ _ _ _
  have hp : (Lanes.Eventmodeling.order g).Perm (List.range g.lanes.length) :=
    List.mergeSort_perm _ _
  have hn : ((Lanes.Eventmodeling.laneBands g c frames).map Prod.fst).Nodup := by
    rw [hkeys]
    exact hp.nodup_iff.mpr (List.nodup_range)
  have hi : i < g.lanes.length := by
    apply List.mem_range.mp
    apply hp.mem_iff.mp
    rw [← hkeys]
    exact List.mem_map.mpr ⟨(i, band), hm, rfl⟩
  exact bandFold_member (Lanes.half c.laneGap) _ hn
    (List.replicate g.lanes.length (0 : Int),
      List.replicate g.lanes.length (0 : Int), [Lanes.half c.lanePadding])
    (i, band) hm (by simpa using hi) (by simpa using hi)

theorem family_lane_band_coordinates {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r) :
    ∃ _dx dy : Int, ∀ i band,
      (i, band) ∈ Lanes.Eventmodeling.laneBands g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile)) →
      ∃ lane, r.lanes[i]? = some lane ∧ lane.y = band.y + dy ∧ lane.h = band.h := by
  obtain ⟨dx, dy, _, hlanes⟩ := family_frame_translation hr
  refine ⟨dx, dy, ?_⟩
  intro i band hm
  let c := Lanes.EventConsts.load profile
  let frames := Lanes.Eventmodeling.columns g c
  have hkeys : (Lanes.Eventmodeling.laneBands g c frames).map Prod.fst =
      Lanes.Eventmodeling.order g := bandWalk_keys _ _ _ _ _
  have hp : (Lanes.Eventmodeling.order g).Perm (List.range g.lanes.length) :=
    List.mergeSort_perm _ _
  have hi : i < g.lanes.length := by
    apply List.mem_range.mp
    apply hp.mem_iff.mp
    rw [← hkeys]
    exact List.mem_map.mpr ⟨(i, band), hm, rfl⟩
  have hc := rows_band_coordinates g c frames hm
  refine ⟨Lanes.shiftRect dx dy
    (Lanes.Eventmodeling.laneRect c (Lanes.Eventmodeling.rows g c frames) i), ?_, ?_, ?_⟩
  · have hindex : (List.range g.lanes.length)[i]? = some i := by simp [hi]
    rw [hlanes, List.getElem?_map, hindex]
    rfl
  · simpa only [Lanes.shiftRect, Lanes.Eventmodeling.laneRect] using
      congrArg (fun y : Int => y + dy) hc.1
  · exact hc.2

private theorem pairwise_map_transport {α β : Type} (xs : List α)
    (f : α → β) (R : α → α → Prop) (S : β → β → Prop)
    (h : xs.Pairwise R)
    (ht : ∀ a ∈ xs, ∀ b ∈ xs, R a b → S (f a) (f b)) :
    (xs.map f).Pairwise S := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    constructor
    · intro b hb
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hb
      exact ht a (by simp) source (by simp [hs]) (ha source hs)
    · exact ih hx (fun a ha b hb => ht a (by simp [ha]) b (by simp [hb]))

theorem family_lanes_band_order_separated {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r) :
    (((Lanes.Eventmodeling.laneBands g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).map
      (fun band => r.lanes.getD band.1 Lanes.zeroRect))).Pairwise
      (fun a b => a.y + a.h ≤ b.y ∧ Disjoint a b) := by
  let bands := Lanes.Eventmodeling.laneBands g (Lanes.EventConsts.load profile)
    (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
  obtain ⟨dx, dy, hc⟩ := family_lane_band_coordinates hr
  have hraw : bands.Pairwise
      (fun a b => a.2.y + a.2.h ≤ b.2.y ∧ Disjoint a.2 b.2) := by
    have h := Lanes.Eventmodeling.eventmodeling_entity_lanes_disjoint g profile
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
    simpa only [List.pairwise_map] using h
  apply pairwise_map_transport bands
    (fun band => r.lanes.getD band.1 Lanes.zeroRect) _ _ hraw
  intro a ha b hb hab
  obtain ⟨lane, hl, hy, hh⟩ := hc a.1 a.2 ha
  obtain ⟨lane', hl', hy', hh'⟩ := hc b.1 b.2 hb
  have hget : r.lanes.getD a.1 Lanes.zeroRect = lane := by
    rw [List.getD_eq_getElem?_getD, hl]
    rfl
  have hget' : r.lanes.getD b.1 Lanes.zeroRect = lane' := by
    rw [List.getD_eq_getElem?_getD, hl']
    rfl
  rw [hget, hget']
  constructor
  · omega
  · unfold Disjoint Rect.meetsInterior
    omega

end Elegant.Kinds.Eventmodeling
