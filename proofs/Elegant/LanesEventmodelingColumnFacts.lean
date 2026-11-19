import Elegant.Kinds.EventmodelingValid

set_option autoImplicit false

namespace Elegant.Lanes.Eventmodeling

theorem frameSize_loaded_bounds (profile : Profile) (f : Frame) :
    3 ≤ (frameSize (EventConsts.load profile) f).w ∧
      0 < (frameSize (EventConsts.load profile) f).h := by
  have hw := frameSize_width_lower (EventConsts.load profile) f
  have hh : (EventConsts.load profile).boxMinHeight +
      2 * (EventConsts.load profile).boxPadding ≤
      (frameSize (EventConsts.load profile) f).h := by
    unfold frameSize clamp
    dsimp only
    have h := Int.le_max_left (EventConsts.load profile).boxMinHeight
      (min (EventConsts.load profile).boxMaxHeight
        (f.name.h + ((f.data.map fun d =>
          (EventConsts.load profile).lineHeight + d.h).getD 0)))
    omega
  have hwmin : 3 ≤ (EventConsts.load profile).boxMinWidth +
      2 * (EventConsts.load profile).boxPadding := by cases profile <;> decide
  have hhmin : 0 < (EventConsts.load profile).boxMinHeight +
      2 * (EventConsts.load profile).boxPadding := by cases profile <;> decide
  omega

theorem columnWalk_size_origin (c : EventConsts) (frames : List Frame)
    (reach : Int) (floor : List Int) :
    ∀ pair ∈ frames.zip (columnWalk c reach floor frames),
      pair.2.w = (frameSize c pair.1).w ∧
        pair.2.h = (frameSize c pair.1).h := by
  induction frames generalizing reach floor with
  | nil => simp
  | cons f fs ih =>
    intro pair hp
    simp only [columnWalk, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with he | hp
    · cases he
      exact ⟨rfl, rfl⟩
    · exact ih _ _ pair hp

theorem columnWalk_length (c : EventConsts) (frames : List Frame)
    (reach : Int) (floor : List Int) :
    (columnWalk c reach floor frames).length = frames.length := by
  induction frames generalizing reach floor with
  | nil => rfl
  | cons f fs ih => simp only [columnWalk, List.length_cons, ih]

theorem rows_indexed_column_origin (g : Input) (c : EventConsts)
    (rects : List Rect) {i : Nat} {f : Frame} {box : Rect}
    (hf : g.frames[i]? = some f) (hb : rects[i]? = some box) :
    ∃ placed, (rows g c rects).frames[i]? = some placed ∧
      placed.x = box.x ∧ placed.w = box.w ∧ placed.h = box.h := by
  let placed : Rect := { box with y := (rows g c rects).laneY.getD f.lane 0 + c.lanePadding }
  refine ⟨placed, ?_, rfl, rfl, rfl⟩
  have hz : (g.frames.zip rects)[i]? = some (f, box) :=
    List.getElem?_zip_eq_some.mpr ⟨hf, hb⟩
  change ((g.frames.zip rects).map (fun pair =>
    { pair.2 with y := (rows g c rects).laneY.getD pair.1.lane 0 + c.lanePadding }))[i]? = _
  rw [List.getElem?_map, hz]
  rfl

theorem raw_indexed_frame_origin (g : Input) (profile : Profile)
    {i : Nat} {f : Frame} (hf : g.frames[i]? = some f) :
    let c := EventConsts.load profile
    let p := rows g c (columns g c)
    ∃ column placed, (columns g c)[i]? = some column ∧
      p.frames[i]? = some placed ∧ placed.x = column.x ∧
      placed.w = (frameSize c f).w ∧ placed.h = (frameSize c f).h := by
  dsimp only
  let c := EventConsts.load profile
  have hi := (List.getElem?_eq_some_iff.mp hf).1
  have hlen : (columns g c).length = g.frames.length := columnWalk_length c _ _ _
  have hic : i < (columns g c).length := by omega
  have hc := List.getElem?_eq_getElem hic
  obtain ⟨placed, hp, hx, hw, hh⟩ := rows_indexed_column_origin g c _ hf hc
  have hz : (g.frames.zip (columns g c))[i]? = some (f, (columns g c)[i]) :=
    List.getElem?_zip_eq_some.mpr ⟨hf, hc⟩
  have hm := List.mem_of_getElem? hz
  have hs := columnWalk_size_origin c g.frames _ _ (f, (columns g c)[i]) hm
  exact ⟨_, placed, hc, hp, hx, hw.trans hs.1, hh.trans hs.2⟩

theorem raw_frame_strict_dimensions (g : Input) (profile : Profile) :
    let c := EventConsts.load profile
    ∀ box ∈ (rows g c (columns g c)).frames, 3 ≤ box.w ∧ 0 < box.h := by
  dsimp only
  intro box hb
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hb
  have hs := columnWalk_size_origin (EventConsts.load profile) g.frames _ _ pair hp
  have bounds := frameSize_loaded_bounds profile pair.1
  cases he
  dsimp only
  omega

theorem raw_frame_ports_strict (g : Input) (profile : Profile) :
    let c := EventConsts.load profile
    ∀ box ∈ (rows g c (columns g c)).frames,
      box.x < box.x + Int.fdiv box.w 3 ∧
      box.x + Int.fdiv box.w 3 < box.x + box.w ∧
      box.x < box.x + Int.fdiv (2 * box.w) 3 ∧
      box.x + Int.fdiv (2 * box.w) 3 < box.x + box.w := by
  dsimp only
  intro box hb
  have hw := (raw_frame_strict_dimensions g profile box hb).1
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide),
    Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

theorem raw_frame_gutter_lower (g : Input) (profile : Profile) :
    let c := EventConsts.load profile
    ∀ box ∈ (rows g c (columns g c)).frames, gutter g c ≤ box.x := by
  dsimp only
  intro box hb
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hb
  have hc := (List.of_mem_zip hp).2
  have hl := columnWalk_lower (EventConsts.load profile)
    (event_constants_positive profile).2.2.2.2.1
    (Int.le_of_lt (event_constants_positive profile).2.2.2.1)
    g.frames (gutter g (EventConsts.load profile) +
      (EventConsts.load profile).boxOverlap - (EventConsts.load profile).boxPadding)
    (List.replicate g.lanes.length 0) pair.2 hc
  cases he
  dsimp only
  omega

theorem frameRight_fold_member (padding : Int) (boxes : List Rect) (initial : Int)
    {box : Rect} (hb : box ∈ boxes) :
    box.x + box.w + padding ≤
      boxes.foldl (fun a r => max a (r.x + r.w + padding)) initial := by
  induction boxes generalizing initial with
  | nil => simp at hb
  | cons first rest ih =>
    rcases List.mem_cons.mp hb with he | hb
    · subst box
      exact Int.le_trans (Int.le_max_right _ _)
        (foldl_ge_initial (fun a r => max a (r.x + r.w + padding))
          (fun _ _ => Int.le_max_left _ _) rest _)
    · exact ih _ hb

theorem raw_maxR_frame_right (g : Input) (profile : Profile) :
    let c := EventConsts.load profile
    let p := rows g c (columns g c)
    ∀ box ∈ p.frames, box.x + box.w ≤ p.maxR := by
  dsimp only
  intro box hb
  have h := frameRight_fold_member (EventConsts.load profile).boxPadding
    (rows g (EventConsts.load profile) (columns g (EventConsts.load profile))).frames 0 hb
  have hp := (event_constants_positive profile).2.2.2.1
  change box.x + box.w + (EventConsts.load profile).boxPadding ≤
    (rows g (EventConsts.load profile) (columns g (EventConsts.load profile))).maxR at h
  omega

theorem raw_gutter_le_maxR (g : Input) (profile : Profile) (hne : g.frames ≠ []) :
    let c := EventConsts.load profile
    gutter g c ≤ (rows g c (columns g c)).maxR := by
  dsimp only
  cases hf : g.frames with
  | nil => exact False.elim (hne hf)
  | cons f fs =>
    have hfirst : g.frames[0]? = some f := by simp [hf]
    obtain ⟨column, box, _, hb, _, _, _⟩ := raw_indexed_frame_origin g profile hfirst
    have hm := List.mem_of_getElem? hb
    have hx := raw_frame_gutter_lower g profile box hm
    have hw := (raw_frame_strict_dimensions g profile box hm).1
    have hr := raw_maxR_frame_right g profile box hm
    omega

end Elegant.Lanes.Eventmodeling
