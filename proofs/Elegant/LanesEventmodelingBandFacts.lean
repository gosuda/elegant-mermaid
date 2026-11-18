import Elegant.Kinds.EventmodelingSeparationFacts
import Elegant.LanesEventmodelingColumnFacts

set_option autoImplicit false

namespace Elegant.Lanes.Eventmodeling

theorem order_perm_range (g : Input) :
    (order g).Perm (List.range g.lanes.length) :=
  List.mergeSort_perm _ _

theorem order_nodup (g : Input) : (order g).Nodup :=
  (order_perm_range g).nodup_iff.mpr List.nodup_range

theorem mem_order_iff (g : Input) (i : Nat) :
    i ∈ order g ↔ i < g.lanes.length := by
  rw [(order_perm_range g).mem_iff, List.mem_range]

theorem rank_lt_lane_count (g : Input) {i : Nat} (hi : i < g.lanes.length) :
    rank g i < g.lanes.length := by
  have hm := (mem_order_iff g i).mpr hi
  have h := List.idxOf_lt_length_of_mem hm
  have hl := (order_perm_range g).length_eq
  simpa only [rank, hl, List.length_range] using h

theorem bandWalk_height (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) {i : Nat} {band : Rect}
    (hm : (i, band) ∈ bandWalk height gap width top indices) :
    band.h = height i := by
  induction indices generalizing top with
  | nil => simp [bandWalk] at hm
  | cons j indices ih =>
    simp only [bandWalk, List.mem_cons] at hm
    rcases hm with he | hm
    · cases he
      rfl
    · exact ih _ hm

theorem bandWalk_index_coverage (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) {i : Nat} (hi : i ∈ indices) :
    ∃ band, (i, band) ∈ bandWalk height gap width top indices := by
  induction indices generalizing top with
  | nil => simp at hi
  | cons j indices ih =>
    rcases List.mem_cons.mp hi with he | hi
    · subst i
      exact ⟨_, List.mem_cons_self⟩
    · obtain ⟨band, hb⟩ := ih (top + height j + gap) hi
      exact ⟨band, List.mem_cons_of_mem _ hb⟩

theorem laneBands_index_coverage (g : Input) (c : EventConsts) (frames : List Rect)
    {i : Nat} (hi : i < g.lanes.length) :
    ∃ band, (i, band) ∈ laneBands g c frames := by
  exact bandWalk_index_coverage _ _ _ _ _ ((mem_order_iff g i).mpr hi)

theorem rows_laneH (g : Input) (c : EventConsts) (frames : List Rect)
    {i : Nat} (hi : i < g.lanes.length) :
    (rows g c frames).laneH.getD i 0 = laneHeight g c frames i := by
  obtain ⟨band, hb⟩ := laneBands_index_coverage g c frames hi
  have hc := Kinds.Eventmodeling.rows_band_coordinates g c frames hb
  exact hc.2.trans (bandWalk_height _ _ _ _ _ hb)

theorem rows_laneY_lookup (g : Input) (c : EventConsts) (frames : List Rect)
    {i : Nat} (hi : i < g.lanes.length) :
    ∃ band, (i, band) ∈ laneBands g c frames ∧
      (rows g c frames).laneY.getD i 0 = band.y ∧
      (rows g c frames).laneH.getD i 0 = band.h := by
  obtain ⟨band, hb⟩ := laneBands_index_coverage g c frames hi
  exact ⟨band, hb, Kinds.Eventmodeling.rows_band_coordinates g c frames hb⟩

theorem successful_native_frame_lane_bounds {g : Input} {profile : Profile}
    {result : Result} (hr : layout g profile = .ok result) :
    ∀ frame ∈ g.frames, frame.lane < g.lanes.length := by
  unfold layout at hr
  by_cases hg : ((!g.frames.all (fun f => decide (f.lane < g.lanes.length))) ||
      !g.relations.all (fun r =>
        decide (r.src < g.frames.length ∧ r.dst < g.frames.length))) = true
  · simp only [hg, ↓reduceIte, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at hr
    cases hr
  · have hall : g.frames.all (fun f => decide (f.lane < g.lanes.length)) = true := by
      cases hf : g.frames.all (fun f => decide (f.lane < g.lanes.length)) <;>
        simp [hf] at hg ⊢
    intro frame hf
    exact of_decide_eq_true ((List.all_eq_true.mp hall) frame hf)

theorem successful_native_frame_rank_bounds {g : Input} {profile : Profile}
    {result : Result} (hr : layout g profile = .ok result)
    {frame : Frame} (hf : frame ∈ g.frames) :
    rank g frame.lane < g.lanes.length :=
  rank_lt_lane_count g (successful_native_frame_lane_bounds hr frame hf)

private theorem pairwise_distinct_vertical {α : Type} (xs : List α) (rect : α → Rect)
    (hp : xs.Pairwise (fun a b => (rect a).y + (rect a).h ≤ (rect b).y ∧
      Disjoint (rect a) (rect b)))
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    (rect a).y + (rect a).h ≤ (rect b).y ∨
      (rect b).y + (rect b).h ≤ (rect a).y := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp ha with he | ha
    · rcases List.mem_cons.mp hb with hb | hb
      · exact False.elim (hne (he.trans hb.symm))
      · exact Or.inl (by simpa only [he] using (hx b hb).1)
    · rcases List.mem_cons.mp hb with he | hb
      · exact Or.inr (by simpa only [he] using (hx a ha).1)
      · exact ih ht ha hb

theorem rows_laneRect_disjoint (g : Input) (profile : Profile) (frames : List Rect)
    {i j : Nat} (hi : i < g.lanes.length) (hj : j < g.lanes.length)
    (hne : i ≠ j) :
    Disjoint
      (laneRect (EventConsts.load profile) (rows g (EventConsts.load profile) frames) i)
      (laneRect (EventConsts.load profile) (rows g (EventConsts.load profile) frames) j) := by
  let c := EventConsts.load profile
  obtain ⟨a, ha⟩ := laneBands_index_coverage g c frames hi
  obtain ⟨b, hb⟩ := laneBands_index_coverage g c frames hj
  have hp : (laneBands g c frames).Pairwise (fun a b =>
      a.2.y + a.2.h ≤ b.2.y ∧ Disjoint a.2 b.2) := by
    simpa only [List.pairwise_map] using
      eventmodeling_entity_lanes_disjoint g profile frames
  have hd := pairwise_distinct_vertical (laneBands g c frames) Prod.snd hp ha hb
    (by intro he; exact hne (congrArg Prod.fst he))
  obtain ⟨hay, hah⟩ := Kinds.Eventmodeling.rows_band_coordinates g c frames ha
  obtain ⟨hby, hbh⟩ := Kinds.Eventmodeling.rows_band_coordinates g c frames hb
  dsimp only [c] at hay hah hby hbh
  unfold Disjoint Rect.meetsInterior
  simp only [laneRect]
  rw [hay, hah, hby, hbh]
  rcases hd with hd | hd <;> dsimp only at hd <;> omega

private theorem heightFold_lower (i : Nat) (pairs : List (Frame × Rect)) (initial : Int) :
    initial ≤ pairs.foldl
      (fun h p => if p.1.lane == i then max h p.2.h else h) initial := by
  induction pairs generalizing initial with
  | nil => exact Int.le_refl _
  | cons p pairs ih =>
    rw [List.foldl_cons]
    split
    · have ht := ih (max initial p.2.h)
      exact Int.le_trans (Int.le_max_left _ _) ht
    · exact ih initial

private theorem heightFold_member (i : Nat) (pairs : List (Frame × Rect))
    (initial : Int) {f : Frame} {r : Rect} (hm : (f, r) ∈ pairs)
    (hl : f.lane = i) :
    r.h ≤ pairs.foldl
      (fun h p => if p.1.lane == i then max h p.2.h else h) initial := by
  induction pairs generalizing initial with
  | nil => simp at hm
  | cons p pairs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp only [hl, BEq.rfl, ↓reduceIte]
      exact Int.le_trans (Int.le_max_right _ _) (heightFold_lower i pairs _)
    · exact ih _ hm

theorem laneHeight_frame_upper (g : Input) (c : EventConsts) (frames : List Rect)
    {f : Frame} {r : Rect} (hm : (f, r) ∈ g.frames.zip frames) :
    r.h + 2 * c.lanePadding ≤ laneHeight g c frames f.lane := by
  have h := heightFold_member f.lane (g.frames.zip frames)
    (max c.laneMinHeight
      ((((g.lanes[f.lane]?).bind (·.caption)).map (·.h)).getD 0)) hm rfl
  have he :
      (fun (h : Int) (p : Frame × Rect) =>
        if p.1.lane == f.lane then max h p.2.h else h) =
      (fun (h : Int) (p : Frame × Rect) =>
        match p with
        | (f', r') => if f'.lane == f.lane then max h r'.h else h) := by
    funext h p
    cases p
    rfl
  simp only [laneHeight]
  rw [← he]
  omega

theorem rows_frame_vertical_containment (g : Input) (profile : Profile)
    (frames : List Rect) {f : Frame} {r : Rect}
    (hm : (f, r) ∈ g.frames.zip frames) (hi : f.lane < g.lanes.length) :
    let c := EventConsts.load profile
    let p := rows g c frames
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    (laneRect c p f.lane).y ≤ placed.y ∧
      placed.y + placed.h ≤ (laneRect c p f.lane).y + (laneRect c p f.lane).h := by
  dsimp only
  have hh := rows_laneH g (EventConsts.load profile) frames hi
  have hu := laneHeight_frame_upper g (EventConsts.load profile) frames hm
  have hs := event_constants_positive profile
  simp only [laneRect]
  rw [hh]
  constructor <;> omega

private theorem corridorFold (offset : Int) (bands : List (Nat × Rect))
    (state : List Int × List Int × List Int) :
    (bands.foldl (fun st band =>
      (st.1.set band.1 band.2.y, st.2.1.set band.1 band.2.h,
        st.2.2 ++ [band.2.y + band.2.h + offset])) state).2.2 =
      state.2.2 ++ bands.map (fun band => band.2.y + band.2.h + offset) := by
  induction bands generalizing state with
  | nil => simp
  | cons band bands ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]

theorem rows_corridors (g : Input) (c : EventConsts) (frames : List Rect) :
    (rows g c frames).corridors =
      [half c.lanePadding] ++
        (laneBands g c frames).map (fun band => band.2.y + band.2.h + half c.laneGap) := by
  exact corridorFold (half c.laneGap) (laneBands g c frames)
    (List.replicate g.lanes.length (0 : Int),
      List.replicate g.lanes.length (0 : Int), [half c.lanePadding])

private theorem bandWalk_length (height : Nat → Int) (gap width top : Int)
    (indices : List Nat) :
    (bandWalk height gap width top indices).length = indices.length := by
  induction indices generalizing top with
  | nil => rfl
  | cons i indices ih =>
    simp only [bandWalk, List.length_cons, ih]

theorem rows_corridors_length (g : Input) (c : EventConsts) (frames : List Rect) :
    (rows g c frames).corridors.length = g.lanes.length + 1 := by
  rw [rows_corridors, List.length_append, List.length_map]
  have hl := bandWalk_length (laneHeight g c frames) c.laneGap
    ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
    0 (order g)
  have ho := (order_perm_range g).length_eq
  change 1 + (laneBands g c frames).length = g.lanes.length + 1
  unfold laneBands
  rw [hl, ho, List.length_range]
  omega

theorem successful_native_frame_vertical_containment {g : Input} {profile : Profile}
    {result : Result} (hr : layout g profile = .ok result)
    {f : Frame} {r : Rect}
    (hm : (f, r) ∈ g.frames.zip (columns g (EventConsts.load profile))) :
    let c := EventConsts.load profile
    let p := rows g c (columns g c)
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    (laneRect c p f.lane).y ≤ placed.y ∧
      placed.y + placed.h ≤ (laneRect c p f.lane).y + (laneRect c p f.lane).h := by
  have hf : f ∈ g.frames := (List.of_mem_zip hm).1
  exact rows_frame_vertical_containment g profile _ hm
    (successful_native_frame_lane_bounds hr f hf)

theorem rows_corridor_index_exists (g : Input) (c : EventConsts) (frames : List Rect)
    {k : Nat} (hk : k ≤ g.lanes.length) :
    ∃ y, (rows g c frames).corridors[k]? = some y := by
  have hl := rows_corridors_length g c frames
  have hb : k < (rows g c frames).corridors.length := by omega
  exact ⟨(rows g c frames).corridors[k], List.getElem?_eq_getElem hb⟩

private theorem bandWalk_after_corridor (height : Nat → Int) (gap width offset : Int)
    (indices : List Nat) (hg : 0 ≤ gap) (hh : ∀ i, 0 ≤ height i)
    (ho : 0 ≤ offset) (hog : offset ≤ gap) :
    ∀ top a b, a ∈ bandWalk height gap width top indices →
      b ∈ bandWalk height gap width top indices →
      a.2.y + a.2.h + offset ≤ b.2.y ∨
        b.2.y + b.2.h ≤ a.2.y + a.2.h + offset := by
  induction indices with
  | nil => simp [bandWalk]
  | cons i indices ih =>
    intro top a b ha hb
    simp only [bandWalk, List.mem_cons] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact Or.inr (by dsimp only; omega)
      · have hlow := bandWalk_lower height gap width (top + height i + gap)
          indices hg hh b.2 (List.mem_map.mpr ⟨b, hb, rfl⟩)
        exact Or.inl (by dsimp only; omega)
    · rcases hb with rfl | hb
      · have hlow := bandWalk_lower height gap width (top + height i + gap)
          indices hg hh a.2 (List.mem_map.mpr ⟨a, ha, rfl⟩)
        have hheight := bandWalk_height height gap width
          (top + height i + gap) indices ha
        have hnonneg := hh a.1
        exact Or.inr (by dsimp only; omega)
      · exact ih _ _ _ ha hb

theorem rows_corridor_outside_frame (g : Input) (profile : Profile)
    (frames : List Rect) {f : Frame} {r : Rect}
    (hm : (f, r) ∈ g.frames.zip frames) (hi : f.lane < g.lanes.length)
    {y : Int} (hy : y ∈ (rows g (EventConsts.load profile) frames).corridors) :
    let c := EventConsts.load profile
    let p := rows g c frames
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    y ≤ placed.y ∨ placed.y + placed.h ≤ y := by
  let c := EventConsts.load profile
  have hpad : 0 ≤ c.lanePadding := (event_constants_positive profile).2.1
  have hgap : 0 ≤ c.laneGap :=
    Int.le_of_lt (event_constants_positive profile).2.2.1
  have hhalf : 0 ≤ half c.laneGap ∧ half c.laneGap ≤ c.laneGap := by
    cases profile <;> decide
  have hfirst : half c.lanePadding ≤ c.lanePadding := by
    cases profile <;> decide
  have hh : ∀ i, 0 ≤ laneHeight g c frames i := by
    intro i
    have hl := laneHeight_lower g c frames i
    have hmin : 0 < c.laneMinHeight := (event_constants_positive profile).1
    omega
  obtain ⟨band, hb, hby, _⟩ := rows_laneY_lookup g c frames hi
  have hupper := laneHeight_frame_upper g c frames hm
  have hheight := bandWalk_height (laneHeight g c frames) c.laneGap
    ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
    0 (order g) hb
  change y ≤ (rows g c frames).laneY.getD f.lane 0 + c.lanePadding ∨
    (rows g c frames).laneY.getD f.lane 0 + c.lanePadding + r.h ≤ y
  rw [hby]
  rw [rows_corridors] at hy
  rcases List.mem_append.mp hy with hy | hy
  · have he : y = half c.lanePadding := List.mem_singleton.mp hy
    have hlow := bandWalk_lower (laneHeight g c frames) c.laneGap
      ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
      0 (order g) hgap hh band (List.mem_map.mpr ⟨(f.lane, band), hb, rfl⟩)
    exact Or.inl (by omega)
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hy
    change a.2.y + a.2.h + half c.laneGap = y at he
    have hsep := bandWalk_after_corridor (laneHeight g c frames) c.laneGap
      ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
      (half c.laneGap) (order g) hgap hh hhalf.1 hhalf.2
      0 a (f.lane, band) ha hb
    dsimp only at hsep
    rcases hsep with hsep | hsep
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

theorem rows_indexed_corridor_outside_frame (g : Input) (profile : Profile)
    (frames : List Rect) {f : Frame} {r : Rect}
    (hm : (f, r) ∈ g.frames.zip frames) (hi : f.lane < g.lanes.length)
    {k : Nat} (hk : k ≤ g.lanes.length) :
    let c := EventConsts.load profile
    let p := rows g c frames
    let y := p.corridors.getD k 0
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    y ≤ placed.y ∨ placed.y + placed.h ≤ y := by
  obtain ⟨y, hy⟩ := rows_corridor_index_exists g (EventConsts.load profile) frames hk
  have hmemb := List.mem_of_getElem? hy
  have h := rows_corridor_outside_frame g profile frames hm hi hmemb
  simpa only [List.getD_eq_getElem?_getD, hy, Option.getD_some] using h

theorem successful_native_corridor_outside_raw_frame {g : Input} {profile : Profile}
    {result : Result} (hr : layout g profile = .ok result)
    {box : Rect}
    (hbox : box ∈ (rows g (EventConsts.load profile)
      (columns g (EventConsts.load profile))).frames)
    {k : Nat} (hk : k ≤ g.lanes.length) :
    let p := rows g (EventConsts.load profile) (columns g (EventConsts.load profile))
    p.corridors.getD k 0 ≤ box.y ∨ box.y + box.h ≤ p.corridors.getD k 0 := by
  change box ∈ (g.frames.zip (columns g (EventConsts.load profile))).map
    (fun pair => { pair.2 with y :=
      ((rows g (EventConsts.load profile) (columns g (EventConsts.load profile))).laneY.getD
        pair.1.lane 0) + (EventConsts.load profile).lanePadding }) at hbox
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hbox
  have hi := successful_native_frame_lane_bounds hr pair.1 (List.of_mem_zip hp).1
  have h := rows_indexed_corridor_outside_frame g profile _ hp hi hk
  cases he
  exact h

private theorem bandWalk_adjacent_corridors (height : Nat → Int)
    (gap width offset padding : Int) (indices : List Nat) (hn : indices.Nodup)
    (hoff : offset ≤ gap + padding) :
    ∀ top first, first ≤ top + padding → ∀ i ∈ indices,
      ∃ band, (i, band) ∈ bandWalk height gap width top indices ∧
        (first :: (bandWalk height gap width top indices).map
          (fun b => b.2.y + b.2.h + offset)).getD (indices.idxOf i) 0 ≤
          band.y + padding ∧
        (first :: (bandWalk height gap width top indices).map
          (fun b => b.2.y + b.2.h + offset)).getD (indices.idxOf i + 1) 0 =
          band.y + band.h + offset := by
  induction indices with
  | nil => simp
  | cons j indices ih =>
    intro top first hfirst i hi
    obtain ⟨hj, ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hi with he | hi
    · subst i
      refine ⟨⟨0, top, width, height j⟩, List.mem_cons_self, ?_, ?_⟩
      · simpa only [List.idxOf_cons_self, List.getD_cons_zero] using hfirst
      · simp only [List.idxOf_cons_self, bandWalk, List.map_cons,
          List.getD_cons_succ, List.getD_cons_zero]
    · have hne : j ≠ i := by
        intro he
        exact hj (he ▸ hi)
      obtain ⟨band, hb, hbefore, hafter⟩ := ih ht
        (top + height j + gap) (top + height j + offset)
        (by omega) i hi
      have hidx : (j :: indices).idxOf i = indices.idxOf i + 1 := by
        simp only [List.idxOf_cons, beq_iff_eq, hne, ↓reduceIte]
      refine ⟨band, List.mem_cons_of_mem _ hb, ?_, ?_⟩
      · simpa only [hidx, bandWalk, List.map_cons, List.getD_cons_succ] using hbefore
      · simpa only [hidx, bandWalk, List.map_cons, List.getD_cons_succ] using hafter

theorem rows_rank_adjacent_corridors (g : Input) (profile : Profile)
    (frames : List Rect) {i : Nat} (hi : i < g.lanes.length) :
    let c := EventConsts.load profile
    let p := rows g c frames
    p.corridors.getD (rank g i) 0 ≤ p.laneY.getD i 0 + c.lanePadding ∧
      p.corridors.getD (rank g i + 1) 0 =
        p.laneY.getD i 0 + p.laneH.getD i 0 + half c.laneGap := by
  let c := EventConsts.load profile
  have hoff : half c.laneGap ≤ c.laneGap + c.lanePadding := by
    cases profile <;> decide
  have hfirst : half c.lanePadding ≤ (0 : Int) + c.lanePadding := by
    cases profile <;> decide
  obtain ⟨band, hb, hbefore, hafter⟩ := bandWalk_adjacent_corridors
    (laneHeight g c frames) c.laneGap
    ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
    (half c.laneGap) c.lanePadding (order g) (order_nodup g) hoff
    0 (half c.lanePadding) hfirst i ((mem_order_iff g i).mpr hi)
  obtain ⟨hy, hh⟩ := Kinds.Eventmodeling.rows_band_coordinates g c frames hb
  change (rows g c frames).corridors.getD (rank g i) 0 ≤
      (rows g c frames).laneY.getD i 0 + c.lanePadding ∧
    (rows g c frames).corridors.getD (rank g i + 1) 0 =
      (rows g c frames).laneY.getD i 0 +
        (rows g c frames).laneH.getD i 0 + half c.laneGap
  rw [hy, hh, rows_corridors]
  exact ⟨hbefore, hafter⟩

theorem rows_frame_adjacent_corridor_bounds (g : Input) (profile : Profile)
    (frames : List Rect) {f : Frame} {r : Rect}
    (hm : (f, r) ∈ g.frames.zip frames) (hi : f.lane < g.lanes.length) :
    let c := EventConsts.load profile
    let p := rows g c frames
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    p.corridors.getD (rank g f.lane) 0 ≤ placed.y ∧
      placed.y + placed.h ≤ p.corridors.getD (rank g f.lane + 1) 0 := by
  dsimp only
  obtain ⟨hbefore, hafter⟩ := rows_rank_adjacent_corridors g profile frames hi
  refine ⟨hbefore, ?_⟩
  rw [hafter, rows_laneH g (EventConsts.load profile) frames hi]
  have hheight := laneHeight_frame_upper g (EventConsts.load profile) frames hm
  have hpad := (event_constants_positive profile).2.1
  have hhalf : 0 ≤ half (EventConsts.load profile).laneGap := by
    cases profile <;> decide
  omega

private def walkCorridors (height : Nat → Int) (gap width offset top first : Int)
    (indices : List Nat) : List Int :=
  first :: (bandWalk height gap width top indices).map
    (fun band => band.2.y + band.2.h + offset)

private theorem bandWalk_foreign_nearside (height : Nat → Int)
    (gap width offset : Int) (indices : List Nat) (hn : indices.Nodup)
    (hg : 0 ≤ gap) (hh : ∀ i, 0 ≤ height i)
    (ho : 0 ≤ offset) (hog : offset ≤ gap) :
    ∀ top first, top - gap + offset ≤ first → ∀ i ∈ indices,
      top - gap + offset ≤
        (walkCorridors height gap width offset top first indices).getD (indices.idxOf i) 0 ∧
      ∀ j band, j ≠ i → (j, band) ∈ bandWalk height gap width top indices →
        band.y + band.h ≤
          (walkCorridors height gap width offset top first indices).getD (indices.idxOf i) 0 ∨
        (walkCorridors height gap width offset top first indices).getD
          (indices.idxOf i + 1) 0 ≤ band.y := by
  induction indices with
  | nil => simp
  | cons head indices ih =>
    intro top first hfirst i hi
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hi with he | hi
    · subst i
      constructor
      · simpa only [walkCorridors, List.idxOf_cons_self, List.getD_cons_zero] using hfirst
      · intro j band hne hb
        simp only [bandWalk, List.mem_cons] at hb
        rcases hb with he | hb
        · exact False.elim (hne (congrArg Prod.fst he))
        · have hl := bandWalk_lower height gap width (top + height head + gap)
            indices hg hh band (List.mem_map.mpr ⟨(j, band), hb, rfl⟩)
          right
          simp only [walkCorridors, bandWalk, List.map_cons,
            List.idxOf_cons_self, List.getD_cons_succ, List.getD_cons_zero]
          omega
    · have hne : head ≠ i := by
        intro he
        exact hnot (he ▸ hi)
      have hidx : (head :: indices).idxOf i = indices.idxOf i + 1 := by
        simp only [List.idxOf_cons, beq_iff_eq, hne, ↓reduceIte]
      obtain ⟨hlower, hforeign⟩ := ih hnodup
        (top + height head + gap) (top + height head + offset)
        (by omega) i hi
      have hbefore :
          (walkCorridors height gap width offset top first (head :: indices)).getD
            ((head :: indices).idxOf i) 0 =
          (walkCorridors height gap width offset (top + height head + gap)
            (top + height head + offset) indices).getD (indices.idxOf i) 0 := by
        simp only [walkCorridors, bandWalk, List.map_cons, hidx, List.getD_cons_succ]
      have hafter :
          (walkCorridors height gap width offset top first (head :: indices)).getD
            ((head :: indices).idxOf i + 1) 0 =
          (walkCorridors height gap width offset (top + height head + gap)
            (top + height head + offset) indices).getD (indices.idxOf i + 1) 0 := by
        simp only [walkCorridors, bandWalk, List.map_cons, hidx, List.getD_cons_succ]
      rw [hbefore]
      constructor
      · have hhead := hh head
        omega
      · intro j band hj hb
        rw [hafter]
        simp only [bandWalk, List.mem_cons] at hb
        rcases hb with he | hb
        · have he' := congrArg Prod.snd he
          cases he'
          left
          dsimp only
          omega
        · exact hforeign j band hj hb

theorem rows_foreign_lane_nearside (g : Input) (profile : Profile)
    (frames : List Rect) {i j : Nat}
    (hi : i < g.lanes.length) (hj : j < g.lanes.length) (hne : j ≠ i) :
    let c := EventConsts.load profile
    let p := rows g c frames
    (laneRect c p j).y + (laneRect c p j).h ≤ p.corridors.getD (rank g i) 0 ∨
      p.corridors.getD (rank g i + 1) 0 ≤ (laneRect c p j).y := by
  let c := EventConsts.load profile
  have hg : 0 ≤ c.laneGap := Int.le_of_lt (event_constants_positive profile).2.2.1
  have hh : ∀ k, 0 ≤ laneHeight g c frames k := by
    intro k
    have hl := laneHeight_lower g c frames k
    have hmin : 0 < c.laneMinHeight := (event_constants_positive profile).1
    have hpad : 0 ≤ c.lanePadding := (event_constants_positive profile).2.1
    omega
  have ho : 0 ≤ half c.laneGap := by cases profile <;> decide
  have hog : half c.laneGap ≤ c.laneGap := by cases profile <;> decide
  have hfirst : (0 : Int) - c.laneGap + half c.laneGap ≤ half c.lanePadding := by
    cases profile <;> decide
  obtain ⟨band, hb, hy, hhband⟩ := rows_laneY_lookup g c frames hj
  have h := (bandWalk_foreign_nearside (laneHeight g c frames) c.laneGap
    ((frames.foldl (fun a r => max a (r.x + r.w + c.boxPadding)) 0) + c.lanePadding)
    (half c.laneGap) (order g) (order_nodup g) hg hh ho hog
    0 (half c.lanePadding) hfirst i ((mem_order_iff g i).mpr hi)).2 j band hne hb
  change (rows g c frames).laneY.getD j 0 + (rows g c frames).laneH.getD j 0 ≤
      (rows g c frames).corridors.getD (rank g i) 0 ∨
    (rows g c frames).corridors.getD (rank g i + 1) 0 ≤
      (rows g c frames).laneY.getD j 0
  rw [hy, hhband, rows_corridors]
  exact h

theorem rows_foreign_frame_nearside (g : Input) (profile : Profile)
    (frames : List Rect) {i : Nat} {f : Frame} {r : Rect}
    (hi : i < g.lanes.length) (hm : (f, r) ∈ g.frames.zip frames)
    (hf : f.lane < g.lanes.length) (hne : f.lane ≠ i) :
    let c := EventConsts.load profile
    let p := rows g c frames
    let placed := { r with y := p.laneY.getD f.lane 0 + c.lanePadding }
    placed.y + placed.h ≤ p.corridors.getD (rank g i) 0 ∨
      p.corridors.getD (rank g i + 1) 0 ≤ placed.y := by
  have hband := rows_foreign_lane_nearside g profile frames hi hf hne
  have hcontain := rows_frame_vertical_containment g profile frames hm hf
  dsimp only at hcontain ⊢
  rcases hband with hband | hband
  · exact Or.inl (Int.le_trans hcontain.2 hband)
  · exact Or.inr (Int.le_trans hband hcontain.1)

theorem successful_native_foreign_frame_nearside {g : Input} {profile : Profile}
    {result : Result} (hr : layout g profile = .ok result)
    {i j : Nat} {source foreign : Frame} {a b : Rect}
    (hsource : g.frames[i]? = some source) (hforeign : g.frames[j]? = some foreign)
    (ha : (rows g (EventConsts.load profile) (columns g (EventConsts.load profile))).frames[i]? =
      some a)
    (hb : (rows g (EventConsts.load profile) (columns g (EventConsts.load profile))).frames[j]? =
      some b)
    (hne : foreign.lane ≠ source.lane) :
    let p := rows g (EventConsts.load profile) (columns g (EventConsts.load profile))
    let before := p.corridors.getD (rank g source.lane) 0
    let after := p.corridors.getD (rank g source.lane + 1) 0
    before ≤ a.y ∧ a.y + a.h ≤ after ∧
      (b.y + b.h ≤ before ∨ after ≤ b.y) := by
  let c := EventConsts.load profile
  let p := rows g c (columns g c)
  obtain ⟨ca, _, hca, _, _, _⟩ := raw_indexed_frame_origin g profile hsource
  obtain ⟨cb, _, hcb, _, _, _⟩ := raw_indexed_frame_origin g profile hforeign
  have hza : (g.frames.zip (columns g c))[i]? = some (source, ca) :=
    List.getElem?_zip_eq_some.mpr ⟨hsource, hca⟩
  have hzb : (g.frames.zip (columns g c))[j]? = some (foreign, cb) :=
    List.getElem?_zip_eq_some.mpr ⟨hforeign, hcb⟩
  have hpa : p.frames[i]? = some
      { ca with y := p.laneY.getD source.lane 0 + c.lanePadding } := by
    change ((g.frames.zip (columns g c)).map
      (fun pair => { pair.2 with y := p.laneY.getD pair.1.lane 0 + c.lanePadding }))[i]? = _
    rw [List.getElem?_map, hza]
    rfl
  have hpb : p.frames[j]? = some
      { cb with y := p.laneY.getD foreign.lane 0 + c.lanePadding } := by
    change ((g.frames.zip (columns g c)).map
      (fun pair => { pair.2 with y := p.laneY.getD pair.1.lane 0 + c.lanePadding }))[j]? = _
    rw [List.getElem?_map, hzb]
    rfl
  have hea := Option.some.inj (ha.symm.trans hpa)
  have heb := Option.some.inj (hb.symm.trans hpb)
  have hsi := successful_native_frame_lane_bounds hr source (List.mem_of_getElem? hsource)
  have hfi := successful_native_frame_lane_bounds hr foreign (List.mem_of_getElem? hforeign)
  have hown := rows_frame_adjacent_corridor_bounds g profile (columns g c)
    (List.mem_of_getElem? hza) hsi
  have hother := rows_foreign_frame_nearside g profile (columns g c) hsi
    (List.mem_of_getElem? hzb) hfi hne
  change p.corridors.getD (rank g source.lane) 0 ≤ a.y ∧
    a.y + a.h ≤ p.corridors.getD (rank g source.lane + 1) 0 ∧
    (b.y + b.h ≤ p.corridors.getD (rank g source.lane) 0 ∨
      p.corridors.getD (rank g source.lane + 1) 0 ≤ b.y)
  rw [hea, heb]
  exact ⟨hown.1, hown.2, hother⟩

end Elegant.Lanes.Eventmodeling
