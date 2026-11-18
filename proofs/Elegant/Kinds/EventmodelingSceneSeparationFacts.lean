import Elegant.Kinds.EventmodelingSeparationFacts
import Elegant.Kinds.EventmodelingClearanceFacts
import Elegant.Kinds.EventmodelingLabelClearanceFacts
import Elegant.LanesEventmodelingBandFacts
import Elegant.RailroadAssemblyFacts

namespace Elegant.Kinds.Eventmodeling

theorem scene_exclusive_pair_sources {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    {a b : Box} (ha : a ∈ s.boxes) (hb : b ∈ s.boxes)
    (hea : a.exclusive = true) (heb : b.exclusive = true)
    (hid : a.id ≠ b.id) :
    ∃ g r sa sb, decode m = .ok g ∧
      Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      sa ∈ m.boxes ∧ sb ∈ m.boxes ∧
      sa.role ≠ .group ∧ sb.role ≠ .group ∧ sa.id ≠ sb.id ∧
      placeBox g r sa = .ok a ∧ placeBox g r sb = .ok b := by
  obtain ⟨g, r, sa, hg, hr, hsa, hpa⟩ := scene_output_origin hs ha
  obtain ⟨g', r', sb, hg', hr', hsb, hpb⟩ := scene_output_origin hs hb
  have hgg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hrr : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have hma := placeBox_metadata hpa
  have hmb := placeBox_metadata hpb
  have hna := scene_exclusive_is_node hwf hs ha hea
  have hnb := scene_exclusive_is_node hwf hs hb heb
  have hsag : sa.role ≠ .group := by
    intro he
    simpa [he, BoxRole.id, hna] using hma.2.2.1
  have hsbg : sb.role ≠ .group := by
    intro he
    simpa [he, BoxRole.id, hnb] using hmb.2.2.1
  refine ⟨g, r, sa, sb, hg, hr, hsa, hsb, hsag, hsbg, ?_, hpa, hpb⟩
  intro he
  exact hid (hma.1.trans (he.trans hmb.1.symm))

theorem placeBox_frame_lane_origin
    {g : Family} {profile : Profile} {r : Lanes.Eventmodeling.Result}
    {source : ModelBox} {out : Box}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (hrole : source.role ≠ .group) (hp : placeBox g r source = .ok out) :
    ∃ (i : Nat) (f : Lanes.Eventmodeling.Frame) (lane : Rect),
      g.frames[i]? = some f ∧ f.id = source.id ∧
      r.frames[i]? = some out.rect ∧ r.lanes[f.lane]? = some lane ∧
      lane.Contained out.rect := by
  obtain ⟨i, f, lane, hi, hf, hlane, hc⟩ :=
    placeBox_node_lane_containment hr hrole hp
  obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  have he : g.frames[i] = f := by
    have hi' := List.getElem?_eq_getElem hib
    exact Option.some.inj (hi'.symm.trans hf)
  have hfid : f.id = source.id := by
    simpa only [he, beq_iff_eq] using hmatch
  have hlookup := placeBox_lookup hp
  simp only [show (source.role == .group) = false from by simpa using hrole,
    Bool.false_eq_true, ↓reduceIte] at hlookup
  obtain ⟨j, hj, hrect⟩ := hlookup
  have hji : j = i := Option.some.inj (hj.symm.trans hi)
  subst j
  exact ⟨i, f, lane, hf, hfid, hrect, hlane, hc⟩

theorem placeBox_pair_lane_cases
    {g : Family} {profile : Profile} {r : Lanes.Eventmodeling.Result}
    {sa sb : ModelBox} {a b : Box}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (hsa : sa.role ≠ .group) (hsb : sb.role ≠ .group)
    (hpa : placeBox g r sa = .ok a) (hpb : placeBox g r sb = .ok b)
    (hid : sa.id ≠ sb.id) :
    Disjoint a.rect b.rect ∨
      ∃ (i j : Nat) (lane lane' : Rect), i ≠ j ∧
        r.lanes[i]? = some lane ∧ r.lanes[j]? = some lane' ∧
        lane.Contained a.rect ∧ lane'.Contained b.rect := by
  obtain ⟨i, f, lane, hf, hfid, hrect, hlane, hc⟩ :=
    placeBox_frame_lane_origin hr hsa hpa
  obtain ⟨j, f', lane', hf', hfid', hrect', hlane', hc'⟩ :=
    placeBox_frame_lane_origin hr hsb hpb
  by_cases he : f.lane = f'.lane
  · exact Or.inl (family_same_lane_disjoint hr hf hf' hrect hrect'
      (fun heid => hid (hfid.symm.trans (heid.trans hfid'))) he)
  · exact Or.inr ⟨f.lane, f'.lane, lane, lane', he, hlane, hlane', hc, hc'⟩

theorem scene_exclusive_pair_lane_cases {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    {a b : Box} (ha : a ∈ s.boxes) (hb : b ∈ s.boxes)
    (hea : a.exclusive = true) (heb : b.exclusive = true)
    (hid : a.id ≠ b.id) :
    Disjoint a.rect b.rect ∨
      ∃ (g : Family) (r : Lanes.Eventmodeling.Result) (i j : Nat)
        (lane lane' : Rect), decode m = .ok g ∧
        Lanes.Eventmodeling.layout g m.profile = .ok r ∧
        i ≠ j ∧ r.lanes[i]? = some lane ∧ r.lanes[j]? = some lane' ∧
        lane.Contained a.rect ∧ lane'.Contained b.rect := by
  obtain ⟨g, r, sa, sb, hg, hr, _, _, hsa, hsb, hids, hpa, hpb⟩ :=
    scene_exclusive_pair_sources hwf hs ha hb hea heb hid
  rcases placeBox_pair_lane_cases hr hsa hsb hpa hpb hids with hd | hc
  · exact Or.inl hd
  · obtain ⟨i, j, lane, lane', hne, hi, hj, hca, hcb⟩ := hc
    exact Or.inr ⟨g, r, i, j, lane, lane', hg, hr, hne, hi, hj, hca, hcb⟩

theorem family_distinct_lanes_disjoint
    {g : Family} {profile : Profile} {r : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    {i j : Nat} {a b : Rect}
    (ha : r.lanes[i]? = some a) (hb : r.lanes[j]? = some b)
    (hne : i ≠ j) : Disjoint a b := by
  have hi : i < g.lanes.length := by
    rw [← family_lanes_length hr]
    exact (List.getElem?_eq_some_iff.mp ha).1
  have hj : j < g.lanes.length := by
    rw [← family_lanes_length hr]
    exact (List.getElem?_eq_some_iff.mp hb).1
  let c := Lanes.EventConsts.load profile
  let frames := Lanes.Eventmodeling.columns g c
  let raw := Lanes.Eventmodeling.rows g c frames
  obtain ⟨dx, dy, _, hlanes⟩ := family_frame_translation hr
  have hia : (List.range g.lanes.length)[i]? = some i := by simp [hi]
  have hjb : (List.range g.lanes.length)[j]? = some j := by simp [hj]
  have hla : r.lanes[i]? =
      some (Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c raw i)) := by
    rw [hlanes, List.getElem?_map, hia]
    rfl
  have hlb : r.lanes[j]? =
      some (Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c raw j)) := by
    rw [hlanes, List.getElem?_map, hjb]
    rfl
  have hea := Option.some.inj (ha.symm.trans hla)
  have heb := Option.some.inj (hb.symm.trans hlb)
  rw [hea, heb]
  have hd := Lanes.Eventmodeling.rows_laneRect_disjoint g profile frames hi hj hne
  change Disjoint (Lanes.Eventmodeling.laneRect c raw i)
    (Lanes.Eventmodeling.laneRect c raw j) at hd
  unfold Disjoint Rect.meetsInterior at hd ⊢
  simp only [Lanes.shiftRect]
  omega

theorem scene_exclusive_boxes_disjoint {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    {a b : Box} (ha : a ∈ s.boxes) (hb : b ∈ s.boxes)
    (hea : a.exclusive = true) (heb : b.exclusive = true)
    (hid : a.id ≠ b.id) : Disjoint a.rect b.rect := by
  rcases scene_exclusive_pair_lane_cases hwf hs ha hb hea heb hid with hd | hl
  · exact hd
  · obtain ⟨g, r, i, j, lane, lane', _, hr, hne, hi, hj, hca, hcb⟩ := hl
    exact contained_rects_disjoint (family_distinct_lanes_disjoint hr hi hj hne) hca hcb

theorem scene_c2 {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s) :
    Validator.C2 s.layoutDump := by
  intro a ha b hb hid hea heb _
  exact scene_exclusive_boxes_disjoint hwf hs ha hb hea heb hid

theorem eventmodeling_c2 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c2 hwf hs


/-- Before witness for C8a: a group whose id is the empty string.  It is placed as the
first lane and its parentless frame sits inside it, so the group frame and that frame are
neither ancestor-related nor disjoint; validation reported `frame-clearance`. -/
def emptyGroupWitness : Model :=
  { kind := "eventmodeling"
    profile := .cell
    boxes :=
      [{ id := "", role := .group, exclusive := false, shape := "lane:0" },
       { id := "n0", parent := "", shape := "event", text := some "A" }]
    labels := [{ id := "cap", owner := "", text := "L" }] }

theorem emptyGroupWitness_wellFormed : WellFormed emptyGroupWitness := by decide

theorem emptyGroupWitness_withinLimits : WithinLimits emptyGroupWitness := by decide

/-- After witness: the empty group id is rejected at admission. -/
theorem emptyGroupWitness_rejected :
    layout emptyGroupWitness = .error (.geometry .domain) := by
  have hguard : hasEmptyGroupId emptyGroupWitness = true := by decide
  unfold layout
  simp only [hguard, ↓reduceIte]

/-! ### Clause C8a -/

private theorem boxes_id_injective {boxes : List Box}
    (h : (boxes.map (·.id)).Nodup) :
    ∀ a ∈ boxes, ∀ c ∈ boxes, a.id = c.id → a = c := by
  induction boxes with
  | nil => intro a ha; cases ha
  | cons first rest ih =>
    obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp h
    intro a ha c hc hid
    rcases List.mem_cons.mp ha with hea | ha
    · subst a
      rcases List.mem_cons.mp hc with hec | hc
      · exact hec.symm
      · exact absurd (by
          change first.id ∈ rest.map (·.id)
          rw [hid]
          exact List.mem_map_of_mem hc) hfirst
    · rcases List.mem_cons.mp hc with hec | hc
      · subst c
        exact absurd (by
          change first.id ∈ rest.map (·.id)
          rw [← hid]
          exact List.mem_map_of_mem ha) hfirst
      · exact ih hrest a ha c hc hid

/-- Scene-level clause C8a: a group frame is disjoint from every box that is neither its
ancestor nor its descendant.  Both boxes are traced back to their model sources.  Two
group boxes land on distinct lane rectangles (equal lanes would force equal ids), and a
group box versus a node box is disjoint unless both resolve to the same lane; the same
lane would make the group id the node's parent, which the clause excludes through the
dump's ancestor walk (a lane whose id is empty is ruled out by the admission guard). -/
theorem scene_c8a {m : Model} {s : Scene}
    (hwf : WellFormed m)
    (hgid : ∀ b ∈ m.boxes, b.role = .group → b.id ≠ "")
    (hs : scene m = .ok s) : Validator.C8a s.layoutDump := by
  intro g hg hrole b hb hne hanc hdesc
  obtain ⟨g₀, r, gb, hgdec, hr, hgbmem, hpg⟩ := scene_output_origin hs hg
  obtain ⟨g₁, r₁, nb, hgdec₁, hr₁, hnbmem, hpb⟩ := scene_output_origin hs hb
  have hgg : g₁ = g₀ := Except.ok.inj (hgdec₁.symm.trans hgdec)
  subst g₁
  have hrr : r₁ = r := Except.ok.inj (hr₁.symm.trans hr)
  subst r₁
  obtain ⟨_, _, hgrole, _⟩ := placeBox_metadata hpg
  have hgbgroup : gb.role = .group := by
    cases hc : gb.role with
    | node =>
      rw [hrole] at hgrole
      simp [hc, BoxRole.id] at hgrole
    | group => rfl
  have hbid : b.id = nb.id := placeBox_metadata hpb |>.1
  have hgid' : gb.id ≠ "" := hgid gb hgbmem hgbgroup
  obtain ⟨ids, ht⟩ := decode_lane_trace hwf hgdec
  have hglookup := placeBox_lookup hpg
  simp only [show (gb.role == .group) = true from by simp [hgbgroup], ↓reduceIte] at hglookup
  obtain ⟨iG, hiG, hrectG⟩ := hglookup
  obtain ⟨hibG, hGpred⟩ := List.findIdx?_eq_some_iff_getElem.mp hiG
  have hlaneG : g₀.lanes[iG].id = gb.id := beq_iff_eq.mp hGpred.1
  have hiGlen : iG < g₀.lanes.length := hibG
  cases hd : nb.role with
  | group =>
    have hblookup := placeBox_lookup hpb
    simp only [show (nb.role == .group) = true from by simp [hd], ↓reduceIte] at hblookup
    obtain ⟨iB, hiB, hrectB⟩ := hblookup
    obtain ⟨hiBlen, hBpred⟩ := List.findIdx?_eq_some_iff_getElem.mp hiB
    have hlaneB : g₀.lanes[iB].id = nb.id := beq_iff_eq.mp hBpred.1
    by_cases he : iG = iB
    · subst he
      have hlaneids : gb.id = nb.id := hlaneG.symm.trans hlaneB
      have hbd : b.id = g.id :=
        hbid.trans (hlaneids.symm.trans (placeBox_metadata hpg).1.symm)
      exact absurd hbd hne
    · exact contained_rects_disjoint
        (family_distinct_lanes_disjoint hr hrectG hrectB he)
        (Rect.Contained.refl _) (Rect.Contained.refl _)
  | node =>
    have hbnode : nb.role ≠ .group := by simp [hd]
    obtain ⟨iB, f, lane, hiF, hf, hlanef, hcont⟩ :=
      placeBox_node_lane_containment hr hbnode hpb
    obtain ⟨hibB, hBpred⟩ := List.findIdx?_eq_some_iff_getElem.mp hiF
    have hfid : f.id = nb.id := by
      have hfeq : g₀.frames[iB] = f :=
        Option.some.inj ((List.getElem?_eq_getElem hibB).symm.trans hf)
      rw [← hfeq]
      exact beq_iff_eq.mp hBpred.1
    by_cases he : iG = f.lane
    · have hfidmem : f ∈ g₀.frames := List.mem_of_getElem? hf
      have hentry := laneTrace_lane_entry ht hfidmem hnbmem hbnode hfid
      rw [← he] at hentry
      simp only [List.getElem?_eq_getElem hiGlen, Option.map_some,
        Option.some.injEq] at hentry
      rcases hentry with hp | hp
      · have hgbparent : gb.id = nb.parent := hlaneG.symm.trans hp
        have hbparent : b.parent = gb.id := (placeBox_metadata hpb).2.1.trans hgbparent.symm
        have hinj : ∀ a ∈ s.boxes, ∀ c ∈ s.boxes, a.id = c.id → a = c :=
          boxes_id_injective (scene_boxIds_nodup hwf hs)
        have hfind : s.layoutDump.box? b.id = some b := by
          show s.boxes.find? (fun c => c.id == b.id) = some b
          exact Railroad.find_box_of_id_injective s.boxes hinj b hb
        have hmem : gb.id ∈ (⟨⟨0, 0⟩, s.boxes, [], []⟩ : LayoutDump).ancestors b.id :=
          Railroad.ancestors_mem_parent hfind hbparent hgid'
        rw [(placeBox_metadata hpg).1] at hanc
        rw [show s.layoutDump.ancestors b.id =
          (⟨⟨0, 0⟩, s.boxes, [], []⟩ : LayoutDump).ancestors b.id from by
          unfold LayoutDump.ancestors
          exact Railroad.ancestors_dump_congr s.boxes.length b.id] at hanc
        exact absurd hmem hanc
      · exact absurd (by rw [← hlaneG]; exact hp) hgid'
    · exact contained_rects_disjoint (family_distinct_lanes_disjoint hr hrectG hlanef he)
        (Rect.Contained.refl _) hcont

theorem eventmodeling_c8a {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c8a hwf (layout_group_ids_nonempty m result h) hs

/-! ### Public validity -/

/-- The public eventmodeling validity theorem: a well-formed, within-limits model whose
layout succeeds produces a dump satisfying every hard constraint. -/
theorem eventmodeling_valid {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (h : layout m = .ok result) :
    HardConstraints result.scene.layoutDump :=
  ⟨eventmodeling_c1 h, eventmodeling_c2 hwf h, eventmodeling_c3 hwf h,
    eventmodeling_c4 hwf h, eventmodeling_c5 hwf h, eventmodeling_c6 hwf h,
    eventmodeling_c7 hwf h, ⟨eventmodeling_c8a hwf h, eventmodeling_c8b h⟩⟩


end Elegant.Kinds.Eventmodeling
