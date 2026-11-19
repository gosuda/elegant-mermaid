import Elegant.Kinds.TimelineValid
import Elegant.Kinds.TimelineIdentityFacts

set_option autoImplicit false

namespace Elegant.Kinds.Timeline

open Lanes Lanes.Timeline

theorem decoded_horizontal_cardRects_disjoint {m : Model} {g : Family}
    {r : Lanes.Timeline.Result} (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r) :
    (cardRects g (horizontalPlan g (TimelineConsts.load m.profile))).Pairwise Disjoint := by
  obtain ⟨hsizes, hsections⟩ := decode_facts hg
  obtain ⟨hw, hph, hsh, heh, hsg, heg, hcg⟩ := native_sizes hr hsizes
  exact horizontal_cardRects_disjoint hsections hw hph hsh heg hsg hcg heh

theorem decoded_horizontal_native_cardRects_disjoint {m : Model} {g : Family}
    {r : Lanes.Timeline.Result} (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) :
    (cardRects g r.geometry).Pairwise Disjoint := by
  apply native_cardRects_disjoint hr
  simpa [Lanes.Timeline.plan, Lanes.Timeline.horizontal, hdirection] using
    decoded_horizontal_cardRects_disjoint hg hr

theorem horizontal_scene_box_rectangles {m : Model} {s : Scene} {g : Family}
    {r : Lanes.Timeline.Result} (hs : scene m = .ok s)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) :
    (∀ out ∈ s.boxes, out.rect ∈ cardRects g r.geometry) ∧
    (∀ a ∈ s.boxes, ∀ b ∈ s.boxes,
      a.rect = b.rect ∨ Disjoint a.rect b.rect) := by
  have hmember : ∀ out ∈ s.boxes, out.rect ∈ cardRects g r.geometry := by
    intro out hout
    obtain ⟨g', r', _box, hg', hr', _hb, _hcorr, hsource⟩ :=
      scene_box_source hs hout
    have hge : g' = g := Except.ok.inj (hg'.symm.trans hg)
    subst g'
    have hre : r' = r := Except.ok.inj (hr'.symm.trans hr)
    subst r'
    exact rectSource_mem hsource
  refine ⟨hmember, ?_⟩
  intro a ha b hb
  by_cases he : a.rect = b.rect
  · exact Or.inl he
  · exact Or.inr (disjoint_of_mem_ne
      (decoded_horizontal_native_cardRects_disjoint hg hr hdirection)
      (hmember a ha) (hmember b hb) he)

theorem horizontal_layout_box_rectangles {m : Model}
    {result : Layered.FamilyResult} {g : Family} {r : Lanes.Timeline.Result}
    (h : layout m = .ok result) (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) :
    ∀ a ∈ result.scene.layoutDump.boxes, ∀ b ∈ result.scene.layoutDump.boxes,
      a.rect = b.rect ∨ Disjoint a.rect b.rect := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact (horizontal_scene_box_rectangles hs hg hr hdirection).2

theorem horizontal_scene_distinct_boxes_disjoint {m : Model} {s : Scene}
    {g : Family} {r : Lanes.Timeline.Result} (hs : scene m = .ok s)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) :
    ∀ a ∈ s.boxes, ∀ b ∈ s.boxes, a.id ≠ b.id → Disjoint a.rect b.rect := by
  have hp := (decoded_horizontal_native_cardRects_disjoint hg hr hdirection).sublist
    (namedRects_sublist g r.geometry)
  intro a ha b hb hne
  obtain ⟨ga, ra, _ba, hga, hra, _hba, _hca, hsa⟩ := scene_box_source hs ha
  obtain ⟨gb, rb, _bb, hgb, hrb, _hbb, _hcb, hsb⟩ := scene_box_source hs hb
  have hea : ga = g := Except.ok.inj (hga.symm.trans hg)
  have heb : gb = g := Except.ok.inj (hgb.symm.trans hg)
  subst ga
  subst gb
  have hera : ra = r := Except.ok.inj (hra.symm.trans hr)
  have herb : rb = r := Except.ok.inj (hrb.symm.trans hr)
  subst ra
  subst rb
  exact named_disjoint hp (rectSource_named hsa) (rectSource_named hsb) hne

theorem horizontal_scene_exclusive {m : Model} {s : Scene}
    {g : Family} {r : Lanes.Timeline.Result} (hs : scene m = .ok s)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) : Validator.C2 s.layoutDump := by
  intro a ha b hb hne _ha _hb _hparent
  exact horizontal_scene_distinct_boxes_disjoint hs hg hr hdirection a ha b hb hne

theorem horizontal_scene_frame_boxes {m : Model} {s : Scene}
    {g : Family} {r : Lanes.Timeline.Result} (hs : scene m = .ok s)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) : Validator.C8a s.layoutDump := by
  intro frame hf _hrole box hb hne _hancestor _hdescendant
  exact horizontal_scene_distinct_boxes_disjoint hs hg hr hdirection
    frame hf box hb (Ne.symm hne)

theorem horizontal_layout_exclusive {m : Model} {result : Layered.FamilyResult}
    {g : Family} {r : Lanes.Timeline.Result} (h : layout m = .ok result)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) : Validator.C2 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact horizontal_scene_exclusive hs hg hr hdirection

theorem horizontal_layout_frame_boxes {m : Model} {result : Layered.FamilyResult}
    {g : Family} {r : Lanes.Timeline.Result} (h : layout m = .ok result)
    (hg : decode m = .ok g) (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) : Validator.C8a result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact horizontal_scene_frame_boxes hs hg hr hdirection

theorem horizontal_layout_box_clearance {m : Model} {result : Layered.FamilyResult}
    {g : Family} (h : layout m = .ok result) (hg : decode m = .ok g)
    (hdirection : g.direction = .LR) :
    Validator.C2 result.scene.layoutDump ∧ Validator.C8a result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  obtain ⟨g', r, hg', hr, _hc, _hl, _hb, _hroute⟩ := scene_execution hs
  have he : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  rw [hdump]
  exact ⟨horizontal_scene_exclusive hs hg hr hdirection,
    horizontal_scene_frame_boxes hs hg hr hdirection⟩

theorem horizontal_routes_fold_indexed (x : Int) (rects : List Rect)
    (initial : Rect) (j : Nat) (source target : Rect)
    (hsource : (initial :: rects)[j]? = some source)
    (htarget : rects[j]? = some target) :
    (rects.foldl (fun (state : Rect × List (List Point)) box =>
      (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]]))
        (initial, [])).2[j]? =
      some [⟨x, source.y + source.h⟩, ⟨x, target.y⟩] := by
  rw [horizontal_routes_fold_geometry]
  simp only [List.nil_append]
  have hzip : ((initial :: rects).zip rects)[j]? = some (source, target) := by
    have zip_index : ∀ (left right : List Rect) (i : Nat),
        left[i]? = some source → right[i]? = some target →
        (left.zip right)[i]? = some (source, target) := by
      intro left
      induction left with
      | nil => intro right i hi; simp at hi
      | cons first rest ih =>
        intro right i hi hj
        cases right with
        | nil => simp at hj
        | cons second tail =>
          cases i with
          | zero =>
            have hs : first = source := Option.some.inj hi
            have ht : second = target := Option.some.inj hj
            subst first
            subst second
            rfl
          | succ i =>
            exact ih tail i hi hj
    exact zip_index _ _ _ hsource htarget
  simp only [List.getElem?_map, hzip, Option.map_some]

theorem horizontal_routes_fold_indexed_ports (x : Int) (rects : List Rect)
    (initial : Rect) (j : Nat) (source target : Rect)
    (hsource : (initial :: rects)[j]? = some source)
    (htarget : rects[j]? = some target)
    (hmid : ∀ rect ∈ initial :: rects, rect.x + Lanes.half rect.w = x)
    (hsize : ∀ rect ∈ initial :: rects, 0 ≤ rect.w ∧ 0 ≤ rect.h) :
    ∃ points,
      (rects.foldl (fun (state : Rect × List (List Point)) box =>
        (box, state.2 ++ [[⟨x, state.1.y + state.1.h⟩, ⟨x, box.y⟩]]))
          (initial, [])).2[j]? = some points ∧
      points.head? = some ⟨x, source.y + source.h⟩ ∧
      points.getLast? = some ⟨x, target.y⟩ ∧
      Validator.onBoundary ⟨x, source.y + source.h⟩ source ∧
      Validator.onBoundary ⟨x, target.y⟩ target := by
  have hs := List.mem_of_getElem? hsource
  have ht := List.mem_cons_of_mem initial (List.mem_of_getElem? htarget)
  refine ⟨_, horizontal_routes_fold_indexed x rects initial j source target
    hsource htarget, rfl, rfl, ?_, ?_⟩
  · rw [← hmid source hs]
    exact bottom_midpoint_boundary source (hsize source hs).1 (hsize source hs).2
  · rw [← hmid target ht]
    exact top_midpoint_boundary target (hsize target ht).1 (hsize target ht).2

theorem horizontalPlan_route_indexed_geometry {g : Family} {c : TimelineConsts}
    {i : Nat} {paths : List (List Point)}
    (hpaths : (horizontalPlan g c).routes[i]? = some paths) :
    ∃ (initial : Rect) (rects : List Rect),
      (horizontalPlan g c).periods[i]? = some initial ∧
      (horizontalPlan g c).events[i]? = some rects ∧
      paths = (rects.foldl (fun (state : Rect × List (List Point)) box =>
        (box, state.2 ++
          [[⟨initial.x + Lanes.half (cardWidth g c), state.1.y + state.1.h⟩,
            ⟨initial.x + Lanes.half (cardWidth g c), box.y⟩]]))
              (initial, [])).2 := by
  change (((horizontalPlan g c).periods.zip (horizontalPlan g c).events).map
    (fun (pair : Rect × List Rect) =>
      (pair.2.foldl (fun (state : Rect × List (List Point)) box =>
        (box, state.2 ++
          [[⟨pair.1.x + Lanes.half (cardWidth g c), state.1.y + state.1.h⟩,
            ⟨pair.1.x + Lanes.half (cardWidth g c), box.y⟩]]))
              (pair.1, [])).2))[i]? = some paths at hpaths
  rw [List.getElem?_map] at hpaths
  cases hpair : ((horizontalPlan g c).periods.zip (horizontalPlan g c).events)[i]? with
  | none => simp only [hpair, Option.map_none] at hpaths; cases hpaths
  | some pair =>
    obtain ⟨initial, rects⟩ := pair
    obtain ⟨hi, he⟩ := getElem?_zip' hpair
    rw [hpair, Option.map_some] at hpaths
    exact ⟨initial, rects, hi, he, (Option.some.inj hpaths).symm⟩

private theorem eventRects_height_nonneg (c : TimelineConsts) (x w : Int) :
    ∀ (events : List Lanes.Timeline.Event) (top : Int),
      (∀ event ∈ events, 0 ≤ eventHeight c event) →
      ∀ rect ∈ eventRects c x w top events, 0 ≤ rect.h := by
  intro events
  induction events with
  | nil => intro top _ rect hm; cases hm
  | cons event rest ih =>
    intro top hs rect hm
    rcases List.mem_cons.mp hm with he | hm
    · subst rect
      exact hs event (List.mem_cons_self ..)
    · exact ih _ (fun e he => hs e (List.mem_cons_of_mem _ he)) rect hm

theorem horizontalPlan_column_geometry {g : Family} {c : TimelineConsts}
    {i : Nat} {initial : Rect} {rects : List Rect}
    (hi : (horizontalPlan g c).periods[i]? = some initial)
    (he : (horizontalPlan g c).events[i]? = some rects)
    (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ eventHeight c event) :
    (∀ rect ∈ initial :: rects,
      rect.x + Lanes.half rect.w = initial.x + Lanes.half (cardWidth g c)) ∧
    (∀ rect ∈ initial :: rects, 0 ≤ rect.w ∧ 0 ≤ rect.h) := by
  obtain ⟨period, pr, hp, hpr, hrects⟩ := horizontalPlan_events_getElem he
  have hsame : pr = initial := Option.some.inj (hpr.symm.trans hi)
  subst pr
  obtain ⟨_index, _period, _hperiod, hinitial⟩ :=
    period_mem_spec (List.mem_of_getElem? hi)
  have hwinitial : initial.w = cardWidth g c := by
    rw [hinitial]
    rfl
  have hhinitial : initial.h = periodHeight g c := by
    rw [hinitial]
    rfl
  have hcolumn : ∀ rect ∈ rects,
      rect.x = initial.x ∧ rect.w = cardWidth g c := by
    rw [hrects]
    exact eventRects_horizontal c initial.x (cardWidth g c) _ _
  have hheight : ∀ rect ∈ rects, 0 ≤ rect.h := by
    rw [hrects]
    exact eventRects_height_nonneg c initial.x (cardWidth g c) _ _
      (heights period (List.mem_of_getElem? hp))
  constructor
  · intro rect hm
    rcases List.mem_cons.mp hm with heq | hm
    · subst rect
      rw [hwinitial]
    · obtain ⟨hx, hwidth⟩ := hcolumn rect hm
      rw [hx, hwidth]
  · intro rect hm
    rcases List.mem_cons.mp hm with heq | hm
    · subst rect
      exact ⟨hwinitial.symm ▸ hw, hhinitial.symm ▸ hh⟩
    · exact ⟨(hcolumn rect hm).2.symm ▸ hw, hheight rect hm⟩

theorem horizontalPlan_indexed_ports {g : Family} {c : TimelineConsts}
    {i j : Nat} {paths : List (List Point)} {initial source target : Rect}
    {rects : List Rect}
    (hpaths : (horizontalPlan g c).routes[i]? = some paths)
    (hi : (horizontalPlan g c).periods[i]? = some initial)
    (he : (horizontalPlan g c).events[i]? = some rects)
    (hsource : (initial :: rects)[j]? = some source)
    (htarget : rects[j]? = some target)
    (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ eventHeight c event) :
    ∃ points first last, paths[j]? = some points ∧
      points.head? = some first ∧ points.getLast? = some last ∧
      Validator.onBoundary first source ∧ Validator.onBoundary last target := by
  obtain ⟨initial', rects', hi', he', hfold⟩ :=
    horizontalPlan_route_indexed_geometry hpaths
  have hsame : initial' = initial := Option.some.inj (hi'.symm.trans hi)
  have hrects : rects' = rects := Option.some.inj (he'.symm.trans he)
  subst initial'
  subst rects'
  obtain ⟨hmid, hsize⟩ := horizontalPlan_column_geometry hi he hw hh heights
  obtain ⟨points, hpoints, hfirst, hlast, hfrom, hto⟩ :=
    horizontal_routes_fold_indexed_ports
      (initial.x + Lanes.half (cardWidth g c)) rects initial j source target
      hsource htarget hmid hsize
  refine ⟨points, _, _, ?_, hfirst, hlast, hfrom, hto⟩
  rw [hfold]
  exact hpoints

private theorem mapped_index_inverse {α β : Type} (f : α → β)
    {xs : List α} {i : Nat} {out : β}
    (h : (xs.map f)[i]? = some out) :
    ∃ input, xs[i]? = some input ∧ f input = out := by
  rw [List.getElem?_map] at h
  cases hi : xs[i]? with
  | none => simp only [hi, Option.map_none] at h; cases h
  | some input =>
    rw [hi, Option.map_some] at h
    exact ⟨input, rfl, Option.some.inj h⟩

theorem horizontalPlan_shifted_indexed_ports {g : Family} {c : TimelineConsts}
    (dx dy : Int) {i j : Nat} {initial source target : Rect}
    {rects : List Rect} {paths : List (List Point)} {points : List Point}
    (hi : ((horizontalPlan g c).shift dx dy).periods[i]? = some initial)
    (he : ((horizontalPlan g c).shift dx dy).events[i]? = some rects)
    (hroutes : ((horizontalPlan g c).shift dx dy).routes[i]? = some paths)
    (hsource : (initial :: rects)[j]? = some source)
    (htarget : rects[j]? = some target)
    (hpoints : paths[j]? = some points)
    (hw : 0 ≤ cardWidth g c) (hh : 0 ≤ periodHeight g c)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ eventHeight c event) :
    ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
      Validator.onBoundary first source ∧ Validator.onBoundary last target := by
  obtain ⟨rawInitial, hrawInitial, hinitial⟩ :=
    mapped_index_inverse (Lanes.shiftRect dx dy) hi
  obtain ⟨rawRects, hrawRects, hrects⟩ :=
    mapped_index_inverse (List.map (Lanes.shiftRect dx dy)) he
  obtain ⟨rawPaths, hrawPaths, hpaths⟩ :=
    mapped_index_inverse (List.map (List.map (Lanes.shiftPoint dx dy))) hroutes
  subst initial
  subst rects
  subst paths
  have hsource' : ((rawInitial :: rawRects).map (Lanes.shiftRect dx dy))[j]? =
      some source := hsource
  obtain ⟨rawSource, hrawSource, hsourceEq⟩ :=
    mapped_index_inverse (Lanes.shiftRect dx dy) hsource'
  obtain ⟨rawTarget, hrawTarget, htargetEq⟩ :=
    mapped_index_inverse (Lanes.shiftRect dx dy) htarget
  obtain ⟨rawPoints, hrawPoints, hpointsEq⟩ :=
    mapped_index_inverse (List.map (Lanes.shiftPoint dx dy)) hpoints
  obtain ⟨provedPoints, first, last, hproved, hfirst, hlast, hfrom, hto⟩ :=
    horizontalPlan_indexed_ports hrawPaths hrawInitial hrawRects hrawSource
      hrawTarget hw hh heights
  have hsame : provedPoints = rawPoints :=
    Option.some.inj (hproved.symm.trans hrawPoints)
  subst provedPoints
  subst source
  subst target
  subst points
  exact route_ports_shift dx dy rawPoints rawSource rawTarget first last
    hfirst hlast hfrom hto

theorem horizontal_native_indexed_ports {m : Model} {g : Family}
    {r : Lanes.Timeline.Result} (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR)
    {i j : Nat} {initial source target : Rect} {rects : List Rect}
    {paths : List (List Point)} {points : List Point}
    (hi : r.geometry.periods[i]? = some initial)
    (he : r.geometry.events[i]? = some rects)
    (hroutes : r.geometry.routes[i]? = some paths)
    (hsource : (initial :: rects)[j]? = some source)
    (htarget : rects[j]? = some target)
    (hpoints : paths[j]? = some points) :
    ∃ first last, points.head? = some first ∧ points.getLast? = some last ∧
      Validator.onBoundary first source ∧ Validator.onBoundary last target := by
  obtain ⟨hgeometry, _hcanvas⟩ := native_layout_geometry hr
  obtain ⟨hw, hh, _hsection, heights, _hsg, _heg, _hcg⟩ :=
    native_sizes hr (decode_facts hg).1
  rw [hgeometry] at hi he hroutes
  simp only [Lanes.Timeline.plan, Lanes.Timeline.horizontal, hdirection] at hi he hroutes
  exact horizontalPlan_shifted_indexed_ports _ _ hi he hroutes hsource htarget
    hpoints (Int.le_of_lt hw) hh heights

theorem eventLinks_indexed_horizontal {m : Model}
    (hdirection : m.options.direction = .LR) :
    ∀ (events : List Lanes.Timeline.Event) (source : String) (j : Nat)
      (event : Lanes.Timeline.Event),
      EventLinks m source events → events[j]? = some event →
      ∃ route ∈ m.routes, route.id = event.link ∧ route.toId = event.id ∧
        (source :: events.map (·.id))[j]? = some route.fromId := by
  intro events
  induction events with
  | nil => intro source j event _ he; simp at he
  | cons first rest ih =>
    intro source j event hlinks he
    cases j with
    | zero =>
      have heq : first = event := Option.some.inj he
      subst event
      obtain ⟨route, hr, hid, hfrom, hto⟩ := hlinks.1
      exact ⟨route, hr, hid, hto, by
        simpa only [List.getElem?_cons_zero] using congrArg some hfrom.symm⟩
    | succ j =>
      have hrest : EventLinks m first.id rest := by
        simpa only [hdirection, BEq.rfl, ↓reduceIte] using hlinks.2
      obtain ⟨route, hr, hid, hto, hfrom⟩ := ih first.id j event hrest he
      exact ⟨route, hr, hid, hto, by
        simpa only [List.map_cons, List.getElem?_cons_succ] using hfrom⟩

private theorem model_route_eq_of_id {routes : List ModelRoute}
    (hu : (routes.map (·.id)).Nodup) {a b : ModelRoute}
    (ha : a ∈ routes) (hb : b ∈ routes) (hid : a.id = b.id) : a = b := by
  induction routes with
  | nil => cases ha
  | cons first rest ih =>
    obtain ⟨hfresh, hrest⟩ := List.nodup_cons.mp hu
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact he.symm
      · exact False.elim (hfresh (List.mem_map.mpr ⟨b, hb, hid.symm⟩))
    · rcases List.mem_cons.mp hb with he | hb
      · subst b
        exact False.elim (hfresh (List.mem_map.mpr ⟨a, ha, hid⟩))
      · exact ih hrest ha hb

theorem horizontal_layout_route_indexed_chain {m : Model}
    {result : Layered.FamilyResult} (hwf : WellFormed m)
    (h : layout m = .ok result) (hdirection : m.options.direction = .LR)
    {out : Route} (hout : out ∈ result.scene.layoutDump.routes) :
    ∃ (g : Family) (r : Lanes.Timeline.Result)
      (period : Lanes.Timeline.Period) (paths : List (List Point))
      (event : Lanes.Timeline.Event) (i j : Nat),
      decode m = .ok g ∧ Lanes.Timeline.layout g m.profile = .ok r ∧
      g.periods[i]? = some period ∧ r.geometry.routes[i]? = some paths ∧
      period.events[j]? = some event ∧ paths[j]? = some out.points ∧
      out.toId = event.id ∧
      (period.id :: period.events.map (·.id))[j]? = some out.fromId := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump] at hout
  obtain ⟨g, r, publicRoute, period, paths, event,
    hg, hr, hpublic, hcorr, hp, he, hid⟩ := scene_route_source hs hout
  obtain ⟨i, hperiod, hpaths⟩ := zip_member_index hp
  obtain ⟨j, hevent, hpoints⟩ := zip_member_index he
  obtain ⟨route, hroute, hlink, hto, hfrom⟩ :=
    eventLinks_indexed_horizontal hdirection period.events period.id j event
      (decode_links hg period (List.mem_of_getElem? hperiod)) hevent
  have heq : route = publicRoute :=
    model_route_eq_of_id (Model.routeIds_nodup hwf) hroute hpublic
      (hlink.trans hid)
  subst route
  refine ⟨g, r, period, paths, event, i, j, hg, hr, hperiod, hpaths,
    hevent, hpoints, hcorr.2.2.1.trans hto, ?_⟩
  rw [hcorr.2.1]
  exact hfrom

private theorem horizontal_C5_of_indexed_geometry
    {m : Model} {result : Layered.FamilyResult} {g : Family}
    (hg : decode m = .ok g) (hdirection : g.direction = .LR)
    (identity : ∀ out ∈ result.scene.layoutDump.routes,
      ∃ (r : Lanes.Timeline.Result) (i j : Nat)
        (initial : Rect) (rects : List Rect) (paths : List (List Point))
        (source target : Box),
        Lanes.Timeline.layout g m.profile = .ok r ∧
        r.geometry.periods[i]? = some initial ∧
        r.geometry.events[i]? = some rects ∧
        r.geometry.routes[i]? = some paths ∧
        paths[j]? = some out.points ∧
        (initial :: rects)[j]? = some source.rect ∧
        rects[j]? = some target.rect ∧
        result.scene.layoutDump.box? out.fromId = some source ∧
        result.scene.layoutDump.box? out.toId = some target) :
    Validator.C5 result.scene.layoutDump := by
  intro out hout
  obtain ⟨r, i, j, initial, rects, paths, source, target,
    hr, hi, he, hroutes, hpoints, hsource, htarget, hfrom, hto⟩ :=
    identity out hout
  obtain ⟨first, last, hfirst, hlast, hsourceBoundary, htargetBoundary⟩ :=
    horizontal_native_indexed_ports hg hr hdirection hi he hroutes
      hsource htarget hpoints
  exact ⟨first, last, source, target, hfirst, hlast, hfrom, hto,
    hsourceBoundary, htargetBoundary⟩

private theorem eventRects_length (c : TimelineConsts) (x w : Int) :
    ∀ (events : List Lanes.Timeline.Event) (top : Int),
      (eventRects c x w top events).length = events.length := by
  intro events
  induction events with
  | nil => intro top; rfl
  | cons event rest ih =>
    intro top
    simpa only [eventRects, List.length_cons] using congrArg Nat.succ (ih _)

theorem horizontal_native_route_column {m : Model} {g : Family}
    {r : Lanes.Timeline.Result} (hr : Lanes.Timeline.layout g m.profile = .ok r)
    (hdirection : g.direction = .LR) {i : Nat}
    {period : Lanes.Timeline.Period} {paths : List (List Point)}
    (hp : g.periods[i]? = some period)
    (hpaths : r.geometry.routes[i]? = some paths) :
    ∃ initial rects, r.geometry.periods[i]? = some initial ∧
      r.geometry.events[i]? = some rects ∧ rects.length = period.events.length := by
  let c := TimelineConsts.load m.profile
  let raw := horizontalPlan g c
  let ext := raw.extent g m.profile
  let dx := c.canvasMargin - ext.x
  let dy := c.canvasMargin - ext.y
  have hgeometry : r.geometry = raw.shift dx dy := by
    simpa [Lanes.Timeline.plan, Lanes.Timeline.horizontal, hdirection]
      using (native_layout_geometry hr).1
  rw [hgeometry] at hpaths
  obtain ⟨rawPaths, hrawPaths, _hshift⟩ :=
    mapped_index_inverse (List.map (List.map (Lanes.shiftPoint dx dy))) hpaths
  obtain ⟨initial, rects, hi, he, _hfold⟩ :=
    horizontalPlan_route_indexed_geometry hrawPaths
  obtain ⟨period', _pr, hp', _hpr, hrects⟩ := horizontalPlan_events_getElem he
  have heq : period' = period := Option.some.inj (hp'.symm.trans hp)
  subst period'
  change raw.periods[i]? = some initial at hi
  change raw.events[i]? = some rects at he
  refine ⟨Lanes.shiftRect dx dy initial, rects.map (Lanes.shiftRect dx dy), ?_, ?_, ?_⟩
  · rw [hgeometry]
    change (raw.periods.map (Lanes.shiftRect dx dy))[i]? = _
    simp only [List.getElem?_map, hi, Option.map_some]
  · rw [hgeometry]
    change (raw.events.map (List.map (Lanes.shiftRect dx dy)))[i]? = _
    simp only [List.getElem?_map, he, Option.map_some]
  · rw [List.length_map, hrects]
    exact eventRects_length _ _ _ _ _

theorem horizontal_layout_ports {m : Model} {result : Layered.FamilyResult}
    {g : Family} (hwf : WellFormed m) (h : layout m = .ok result)
    (hg : decode m = .ok g) (hdirection : g.direction = .LR) :
    Validator.C5 result.scene.layoutDump := by
  apply horizontal_C5_of_indexed_geometry hg hdirection
  intro out hout
  have hdir : m.options.direction = .LR :=
    (decode_direction_horizontal hg).symm.trans hdirection
  obtain ⟨g', r, period, paths, event, i, j,
    hg', hr, hp, hpaths, hevent, hpoints, hto, hfrom⟩ :=
    horizontal_layout_route_indexed_chain hwf h hdir hout
  have hge : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  obtain ⟨initial, rects, hi, he, hlength⟩ :=
    horizontal_native_route_column hr hdirection hp hpaths
  have hj : j < rects.length := by
    rw [hlength]
    exact (List.getElem?_eq_some_iff.mp hevent).1
  obtain ⟨targetRect, htargetRect⟩ := getElem?_of_lt hj
  have htargetSource : RectSource g r.geometry out.toId targetRect :=
    Or.inr (Or.inr (Or.inr ⟨period, rects, event,
      getElem_zip_some hp he, getElem_zip_some hevent htargetRect, hto.symm⟩))
  obtain ⟨targetBox, htargetBox, htargetEq⟩ :=
    layout_modelId_rectFor_lookup hwf h hg hr
      (rectSource_model_id hg htargetSource)
  have htargetRectEq : targetBox.rect = targetRect := Option.some.inj
    (htargetEq.symm.trans (rectFor_complete hwf hg htargetSource))
  have hsourceRect : ∃ sourceRect, (initial :: rects)[j]? = some sourceRect ∧
      RectSource g r.geometry out.fromId sourceRect := by
    cases j with
    | zero =>
      have hid : period.id = out.fromId := Option.some.inj hfrom
      exact ⟨initial, rfl, Or.inr (Or.inr (Or.inl ⟨i, period, hp, hid, hi⟩))⟩
    | succ k =>
      have hk : k < period.events.length := by omega
      obtain ⟨previous, hprevious⟩ := getElem?_of_lt hk
      have hpreviousId : previous.id = out.fromId := by
        simpa only [List.getElem?_cons_succ, List.getElem?_map, hprevious,
          Option.map_some, Option.some.injEq] using hfrom
      obtain ⟨sourceRect, hsourceRect⟩ :=
        getElem?_of_lt (show k < rects.length by omega)
      exact ⟨sourceRect, hsourceRect, Or.inr (Or.inr (Or.inr
        ⟨period, rects, previous, getElem_zip_some hp he,
          getElem_zip_some hprevious hsourceRect, hpreviousId⟩))⟩
  obtain ⟨sourceRect, hsourceRect, hsourceSource⟩ := hsourceRect
  obtain ⟨sourceBox, hsourceBox, hsourceEq⟩ :=
    layout_modelId_rectFor_lookup hwf h hg hr
      (rectSource_model_id hg hsourceSource)
  have hsourceRectEq : sourceBox.rect = sourceRect := Option.some.inj
    (hsourceEq.symm.trans (rectFor_complete hwf hg hsourceSource))
  refine ⟨r, i, j, initial, rects, paths, sourceBox, targetBox,
    hr, hi, he, hpaths, hpoints, ?_, ?_, hsourceBox, htargetBox⟩
  · rw [hsourceRectEq]
    exact hsourceRect
  · rw [htargetRectEq]
    exact htargetRect

private def axisMiss (a b : Point) (rect : Rect) : Prop :=
  max a.x b.x ≤ rect.x ∨ rect.x + rect.w ≤ min a.x b.x ∨
    max a.y b.y ≤ rect.y ∨ rect.y + rect.h ≤ min a.y b.y

private theorem axisMiss_shift (dx dy : Int) {a b : Point} {rect : Rect}
    (h : axisMiss a b rect) :
    axisMiss (Lanes.shiftPoint dx dy a) (Lanes.shiftPoint dx dy b)
      (Lanes.shiftRect dx dy rect) := by
  unfold axisMiss Lanes.shiftPoint Lanes.shiftRect at *
  dsimp only at *
  omega

private theorem axisMiss_not_hits {a b : Point} {rect : Rect}
    (h : axisMiss a b rect) : ¬ Polyline.hitsRect [a, b] rect := by
  apply Polyline.not_hits_of_allMiss
  refine ⟨?_, trivial⟩
  unfold axisMiss at h
  rcases h with hx | hx | hy | hy
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (Or.inl hy))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hy)))

private theorem ordered_stack_gap_clearance {stack : List Rect}
    (horder : stack.Pairwise (fun a b => a.y + a.h ≤ b.y))
    (hsize : ∀ b ∈ stack, 0 ≤ b.h)
    {j : Nat} {source target : Rect}
    (hs : stack[j]? = some source) (ht : stack[j + 1]? = some target) :
    ∀ b ∈ stack,
      b.y + b.h ≤ min (source.y + source.h) target.y ∨
        max (source.y + source.h) target.y ≤ b.y := by
  obtain ⟨hjs, hsource⟩ := List.getElem?_eq_some_iff.mp hs
  obtain ⟨hjt, htarget⟩ := List.getElem?_eq_some_iff.mp ht
  have hgap : source.y + source.h ≤ target.y := by
    simpa only [hsource, htarget] using
      horder.rel_getElem_of_lt hjs hjt (show j < j + 1 by omega)
  intro b hb
  obtain ⟨k, hk, hbox⟩ := List.mem_iff_getElem.mp hb
  by_cases hkj : k ≤ j
  · apply Or.inl
    have hbefore : b.y + b.h ≤ source.y + source.h := by
      by_cases heq : k = j
      · subst k
        have he : b = source := hbox.symm.trans hsource
        simpa only [he] using Int.le_refl (source.y + source.h)
      · have hrel : b.y + b.h ≤ source.y := by
          simpa only [hbox, hsource] using
            horder.rel_getElem_of_lt hk hjs (show k < j by omega)
        have hh := hsize source (List.mem_of_getElem? hs)
        omega
    omega
  · apply Or.inr
    have hafter : target.y ≤ b.y := by
      by_cases heq : k = j + 1
      · subst k
        have he : b = target := hbox.symm.trans htarget
        simpa only [he] using Int.le_refl target.y
      · have hrel : target.y + target.h ≤ b.y := by
          simpa only [htarget, hbox] using
            horder.rel_getElem_of_lt hjt hk (show j + 1 < k by omega)
        have hh := hsize target (List.mem_of_getElem? ht)
        omega
    omega

private theorem horizontal_column_stack {g : Family} {c : TimelineConsts}
    {i : Nat} {initial : Rect} {rects : List Rect}
    (hi : (horizontalPlan g c).periods[i]? = some initial)
    (he : (horizontalPlan g c).events[i]? = some rects)
    (_hh : 0 ≤ periodHeight g c) (hsg : 0 ≤ c.sectionGap)
    (heg : 0 ≤ c.eventGap)
    (heights : ∀ period ∈ g.periods, ∀ event ∈ period.events,
      0 ≤ eventHeight c event) :
    (initial :: rects).Pairwise (fun a b => a.y + a.h ≤ b.y) := by
  obtain ⟨period, pr, hp, hpr, hrects⟩ := horizontalPlan_events_getElem he
  have heq : pr = initial := Option.some.inj (hpr.symm.trans hi)
  subst pr
  obtain ⟨hy, hheight⟩ := period_rect_y (List.mem_of_getElem? hi)
  apply List.pairwise_cons.mpr
  constructor
  · intro box hb
    rw [hrects] at hb
    have hlow := eventRects_lower c initial.x (cardWidth g c) _ period.events
      heg (heights period (List.mem_of_getElem? hp)) box hb
    omega
  · exact (horizontalPlan_events_stack_disjoint g c heg heights
      (List.mem_of_getElem? he)).imp (fun h => h.1)

private theorem horizontal_raw_gap_clearance {m : Model} {g : Family}
    {r : Lanes.Timeline.Result} (hg : decode m = .ok g)
    (hr : Lanes.Timeline.layout g m.profile = .ok r)
    {i : Nat} {initial source target : Rect} {rects : List Rect}
    (hi : (horizontalPlan g (TimelineConsts.load m.profile)).periods[i]? = some initial)
    (he : (horizontalPlan g (TimelineConsts.load m.profile)).events[i]? = some rects)
    (hpair : (source, target) ∈ (initial :: rects).zip rects) :
    ∀ box ∈ cardRects g (horizontalPlan g (TimelineConsts.load m.profile)),
      axisMiss
        ⟨initial.x + Lanes.half (cardWidth g (TimelineConsts.load m.profile)),
          source.y + source.h⟩
        ⟨initial.x + Lanes.half (cardWidth g (TimelineConsts.load m.profile)), target.y⟩
        box := by
  let c := TimelineConsts.load m.profile
  obtain ⟨hsizes, hsections⟩ := decode_facts hg
  obtain ⟨hw, hh, hsh, heights, hsg, heg, hcg⟩ := native_sizes hr hsizes
  obtain ⟨hmid, hsize⟩ :=
    horizontalPlan_column_geometry hi he (Int.le_of_lt hw) hh heights
  obtain ⟨j, hs, ht⟩ := zip_member_index hpair
  have ht' : (initial :: rects)[j + 1]? = some target := ht
  have horder := horizontal_column_stack hi he hh hsg heg heights
  have hclear := ordered_stack_gap_clearance horder (fun b hb => (hsize b hb).2) hs ht'
  obtain ⟨period, pr, hp, hpr, hrects⟩ := horizontalPlan_events_getElem he
  have hprEq : pr = initial := Option.some.inj (hpr.symm.trans hi)
  subst pr
  obtain ⟨hy, hheight⟩ := period_rect_y (List.mem_of_getElem? hi)
  have hbase : initial.y + initial.h ≤ source.y + source.h ∧
      initial.y + initial.h ≤ target.y := by
    have eventLower : ∀ b ∈ rects, initial.y + initial.h ≤ b.y := by
      intro b hb
      rw [hrects] at hb
      have hlow := eventRects_lower c initial.x (cardWidth g c) _ period.events
        heg (heights period (List.mem_of_getElem? hp)) b hb
      omega
    constructor
    · rcases List.mem_cons.mp (List.mem_of_getElem? hs) with hsame | hmem
      · subst source
        omega
      · have hlo := eventLower source hmem
        have hnonneg := (hsize source (List.mem_of_getElem? hs)).2
        omega
    · exact eventLower target (List.mem_of_getElem? ht)
  intro box hb
  simp only [cardRects, List.mem_append] at hb
  rcases hb with ((htitle | hsection) | hperiod) | hevent
  · have htitleSome : ∃ title, g.title = some title := by
      cases htitle' : g.title with
      | none => simp [htitle'] at htitle
      | some title => exact ⟨title, rfl⟩
    obtain ⟨title, htitleSome⟩ := htitleSome
    have hbox : box = (horizontalPlan g c).title := by
      simpa only [htitleSome, Option.isSome_some, ↓reduceIte, List.mem_singleton]
        using htitle
    subst box
    obtain ⟨hty, _htw, hth⟩ := horizontalPlan_title_facts (c := c) htitleSome
    have htop : contentTop g c = title.caption.h + c.eventGap := by
      simp only [contentTop, htitleSome, Option.map_some, Option.getD_some]
    have htopPeriod := top_le_periodY (g := g) (c := c) hsh hsg
    dsimp only [c] at hty hth htop htopPeriod
    unfold axisMiss
    dsimp only [c]
    omega
  · have hsectionBottom := section_bottom_le_periodY hsection hsh hsg
    unfold axisMiss
    dsimp only
    omega
  · obtain ⟨hby, hbh⟩ := period_rect_y hperiod
    unfold axisMiss
    dsimp only
    omega
  · obtain ⟨k, other, otherRect, hk, hotherRect, hbox⟩ := event_member_spec hevent
    by_cases hki : k = i
    · subst k
      have hotherEq : other = period := Option.some.inj (hk.symm.trans hp)
      have hrectEq : otherRect = initial := Option.some.inj (hotherRect.symm.trans hi)
      subst other
      subst otherRect
      have hboxMem : box ∈ rects := by rw [hrects]; exact hbox
      have hc := hclear box (List.mem_cons_of_mem initial hboxMem)
      unfold axisMiss
      dsimp only
      omega
    · obtain ⟨hboxX, hboxW⟩ := eventRects_horizontal c otherRect.x (cardWidth g c)
        other.events _ box hbox
      have hwi : initial.w = cardWidth g c := by
        obtain ⟨_i, _p, _hp, heq⟩ := period_mem_spec (List.mem_of_getElem? hi)
        rw [heq]
        rfl
      have hwo : otherRect.w = cardWidth g c := by
        obtain ⟨_i, _p, _hp, heq⟩ := period_mem_spec (List.mem_of_getElem? hotherRect)
        rw [heq]
        rfl
      have hslots : slot g i period ≠ slot g k other := by
        intro heq
        exact hki (slot_inj hsections hk hp heq.symm)
      have hhalfLo : 0 ≤ Lanes.half (cardWidth g c) :=
        Int.fdiv_nonneg (Int.le_of_lt hw) (by decide)
      have hhalfHi : Lanes.half (cardWidth g c) ≤ cardWidth g c :=
        Int.fdiv_le_self 2 (Int.le_of_lt hw)
      dsimp only [c] at hboxX hboxW hwi hwo hhalfLo hhalfHi
      unfold axisMiss
      dsimp only
      rcases Nat.lt_trichotomy (slot g i period) (slot g k other) with hlt | heq | hgt
      · have hsep := (horizontal_periods_separated hp hk hi hotherRect hlt).2.1
        omega
      · exact False.elim (hslots heq)
      · have hsep := (horizontal_periods_separated hk hp hotherRect hi hgt).2.1
        omega

theorem horizontal_layout_route_clearance {m : Model}
    {result : Layered.FamilyResult} {g : Family} (_hwf : WellFormed m)
    (h : layout m = .ok result) (hg : decode m = .ok g)
    (hdirection : g.direction = .LR) :
    Validator.C6 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  intro out hout box hb _hexclusive _hscope
  obtain ⟨g', r, _publicRoute, period, paths, event,
    hg', hr, _hpublic, _hcorr, hp, hevent, _hid⟩ := scene_route_source hs hout
  have hge : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  obtain ⟨i, _hperiod, hpaths⟩ := zip_member_index hp
  have hpoints : out.points ∈ paths := (List.of_mem_zip hevent).2
  have hbox := (horizontal_scene_box_rectangles hs hg hr hdirection).1 box hb
  let c := TimelineConsts.load m.profile
  let raw := horizontalPlan g c
  let ext := raw.extent g m.profile
  let dx := c.canvasMargin - ext.x
  let dy := c.canvasMargin - ext.y
  have hgeometry : r.geometry = raw.shift dx dy := by
    simpa [Lanes.Timeline.plan, Lanes.Timeline.horizontal, hdirection]
      using (native_layout_geometry hr).1
  rw [hgeometry] at hpaths hbox
  rw [cardRects_shift] at hbox
  obtain ⟨rawBox, hrawBox, hboxEq⟩ := List.mem_map.mp hbox
  obtain ⟨rawPaths, hrawPaths, hpathsEq⟩ :=
    mapped_index_inverse (List.map (List.map (Lanes.shiftPoint dx dy))) hpaths
  rw [← hpathsEq] at hpoints
  obtain ⟨rawPoints, hrawPoints, hpointsEq⟩ := List.mem_map.mp hpoints
  obtain ⟨initial, rects, hi, he, hfold⟩ :=
    horizontalPlan_route_indexed_geometry hrawPaths
  rw [hfold, horizontal_routes_fold_geometry] at hrawPoints
  simp only [List.nil_append] at hrawPoints
  obtain ⟨⟨source, target⟩, hpair, hrawPointsEq⟩ := List.mem_map.mp hrawPoints
  subst rawPoints
  rw [← hpointsEq, ← hboxEq]
  apply axisMiss_not_hits
  exact axisMiss_shift dx dy (horizontal_raw_gap_clearance hg hr hi he hpair rawBox hrawBox)

end Elegant.Kinds.Timeline
