import Elegant.Kinds.EventmodelingValid
import Elegant.LanesEventmodelingColumnFacts
import Elegant.LanesEventmodelingBandFacts

set_option autoImplicit false

namespace Elegant.Kinds.Eventmodeling

open Common

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem label_mapM_members {α β : Type} (f : α → Except LayoutError β) :
    ∀ (input : List α) (output : List β), input.mapM f = .ok output →
      input.length = output.length ∧
        ∀ pair ∈ input.zip output, f pair.1 = .ok pair.2 := by
  intro input
  induction input with
  | nil =>
    intro output h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst output
    exact ⟨rfl, by simp⟩
  | cons a rest ih =>
    intro output h
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst output
    obtain ⟨hlen, hrel⟩ := ih bs hbs
    refine ⟨by simpa using hlen, ?_⟩
    intro pair hp
    rcases List.mem_cons.mp hp with he | hp
    · cases he
      exact hb
    · exact hrel pair hp

theorem scene_label_origins {m : Model} {s : Scene} (h : scene m = .ok s) :
    ∃ g r, decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      m.labels.length = s.labels.length ∧
      ∀ pair ∈ m.labels.zip s.labels,
        ∃ i lane cap,
          g.lanes.findIdx? (·.id == pair.1.owner) = some i ∧
          g.lanes[i]? = some lane ∧ lane.caption = some cap ∧
          r.labels[i]? = some pair.2.rect ∧
          pair.2.id = pair.1.id ∧ pair.2.owner = pair.1.owner ∧
          pair.2.text = pair.1.text ∧
          pair.2.lines = cap.lines.map (fun line => String.ofList line.text) := by
  unfold scene at h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨boxes, _, h⟩ := bind_ok h
  obtain ⟨labels, hl, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst s
  obtain ⟨hlen, hrel⟩ := label_mapM_members _ m.labels labels hl
  refine ⟨g, r, hg, hr, hlen, ?_⟩
  intro pair hp
  have he := hrel pair hp
  cases hi : g.lanes.findIdx? (·.id == pair.1.owner) with
  | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at he
  | some i =>
    cases hlane : g.lanes[i]? with
    | none => simp [hi, hlane, throw, throwThe, MonadExceptOf.throw] at he
    | some lane =>
      cases hcap : lane.caption with
      | none => simp [hi, hlane, hcap, throw, throwThe, MonadExceptOf.throw] at he
      | some cap =>
        cases hrect : r.labels[i]? with
        | none => simp [hi, hlane, hcap, hrect, throw, throwThe, MonadExceptOf.throw] at he
        | some rect =>
          simp only [hi, hlane, hcap, hrect, pure,
            Except.pure, Except.ok.injEq] at he
          rw [← he]
          refine ⟨i, lane, cap, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;>
            first | rfl | assumption

theorem family_label_frame_translation {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∃ paths dx dy,
      g.relations.mapM (Lanes.Eventmodeling.route g profile raw) = .ok paths ∧
      r.labels = (List.range g.lanes.length).map (fun i =>
        Lanes.shiftRect dx dy (Lanes.Eventmodeling.labelRect g c raw i)) ∧
      r.lanes = (List.range g.lanes.length).map (fun i =>
        Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c raw i)) ∧
      r.frames = raw.frames.map (Lanes.shiftRect dx dy) := by
  unfold Lanes.Eventmodeling.layout at h
  by_cases hg : ((!g.frames.all (fun f => decide (f.lane < g.lanes.length))) ||
      !g.relations.all (fun relation =>
        decide (relation.src < g.frames.length ∧ relation.dst < g.frames.length))) = true
  · simp only [hg, ↓reduceIte, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
    cases h
  · simp only [hg, bind, Except.bind] at h
    obtain ⟨paths, hpaths, h⟩ := bind_ok h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst r
      exact ⟨paths, _, _, hpaths, rfl, rfl, rfl⟩

theorem family_label_translation {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∃ paths dx dy,
      g.relations.mapM (Lanes.Eventmodeling.route g profile raw) = .ok paths ∧
      r.labels = (List.range g.lanes.length).map (fun i =>
        Lanes.shiftRect dx dy (Lanes.Eventmodeling.labelRect g c { raw with routes := paths } i)) ∧
      r.lanes = (List.range g.lanes.length).map (fun i =>
        Lanes.shiftRect dx dy (Lanes.Eventmodeling.laneRect c { raw with routes := paths } i)) := by
  obtain ⟨paths, dx, dy, hpaths, hlabels, hlanes, _⟩ :=
    family_label_frame_translation h
  exact ⟨paths, dx, dy, hpaths, hlabels, hlanes⟩

theorem laneHeight_caption_lower (g : Family) (c : Lanes.EventConsts)
    (frames : List Rect) (i : Nat) (lane : Lanes.Eventmodeling.Lane)
    (cap : Lanes.Caption) (hlane : g.lanes[i]? = some lane)
    (hcap : lane.caption = some cap) :
    cap.h + 2 * c.lanePadding ≤ Lanes.Eventmodeling.laneHeight g c frames i := by
  have hfold : ∀ (pairs : List (Lanes.Eventmodeling.Frame × Rect)) (initial : Int),
      initial ≤ pairs.foldl (fun h pair => if pair.1.lane == i then max h pair.2.h else h) initial := by
    intro pairs
    induction pairs with
    | nil => intro initial; exact Int.le_refl _
    | cons pair rest ih =>
      intro initial
      simp only [List.foldl_cons]
      apply Int.le_trans _ (ih _)
      split
      · exact Int.le_max_left _ _
      · exact Int.le_refl _
  unfold Lanes.Eventmodeling.laneHeight
  simp only [hlane, Option.bind_some, hcap, Option.map_some, Option.getD_some]
  have h := hfold (g.frames.zip frames) (max c.laneMinHeight cap.h)
  have hbase := Int.le_max_right c.laneMinHeight cap.h
  omega

theorem labelRect_caption (g : Family) (c : Lanes.EventConsts)
    (p : Lanes.Eventmodeling.Plan) (i : Nat) (lane : Lanes.Eventmodeling.Lane)
    (cap : Lanes.Caption) (hlane : g.lanes[i]? = some lane)
    (hcap : lane.caption = some cap) :
    Lanes.Eventmodeling.labelRect g c p i =
      ⟨2 * c.lanePadding, p.laneY.getD i 0 + c.lanePadding, cap.w, cap.h⟩ := by
  simp [Lanes.Eventmodeling.labelRect, hlane, hcap]

theorem gutter_caption_lower (g : Family) (c : Lanes.EventConsts)
    (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption)
    (hlane : lane ∈ g.lanes) (hcap : lane.caption = some cap) :
    4 * c.lanePadding + cap.w ≤ Lanes.Eventmodeling.gutter g c := by
  have monotone : ∀ (lanes : List Lanes.Eventmodeling.Lane) (initial : Int),
      initial ≤ lanes.foldl (fun w l =>
        match l.caption with
        | none => w
        | some caption => max w (4 * c.lanePadding + caption.w)) initial := by
    intro lanes
    induction lanes with
    | nil => intro initial; exact Int.le_refl _
    | cons head rest ih =>
      intro initial
      simp only [List.foldl_cons]
      apply Int.le_trans _ (ih _)
      cases head.caption with
      | none => exact Int.le_refl _
      | some caption => exact Int.le_max_left _ _
  have member : ∀ (lanes : List Lanes.Eventmodeling.Lane) (initial : Int),
      lane ∈ lanes →
      4 * c.lanePadding + cap.w ≤ lanes.foldl (fun w l =>
        match l.caption with
        | none => w
        | some caption => max w (4 * c.lanePadding + caption.w)) initial := by
    intro lanes
    induction lanes with
    | nil => intro initial hm; simp at hm
    | cons head rest ih =>
      intro initial hm
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hm with he | hm
      · subst head
        simp only [hcap]
        exact Int.le_trans (Int.le_max_right _ _) (monotone rest _)
      · exact ih _ hm
  exact member g.lanes c.contentStartX hlane

theorem measureCaption_nonnegative {fontFamily : Bool} {profile : Profile} {role : TextRole}
    {target : Int} {text : String} {cap : Lanes.Caption}
    (h : measureCaption profile role target text fontFamily = .ok cap) :
    0 ≤ cap.w ∧ 0 ≤ cap.h := by
  let finish (metric : Measure.Metric) : Except LayoutError Lanes.Caption := do
    let lines ← match StyledMeasure.wrap metric target text.toList with
      | .ok lines => pure lines
      | .error _ => throw .overflow
    return ⟨lines, lines.foldl (fun w line => max w line.width) 0,
      (lines.length : Int) * LayoutConst.line_h.get profile, role⟩
  have process (metric : Measure.Metric) (hm : finish metric = .ok cap) :
      0 ≤ cap.w ∧ 0 ≤ cap.h := by
    dsimp only [finish] at hm
    cases hw : StyledMeasure.wrap metric target text.toList with
    | error error =>
      rw [hw] at hm
      change Except.error LayoutError.overflow = Except.ok cap at hm
      cases hm
    | ok lines =>
      rw [hw] at hm
      change Except.ok
        (⟨lines, lines.foldl (fun w line => max w line.width) 0,
          (lines.length : Int) * LayoutConst.line_h.get profile, role⟩ : Lanes.Caption) =
        Except.ok cap at hm
      cases hm
      constructor
      · exact Lanes.Eventmodeling.foldl_ge_initial
          (fun w line => max w line.width) (fun w line => Int.le_max_left _ _) lines 0
      · have hline : 0 ≤ LayoutConst.line_h.get profile := by
          cases profile <;> decide
        exact Int.mul_nonneg (by omega) hline
  cases profile with
  | cell =>
    apply process Measure.Metric.cell
    exact h
  | vector =>
    change (((if role == .body then Measure.Role.body else Measure.Role.label).metric fontFamily).bind
      finish) = .ok cap at h
    obtain ⟨metric, _, hm⟩ := bind_ok h
    exact process metric hm

theorem raw_label_frame_clearance (g : Family) (profile : Profile)
    (i : Nat) (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption)
    (hlane : g.lanes[i]? = some lane) (hcap : lane.caption = some cap)
    (box : Rect)
    (hbox : box ∈ (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    let label := Lanes.Eventmodeling.labelRect g c raw i
    label.x + label.w < box.x ∧ Disjoint label box := by
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  have hgutter := gutter_caption_lower g c lane cap (List.mem_of_getElem? hlane) hcap
  have hboxx := Lanes.Eventmodeling.raw_frame_gutter_lower g profile box hbox
  change Lanes.Eventmodeling.gutter g c ≤ box.x at hboxx
  have hpadding : 0 < c.lanePadding := by cases profile <;> decide
  have hrect := labelRect_caption g c raw i lane cap hlane hcap
  change (Lanes.Eventmodeling.labelRect g c raw i).x +
      (Lanes.Eventmodeling.labelRect g c raw i).w < box.x ∧
    Disjoint (Lanes.Eventmodeling.labelRect g c raw i) box
  rw [hrect]
  constructor
  · change 2 * c.lanePadding + cap.w < box.x
    omega
  · unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

theorem family_label_frame_clearance {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (i : Nat) (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption)
    (hlane : g.lanes[i]? = some lane) (hcap : lane.caption = some cap)
    (label box : Rect) (hlabel : r.labels[i]? = some label)
    (hbox : box ∈ r.frames) : Disjoint label box := by
  obtain ⟨paths, dx, dy, _, hlabels, _, hframes⟩ := family_label_frame_translation hr
  have hi : i < g.lanes.length := by
    by_cases h : i < g.lanes.length
    · exact h
    · have he : g.lanes[i]? = none := List.getElem?_eq_none (by omega)
      rw [he] at hlane
      contradiction
  rw [hlabels] at hlabel
  have he :
      Lanes.shiftRect dx dy (Lanes.Eventmodeling.labelRect g
        (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
          (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))) i) = label := by
    simpa [List.getElem?_map, hi] using hlabel
  rw [hframes] at hbox
  obtain ⟨rawBox, hrawBox, hbox⟩ := List.mem_map.mp hbox
  subst box
  rw [← he]
  have hclear := (raw_label_frame_clearance g profile i lane cap hlane hcap rawBox hrawBox).1
  unfold Disjoint Rect.meetsInterior
  dsimp only [Lanes.shiftRect]
  omega

theorem raw_label_lane_clearance (g : Family) (profile : Profile)
    (i j : Nat) (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption)
    (hlane : g.lanes[i]? = some lane) (hcap : lane.caption = some cap)
    (hi : i < g.lanes.length) (hj : j < g.lanes.length) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    let label := Lanes.Eventmodeling.labelRect g c raw i
    let band := Lanes.Eventmodeling.laneRect c raw j
    Disjoint band label ∨ band.StrictInside label := by
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  have hrect := labelRect_caption g c raw i lane cap hlane hcap
  have hpadding : 0 < c.lanePadding := by cases profile <;> decide
  change Disjoint (Lanes.Eventmodeling.laneRect c raw j)
      (Lanes.Eventmodeling.labelRect g c raw i) ∨
    (Lanes.Eventmodeling.laneRect c raw j).StrictInside
      (Lanes.Eventmodeling.labelRect g c raw i)
  by_cases hempty : g.frames = []
  · have hmax : raw.maxR = 0 := by
      simp [raw, Lanes.Eventmodeling.rows, Lanes.Eventmodeling.columns,
        Lanes.Eventmodeling.columnWalk, hempty]
    left
    rw [hrect]
    unfold Disjoint Rect.meetsInterior Lanes.Eventmodeling.laneRect
    dsimp only
    rw [hmax]
    omega
  · have hgutter := gutter_caption_lower g c lane cap (List.mem_of_getElem? hlane) hcap
    have hmax := Lanes.Eventmodeling.raw_gutter_le_maxR g profile hempty
    change Lanes.Eventmodeling.gutter g c ≤ raw.maxR at hmax
    have hheight := laneHeight_caption_lower g c
      (Lanes.Eventmodeling.columns g c) i lane cap hlane hcap
    have hlookup := Lanes.Eventmodeling.rows_laneH g c
      (Lanes.Eventmodeling.columns g c) hi
    change raw.laneH.getD i 0 = _ at hlookup
    have hstrict : (Lanes.Eventmodeling.laneRect c raw i).StrictInside
        (Lanes.Eventmodeling.labelRect g c raw i) := by
      rw [hrect]
      unfold Rect.StrictInside Lanes.Eventmodeling.laneRect
      dsimp only
      omega
    by_cases heq : j = i
    · subst j
      exact Or.inr hstrict
    · left
      have hdisjoint := Lanes.Eventmodeling.rows_laneRect_disjoint g profile
        (Lanes.Eventmodeling.columns g c) hj hi heq
      have hcontained : (Lanes.Eventmodeling.laneRect c raw i).Contained
          (Lanes.Eventmodeling.labelRect g c raw i) := by
        unfold Rect.StrictInside at hstrict
        unfold Rect.Contained
        omega
      exact contained_rects_disjoint hdisjoint (Rect.Contained.refl _) hcontained

theorem family_label_lane_clearance {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    (i j : Nat) (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption)
    (hlane : g.lanes[i]? = some lane) (hcap : lane.caption = some cap)
    (hj : j < g.lanes.length) (label band : Rect)
    (hlabel : r.labels[i]? = some label) (hband : r.lanes[j]? = some band) :
    Disjoint band label ∨ band.StrictInside label := by
  obtain ⟨_, dx, dy, _, hlabels, hlanes, _⟩ := family_label_frame_translation hr
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hlane
  rw [hlabels] at hlabel
  rw [hlanes] at hband
  have helabel := hlabel
  have heband := hband
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at helabel
  simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.some.injEq] at heband
  rw [← helabel, ← heband]
  rcases raw_label_lane_clearance g profile i j lane cap hlane hcap hi hj with hd | hs
  · left
    unfold Disjoint Rect.meetsInterior at hd ⊢
    dsimp only [Lanes.shiftRect]
    omega
  · right
    unfold Rect.StrictInside at hs ⊢
    dsimp only [Lanes.shiftRect]
    omega

theorem scene_label_member_origin {m : Model} {s : Scene}
    (hs : scene m = .ok s) {label : SceneLabel} (hm : label ∈ s.labels) :
    ∃ (g : Family) (r : Lanes.Eventmodeling.Result) (i : Nat)
      (lane : Lanes.Eventmodeling.Lane) (cap : Lanes.Caption), decode m = .ok g ∧
      Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      g.lanes[i]? = some lane ∧ lane.caption = some cap ∧
      r.labels[i]? = some label.rect := by
  obtain ⟨g, r, hg, hr, hlen, hrel⟩ := scene_label_origins hs
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨hib, _⟩ := List.getElem?_eq_some_iff.mp hindex
  have hin : index < m.labels.length := by omega
  have hz : (m.labels.zip s.labels)[index]? = some (m.labels[index], label) :=
    List.getElem?_zip_eq_some.mpr ⟨List.getElem?_eq_getElem hin, hindex⟩
  obtain ⟨i, lane, cap, _, hlane, hcap, hlabel, _⟩ :=
    hrel (m.labels[index], label) (List.mem_of_getElem? hz)
  exact ⟨g, r, i, lane, cap, hg, hr, hlane, hcap, hlabel⟩

theorem scene_c7 {m : Model} {s : Scene} (hwf : WellFormed m)
    (hs : scene m = .ok s) : Validator.C7 s.layoutDump := by
  intro label hlabel box hbox hexclusive _
  obtain ⟨out, hout, he⟩ := List.mem_map.mp hlabel
  subst label
  obtain ⟨g, r, i, lane, cap, hg, hr, hlane, hcap, hrect⟩ :=
    scene_label_member_origin hs hout
  obtain ⟨g', r', source, hg', hr', hsource, hplace⟩ := scene_output_origin hs hbox
  have heqg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have heqr : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have hmetadata := placeBox_metadata hplace
  have hall : m.boxes.all (fun b => b.role != .group || !b.exclusive) = true := by
    have h := hwf
    simp only [WellFormed, modelWellFormed, Bool.and_eq_true] at h
    exact h.2
  have hsourceWF := List.all_eq_true.mp hall source hsource
  have hnotgroup : ¬ (source.role == .group) = true := by
    intro hgroup
    have hex : source.exclusive = true := hmetadata.2.2.2.symm.trans hexclusive
    have heq : source.role = .group := beq_iff_eq.mp hgroup
    simp [heq, hex] at hsourceWF
  have hlookup := placeBox_lookup hplace
  simp only [hnotgroup] at hlookup
  obtain ⟨_, _, hframe⟩ := hlookup
  exact family_label_frame_clearance hr i lane cap hlane hcap out.rect box.rect hrect
    (List.mem_of_getElem? hframe)

theorem scene_c8b {m : Model} {s : Scene}
    (hs : scene m = .ok s) : Validator.C8b s.layoutDump := by
  intro box hbox hgroup label hlabel
  obtain ⟨out, hout, he⟩ := List.mem_map.mp hlabel
  subst label
  obtain ⟨g, r, i, lane, cap, hg, hr, hlane, hcap, hrect⟩ :=
    scene_label_member_origin hs hout
  obtain ⟨g', r', source, hg', hr', _, hplace⟩ := scene_output_origin hs hbox
  have heqg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have heqr : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have hmetadata := placeBox_metadata hplace
  have hsourcegroup : source.role = .group := by
    have he := hmetadata.2.2.1.symm.trans hgroup
    cases hrole : source.role with
    | node => simp [hrole, BoxRole.id] at he
    | group => rfl
  have hlookup := placeBox_lookup hplace
  simp only [hsourcegroup, beq_self_eq_true, ↓reduceIte] at hlookup
  obtain ⟨j, hfind, hband⟩ := hlookup
  obtain ⟨hj, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  exact family_label_lane_clearance hr i j lane cap hlane hcap hj out.rect box.rect hrect hband

theorem eventmodeling_c7 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C7 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c7 hwf hs

theorem eventmodeling_c8b {m : Model} {result : Layered.FamilyResult}
    (h : layout m = .ok result) : Validator.C8b result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c8b hs

end Elegant.Kinds.Eventmodeling
