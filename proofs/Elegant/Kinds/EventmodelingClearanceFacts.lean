import Elegant.Kinds.EventmodelingValid
import Elegant.Layered.RouteTransport
import Elegant.LanesEventmodelingColumnFacts
import Elegant.LanesEventmodelingBandFacts
import Elegant.LanesEventmodelingTidyFacts

set_option autoImplicit false

namespace Elegant.Kinds.Eventmodeling

private theorem hits_loop_false
    (relation : Lanes.Eventmodeling.Relation) (path : List Point)
    (frames : List (Rect × Nat)) (initial : Bool)
    (h : (ForIn.forIn (m := Except LayoutError) frames initial
      (fun (b, i) hit => do
        let mut hit := hit
        if i != relation.src && i != relation.dst then
          if !([b.x, b.y, b.w, b.h, b.x + b.w, b.y + b.h].all Lanes.withinLimit) then
            throw .overflow
          if Polyline.hitsRectB path b then hit := true
        pure (ForInStep.yield hit))) = .ok false) :
    initial = false ∧
      ∀ entry ∈ frames, entry.2 ≠ relation.src → entry.2 ≠ relation.dst →
        Polyline.hitsRectB path entry.1 = false := by
  induction frames generalizing initial with
  | nil =>
    simp only [List.forIn_nil] at h
    cases h
    exact ⟨rfl, by simp⟩
  | cons entry rest ih =>
    rcases entry with ⟨box, index⟩
    rw [List.forIn_cons] at h
    by_cases hs : index = relation.src
    · simp only [hs, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, pure, Except.pure, Bind.bind, Except.bind] at h
      obtain ⟨hi, hr⟩ := ih initial h
      refine ⟨hi, ?_⟩
      intro entry he hsrc hdst
      rcases List.mem_cons.mp he with he | he
      · cases he
        exact False.elim (hsrc hs)
      · exact hr entry he hsrc hdst
    · by_cases ht : index = relation.dst
      · simp only [ht, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, pure, Except.pure, Bind.bind, Except.bind] at h
        obtain ⟨hi, hr⟩ := ih initial h
        refine ⟨hi, ?_⟩
        intro entry he hsrc hdst
        rcases List.mem_cons.mp he with he | he
        · cases he
          exact False.elim (hdst ht)
        · exact hr entry he hsrc hdst
      · have hne : (index != relation.src && index != relation.dst) = true := by
          simp [hs, ht]
        simp only [hne, ↓reduceIte] at h
        cases hb : ([box.x, box.y, box.w, box.h,
            box.x + box.w, box.y + box.h].all Lanes.withinLimit) with
        | false => simp [hb, Bind.bind, Except.bind] at h
        | true =>
          simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases hh : Polyline.hitsRectB path box with
          | true =>
            simp only [hh, ↓reduceIte, pure, Except.pure, Bind.bind, Except.bind] at h
            have impossible := (ih true h).1
            cases impossible
          | false =>
            simp only [hh, Bool.false_eq_true, ↓reduceIte,
              pure, Except.pure, Bind.bind, Except.bind] at h
            obtain ⟨hi, hr⟩ := ih initial h
            refine ⟨hi, ?_⟩
            intro entry he hsrc hdst
            rcases List.mem_cons.mp he with he | he
            · cases he
              exact hh
            · exact hr entry he hsrc hdst

theorem family_hits_clear
    (plan : Lanes.Eventmodeling.Plan)
    (relation : Lanes.Eventmodeling.Relation) (path : List Point)
    (h : Lanes.Eventmodeling.hits plan relation path = .ok false) :
    ∀ entry ∈ plan.frames.zipIdx,
      entry.2 ≠ relation.src → entry.2 ≠ relation.dst →
        ¬ Polyline.hitsRect path entry.1 := by
  unfold Lanes.Eventmodeling.hits at h
  cases hp : (path.flatMap (Lanes.pointValues 0 0)).all Lanes.withinLimit with
  | false => simp [hp, Bind.bind, Except.bind] at h
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_pure] at h
    have hloop := (hits_loop_false relation path plan.frames.zipIdx false h).2
    intro entry he hs ht
    exact (Polyline.hitsRectB_eq_false_iff path entry.1).mp (hloop entry he hs ht)

theorem family_route_branch_provenance
    (g : Family) (profile : Profile) (plan : Lanes.Eventmodeling.Plan)
    (relation : Lanes.Eventmodeling.Relation) (points : List Point)
    (h : Lanes.Eventmodeling.route g profile plan relation = .ok points) :
    let src := plan.frames.getD relation.src Lanes.zeroRect
    let dst := plan.frames.getD relation.dst Lanes.zeroRect
    let a := Lanes.Eventmodeling.rank g
      (((g.frames[relation.src]?).map (·.lane)).getD 0)
    let b := Lanes.Eventmodeling.rank g
      (((g.frames[relation.dst]?).map (·.lane)).getD 0)
    let start : Point :=
      ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩
    let finish : Point :=
      ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩
    let ca := plan.corridors.getD (if a < b then a + 1 else a) 0
    let cb := plan.corridors.getD (if b < a then b + 1 else b) 0
    (points = [start, finish] ∧
      Lanes.Eventmodeling.hits plan relation [start, finish] = .ok false) ∨
    ∃ column : Int,
      points = Lanes.Eventmodeling.tidy
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish] ∧
      ((column = start.x ∧
          Lanes.Eventmodeling.hits plan relation
            [⟨start.x, ca⟩, ⟨start.x, cb⟩] = .ok false) ∨
        (column = finish.x ∧
          Lanes.Eventmodeling.hits plan relation
            [⟨finish.x, ca⟩, ⟨finish.x, cb⟩] = .ok false) ∨
        column = plan.maxR) := by
  let src := plan.frames.getD relation.src Lanes.zeroRect
  let dst := plan.frames.getD relation.dst Lanes.zeroRect
  let a := Lanes.Eventmodeling.rank g
    (((g.frames[relation.src]?).map (·.lane)).getD 0)
  let b := Lanes.Eventmodeling.rank g
    (((g.frames[relation.dst]?).map (·.lane)).getD 0)
  let start : Point :=
    ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩
  let finish : Point :=
    ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩
  let ca := plan.corridors.getD (if a < b then a + 1 else a) 0
  let cb := plan.corridors.getD (if b < a then b + 1 else b) 0
  change (points = [start, finish] ∧
      Lanes.Eventmodeling.hits plan relation [start, finish] = .ok false) ∨
    ∃ column : Int,
      points = Lanes.Eventmodeling.tidy
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish] ∧
      ((column = start.x ∧ Lanes.Eventmodeling.hits plan relation
          [⟨start.x, ca⟩, ⟨start.x, cb⟩] = .ok false) ∨
        (column = finish.x ∧ Lanes.Eventmodeling.hits plan relation
          [⟨finish.x, ca⟩, ⟨finish.x, cb⟩] = .ok false) ∨ column = plan.maxR)
  change (do
    if profile == Profile.vector && a != b then
      if !(← Lanes.Eventmodeling.hits plan relation [start, finish]) then
        return [start, finish]
    let mut column := plan.maxR
    if !(← Lanes.Eventmodeling.hits plan relation
        [⟨start.x, ca⟩, ⟨start.x, cb⟩]) then
      column := start.x
    else if !(← Lanes.Eventmodeling.hits plan relation
        [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]) then
      column := finish.x
    return Lanes.Eventmodeling.tidy
      [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
        ⟨finish.x, cb⟩, finish]) = .ok points at h
  cases hd : Lanes.Eventmodeling.hits plan relation [start, finish] <;>
    cases hs : Lanes.Eventmodeling.hits plan relation
      [⟨start.x, ca⟩, ⟨start.x, cb⟩] <;>
    cases ht : Lanes.Eventmodeling.hits plan relation
      [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]
  all_goals
    simp_all only [Bind.bind, Except.bind] <;>
      (try split at h) <;> (try split at h) <;>
      (try split at h) <;> (try split at h) <;>
      (try dsimp only [pure, Except.pure] at h) <;>
      first
        | contradiction
        | (cases h; exact Or.inl ⟨rfl, by simp_all⟩)
        | (cases h; exact Or.inr ⟨start.x, rfl, Or.inl ⟨rfl, by simp_all⟩⟩)
        | (cases h; exact Or.inr ⟨finish.x, rfl, Or.inr (Or.inl ⟨rfl, by simp_all⟩)⟩)
        | (cases h; exact Or.inr ⟨plan.maxR, rfl, Or.inr (Or.inr rfl)⟩)

theorem corridor_orthogonal (start finish : Point) (ca cb column : Int) :
    Polyline.isOrthogonal
      [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
        ⟨finish.x, cb⟩, finish] = true := by
  simp [Polyline.isOrthogonal]

theorem family_maxR_leg_clear (g : Family) (profile : Profile) (ca cb : Int) :
    let c := Lanes.EventConsts.load profile
    let plan := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∀ box ∈ plan.frames,
      ¬ Polyline.hitsRect [⟨plan.maxR, ca⟩, ⟨plan.maxR, cb⟩] box := by
  dsimp only
  intro box hb hhit
  have hright := Lanes.Eventmodeling.raw_maxR_frame_right g profile box hb
  apply hhit.2.2
  refine ⟨Or.inr (Or.inl ?_), trivial⟩
  dsimp only
  omega

theorem family_clear_shift (dx dy : Int) (points : List Point) (box : Rect)
    (h : ¬ Polyline.hitsRect points box) :
    ¬ Polyline.hitsRect (points.map (Lanes.shiftPoint dx dy))
      (Lanes.shiftRect dx dy box) := by
  exact Layered.not_hitsRect_shift dx dy points box h

theorem scene_exclusive_frame_origin {m : Model} {s : Scene} {g : Family}
    {result : Lanes.Eventmodeling.Result}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    (hg : decode m = .ok g)
    (hr : Lanes.Eventmodeling.layout g m.profile = .ok result)
    {out : Box} (hout : out ∈ s.boxes) (hexclusive : out.exclusive = true) :
    ∃ index, g.frames.findIdx? (·.id == out.id) = some index ∧
      result.frames[index]? = some out.rect := by
  obtain ⟨g', result', source, hg', hr', _, hplace⟩ :=
    scene_output_origin hs hout
  have hgeq : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have hreq : result' = result := Except.ok.inj (hr'.symm.trans hr)
  subst result'
  have hmetadata := placeBox_metadata hplace
  have hnode := scene_exclusive_is_node hwf hs hout hexclusive
  have hrole : source.role ≠ .group := by
    intro he
    simpa [he, BoxRole.id, hnode] using hmetadata.2.2.1
  have hlookup := placeBox_lookup hplace
  simp only [show (source.role == .group) = false from by simp [hrole],
    Bool.false_eq_true, ↓reduceIte] at hlookup
  obtain ⟨index, hfind, hrect⟩ := hlookup
  exact ⟨index, by simpa only [hmetadata.1] using hfind, hrect⟩

theorem scene_foreign_route_frame_indices {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s)
    {route : Route} {box : Box}
    (hroute : route ∈ s.routes) (hbox : box ∈ s.boxes)
    (hexclusive : box.exclusive = true)
    (hscope : box.id ∉ s.layoutDump.routeScope route) :
    ∃ (g : Family) (result : Lanes.Eventmodeling.Result) (i : Nat)
        (relation : Lanes.Eventmodeling.Relation) (j : Nat),
      decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok result ∧
      g.relations[i]? = some relation ∧ result.routes[i]? = some route.points ∧
      result.frames[j]? = some box.rect ∧ j ≠ relation.src ∧ j ≠ relation.dst := by
  obtain ⟨g, result, i, input, hg, hr, hinput, hpoints, hfrom, hto, _⟩ :=
    scene_route_origin hs hroute
  obtain ⟨j, hfind, hrect⟩ :=
    scene_exclusive_frame_origin hwf hs hg hr hbox hexclusive
  have hidentity := (decode_relation_identity hwf hg).1
  have hilength : i < g.relations.length := by
    have hi := (List.getElem?_eq_some_iff.mp hinput).1
    have hlength := hidentity.lengths
    omega
  let relation := g.relations[i]
  have hrelation : g.relations[i]? = some relation :=
    List.getElem?_eq_getElem hilength
  obtain ⟨hsrc, hdst⟩ := hidentity.lookup hinput hrelation
  have hnotfrom : box.id ≠ route.fromId := by
    intro he
    exact hscope (by simp [LayoutDump.routeScope, he])
  have hnotto : box.id ≠ route.toId := by
    intro he
    exact hscope (by simp [LayoutDump.routeScope, he])
  refine ⟨g, result, i, relation, j, hg, hr, hrelation, hpoints, hrect, ?_, ?_⟩
  · intro he
    subst j
    have hbid := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
    have hsid := (List.findIdx?_eq_some_iff_getElem.mp hsrc).2.1
    have heid : box.id = input.fromId :=
      (beq_iff_eq.mp hbid).symm.trans (beq_iff_eq.mp hsid)
    exact hnotfrom (heid.trans hfrom.symm)
  · intro he
    subst j
    have hbid := (List.findIdx?_eq_some_iff_getElem.mp hfind).2.1
    have htid := (List.findIdx?_eq_some_iff_getElem.mp hdst).2.1
    have heid : box.id = input.toId :=
      (beq_iff_eq.mp hbid).symm.trans (beq_iff_eq.mp htid)
    exact hnotto (heid.trans hto.symm)

theorem family_corridor_horizontal_misses {g : Family} {profile : Profile}
    {result : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok result)
    {box : Rect}
    (hbox : box ∈ (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames)
    {k : Nat} (hk : k ≤ g.lanes.length) (left right : Int) :
    let plan := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
    Polyline.segMisses ⟨left, plan.corridors.getD k 0⟩
      ⟨right, plan.corridors.getD k 0⟩ box := by
  dsimp only
  rcases Lanes.Eventmodeling.successful_native_corridor_outside_raw_frame
      hr hbox hk with hbefore | hafter
  · refine Or.inr (Or.inr (Or.inl ?_))
    dsimp only
    simpa only [Int.max_self] using hbefore
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    dsimp only
    simpa only [Int.min_self] using hafter

theorem family_same_lane_stub_clear {g : Family} {profile : Profile}
    {result : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok result)
    {i j : Nat} {frame other : Lanes.Eventmodeling.Frame} {box obstacle : Rect}
    (hi : g.frames[i]? = some frame) (hj : g.frames[j]? = some other)
    (hbox : (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames[i]? = some box)
    (hobstacle : (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames[j]? = some obstacle)
    (hne : i ≠ j) (hlane : frame.lane = other.lane)
    (x y₁ y₂ : Int) (hxleft : box.x ≤ x) (hxright : x ≤ box.x + box.w) :
    ¬ Polyline.hitsRect [⟨x, y₁⟩, ⟨x, y₂⟩] obstacle := by
  have hp := family_rows_same_lane_disjoint hr
  have hzi : (g.frames.zip
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames)[i]? =
      some (frame, box) := List.getElem?_zip_eq_some.mpr ⟨hi, hbox⟩
  have hzj : (g.frames.zip
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames)[j]? =
      some (other, obstacle) := List.getElem?_zip_eq_some.mpr ⟨hj, hobstacle⟩
  obtain ⟨hib, hieq⟩ := List.getElem?_eq_some_iff.mp hzi
  obtain ⟨hjb, hjeq⟩ := List.getElem?_eq_some_iff.mp hzj
  have hseparated : box.x + box.w ≤ obstacle.x ∨ obstacle.x + obstacle.w ≤ box.x := by
    by_cases hij : i < j
    · have hpair := hp.rel_getElem_of_lt hib hjb hij
      rw [hieq, hjeq] at hpair
      exact Or.inl (hpair hlane).1
    · have hji : j < i := by omega
      have hpair := hp.rel_getElem_of_lt hjb hib hji
      rw [hjeq, hieq] at hpair
      exact Or.inr (hpair hlane.symm).1
  intro hit
  apply hit.2.2
  refine ⟨?_, trivial⟩
  rcases hseparated with hright | hleft
  · refine Or.inl ?_
    dsimp only
    omega
  · refine Or.inr (Or.inl ?_)
    dsimp only
    omega

theorem family_frame_stubs_clear {g : Family} {profile : Profile}
    {result : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok result)
    {i j : Nat} {frame other : Lanes.Eventmodeling.Frame} {box obstacle : Rect}
    (hi : g.frames[i]? = some frame) (hj : g.frames[j]? = some other)
    (hbox : (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames[i]? = some box)
    (hobstacle : (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames[j]? = some obstacle)
    (hne : i ≠ j) (x : Int) (hxleft : box.x ≤ x) (hxright : x ≤ box.x + box.w) :
    let plan := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
    (¬ Polyline.hitsRect
      [⟨x, box.y⟩, ⟨x, plan.corridors.getD (Lanes.Eventmodeling.rank g frame.lane) 0⟩]
      obstacle) ∧
    (¬ Polyline.hitsRect
      [⟨x, box.y + box.h⟩,
        ⟨x, plan.corridors.getD (Lanes.Eventmodeling.rank g frame.lane + 1) 0⟩]
      obstacle) := by
  let plan := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
    (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
  let before := plan.corridors.getD (Lanes.Eventmodeling.rank g frame.lane) 0
  let after := plan.corridors.getD (Lanes.Eventmodeling.rank g frame.lane + 1) 0
  change (¬ Polyline.hitsRect [⟨x, box.y⟩, ⟨x, before⟩] obstacle) ∧
    (¬ Polyline.hitsRect [⟨x, box.y + box.h⟩, ⟨x, after⟩] obstacle)
  by_cases hlane : frame.lane = other.lane
  · exact ⟨family_same_lane_stub_clear hr hi hj hbox hobstacle hne hlane
      x box.y before hxleft hxright,
      family_same_lane_stub_clear hr hi hj hbox hobstacle hne hlane
        x (box.y + box.h) after hxleft hxright⟩
  · have hnear := Lanes.Eventmodeling.successful_native_foreign_frame_nearside
      hr hi hj hbox hobstacle (Ne.symm hlane)
    change before ≤ box.y ∧ box.y + box.h ≤ after ∧
      (obstacle.y + obstacle.h ≤ before ∨ after ≤ obstacle.y) at hnear
    have hheight := (Lanes.Eventmodeling.raw_frame_strict_dimensions g profile box
      (List.mem_of_getElem? hbox)).2
    have clear_interval : ∀ y₁ y₂ : Int,
        before ≤ y₁ → y₁ ≤ after → before ≤ y₂ → y₂ ≤ after →
        ¬ Polyline.hitsRect [⟨x, y₁⟩, ⟨x, y₂⟩] obstacle := by
      intro y₁ y₂ h₁ h₂ h₃ h₄ hit
      apply hit.2.2
      refine ⟨?_, trivial⟩
      rcases hnear.2.2 with hbefore | hafter
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        dsimp only
        omega
      · refine Or.inr (Or.inr (Or.inl ?_))
        dsimp only
        omega
    constructor
    · apply clear_interval <;> omega
    · apply clear_interval <;> omega

theorem family_raw_route_clear {g : Family} {profile : Profile}
    {result : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok result)
    {relation : Lanes.Eventmodeling.Relation} (hrelation : relation ∈ g.relations)
    {points : List Point}
    (hroute : Lanes.Eventmodeling.route g profile
      (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
        (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile)))
      relation = .ok points)
    {j : Nat} {foreign : Lanes.Eventmodeling.Frame} {obstacle : Rect}
    (hforeign : g.frames[j]? = some foreign)
    (hobstacle : (Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))).frames[j]? = some obstacle)
    (hsrcne : j ≠ relation.src) (hdstne : j ≠ relation.dst) :
    ¬ Polyline.hitsRect points obstacle := by
  let plan := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
    (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
  have hall : (g.relations.all fun r =>
      decide (r.src < g.frames.length ∧ r.dst < g.frames.length)) = true := by
    cases ha : g.relations.all (fun r =>
        decide (r.src < g.frames.length ∧ r.dst < g.frames.length)) with
    | true => rfl
    | false =>
      simp only [Lanes.Eventmodeling.layout, ha, Bool.not_false, Bool.or_true,
        ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr <;>
        cases hr
  have hbounds : relation.src < g.frames.length ∧ relation.dst < g.frames.length :=
    of_decide_eq_true (List.all_eq_true.mp hall relation hrelation)
  let source := g.frames[relation.src]
  let target := g.frames[relation.dst]
  have hs : g.frames[relation.src]? = some source :=
    List.getElem?_eq_getElem hbounds.1
  have ht : g.frames[relation.dst]? = some target :=
    List.getElem?_eq_getElem hbounds.2
  obtain ⟨_, src, _, hsrc, _, _, _⟩ :=
    Lanes.Eventmodeling.raw_indexed_frame_origin g profile hs
  obtain ⟨_, dst, _, hdst, _, _, _⟩ :=
    Lanes.Eventmodeling.raw_indexed_frame_origin g profile ht
  change plan.frames[relation.src]? = some src at hsrc
  change plan.frames[relation.dst]? = some dst at hdst
  have hsrcD : plan.frames.getD relation.src Lanes.zeroRect = src := by
    simp only [List.getD_eq_getElem?_getD, hsrc, Option.getD_some]
  have hdstD : plan.frames.getD relation.dst Lanes.zeroRect = dst := by
    simp only [List.getD_eq_getElem?_getD, hdst, Option.getD_some]
  let a := Lanes.Eventmodeling.rank g source.lane
  let b := Lanes.Eventmodeling.rank g target.lane
  let start : Point := ⟨src.x + Int.fdiv (2 * src.w) 3,
    if a < b then src.y + src.h else src.y⟩
  let finish : Point := ⟨dst.x + Int.fdiv dst.w 3,
    if b < a then dst.y + dst.h else dst.y⟩
  let ca := plan.corridors.getD (if a < b then a + 1 else a) 0
  let cb := plan.corridors.getD (if b < a then b + 1 else b) 0
  have hmember : (obstacle, j) ∈ plan.frames.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hobstacle
  have hclear_check : ∀ path,
      Lanes.Eventmodeling.hits plan relation path = .ok false →
      ¬ Polyline.hitsRect path obstacle := by
    intro path hcheck
    exact family_hits_clear plan relation path hcheck (obstacle, j) hmember hsrcne hdstne
  have hbranch := family_route_branch_provenance g profile plan relation points hroute
  dsimp only at hbranch
  simp only [hsrcD, hdstD, hs, ht, Option.map_some, Option.getD_some] at hbranch
  change (points = [start, finish] ∧
      Lanes.Eventmodeling.hits plan relation [start, finish] = .ok false) ∨
    (∃ column : Int,
      points = Lanes.Eventmodeling.tidy
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish] ∧
      ((column = start.x ∧ Lanes.Eventmodeling.hits plan relation
          [⟨start.x, ca⟩, ⟨start.x, cb⟩] = .ok false) ∨
        (column = finish.x ∧ Lanes.Eventmodeling.hits plan relation
          [⟨finish.x, ca⟩, ⟨finish.x, cb⟩] = .ok false) ∨ column = plan.maxR)) at hbranch
  rcases hbranch with ⟨hpoints, hcheck⟩ | ⟨column, hpoints, hcolumn⟩
  · rw [hpoints]
    exact hclear_check _ hcheck
  · have hobsMem : obstacle ∈ plan.frames := List.mem_of_getElem? hobstacle
    have hdims := Lanes.Eventmodeling.raw_frame_strict_dimensions g profile obstacle hobsMem
    have miss_of_clear : ∀ path, (¬ Polyline.hitsRect path obstacle) →
        Polyline.allSegsMiss path obstacle := by
      intro path hclear
      apply Classical.byContradiction
      intro hn
      exact hclear ⟨by omega, hdims.2, hn⟩
    have hsrcports := Lanes.Eventmodeling.raw_frame_ports_strict g profile src
      (List.mem_of_getElem? hsrc)
    have hdstports := Lanes.Eventmodeling.raw_frame_ports_strict g profile dst
      (List.mem_of_getElem? hdst)
    have hsrcstubs := family_frame_stubs_clear hr hs hforeign hsrc hobstacle
      (Ne.symm hsrcne) start.x (Int.le_of_lt hsrcports.2.2.1)
      (Int.le_of_lt hsrcports.2.2.2)
    have hdststubs := family_frame_stubs_clear hr ht hforeign hdst hobstacle
      (Ne.symm hdstne) finish.x (Int.le_of_lt hdstports.1)
      (Int.le_of_lt hdstports.2.1)
    have hstart : ¬ Polyline.hitsRect [start, ⟨start.x, ca⟩] obstacle := by
      by_cases hab : a < b
      · simpa only [start, ca, hab, ↓reduceIte] using hsrcstubs.2
      · simpa only [start, ca, hab, ↓reduceIte] using hsrcstubs.1
    have hfinish : ¬ Polyline.hitsRect [finish, ⟨finish.x, cb⟩] obstacle := by
      by_cases hba : b < a
      · simpa only [finish, cb, hba, ↓reduceIte] using hdststubs.2
      · simpa only [finish, cb, hba, ↓reduceIte] using hdststubs.1
    have haBound : a < g.lanes.length :=
      Lanes.Eventmodeling.successful_native_frame_rank_bounds hr (List.mem_of_getElem? hs)
    have hbBound : b < g.lanes.length :=
      Lanes.Eventmodeling.successful_native_frame_rank_bounds hr (List.mem_of_getElem? ht)
    have hcaBound : (if a < b then a + 1 else a) ≤ g.lanes.length := by split <;> omega
    have hcbBound : (if b < a then b + 1 else b) ≤ g.lanes.length := by split <;> omega
    have hhorizontalA := family_corridor_horizontal_misses hr hobsMem hcaBound start.x column
    have hhorizontalB := family_corridor_horizontal_misses hr hobsMem hcbBound column finish.x
    have hvertical : ¬ Polyline.hitsRect [⟨column, ca⟩, ⟨column, cb⟩] obstacle := by
      rcases hcolumn with ⟨heq, hcheck⟩ | ⟨heq, hcheck⟩ | heq
      · subst column
        exact hclear_check _ hcheck
      · subst column
        exact hclear_check _ hcheck
      · subst column
        exact family_maxR_leg_clear g profile ca cb obstacle hobsMem
    have hraw : ¬ Polyline.hitsRect
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish] obstacle := by
      intro hit
      apply hit.2.2
      exact ⟨(miss_of_clear _ hstart).1, hhorizontalA,
        (miss_of_clear _ hvertical).1, hhorizontalB,
        (Layered.segMisses_comm finish ⟨finish.x, cb⟩ obstacle).mpr
          (miss_of_clear _ hfinish).1, trivial⟩
    rw [hpoints]
    exact Lanes.Eventmodeling.tidy_not_hitsRect
      (corridor_orthogonal start finish ca cb column) hraw

theorem family_result_route_clear {g : Family} {profile : Profile}
    {result : Lanes.Eventmodeling.Result}
    (hr : Lanes.Eventmodeling.layout g profile = .ok result)
    {i j : Nat} {relation : Lanes.Eventmodeling.Relation}
    {points : List Point} {box : Rect}
    (hrelation : g.relations[i]? = some relation)
    (hpoints : result.routes[i]? = some points)
    (hbox : result.frames[j]? = some box)
    (hsrcne : j ≠ relation.src) (hdstne : j ≠ relation.dst) :
    ¬ Polyline.hitsRect points box := by
  let raw := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
    (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
  have hj : j < g.frames.length := by
    have hbound := (List.getElem?_eq_some_iff.mp hbox).1
    have hlength := family_frames_length hr
    omega
  let foreign := g.frames[j]
  have hforeign : g.frames[j]? = some foreign := List.getElem?_eq_getElem hj
  obtain ⟨_, rawBox, _, hrawBox, _, _, _⟩ :=
    Lanes.Eventmodeling.raw_indexed_frame_origin g profile hforeign
  obtain ⟨paths, dx, dy, hpaths, hframes, hroutes⟩ := family_route_translation hr
  have hboxShift : Lanes.shiftRect dx dy rawBox = box := by
    rw [hframes, List.getElem?_map] at hbox
    simpa only [hrawBox, Option.map_some, Option.some.injEq] using hbox
  rw [hroutes, List.getElem?_map] at hpoints
  cases hi : paths[i]? with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hpoints
  | some path =>
    have hpathShift : path.map (Lanes.shiftPoint dx dy) = points := by
      simpa only [hi, Option.map_some, Option.some.injEq] using hpoints
    obtain ⟨_, hcorr⟩ :=
      family_routes_correspond g profile raw g.relations paths hpaths
    have hzip : (g.relations.zip paths)[i]? = some (relation, path) :=
      List.getElem?_zip_eq_some.mpr ⟨hrelation, hi⟩
    have hroute := hcorr (relation, path) (List.mem_of_getElem? hzip)
    have hclear := family_raw_route_clear hr (List.mem_of_getElem? hrelation)
      hroute hforeign hrawBox hsrcne hdstne
    rw [← hpathShift, ← hboxShift]
    exact family_clear_shift dx dy path rawBox hclear

theorem scene_c6 {m : Model} {s : Scene}
    (hwf : WellFormed m) (hs : scene m = .ok s) :
    Validator.C6 s.layoutDump := by
  intro route hroute box hbox hexclusive hscope
  obtain ⟨g, result, i, relation, j, _hg, hr, hrelation, hpoints, hrect, hsrcne, hdstne⟩ :=
    scene_foreign_route_frame_indices hwf hs hroute hbox hexclusive hscope
  exact family_result_route_clear hr hrelation hpoints hrect hsrcne hdstne

theorem eventmodeling_c6 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C6 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c6 hwf hs

theorem family_route_orthogonal_of_no_shortcut
    (g : Family) (profile : Profile) (plan : Lanes.Eventmodeling.Plan)
    (relation : Lanes.Eventmodeling.Relation) (points : List Point)
    (hno : (profile == Profile.vector &&
      (Lanes.Eventmodeling.rank g (((g.frames[relation.src]?).map (·.lane)).getD 0) !=
        Lanes.Eventmodeling.rank g
          (((g.frames[relation.dst]?).map (·.lane)).getD 0))) = false)
    (h : Lanes.Eventmodeling.route g profile plan relation = .ok points) :
    Polyline.isOrthogonal points = true := by
  let src := plan.frames.getD relation.src Lanes.zeroRect
  let dst := plan.frames.getD relation.dst Lanes.zeroRect
  let a := Lanes.Eventmodeling.rank g
    (((g.frames[relation.src]?).map (·.lane)).getD 0)
  let b := Lanes.Eventmodeling.rank g
    (((g.frames[relation.dst]?).map (·.lane)).getD 0)
  let start : Point :=
    ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩
  let finish : Point :=
    ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩
  let ca := plan.corridors.getD (if a < b then a + 1 else a) 0
  let cb := plan.corridors.getD (if b < a then b + 1 else b) 0
  have hno' : (profile == Profile.vector && a != b) = false := hno
  change (do
    if profile == Profile.vector && a != b then
      if !(← Lanes.Eventmodeling.hits plan relation [start, finish]) then
        return [start, finish]
    let mut column := plan.maxR
    if !(← Lanes.Eventmodeling.hits plan relation
        [⟨start.x, ca⟩, ⟨start.x, cb⟩]) then
      column := start.x
    else if !(← Lanes.Eventmodeling.hits plan relation
        [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]) then
      column := finish.x
    return Lanes.Eventmodeling.tidy
      [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
        ⟨finish.x, cb⟩, finish]) = .ok points at h
  simp only [hno', Bool.false_eq_true, ↓reduceIte] at h
  cases hs : Lanes.Eventmodeling.hits plan relation [⟨start.x, ca⟩, ⟨start.x, cb⟩] <;>
    cases ht : Lanes.Eventmodeling.hits plan relation [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]
  all_goals
    simp_all only [Bind.bind, Except.bind] <;>
      (try split at h) <;> (try split at h) <;>
      (try split at h) <;> (try split at h) <;>
      (try dsimp only [pure, Except.pure] at h) <;>
      first
        | contradiction
        | (cases h
           exact Lanes.Eventmodeling.tidy_orthogonal
             (corridor_orthogonal start finish ca cb _))

theorem memIdUnique {boxes : List ModelBox}
    (h : (boxes.map (·.id)).Nodup)
    {x y : ModelBox} (hx : x ∈ boxes) (hy : y ∈ boxes) (hid : x.id = y.id) : x = y := by
  induction boxes with
  | nil => cases hx
  | cons a rest ih =>
    have hn := List.nodup_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · have hy_mem : y.id ∈ rest.map (·.id) := List.mem_map_of_mem hy'
        rw [← hid] at hy_mem
        exact absurd hy_mem hn.1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hx_mem : x.id ∈ rest.map (·.id) := List.mem_map_of_mem hx'
        rw [hid] at hx_mem
        exact absurd hx_mem hn.1
      · exact ih hn.2 hx' hy'

theorem modelBox_find_of_mem {boxes : List ModelBox}
    (hunique : (boxes.map (·.id)).Nodup) {b : ModelBox} (hb : b ∈ boxes) :
    boxes.find? (fun x => x.id == b.id) = some b := by
  induction boxes with
  | nil => simp at hb
  | cons first rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hunique
    rcases List.mem_cons.mp hb with he | hm
    · subst he
      simp
    · have hne : first.id ≠ b.id := by
        intro he
        exact hnot (List.mem_map.mpr ⟨b, hm, he.symm⟩)
      simp only [List.find?_cons, show (first.id == b.id) = false from by simpa using hne]
      exact ih hrest hm

theorem frame_lane_eq_of_route_parent {m : Model} {g : Family}
    (hwf : WellFormed m) (hg : decode m = .ok g)
    (hsame : ∀ q ∈ m.routes, q.orthogonal = true → m.profile = .vector →
      ∀ srcBox dstBox : ModelBox,
        m.boxes.find? (fun b => b.id == q.fromId) = some srcBox →
        m.boxes.find? (fun b => b.id == q.toId) = some dstBox →
        srcBox.parent = dstBox.parent)
    {route : ModelRoute} (hrmem : route ∈ m.routes) (horth : route.orthogonal = true)
    {src dst : Nat} {f f' : Lanes.Eventmodeling.Frame}
    (hsrc : g.frames.findIdx? (·.id == route.fromId) = some src)
    (hdst : g.frames.findIdx? (·.id == route.toId) = some dst)
    (hf : g.frames[src]? = some f) (hf' : g.frames[dst]? = some f')
    (hprofile : m.profile = .vector) :
    f.lane = f'.lane := by
  have hunique := Model.boxIds_nodup hwf
  have hsrcbound := (List.findIdx?_eq_some_iff_getElem.mp hsrc).1
  have hdstbound := (List.findIdx?_eq_some_iff_getElem.mp hdst).1
  have hfeq : f = g.frames[src] :=
    Option.some.inj (hf.symm.trans (List.getElem?_eq_getElem hsrcbound))
  have hf'eq : f' = g.frames[dst] :=
    Option.some.inj (hf'.symm.trans (List.getElem?_eq_getElem hdstbound))
  have hfid : f.id = route.fromId := by
    rw [hfeq]
    exact beq_iff_eq.mp (List.findIdx?_eq_some_iff_getElem.mp hsrc).2.1
  have hf'id : f'.id = route.toId := by
    rw [hf'eq]
    exact beq_iff_eq.mp (List.findIdx?_eq_some_iff_getElem.mp hdst).2.1
  have hfm : f ∈ g.frames := by rw [hfeq]; exact List.getElem_mem hsrcbound
  have hf'm : f' ∈ g.frames := by rw [hf'eq]; exact List.getElem_mem hdstbound
  obtain ⟨b0, hb0mem, hb0role, hb0id⟩ :=
    (decode_relation_identity hwf hg).2 f hfm
  obtain ⟨b1, hb1mem, hb1role, hb1id⟩ :=
    (decode_relation_identity hwf hg).2 f' hf'm
  have hid0 : b0.id = route.fromId := hb0id.symm.trans hfid
  have hid1 : b1.id = route.toId := hb1id.symm.trans hf'id
  have hb0find : m.boxes.find? (fun b => b.id == route.fromId) = some b0 := by
    rw [← hid0]
    exact modelBox_find_of_mem hunique hb0mem
  have hb1find : m.boxes.find? (fun b => b.id == route.toId) = some b1 := by
    rw [← hid1]
    exact modelBox_find_of_mem hunique hb1mem
  have hparent : b0.parent = b1.parent :=
    hsame route hrmem horth hprofile b0 b1 hb0find hb1find
  obtain ⟨ids, ht⟩ := decode_lane_trace hwf hg
  exact laneTrace_lane_eq_of_parent ht hfm hf'm hb0mem hb1mem hb0role hb1role
    hb0id hb1id hparent



theorem scene_c4 {m : Model} {s : Scene}
    (hwf : WellFormed m)
    (hsame : ∀ q ∈ m.routes, q.orthogonal = true → m.profile = .vector →
      ∀ srcBox dstBox : ModelBox,
        m.boxes.find? (fun b => b.id == q.fromId) = some srcBox →
        m.boxes.find? (fun b => b.id == q.toId) = some dstBox →
        srcBox.parent = dstBox.parent)
    (hs : scene m = .ok s) : Validator.C4 s.layoutDump := by
  intro out hout horth
  obtain ⟨g, r, i, route, hg, hr, hinput, hpoints, hfrom, hto, horthflag⟩ :=
    scene_route_origin hs hout
  have hidx := (List.getElem?_eq_some_iff.mp hinput).1
  have hrget : m.routes[i] = route :=
    Option.some.inj ((List.getElem?_eq_getElem hidx).symm.trans hinput)
  have hrmem : route ∈ m.routes := by rw [← hrget]; exact List.getElem_mem hidx
  have hrouteorth : route.orthogonal = true := by rw [← horthflag]; exact horth
  have hidentity := (decode_relation_identity hwf hg).1
  have hlen := hidentity.lengths
  have hirel : i < g.relations.length := by omega
  have hrelation : g.relations[i]? = some g.relations[i] := List.getElem?_eq_getElem hirel
  obtain ⟨hsrc, hdst⟩ := hidentity.lookup hinput hrelation
  have hsrcbound := (List.findIdx?_eq_some_iff_getElem.mp hsrc).1
  have hdstbound := (List.findIdx?_eq_some_iff_getElem.mp hdst).1
  let c := Lanes.EventConsts.load m.profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  obtain ⟨paths, dx, dy, hpaths, hframes, hroutes⟩ := family_route_translation hr
  rw [hroutes, List.getElem?_map] at hpoints
  cases hpath : paths[i]? with
  | none => simp only [hpath, Option.map_none, reduceCtorEq] at hpoints
  | some path =>
    have hptseq : path.map (Lanes.shiftPoint dx dy) = out.points := by
      simpa only [hpath, Option.map_some, Option.some.injEq] using hpoints
    have hroute := (family_routes_correspond g m.profile raw g.relations paths hpaths).2
      (g.relations[i], path) (List.mem_of_getElem?
        (List.getElem?_zip_eq_some.mpr ⟨hrelation, hpath⟩))
    have hf : g.frames[g.relations[i].src]? = some g.frames[g.relations[i].src] :=
      List.getElem?_eq_getElem hsrcbound
    have hf' : g.frames[g.relations[i].dst]? = some g.frames[g.relations[i].dst] :=
      List.getElem?_eq_getElem hdstbound
    have hno : (m.profile == Profile.vector &&
        (Lanes.Eventmodeling.rank g
            (((g.frames[g.relations[i].src]?).map (·.lane)).getD 0) !=
          Lanes.Eventmodeling.rank g
            (((g.frames[g.relations[i].dst]?).map (·.lane)).getD 0))) = false := by
      by_cases hvec : (m.profile == Profile.vector) = true
      · have hprofile : m.profile = .vector := by simpa using hvec
        have hlane := frame_lane_eq_of_route_parent hwf hg hsame hrmem hrouteorth
          hsrc hdst hf hf' hprofile
        rw [hf, hf']
        simp only [hvec, hlane, Option.map_some, Option.getD_some, bne_self_eq_false,
          Bool.and_false]
      · simp only [hvec, Bool.false_and]
    have horthraw := family_route_orthogonal_of_no_shortcut g m.profile raw
      g.relations[i] path hno hroute
    have hshift : Polyline.isOrthogonal (path.map (Lanes.shiftPoint dx dy)) = true :=
      (Layered.isOrthogonal_shift dx dy path).mpr horthraw
    rw [← hptseq]
    exact hshift



theorem eventmodeling_c4 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C4 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  refine scene_c4 hwf ?_ hs
  intro q hq horth hprofile
  exact layout_orthogonal_routes_same_lane m result h hprofile q hq horth


/-- Before witness for C4: two frames in different lanes joined by a route marked
orthogonal.  The vector-profile shortcut returns the straight segment between the two
ports, which is diagonal; the adapter's admission guard now rejects the model. -/
def diagonalRouteWitness : Model :=
  { kind := "eventmodeling"
    profile := .vector
    boxes :=
      [{ id := "g0", role := .group, exclusive := false, shape := "lane:0" },
       { id := "g1", role := .group, exclusive := false, shape := "lane:1" },
       { id := "n0", parent := "g0", shape := "event", text := some "AAAAAAAAAA" },
       { id := "n1", parent := "g1", shape := "event", text := some "BBBBBBBBBB" }]
    routes := [{ id := "e", fromId := "n0", toId := "n1", orthogonal := true }] }

theorem diagonalRouteWitness_wellFormed : WellFormed diagonalRouteWitness := by decide

theorem diagonalRouteWitness_withinLimits : WithinLimits diagonalRouteWitness := by decide

/-- After witness: the same model is rejected at admission with `.geometry .domain`. -/
theorem diagonalRouteWitness_rejected :
    layout diagonalRouteWitness = .error (.geometry .domain) := by
  have hguard : crossLaneOrthogonalRoute diagonalRouteWitness = true := by decide
  have hempty : hasEmptyGroupId diagonalRouteWitness = false := by decide
  unfold layout
  simp only [hempty, Bool.false_eq_true, ↓reduceIte, hguard]

/-- Control: the same two frames in one lane stay admitted, and C4 holds because the
tidy corridor polyline is orthogonal. -/
def sameLaneRouteWitness : Model :=
  { kind := "eventmodeling"
    profile := .vector
    boxes :=
      [{ id := "g0", role := .group, exclusive := false, shape := "lane:0" },
       { id := "n0", parent := "g0", shape := "event", text := some "AAAAAAAAAA" },
       { id := "n1", parent := "g0", shape := "event", text := some "BBBBBBBBBB" }]
    routes := [{ id := "e", fromId := "n0", toId := "n1", orthogonal := true }] }

theorem sameLaneRouteWitness_c4 :
    ∀ result : Layered.FamilyResult, layout sameLaneRouteWitness = .ok result →
      Validator.C4 result.scene.layoutDump :=
  fun result h => eventmodeling_c4 (by decide) h


end Elegant.Kinds.Eventmodeling
