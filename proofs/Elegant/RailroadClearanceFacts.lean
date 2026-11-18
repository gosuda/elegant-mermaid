import Elegant.RailroadAssemblyFacts

namespace Elegant.Railroad

def RoutesBefore (stage : RuleState) : Prop :=
  ∀ route ∈ stage.state.routes,
    ∃ left right baseline,
      route.points = [⟨left, baseline⟩, ⟨right, baseline⟩] ∧ baseline ≤ stage.y

theorem routesBefore_avoids_later_box {stage : RuleState}
    (h : RoutesBefore stage) (route : Route) (hr : route ∈ stage.state.routes)
    (box : Box) (hb : stage.y ≤ box.rect.y) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, hp, hy⟩ := h route hr
  rw [hp]
  exact horizontal_route_avoids left right baseline box.rect
    (Or.inr (Or.inr (Or.inl (by omega))))

theorem placeRule_routes_before (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : RoutesBefore before)
    (h : placeRule m metric before rule = .ok after) :
    RoutesBefore after := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs, bind, Except.bind] at h
  | ok s =>
    have hg := measure_geometry _ _ _ _ _ hs
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs, ht, bind, Except.bind] at h
    | ok title =>
      have hn := Measure.textWidth_nonneg ht
      let g := ruleGeometry m.profile s title
      have hc := rule_contains_definition m.profile s title before.y hn
      have hvsep : 0 ≤ constant m.profile "vsep" :=
        (spacing_nonnegative m.profile).2.2.2.2.2
      have hheight := hg.nonnegative
      unfold Nonnegative at hheight
      have hdef : before.y + g.defY + s.height ≤ before.y + g.height := by
        change before.y + (ruleGeometry m.profile s title).defY + s.height ≤
          before.y + (ruleGeometry m.profile s title).height
        unfold Rect.Contained ruleFrame shapeRect at hc
        dsimp only at hc
        omega
      have hlow : 0 ≤ g.defY := by
        change 0 ≤ max (constant m.profile "rule_min_baseline") s.up - s.up
        have hm := Int.le_max_right (constant m.profile "rule_min_baseline") s.up
        omega
      have hsheight : 0 ≤ s.height := by
        unfold Shape.height
        omega
      have hy : before.y ≤ before.y + g.height + constant m.profile "vsep" := by
        omega
      simp only [hs, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          have horigin := placeNode_route_origin (m.boxes.length+1) m.profile s
            (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
            (addRule m.profile rule s g before.y before.state) state hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          intro route hr
          rcases horigin route hr with hold | hnew
          · have hold' : route ∈ before.state.routes := by
              unfold addRule at hold
              split at hold <;> exact hold
            obtain ⟨left, right, baseline, he, hb⟩ := hi route hold'
            refine ⟨left, right, baseline, he, ?_⟩
            change baseline ≤ before.y + (ruleGeometry m.profile s title).height +
              constant m.profile "vsep"
            change before.y ≤ before.y + (ruleGeometry m.profile s title).height +
              constant m.profile "vsep" at hy
            exact Int.le_trans hb hy
          · obtain ⟨left, right, baseline, he, _, hb⟩ :=
              hnew.horizontal_bounds hg
            refine ⟨left, right, baseline, he, ?_⟩
            change baseline ≤ before.y + (ruleGeometry m.profile s title).height +
              constant m.profile "vsep"
            change baseline ≤ before.y + g.defY + s.height at hb
            change before.y + g.defY + s.height ≤
              before.y + (ruleGeometry m.profile s title).height at hdef
            omega

theorem ruleFold_routes_before (m : Model) (metric : Measure.Metric)
    (rules : List Rule) (result : RuleState)
    (h : rules.foldlM (placeRule m metric)
      {y := constant m.profile "margin"} = .ok result) :
    RoutesBefore result := by
  exact foldlM_preserves (placeRule m metric) RoutesBefore
    (fun rule before after hi he =>
      placeRule_routes_before m metric before after rule hi he)
    rules _ result (by intro route hr; cases hr) h

theorem earlier_route_avoids_definition (m : Model) (s : Shape)
    (title : Int) (before : RuleState) (parent : String)
    (hg : Geometry s) (hi : RoutesBefore before)
    (route : Route) (hr : route ∈ before.state.routes)
    (box : Box)
    (hb : PlacedBox s
      (constant m.profile "margin"+(ruleGeometry m.profile s title).defX)
      (before.y+(ruleGeometry m.profile s title).defY) parent box) :
    ¬ Polyline.hitsRect route.points box.rect := by
  apply routesBefore_avoids_later_box hi route hr box
  have hc := descendant_contained hb.descendant hg
  have hdef : 0 ≤ (ruleGeometry m.profile s title).defY := by
    dsimp [ruleGeometry]
    omega
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  omega

theorem placeRule_old_routes_avoid_new_exclusive
    (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : RoutesBefore before)
    (h : placeRule m metric before rule = .ok after)
    (route : Route) (hr : route ∈ before.state.routes)
    (box : Box) (hb : box ∈ after.state.boxes)
    (hex : box.exclusive = true) (hnew : box ∉ before.state.boxes) :
    ¬ Polyline.hitsRect route.points box.rect := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs, bind, Except.bind] at h
  | ok s =>
    have hg := measure_geometry _ _ _ _ _ hs
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs, ht, bind, Except.bind] at h
    | ok title =>
      let g := ruleGeometry m.profile s title
      simp only [hs, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          have ho := placeNode_box_origin (m.boxes.length+1) m.profile s
            (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
            (addRule m.profile rule s g before.y before.state) state hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          change box ∈ state.boxes at hb
          rcases ho box hb with hold | hplaced
          · exact False.elim (hnew
              (addRule_exclusive_box_origin m.profile rule s g before.y
                before.state box hold hex))
          · exact earlier_route_avoids_definition m s title before rule.id hg hi
              route hr box hplaced

theorem placeRule_new_routes_avoid_old_boxes
    (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : StageBounds m.profile before)
    (h : placeRule m metric before rule = .ok after)
    (route : Route) (hr : route ∈ after.state.routes)
    (hnew : route ∉ before.state.routes)
    (box : Box) (hb : box ∈ before.state.boxes) :
    ¬ Polyline.hitsRect route.points box.rect := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs, bind, Except.bind] at h
  | ok s =>
    have hg := measure_geometry _ _ _ _ _ hs
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs, ht, bind, Except.bind] at h
    | ok title =>
      let g := ruleGeometry m.profile s title
      have hy : before.y ≤ before.y + g.defY := by
        have hm := Int.le_max_right (constant m.profile "rule_min_baseline") s.up
        change before.y ≤ before.y +
          (max (constant m.profile "rule_min_baseline") s.up - s.up)
        omega
      simp only [hs, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          have ho := placeNode_route_origin (m.boxes.length+1) m.profile s
            (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
            (addRule m.profile rule s g before.y before.state) state hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          change route ∈ state.routes at hr
          rcases ho route hr with hold | hplaced
          · have hold' : route ∈ before.state.routes := by
              unfold addRule at hold
              split at hold <;> exact hold
            exact False.elim (hnew hold')
          · exact placed_route_avoids_previous_stage m.profile before hi s
              (constant m.profile "margin"+g.defX) (before.y+g.defY) route
              hg hplaced hy box hb

theorem sequenceLayout_child_horizontal_gap (p : Profile) (kids : List Shape)
    (up x : Int) (i : Nat) (a b : Shape × Point)
    (ha : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[i]? =
      some a)
    (hb : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[i+1]? =
      some b) :
    b.2.x - (a.2.x + a.1.w) = constant p "hsep" ∧
      a.2.x + a.1.w ≤ b.2.x := by
  have hj := ConsecutiveJoins.at up (constant p "hsep") _
    (sequence_all_rail_joins up (constant p "hsep") kids x) i a b ha hb
  have hgap := hj.2.2
  have hnonneg := (spacing_nonnegative p).2.2.2.2.1
  exact ⟨hgap, by omega⟩

theorem measure_sequence_horizontal_gap (fuel : Nat) (p : Profile)
    (metric : Measure.Metric) (node : Node) (shape : Shape)
    (hm : measure (fuel+1) p metric node = .ok shape)
    (hk : shape.kind = "sequence") :
    ∃ kids, node.children.mapM (measure fuel p metric) = .ok kids ∧
      shape = sequenceShape p node kids ∧
      ∀ (i : Nat) (a b : Shape × Point),
        (shape.children.zip shape.offsets)[i]? = some a →
        (shape.children.zip shape.offsets)[i+1]? = some b →
        b.2.x - (a.2.x + a.1.w) = constant p "hsep" ∧
          a.2.x + a.1.w ≤ b.2.x := by
  obtain ⟨kids, hc, he, _⟩ := measure_sequence_shape fuel p metric node shape hm hk
  refine ⟨kids, hc, he, ?_⟩
  subst shape
  intro i a b ha hb
  simp only [sequenceShape] at ha hb
  exact sequenceLayout_child_horizontal_gap p kids
    (kids.foldl (fun n (kid : Shape) => max n kid.up) 0) 0 i a b ha hb

theorem Geometry.indexed_child_inside {s : Shape} (hg : Geometry s)
    (i : Nat) (hi : i < s.children.length) :
    0 ≤ s.offsets[i]!.x ∧
      s.offsets[i]!.x + s.children[i]!.w ≤ s.w ∧
      0 ≤ s.children[i]!.w := by
  have hlen : s.offsets.length = s.children.length := by
    cases hg with
    | node _ _ _ h _ _ => exact h
  have ho : i < s.offsets.length := by omega
  have hc : s.children[i]? = some s.children[i]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hp : s.offsets[i]? = some s.offsets[i]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ho]
  have hz : (s.children.zip s.offsets)[i]? =
      some (s.children[i]!, s.offsets[i]!) :=
    List.getElem?_zip_eq_some.mpr ⟨hc, hp⟩
  have hb := hg.inside _ (List.mem_of_getElem? hz)
  exact ⟨hb.1, hb.2.2.1,
    (hg.child _ (List.mem_of_getElem? hz)).nonnegative.1⟩

theorem PlacedRoute.x_bounds {s : Shape} {x y : Int} {route : Route}
    (hr : PlacedRoute s x y route) (hg : Geometry s) :
    ∀ point ∈ route.points, x ≤ point.x ∧ point.x ≤ x+s.w := by
  induction hr with
  | @sequence s x y route _ hr =>
    obtain ⟨i, hi, _, _, hp⟩ := hr
    have hi' : i < s.children.length - 1 := List.mem_range.mp hi
    have ha := hg.indexed_child_inside i (by omega)
    have hb := hg.indexed_child_inside (i+1) (by omega)
    intro point hpoint
    rw [hp] at hpoint
    rcases List.mem_cons.mp hpoint with rfl | hpoint
    · dsimp only
      omega
    · have he : point = ⟨x+s.offsets[i+1]!.x,y+s.up⟩ :=
        List.mem_singleton.mp hpoint
      subst point
      dsimp only
      omega
  | @child s x y route pair hp _ _ ih =>
    intro point hpoint
    have hb := ih (hg.child pair hp) point hpoint
    have hc := hg.inside pair hp
    omega

theorem placed_route_avoids_horizontal_subtree
    {source target : Shape} {sx sy tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hs : Geometry source) (ht : Geometry target)
    (hr : PlacedRoute source sx sy route)
    (hb : PlacedBox target tx ty parent box)
    (hsep : sx + source.w ≤ tx ∨ tx + target.w ≤ sx) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, he, _, _⟩ := hr.horizontal_bounds hs
  have hl := hr.x_bounds hs ⟨left, baseline⟩ (by simp [he])
  have hh := hr.x_bounds hs ⟨right, baseline⟩ (by simp [he])
  have hc := descendant_contained hb.descendant ht
  unfold Rect.Contained shapeRect at hc
  dsimp only at hl hh hc
  rw [he]
  apply horizontal_route_avoids
  rcases hsep with hsep | hsep
  · exact Or.inl (Int.max_le.mpr ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inl (Int.le_min.mpr ⟨by omega, by omega⟩))

theorem placed_route_avoids_horizontal_siblings
    {s : Shape} (hg : Geometry s) (x y : Int)
    (source target : Shape × Point)
    (hs : source ∈ s.children.zip s.offsets)
    (ht : target ∈ s.children.zip s.offsets)
    (parent : String) (route : Route) (box : Box)
    (hr : PlacedRoute source.1 (x+source.2.x) (y+source.2.y) route)
    (hb : PlacedBox target.1 (x+target.2.x) (y+target.2.y) parent box)
    (hsep : source.2.x + source.1.w ≤ target.2.x ∨
      target.2.x + target.1.w ≤ source.2.x) :
    ¬ Polyline.hitsRect route.points box.rect := by
  apply placed_route_avoids_horizontal_subtree (hg.child source hs)
    (hg.child target ht) hr hb
  rcases hsep with hsep | hsep
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem sequenceLayout_indexed_horizontal_order (p : Profile)
    (kids : List Shape) (hk : ∀ kid ∈ kids, Nonnegative kid)
    (up x : Int) (i j : Nat) (a b : Shape × Point)
    (ha : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[i]? =
      some a)
    (hb : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[j]? =
      some b)
    (hij : i < j) :
    a.2.x + a.1.w ≤ b.2.x := by
  have hp := sequence_children_disjoint up (constant p "hsep")
    (spacing_nonnegative p).2.2.2.2.1 kids x
    (fun kid hmem => (hk kid hmem).1)
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.mp hb
  have ho := List.pairwise_iff_getElem.mp hp i j hi hj hij
  simpa [hai, hbj] using ho

theorem sequenceLayout_indexed_corridor (p : Profile)
    (kids : List Shape) (hk : ∀ kid ∈ kids, Nonnegative kid)
    (up x : Int) (i j : Nat) (a b target : Shape × Point)
    (ha : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[i]? =
      some a)
    (hb : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[i+1]? =
      some b)
    (ht : (kids.zip (sequenceLayout up (constant p "hsep") x kids).2)[j]? =
      some target) :
    target.2.x + target.1.w ≤ min (a.2.x+a.1.w) b.2.x ∨
      max (a.2.x+a.1.w) b.2.x ≤ target.2.x := by
  have hab := (sequenceLayout_child_horizontal_gap p kids up x i a b ha hb).2
  have haw := (hk a.1 (List.of_mem_zip (List.mem_of_getElem? ha)).1).1
  have hbw := (hk b.1 (List.of_mem_zip (List.mem_of_getElem? hb)).1).1
  by_cases hji : j ≤ i
  · apply Or.inl
    have hleft : target.2.x + target.1.w ≤ a.2.x+a.1.w := by
      by_cases he : j = i
      · subst j
        have ht' : target = a := Option.some.inj (ht.symm.trans ha)
        subst target
        omega
      · have ho := sequenceLayout_indexed_horizontal_order p kids hk up x
          j i target a ht ha (by omega)
        omega
    exact Int.le_min.mpr ⟨hleft, by omega⟩
  · apply Or.inr
    have hright : b.2.x ≤ target.2.x := by
      by_cases he : j = i+1
      · subst j
        have ht' : target = b := Option.some.inj (ht.symm.trans hb)
        subst target
        omega
      · have ho := sequenceLayout_indexed_horizontal_order p kids hk up x
          (i+1) j b target hb ht (by omega)
        omega
    exact Int.max_le.mpr ⟨by omega, hright⟩

def ClosedSiblingGap (a b : Shape × Point) : Prop :=
  a.2.x+a.1.w ≤ b.2.x ∨ b.2.x+b.1.w ≤ a.2.x ∨
    a.2.y+a.1.height ≤ b.2.y ∨ b.2.y+b.1.height ≤ a.2.y

theorem ClosedSiblingGap.symm {a b : Shape × Point}
    (h : ClosedSiblingGap a b) : ClosedSiblingGap b a := by
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem sizeRaw_children_closed_separated (p : Profile) (metric : Measure.Metric)
    (n : Node) (kids : List Shape) (s : Shape)
    (hk : ∀ k ∈ kids, Nonnegative k)
    (h : sizeRaw p metric n kids = .ok s) :
    (s.children.zip s.offsets).Pairwise ClosedSiblingGap := by
  unfold sizeRaw at h
  split at h
  · split at h
    · cases h
    · cases hw : Measure.textWidth metric n.text.toList with
      | error e => simp [hw, bind, Except.bind] at h
      | ok width =>
        simp only [hw, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst s
        simp [leafShape]
  · split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h
        subst s
        have hp := sequence_children_disjoint
          (kids.foldl (fun a k => max a k.up) 0) (constant p "hsep")
          (spacing_nonnegative p).2.2.2.2.1 kids 0
          (fun k hmem => (hk k hmem).1)
        exact List.Pairwise.imp (fun {_ _} hab => Or.inl hab) hp
    · split at h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s
          have hp := choice_children_disjoint (constant p "arc_radius")
            (kids.foldl (fun a k => max a k.w) 0) (constant p "vsep")
            (spacing_nonnegative p).2.2.2.2.2 kids 0
            (fun k hmem => Int.add_nonneg (hk k hmem).2.1 (hk k hmem).2.2)
          exact List.Pairwise.imp (fun {_ _} hab => Or.inr (Or.inr (Or.inl hab))) hp
      · split at h
        · cases kids with
          | nil => cases h
          | cons kid tail =>
            cases tail with
            | nil =>
              simp only [Except.ok.injEq] at h
              subst s
              simp [wrapperShape]
            | cons second rest => cases h
        · cases h

theorem measure_children_closed_separated (fuel : Nat) (p : Profile)
    (metric : Measure.Metric) (n : Node) (s : Shape)
    (h : measure fuel p metric n = .ok s) :
    (s.children.zip s.offsets).Pairwise ClosedSiblingGap := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    simp only [measure] at h
    cases hk : n.children.mapM (measure fuel p metric) with
    | error e => simp [hk, bind, Except.bind] at h
    | ok kids =>
      have hn := mapM_nonnegative (measure fuel p metric)
        (fun n s he => railroad_box_nonneg fuel p metric n s he) n.children kids hk
      simp only [hk, bind, Except.bind] at h
      exact sizeRaw_children_closed_separated p metric n kids s hn
        (size_raw_of_ok p metric n kids s h)

theorem placed_route_avoids_disjoint_subtree
    {source target : Shape} {sx sy tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hs : Geometry source) (ht : Geometry target)
    (hr : PlacedRoute source sx sy route)
    (hb : PlacedBox target tx ty parent box)
    (hd : sx+source.w ≤ tx ∨ tx+target.w ≤ sx ∨
      sy+source.height ≤ ty ∨ ty+target.height ≤ sy) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, he, hlo, hhi⟩ := hr.horizontal_bounds hs
  have hl := hr.x_bounds hs ⟨left, baseline⟩ (by simp [he])
  have hh := hr.x_bounds hs ⟨right, baseline⟩ (by simp [he])
  have hc := descendant_contained hb.descendant ht
  unfold Rect.Contained shapeRect at hc
  dsimp only at hl hh hc
  rw [he]
  apply horizontal_route_avoids
  rcases hd with hd | hd | hd | hd
  · exact Or.inl (Int.max_le.mpr ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inl (Int.le_min.mpr ⟨by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem SequenceRoute.sequence_avoids_child (p : Profile) (node : Node)
    (kids : List Shape) (hk : ∀ kid ∈ kids, Nonnegative kid)
    (x y : Int) (route : Route)
    (hr : SequenceRoute (sequenceShape p node kids) x y route)
    (target : Shape × Point)
    (ht : target ∈ (sequenceShape p node kids).children.zip
      (sequenceShape p node kids).offsets)
    (hg : Geometry target.1) (parent : String) (box : Box)
    (hb : PlacedBox target.1 (x+target.2.x) (y+target.2.y) parent box) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨i, hi, _, _, hp⟩ := hr
  let up := kids.foldl (fun n kid => max n kid.up) 0
  let offsets := (sequenceLayout up (constant p "hsep") 0 kids).2
  have hi' : i < kids.length-1 := by simpa [sequenceShape] using hi
  have hlen : offsets.length = kids.length := sequence_offsets_length _ _ _ _
  have hc0 : kids[i]? = some kids[i]! := by
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < kids.length by omega)]
  have hc1 : kids[i+1]? = some kids[i+1]! := by
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i+1 < kids.length by omega)]
  have ho0 : offsets[i]? = some offsets[i]! := by
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i < offsets.length by omega)]
  have ho1 : offsets[i+1]? = some offsets[i+1]! := by
    simp [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i+1 < offsets.length by omega)]
  have ha : (kids.zip offsets)[i]? = some (kids[i]!, offsets[i]!) :=
    List.getElem?_zip_eq_some.mpr ⟨hc0, ho0⟩
  have hb' : (kids.zip offsets)[i+1]? = some (kids[i+1]!, offsets[i+1]!) :=
    List.getElem?_zip_eq_some.mpr ⟨hc1, ho1⟩
  have ht' : target ∈ kids.zip offsets := by simpa [sequenceShape, offsets, up] using ht
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp ht'
  have corridor := sequenceLayout_indexed_corridor p kids hk up 0 i j
    (kids[i]!, offsets[i]!) (kids[i+1]!, offsets[i+1]!) target ha hb' hj
  rw [hp]
  apply descendants_avoid_separated_gap hg hb.descendant
  dsimp only [sequenceShape] at *
  change
    max (x+offsets[i]!.x+kids[i]!.w) (x+offsets[i+1]!.x) ≤ x+target.2.x ∨
      x+target.2.x+target.1.w ≤
        min (x+offsets[i]!.x+kids[i]!.w) (x+offsets[i+1]!.x) ∨
      y+up ≤ y+target.2.y ∨
      y+target.2.y+target.1.height ≤ y+up
  rcases corridor with hleft | hright
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

theorem placedRoute_exclusive_clear :
    ∀ (fuel : Nat) (p : Profile) (metric : Measure.Metric)
      (node : Node) (shape : Shape) (x y : Int) (parent : String)
      (route : Route) (box : Box),
      measure fuel p metric node = .ok shape →
      PlacedRoute shape x y route →
      PlacedBox shape x y parent box → box.exclusive = true →
      ¬ Polyline.hitsRect route.points box.rect := by
  intro fuel
  induction fuel with
  | zero => intro p metric node shape x y parent route box hm; cases hm
  | succ fuel ih =>
    intro p metric node shape x y parent route box hm hr hb hex
    have hg := measure_geometry _ _ _ _ _ hm
    cases hr with
    | sequence hkind hr =>
      obtain ⟨kids, hc, he, hn⟩ :=
        measure_sequence_shape fuel p metric node shape hm hkind
      have hkids := mapM_nonnegative (measure fuel p metric)
        (fun n s h => railroad_box_nonneg fuel p metric n s h)
        node.children kids hc
      cases hb with
      | root => simp [hkind, leaf] at hex
      | child target ht _ hb =>
        subst shape
        exact SequenceRoute.sequence_avoids_child p node kids hkids x y route
          hr target ht (hg.child target ht) _ box hb
    | child source hs hn hr =>
      cases hb with
      | root => simp [hn] at hex
      | child target ht _ hb =>
        by_cases he : source = target
        · subst target
          obtain ⟨child, hc, hmchild⟩ :=
            measure_child_origin fuel p metric node shape source.1 hm
              (List.of_mem_zip hs).1
          exact ih p metric child source.1 (x+source.2.x) (y+source.2.y)
            shape.id route box hmchild hr hb hex
        · have hsep := measure_children_closed_separated (fuel+1) p metric node shape hm
          have hgap := pairwise_symmetric_members ClosedSiblingGap
            (fun _ _ h => h.symm) _ hsep source hs target ht he
          apply placed_route_avoids_disjoint_subtree (hg.child source hs)
            (hg.child target ht) hr hb
          unfold ClosedSiblingGap at hgap
          rcases hgap with hgap | hgap | hgap | hgap
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inl (by omega))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
          · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem placeRule_new_routes_avoid_new_exclusive
    (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (h : placeRule m metric before rule = .ok after)
    (route : Route) (hr : route ∈ after.state.routes)
    (hrnew : route ∉ before.state.routes)
    (box : Box) (hb : box ∈ after.state.boxes)
    (hex : box.exclusive = true) (hbnew : box ∉ before.state.boxes) :
    ¬ Polyline.hitsRect route.points box.rect := by
  unfold placeRule at h
  cases hs : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hs, bind, Except.bind] at h
  | ok s =>
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hs, ht, bind, Except.bind] at h
    | ok title =>
      let g := ruleGeometry m.profile s title
      simp only [hs, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          have hro := placeNode_route_origin _ _ _ _ _ _ _ _ hp
          have hbo := placeNode_box_origin _ _ _ _ _ _ _ _ hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          change route ∈ state.routes at hr
          change box ∈ state.boxes at hb
          rcases hro route hr with hold | hroute
          · have hold' : route ∈ before.state.routes := by
              unfold addRule at hold
              split at hold <;> exact hold
            exact False.elim (hrnew hold')
          · rcases hbo box hb with hold | hbox
            · exact False.elim (hbnew
                (addRule_exclusive_box_origin m.profile rule s g before.y
                  before.state box hold hex))
            · exact placedRoute_exclusive_clear (m.boxes.length+1)
                m.profile metric rule.root s _ _ rule.id route box hs hroute hbox hex

def RoutesExclusiveClear (state : State) : Prop :=
  ∀ route ∈ state.routes, ∀ box ∈ state.boxes, box.exclusive = true →
    ¬ Polyline.hitsRect route.points box.rect

theorem placeRule_routes_exclusive_clear
    (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hstage : StageBounds m.profile before) (hbefore : RoutesBefore before)
    (hclear : RoutesExclusiveClear before.state)
    (h : placeRule m metric before rule = .ok after) :
    RoutesExclusiveClear after.state := by
  intro route hr box hb hex
  by_cases hrold : route ∈ before.state.routes
  · by_cases hbold : box ∈ before.state.boxes
    · exact hclear route hrold box hbold hex
    · exact placeRule_old_routes_avoid_new_exclusive m metric before after rule
        hbefore h route hrold box hb hex hbold
  · by_cases hbold : box ∈ before.state.boxes
    · exact placeRule_new_routes_avoid_old_boxes m metric before after rule
        hstage h route hr hrold box hbold
    · exact placeRule_new_routes_avoid_new_exclusive m metric before after rule h
        route hr hrold box hb hex hbold

theorem layout_routes_exclusive_clear (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) :
    Validator.C6 scene.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => StageBounds m.profile state ∧ RoutesBefore state ∧
          RoutesExclusiveClear state.state)
        (fun rule before after hi he =>
          ⟨placeRule_stage_bounds m metric before after rule hi.1 he,
            placeRule_routes_before m metric before after rule hi.2.1 he,
            placeRule_routes_exclusive_clear m metric before after rule
              hi.1 hi.2.1 hi.2.2 he⟩)
        rules {y := constant m.profile "margin"} result
        ⟨initial_stage_bounds m.profile, (by intro route hr; cases hr),
          (by intro route hr; cases hr)⟩ hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           intro route hr box hb hex _
           exact hinv.2.2 route hr box hb hex)

theorem railroad_routes_exclusive_clear (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C6 result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_routes_exclusive_clear m rules scene hs

end Elegant.Railroad
