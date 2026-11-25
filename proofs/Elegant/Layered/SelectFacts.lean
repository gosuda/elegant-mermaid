import Elegant.Layered.CoordGraph
import Elegant.Layered.Assembly

/-!
Recursive subdivision of the layered pipeline: how `selectInput` and `expandChild` act on
box and route identifiers, and how a property of the base layout lifts to every layout that
`layoutRecursive` performs.
-/

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

def RoutesCovered (inp : Input) : Prop :=
  ∀ r ∈ inp.routes, (∃ b ∈ inp.boxes, b.id = r.fromId) ∧ ∃ b ∈ inp.boxes, b.id = r.toId

theorem zipIdx_filter_map_fst {α β : Type} (keep : α → Bool) (f : α → β) :
    ∀ (l : List α) (k : Nat), ((l.zipIdx k).filter fun q => keep q.1).map (fun q => f q.1) =
      (l.filter keep).map f
  | [], _ => rfl
  | a :: l, k => by
    have ih := zipIdx_filter_map_fst keep f l (k + 1)
    rw [List.zipIdx_cons]
    cases hk : keep a <;> simp [hk, ih]

theorem selectInput_box_ids (inp : Input) (keep : ModelBox → Bool) (root : String) :
    (selectInput inp keep root).boxes.map (·.id) = (inp.boxes.filter keep).map (·.id) := by
  unfold selectInput
  dsimp only
  rw [List.map_map, ← zipIdx_filter_map_fst keep (·.id) inp.boxes 0]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_apply]
  split <;> rfl

theorem mem_zipIdx_filter_map_fst {α : Type} (keep : α → Bool) :
    ∀ (l : List α) (k : Nat) (x : α), x ∈ ((l.zipIdx k).filter fun q => keep q.1).map (·.1) ↔
      x ∈ l ∧ keep x = true
  | [], _, _ => by simp
  | a :: l, k, x => by
    have ih := mem_zipIdx_filter_map_fst keep l (k + 1) x
    rw [List.zipIdx_cons]
    cases hk : keep a
    · simp only [List.filter_cons, hk]
      simp only [Bool.false_eq_true, ↓reduceIte, ih, List.mem_cons]
      constructor
      · rintro ⟨hx, h⟩
        exact ⟨Or.inr hx, h⟩
      · rintro ⟨hx | hx, h⟩
        · subst hx
          simp [hk] at h
        · exact ⟨hx, h⟩
    · simp only [List.filter_cons, hk, ↓reduceIte, List.map_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hx, h⟩)
        · exact ⟨Or.inl rfl, hk⟩
        · exact ⟨Or.inr hx, h⟩
      · rintro ⟨hx | hx, h⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hx, h⟩

theorem selectInput_route_mem (inp : Input) (keep : ModelBox → Bool) (root : String)
    (r : ModelRoute) :
    r ∈ (selectInput inp keep root).routes ↔
      r ∈ inp.routes ∧ (selectInput inp keep root).boxes.any (fun box => box.id == r.fromId) = true ∧
        (selectInput inp keep root).boxes.any (fun box => box.id == r.toId) = true := by
  have key := mem_zipIdx_filter_map_fst
    (fun r : ModelRoute => ((selectInput inp keep root).boxes.any fun box => box.id == r.fromId) &&
      ((selectInput inp keep root).boxes.any fun box => box.id == r.toId)) inp.routes 0 r
  simp only [Bool.and_eq_true] at key
  exact key

theorem selectInput_routesCovered (inp : Input) (keep : ModelBox → Bool) (root : String) :
    RoutesCovered (selectInput inp keep root) := by
  intro r hr
  obtain ⟨_, h1, h2⟩ := (selectInput_route_mem inp keep root r).mp hr
  rw [List.any_eq_true] at h1 h2
  obtain ⟨b1, hb1, e1⟩ := h1
  obtain ⟨b2, hb2, e2⟩ := h2
  exact ⟨⟨b1, hb1, by simpa using e1⟩, ⟨b2, hb2, by simpa using e2⟩⟩

theorem independent_inside {boxes : List ModelBox} {routes : List ModelRoute} {box : ModelBox}
    (h : Compound.independent boxes routes box = true) :
    ∀ r ∈ routes, Compound.inside boxes box.id r.fromId = Compound.inside boxes box.id r.toId := by
  unfold Compound.independent Compound.crosses at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  intro r hr
  have h2 := List.any_eq_false.mp h.2 r hr
  simpa using h2

theorem layoutRecursive_succ_sources
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursive (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧ layout inp o = .ok res) ∨
    ∃ (group : ModelBox) (P : Params) (metric : Measure.Metric)
      (child : FamilyResult) (titleLines : List Measure.Line) (parent : FamilyResult),
      inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      checkedParams o.profile inp.kind = .ok P ∧
      metricOf o.profile o.fontFamily = .ok metric ∧
      layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child ∧
      StyledMeasure.wrap metric
        (Measure.wrapTarget metric.profile P.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
        (inp.texts.getD
          ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines ∧
      let titleWidth := titleLines.foldl (fun width line => max width line.width) 0
      let titleHeight := (max 1 titleLines.length : Int) * P.lineH
      let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
        ⟨child.scene.canvas.w - 2 * P.canvasMargin, child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      layoutRecursive fuel
        { parentInput with
          fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
          fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] } o = .ok parent ∧
      expandChild P inp o group titleHeight parent child = .ok res := by
  unfold layoutRecursive at h
  dsimp only at h
  split at h
  · next hn => exact Or.inl ⟨hn, h⟩
  · next group hg =>
    obtain ⟨P, hP, h⟩ := bind_ok' h
    obtain ⟨metric, hm, h⟩ := bind_ok' h
    obtain ⟨child, hc, h⟩ := bind_ok' h
    obtain ⟨titleLines, ht, h⟩ := bind_ok' h
    obtain ⟨parent, hp, h⟩ := bind_ok' h
    exact Or.inr ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, h⟩

theorem layoutRecursive_succ {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRecursive (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧ layout inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursive fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursive fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursive_succ_sources h with hflat |
    ⟨group, P, metric, child, titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

theorem filterMap_find_ids {α : Type} (key : α → String) (ids : List String) (items : List α)
    (cover : ∀ id ∈ ids, ∃ item ∈ items, key item = id) {β : Type} (src : List β) (idOf : β → String)
    (hs : src.map idOf = ids) :
    (src.filterMap fun m => items.find? (fun item => key item == idOf m)).map key = ids := by
  rw [← hs]
  have : (src.filterMap fun m => items.find? (fun item => key item == idOf m)) =
      (src.map idOf).filterMap fun id => items.find? (fun item => key item == id) := by
    rw [List.filterMap_map]
    rfl
  rw [this, hs]
  exact Assembly.ordered_merge_ids key ids items cover

theorem expandChild_ids {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res)
    (hbox : ∀ b ∈ inp.boxes, ∃ x ∈ child.scene.boxes ++ parent.scene.boxes, x.id = b.id)
    (hroute : ∀ r ∈ inp.routes, ∃ x ∈ child.scene.routes ++ parent.scene.routes, x.id = r.id) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold expandChild at h
  cases hf : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none => simp [hf, bind, Except.bind] at h
  | some frame =>
    simp only [hf] at h
    obtain ⟨_, _, h⟩ := bind_ok' h
    obtain ⟨_, _, h⟩ := bind_ok' h
    obtain ⟨_, _, h⟩ := bind_ok' h
    obtain ⟨_, _, h⟩ := bind_ok' h
    obtain ⟨_, _, h⟩ := bind_ok' h
    have h : (Except.ok _ : Except LayoutError FamilyResult) = Except.ok res := h
    have h := Except.ok.inj h
    subst h
    dsimp only
    refine ⟨?_, ?_⟩
    · refine filterMap_find_ids (fun b : Box => b.id) (inp.boxes.map (·.id)) _ ?_ inp.boxes
        (fun b : ModelBox => b.id) rfl
      intro id hid
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hid
      obtain ⟨x, hx, hxid⟩ := hbox b hb
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hx), hxid⟩
      · exact ⟨x, List.mem_append_right _ hx, hxid⟩
    · refine filterMap_find_ids (fun b : Route => b.id) (inp.routes.map (·.id)) _ ?_ inp.routes
        (fun b : ModelRoute => b.id) rfl
      intro id hid
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hid
      obtain ⟨x, hx, hxid⟩ := hroute b hb
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hx), hxid⟩
      · exact ⟨x, List.mem_append_right _ hx, hxid⟩

theorem any_id_iff (bs : List ModelBox) (s : String) :
    (bs.any fun box => box.id == s) = true ↔ s ∈ bs.map (·.id) := by
  rw [List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨b, hb, e⟩
    exact ⟨b, hb, by simpa using e⟩
  · rintro ⟨b, hb, e⟩
    exact ⟨b, hb, by simpa using e⟩

theorem mem_filter_ids (inp : Input) (keep : ModelBox → Bool) (b : ModelBox) (hb : b ∈ inp.boxes)
    (hk : keep b = true) : b.id ∈ (inp.boxes.filter keep).map (·.id) :=
  List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hk⟩, rfl⟩

theorem layoutRecursive_ids
    (hbase : ∀ (inp : Input) (o : Options) (res : FamilyResult), layout inp o = .ok res →
      res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
        res.scene.routes.map (·.id) = inp.routes.map (·.id)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursive fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id)
  | 0, inp, o, res, _, h => hbase inp o res h
  | fuel + 1, inp, o, res, hc, h => by
    rcases layoutRecursive_succ h with ⟨_, hl⟩ | ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact hbase inp o res hl
    · have hgi := List.find?_some hg
      simp only [Bool.and_eq_true] at hgi
      have hin := independent_inside hgi.1
      have ih1 := layoutRecursive_ids hbase fuel _ _ _
        (selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
      have ih2 := layoutRecursive_ids hbase fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } o parent
        (selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "") hparent
      have idsC := selectInput_box_ids inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have idsP := selectInput_box_ids inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
      refine expandChild_ids hexp ?_ ?_
      · intro bx hbx
        by_cases hi : Compound.inside inp.boxes group.id bx.id = true
        · have hm : bx.id ∈ child.scene.boxes.map (·.id) := by
            rw [ih1.1, idsC]
            exact mem_filter_ids inp _ bx hbx hi
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hm : bx.id ∈ parent.scene.boxes.map (·.id) := by
            rw [ih2.1]
            show bx.id ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)
            rw [idsP]
            exact mem_filter_ids inp _ bx hbx (by simpa using hi)
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩
      · intro r hr
        obtain ⟨⟨bf, hbf, ef⟩, ⟨bt, hbt, et⟩⟩ := hc r hr
        have heq := hin r hr
        by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
        · have hit : Compound.inside inp.boxes group.id r.toId = true := by rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsC]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; exact hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; exact hit)
          have hm : r.id ∈ child.scene.routes.map (·.id) := by
            rw [ih1.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hit : ¬ Compound.inside inp.boxes group.id r.toId = true := by rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsP]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; simpa using hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; simpa using hit)
          have hm : r.id ∈ parent.scene.routes.map (·.id) := by
            rw [ih2.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩


/-- A property of every layout that `layoutRecursive` actually performs. -/
def TraceOf (Q : Input → Options → Prop) : Nat → Input → Options → Prop
  | 0, inp, o => Q inp o
  | fuel + 1, inp, o =>
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧ Q inp o) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      TraceOf Q fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } ∧
      ∃ a b c, TraceOf Q fuel
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } o

theorem layoutRecursive_trace {Q : Input → Options → Prop}
    (hbase : ∀ (inp : Input) (o : Options) (res : FamilyResult), layout inp o = .ok res → Q inp o) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      layoutRecursive fuel inp o = .ok res → TraceOf Q fuel inp o
  | 0, inp, o, res, h => hbase inp o res h
  | fuel + 1, inp, o, res, h => by
    rcases layoutRecursive_succ h with ⟨hn, hl⟩ | ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, _⟩
    · exact Or.inl ⟨hn, hbase inp o res hl⟩
    · exact Or.inr ⟨group, hg, layoutRecursive_trace hbase fuel _ _ _ hchild,
        a, b, c, layoutRecursive_trace hbase fuel _ _ _ hparent⟩

end PipelineImpl
end Layered
end Elegant
