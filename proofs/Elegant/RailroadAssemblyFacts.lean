import Elegant.RailroadFacts
import Elegant.Kinds.Railroad

set_option autoImplicit false

namespace Elegant.Railroad

theorem initial_stage_bounds (p : Profile) :
    StageBounds p ({y := constant p "margin"} : RuleState) := by
  refine ⟨(rule_spacing_nonnegative p).1,by change (0 : Int) ≤ 0; omega,?_⟩
  intro box hb
  cases hb

/-- The rule fold's stage frame contains every emitted box. The final canvas adds
only the trailing margin; the empty-rule canvas has no boxes. -/
theorem layout_canvas (m : Model) (rules : List Rule) (s : Scene)
    (h : layout m rules = .ok s) : Validator.C1 s.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm,bind,Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric) {y := constant m.profile "margin"} with
    | error e => simp [hm,hf,bind,Except.bind] at h
    | ok result =>
      have hb := foldlM_preserves (placeRule m metric) (StageBounds m.profile)
        (fun rule before after hi he => placeRule_stage_bounds m metric before after rule hi he)
        rules {y := constant m.profile "margin"} result (initial_stage_bounds m.profile) hf
      have hempty : rules = [] → result.state.boxes = [] := by
        intro he
        subst rules
        simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at hf
        subst result
        rfl
      simp only [hm,hf,bind,Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (try simp only [pure,Except.pure,Except.ok.injEq] at h
           subst s
           intro box hbox
           first
           | (have hz := hempty (by simpa using ‹rules.isEmpty = true›)
              rw [hz] at hbox
              cases hbox)
           | (have hc := hb.2.2 box hbox
              have margin := (rule_spacing_nonnegative m.profile).1
              unfold StageFrame Rect.Contained at hc
              unfold Validator.canvasRect Rect.Contained Scene.layoutDump
              dsimp only at *
              omega))
/-- A placement step only appends boxes. This invariant lets later id lookup
proofs retain every previously declared ancestor across the child traversal. -/
def ExtendsBoxes (initial final : State) : Prop :=
  ∃ suffix, final.boxes = initial.boxes ++ suffix

theorem ExtendsBoxes.refl (state : State) : ExtendsBoxes state state :=
  ⟨[],by simp⟩

theorem ExtendsBoxes.trans {a b c : State} (hab : ExtendsBoxes a b)
    (hbc : ExtendsBoxes b c) : ExtendsBoxes a c := by
  obtain ⟨ab,hab⟩ := hab
  obtain ⟨bc,hbc⟩ := hbc
  exact ⟨ab++bc,by rw [hbc,hab,List.append_assoc]⟩

theorem joinStep_boxes (s : Shape) (x y : Int) (state : State) (i : Nat) :
    (joinStep s x y state i).boxes = state.boxes := rfl

theorem sequenceJoins_boxes (s : Shape) (x y : Int) (state : State) :
    (sequenceJoins s x y state).boxes = state.boxes := by
  apply foldl_preserves (joinStep s x y) (fun acc => acc.boxes = state.boxes)
  · intro i acc h
    exact h
  · rfl

theorem placeNode_extends_boxes :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      ExtendsBoxes initial final := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final h
    simp only [placeNode] at h
    split at h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst final
      exact ⟨_,rfl⟩
    · refine foldlM_preserves _ (ExtendsBoxes initial) ?_ _ _ final ?_ h
      · intro pair before after hb he
        exact hb.trans (ih p pair.1 _ _ s.id before after he)
      · split
        · exact ⟨_,sequenceJoins_boxes s x y _⟩
        · exact ⟨_,rfl⟩


theorem find_append_preserved {α : Type} (test : α → Bool) :
    ∀ (front suffix : List α) (value : α), front.find? test = some value →
      (front++suffix).find? test = some value := by
  intro front
  induction front with
  | nil => intro suffix value h; cases h
  | cons first rest ih =>
    intro suffix value h
    simp only [List.find?_cons] at h ⊢
    split at h
    · simp [*]
    · simp [*, ih suffix value h]

/-- An existing parent lookup is stable when descendants and later rules append
their boxes. This does not assume that newly emitted ids are distinct. -/
theorem ExtendsBoxes.find_preserved {initial final : State}
    (he : ExtendsBoxes initial final) (id : String) (box : Box)
    (hf : initial.boxes.find? (fun b => b.id == id) = some box) :
    final.boxes.find? (fun b => b.id == id) = some box := by
  obtain ⟨suffix,he⟩ := he
  rw [he]
  exact find_append_preserved _ _ _ _ hf

theorem ExtendsBoxes.mem {initial final : State} (he : ExtendsBoxes initial final)
    (box : Box) (hb : box ∈ initial.boxes) : box ∈ final.boxes := by
  obtain ⟨suffix,he⟩ := he
  rw [he]
  exact List.mem_append_left suffix hb

theorem placeNode_root_mem :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      Box.mk s.id (if leaf s.kind then "node" else "group") (shapeRect s x y)
        parent (leaf s.kind) ∈ final.boxes := by
  intro fuel
  cases fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel =>
    intro p s x y parent initial final h
    simp only [placeNode] at h
    split at h
    · simp only [pure,Except.pure,Except.ok.injEq] at h
      subst final
      simp_all
    · have hbase : ExtendsBoxes
        ({boxes := initial.boxes ++
          [Box.mk s.id "group" (shapeRect s x y) parent (leaf s.kind)]
          routes := initial.routes, labels := initial.labels
          groups := initial.groups ++ [Group.mk .group s.id (rails p s x y)]
          edges := initial.edges, nodes := initial.nodes} : State) final := by
        refine foldlM_preserves _ (ExtendsBoxes _) ?_ _ _ final ?_ h
        · intro pair before after hb he
          exact hb.trans (placeNode_extends_boxes fuel p pair.1 _ _ s.id before after he)
        · split
          · exact ⟨[],by rw [sequenceJoins_boxes]; simp⟩
          · exact ExtendsBoxes.refl _
      have hm := hbase.mem (Box.mk s.id "group" (shapeRect s x y) parent (leaf s.kind))
        (by simp)
      simpa [*] using hm

theorem decodeNode_metadata :
    ∀ (fuel : Nat) (m : Model) (b : ModelBox) (n : Node),
      Kinds.Railroad.decodeNode fuel m b = .ok n →
      n.id = b.id ∧ n.text = Kinds.Railroad.display m b := by
  intro fuel
  cases fuel with
  | zero => intro m b n h; cases h
  | succ fuel =>
    intro m b n h
    simp only [Kinds.Railroad.decodeNode] at h
    cases hc : (Kinds.Railroad.children m b.id).mapM (Kinds.Railroad.decodeNode fuel m) with
    | error e => simp [hc,bind,Except.bind] at h
    | ok kids =>
      simp only [hc,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
      subst n
      exact ⟨rfl,rfl⟩

theorem foldlM_boxes_extends {α : Type} (f : State → α → Except LayoutError State)
    (hf : ∀ a before after, f before a = .ok after → ExtendsBoxes before after) :
    ∀ (xs : List α) (initial final : State), xs.foldlM f initial = .ok final →
      ExtendsBoxes initial final := by
  intro xs initial final h
  exact foldlM_preserves f (ExtendsBoxes initial)
    (fun a before after hb he => hb.trans (hf a before after he))
    xs initial final (ExtendsBoxes.refl initial) h

theorem find_first_appended {initial : List Box} {box : Box}
    (h : initial.find? (fun b => b.id == box.id) = none) :
    (initial ++ [box]).find? (fun b => b.id == box.id) = some box := by
  induction initial with
  | nil => simp
  | cons a rest ih =>
    simp only [List.find?_cons] at h ⊢
    split at h
    · cases h
    · simp [*]

/-- A fresh root's own lookup is present immediately and survives all later
child writes. Freshness is proved from the frontend's unique box ids at the
public adapter boundary, not checked by the layout. -/
theorem placeNode_root_lookup (fuel : Nat) (p : Profile) (s : Shape) (x y : Int)
    (parent : String) (initial final : State)
    (hfresh : initial.boxes.find? (fun b => b.id == s.id) = none)
    (h : placeNode (fuel+1) p s x y parent initial = .ok final) :
    final.boxes.find? (fun b => b.id == s.id) =
      some (Box.mk s.id (if leaf s.kind then "node" else "group")
        (shapeRect s x y) parent (leaf s.kind)) := by
  let root := Box.mk s.id (if leaf s.kind then "node" else "group")
    (shapeRect s x y) parent (leaf s.kind)
  have hroot : (initial.boxes ++ [root]).find? (fun b => b.id == s.id) = some root :=
    find_first_appended (box := root) (by simpa only [root] using hfresh)
  simp only [placeNode] at h
  split at h
  · simp only [pure,Except.pure,Except.ok.injEq] at h
    subst final
    simp [*]
  · have he := foldlM_boxes_extends
      (fun acc (pair : Shape × Point) => placeNode fuel p pair.1 (x+pair.2.x) (y+pair.2.y) s.id acc)
      (fun (pair : Shape × Point) before after hp => placeNode_extends_boxes fuel p pair.1 _ _ s.id before after hp)
      _ _ final h
    apply he.find_preserved s.id root
    split
    · simp [sequenceJoins_boxes,root, *]
    · simp [root, *]

/-- Every emitted box retains its source parent id. The root is the one new
entry; recursive calls explicitly pass the enclosing node's id. -/
theorem placeNode_old_parent_lookup (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State) (id : String) (box : Box)
    (hf : initial.boxes.find? (fun b => b.id == id) = some box)
    (h : placeNode fuel p s x y parent initial = .ok final) :
    final.boxes.find? (fun b => b.id == id) = some box :=
  (placeNode_extends_boxes fuel p s x y parent initial final h).find_preserved id box hf

theorem descendants_avoid_left_gap {s : Shape} {x y : Int} {r : Rect}
    (hg : Geometry s) (hd : DescendantFrame s x y r) (left right baseline : Int)
    (hright : max left right ≤ x) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] r := by
  have hc := descendant_contained hd hg
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  apply horizontal_route_avoids
  exact Or.inl (Int.le_trans hright hc.1)

theorem descendants_avoid_right_gap {s : Shape} {x y : Int} {r : Rect}
    (hg : Geometry s) (hd : DescendantFrame s x y r) (left right baseline : Int)
    (hleft : x+s.w ≤ min left right) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] r := by
  have hc := descendant_contained hd hg
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  apply horizontal_route_avoids
  exact Or.inr (Or.inl (Int.le_trans hc.2.1 hleft))

theorem descendants_avoid_above_gap {s : Shape} {x y : Int} {r : Rect}
    (hg : Geometry s) (hd : DescendantFrame s x y r) (left right baseline : Int)
    (hbelow : baseline ≤ y) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] r := by
  have hc := descendant_contained hd hg
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  apply horizontal_route_avoids
  exact Or.inr (Or.inr (Or.inl (Int.le_trans hbelow hc.2.2.1)))

theorem descendants_avoid_below_gap {s : Shape} {x y : Int} {r : Rect}
    (hg : Geometry s) (hd : DescendantFrame s x y r) (left right baseline : Int)
    (habove : y+s.height ≤ baseline) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] r := by
  have hc := descendant_contained hd hg
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  apply horizontal_route_avoids
  exact Or.inr (Or.inr (Or.inr (Int.le_trans hc.2.2.2 habove)))

theorem descendants_avoid_separated_gap {s : Shape} {x y : Int} {r : Rect}
    (hg : Geometry s) (hd : DescendantFrame s x y r) (left right baseline : Int)
    (hgap : max left right ≤ x ∨ x+s.w ≤ min left right ∨
      baseline ≤ y ∨ y+s.height ≤ baseline) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] r := by
  rcases hgap with h | h | h | h
  · exact descendants_avoid_left_gap hg hd left right baseline h
  · exact descendants_avoid_right_gap hg hd left right baseline h
  · exact descendants_avoid_above_gap hg hd left right baseline h
  · exact descendants_avoid_below_gap hg hd left right baseline h

/-- Every successful decoder output comes from one executed source call. -/
theorem mapM_success_origin {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y := by
  intro xs
  induction xs with
  | nil =>
    intro ys h y hy
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst ys
    cases hy
  | cons x xs ih =>
    intro ys h value hv
    cases hx : f x with
    | error e => simp [List.mapM_cons, hx, bind, Except.bind] at h
    | ok y =>
      cases hxs : xs.mapM f with
      | error e => simp [List.mapM_cons, hx, hxs, bind, Except.bind] at h
      | ok rest =>
        simp only [List.mapM_cons, hx, hxs, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq] at h
        subst ys
        rcases List.mem_cons.mp hv with hv | hv
        · subst value
          exact ⟨x, by simp, hx⟩
        · obtain ⟨source, hs, hd⟩ := ih rest hxs value hv
          exact ⟨source, by simp [hs], hd⟩

theorem decodeNode_children (fuel : Nat) (m : Model) (b : ModelBox)
    (n : Node) (h : Kinds.Railroad.decodeNode (fuel+1) m b = .ok n) :
    ∀ child ∈ n.children, ∃ source ∈ Kinds.Railroad.children m b.id,
      Kinds.Railroad.decodeNode fuel m source = .ok child := by
  simp only [Kinds.Railroad.decodeNode] at h
  cases hc : (Kinds.Railroad.children m b.id).mapM
      (Kinds.Railroad.decodeNode fuel m) with
  | error e => simp [hc, bind, Except.bind] at h
  | ok kids =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst n
    exact mapM_success_origin _ _ _ hc

/-- The parent identity comes from the decoded model edge, not from a later
scene lookup or a geometric containment assumption. -/
theorem decodeNode_child_origin (fuel : Nat) (m : Model) (b : ModelBox)
    (n child : Node)
    (h : Kinds.Railroad.decodeNode (fuel+1) m b = .ok n)
    (hc : child ∈ n.children) :
    ∃ source ∈ m.boxes, source.parent = b.id ∧
      child.id = source.id ∧
      Kinds.Railroad.decodeNode fuel m source = .ok child := by
  obtain ⟨source, hs, hd⟩ :=
    decodeNode_children fuel m b n h child hc
  have hs' := List.mem_filter.mp hs
  exact ⟨source, hs'.1, by simpa using hs'.2,
    (decodeNode_metadata fuel m source child hd).1, hd⟩

theorem lower_rule_origin (m : Model) (rules : List Rule)
    (h : Kinds.Railroad.lower m = .ok rules) (rule : Rule) (hr : rule ∈ rules) :
    ∃ source ∈ m.boxes, source.parent = "" ∧
      Kinds.Railroad.decodeRule m source = .ok rule := by
  obtain ⟨source, hs, hd⟩ :=
    mapM_success_origin (Kinds.Railroad.decodeRule m)
      (Kinds.Railroad.children m "") rules h rule hr
  have hs' := List.mem_filter.mp hs
  exact ⟨source, hs'.1, by simpa using hs'.2, hd⟩

/-- A box's exact placement address in the measured forest. The child case
records the executed zip, including its offset and enclosing id. -/
inductive PlacedBox : Shape → Int → Int → String → Box → Prop
  | root (s : Shape) (x y : Int) (parent : String) :
      PlacedBox s x y parent
        (Box.mk s.id (if leaf s.kind then "node" else "group")
          (shapeRect s x y) parent (leaf s.kind))
  | child {s : Shape} {x y : Int} {parent : String}
      (pair : Shape × Point) (hp : pair ∈ s.children.zip s.offsets)
      (hn : leaf s.kind = false)
      {box : Box} (hb : PlacedBox pair.1 (x+pair.2.x) (y+pair.2.y) s.id box) :
      PlacedBox s x y parent box


/-- Exhaustiveness for actual emitted boxes, with old boxes explicitly
separated from this traversal's output. -/
theorem placeNode_box_origin :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      ∀ box ∈ final.boxes, box ∈ initial.boxes ∨ PlacedBox s x y parent box := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final h
    let root := Box.mk s.id (if leaf s.kind then "node" else "group")
      (shapeRect s x y) parent (leaf s.kind)
    let P := fun state : State =>
      ∀ box ∈ state.boxes, box ∈ initial.boxes ∨ PlacedBox s x y parent box
    have hbase : ∀ box ∈ initial.boxes ++ [root],
        box ∈ initial.boxes ∨ PlacedBox s x y parent box := by
      intro box hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inl hb
      · have he : box = root := by simpa using hb
        subst box
        exact Or.inr (.root s x y parent)
    simp only [placeNode] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst final
      simpa [root, *] using hbase
    · have hfold : P final := by
        apply foldlM_preserves_mem _ P _ ?_ _ final ?_ h
        · intro pair hp before after hb he box hbox
          rcases ih p pair.1 (x+pair.2.x) (y+pair.2.y) s.id before after he box hbox with
            hold | hnew
          · exact hb box hold
          · exact Or.inr (.child pair hp (by simp_all) hnew)
        · split
          · simpa [P, root, sequenceJoins_boxes, *] using hbase
          · simpa [P, root, *] using hbase
      exact hfold


theorem PlacedBox.descendant {s : Shape} {x y : Int} {parent : String} {box : Box}
    (h : PlacedBox s x y parent box) : DescendantFrame s x y box.rect := by
  induction h with
  | root s x y parent => exact .self s x y
  | child pair hp _ _ ih => exact .child _ _ _ pair _ hp ih

/-- This is containment of the boxes actually emitted by `placeNode`, rather
than containment of an independently postulated valid scene. -/
theorem placeNode_new_box_contained (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hg : Geometry s) (h : placeNode fuel p s x y parent initial = .ok final)
    (box : Box) (hb : box ∈ final.boxes) (hnew : box ∉ initial.boxes) :
    (shapeRect s x y).Contained box.rect := by
  rcases placeNode_box_origin fuel p s x y parent initial final h box hb with hold | hplaced
  · exact False.elim (hnew hold)
  · exact descendant_contained hplaced.descendant hg

theorem placed_boxes_in_separated_children {s : Shape} (hg : Geometry s)
    (x y : Int) (a b : Shape × Point)
    (ha : a ∈ s.children.zip s.offsets) (hb : b ∈ s.children.zip s.offsets)
    (pa pb : String) (boxA boxB : Box)
    (hA : PlacedBox a.1 (x+a.2.x) (y+a.2.y) pa boxA)
    (hB : PlacedBox b.1 (x+b.2.x) (y+b.2.y) pb boxB)
    (hsep : Disjoint (shapeRect a.1 (x+a.2.x) (y+a.2.y))
      (shapeRect b.1 (x+b.2.x) (y+b.2.y))) :
    Disjoint boxA.rect boxB.rect :=
  descendant_siblings_disjoint hg x y a b ha hb boxA.rect boxB.rect
    hsep hA.descendant hB.descendant

theorem placed_box_avoids_separated_gap {s : Shape} {x y : Int}
    {parent : String} {box : Box} (hg : Geometry s)
    (hb : PlacedBox s x y parent box) (left right baseline : Int)
    (hgap : max left right ≤ x ∨ x+s.w ≤ min left right ∨
      baseline ≤ y ∨ y+s.height ≤ baseline) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] box.rect :=
  descendants_avoid_separated_gap hg hb.descendant left right baseline hgap

inductive NodeIn : Node → Node → Prop where
  | root (node : Node) : NodeIn node node
  | child {root child node : Node} (hc : child ∈ root.children)
      (hn : NodeIn child node) : NodeIn root node

theorem decodeNode_descendant_origin :
    ∀ (fuel : Nat) (m : Model) (source : ModelBox) (root node : Node),
      source ∈ m.boxes →
      Kinds.Railroad.decodeNode fuel m source = .ok root →
      NodeIn root node →
      ∃ box ∈ m.boxes, node.id = box.id := by
  intro fuel
  induction fuel with
  | zero => intro m source root node _ h _; cases h
  | succ fuel ih =>
    intro m source root node hs h hn
    cases hn with
    | root =>
      exact ⟨source, hs, (decodeNode_metadata (fuel+1) m source root h).1⟩
    | child hc hn =>
      obtain ⟨box, hb, _, _, hd⟩ :=
        decodeNode_child_origin fuel m source root _ h hc
      exact ih m box _ node hb hd hn

theorem measure_child_origin (fuel : Nat) (p : Profile) (metric : Measure.Metric)
    (node : Node) (shape child : Shape)
    (h : measure (fuel+1) p metric node = .ok shape)
    (hc : child ∈ shape.children) :
    ∃ source ∈ node.children, measure fuel p metric source = .ok child := by
  simp only [measure] at h
  cases hk : node.children.mapM (measure fuel p metric) with
  | error e => simp [hk, bind, Except.bind] at h
  | ok kids =>
    simp only [hk, bind, Except.bind] at h
    have hm := size_metadata p metric node kids shape h
    rw [hm.2.2] at hc
    exact mapM_success_origin _ _ _ hk child hc

/-- Placement addresses retain a measured source node, including nodes below
arbitrarily nested wrappers. No id lookup or scene-validity premise is used. -/
theorem placedBox_measured_origin :
    ∀ (fuel : Nat) (p : Profile) (metric : Measure.Metric)
      (node : Node) (shape : Shape) (x y : Int) (parent : String) (box : Box),
      measure fuel p metric node = .ok shape →
      PlacedBox shape x y parent box →
      ∃ source, NodeIn node source ∧ box.id = source.id := by
  intro fuel
  induction fuel with
  | zero => intro p metric node shape x y parent box h _; cases h
  | succ fuel ih =>
    intro p metric node shape x y parent box h hp
    cases hp with
    | root =>
      refine ⟨node, .root node, ?_⟩
      simp only [measure] at h
      cases hk : node.children.mapM (measure fuel p metric) with
      | error e => simp [hk, bind, Except.bind] at h
      | ok kids =>
        simp only [hk, bind, Except.bind] at h
        exact (size_metadata p metric node kids shape h).1
    | child pair hpair _ hplaced =>
      obtain ⟨source, hs, hm⟩ :=
        measure_child_origin fuel p metric node shape pair.1 h
          (List.of_mem_zip hpair).1
      obtain ⟨descendant, hd, hid⟩ := ih p metric source pair.1 _ _ _ box hm hplaced
      exact ⟨descendant, .child hs hd, hid⟩

theorem placedBox_decoded_origin (decodeFuel measureFuel : Nat)
    (m : Model) (source : ModelBox) (node : Node) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String) (box : Box)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeNode decodeFuel m source = .ok node)
    (hm : measure measureFuel m.profile metric node = .ok shape)
    (hp : PlacedBox shape x y parent box) :
    ∃ original ∈ m.boxes, box.id = original.id := by
  obtain ⟨descendant, hn, hid⟩ :=
    placedBox_measured_origin measureFuel m.profile metric node shape x y parent box hm hp
  obtain ⟨original, ho, he⟩ :=
    decodeNode_descendant_origin decodeFuel m source node descendant hs hd hn
  exact ⟨original, ho, hid.trans he⟩

theorem placeNode_decoded_origin (decodeFuel measureFuel placeFuel : Nat)
    (m : Model) (source : ModelBox) (node : Node) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String)
    (initial final : State)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeNode decodeFuel m source = .ok node)
    (hm : measure measureFuel m.profile metric node = .ok shape)
    (hp : placeNode placeFuel m.profile shape x y parent initial = .ok final)
    (box : Box) (hb : box ∈ final.boxes) (hfresh : box ∉ initial.boxes) :
    ∃ original ∈ m.boxes, box.id = original.id := by
  rcases placeNode_box_origin placeFuel m.profile shape x y parent initial final hp box hb with
    hold | hplaced
  · exact False.elim (hfresh hold)
  · exact placedBox_decoded_origin decodeFuel measureFuel m source node shape metric
      x y parent box hs hd hm hplaced

/-- A source ancestry path records the actual parent edges traversed by the
decoder. In particular it does not infer ancestry from equal display text. -/
inductive SourceDescendant (m : Model) : ModelBox → ModelBox → Prop where
  | root (box : ModelBox) : SourceDescendant m box box
  | child {root child descendant : ModelBox}
      (hc : child ∈ m.boxes) (hp : child.parent = root.id)
      (hd : SourceDescendant m child descendant) :
      SourceDescendant m root descendant

theorem decodeNode_descendant_parent_origin :
    ∀ (fuel : Nat) (m : Model) (source : ModelBox) (root node : Node),
      source ∈ m.boxes →
      Kinds.Railroad.decodeNode fuel m source = .ok root →
      NodeIn root node →
      ∃ box ∈ m.boxes, node.id = box.id ∧ SourceDescendant m source box := by
  intro fuel
  induction fuel with
  | zero => intro m source root node _ h _; cases h
  | succ fuel ih =>
    intro m source root node hs h hn
    cases hn with
    | root =>
      exact ⟨source, hs, (decodeNode_metadata (fuel+1) m source root h).1,
        .root source⟩
    | child hc hn =>
      obtain ⟨child, hchild, hparent, _, hd⟩ :=
        decodeNode_child_origin fuel m source root _ h hc
      obtain ⟨box, hb, hid, hpath⟩ := ih m child _ node hchild hd hn
      exact ⟨box, hb, hid, .child hchild hparent hpath⟩

/-- Every non-root placement's parent is itself a placement in the same
executed traversal. The alternative is precisely the caller-supplied parent. -/
theorem PlacedBox.parent_origin {s : Shape} {x y : Int} {parent : String}
    {box : Box} (h : PlacedBox s x y parent box) :
    box.parent = parent ∨
      ∃ enclosing, PlacedBox s x y parent enclosing ∧ box.parent = enclosing.id := by
  induction h with
  | root s x y parent => exact Or.inl rfl
  | @child s x y parent pair hp hn box hb ih =>
    rcases ih with hparent | ⟨enclosing, he, hid⟩
    · exact Or.inr ⟨Box.mk s.id (if leaf s.kind then "node" else "group")
        (shapeRect s x y) parent (leaf s.kind), .root s x y parent, hparent⟩
    · exact Or.inr ⟨enclosing, .child pair hp hn he, hid⟩

theorem placedBox_decoded_parent_origin (decodeFuel measureFuel : Nat)
    (m : Model) (source : ModelBox) (node : Node) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String) (box : Box)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeNode decodeFuel m source = .ok node)
    (hm : measure measureFuel m.profile metric node = .ok shape)
    (hp : PlacedBox shape x y parent box) :
    ∃ original ∈ m.boxes, box.id = original.id ∧
      SourceDescendant m source original := by
  obtain ⟨descendant, hn, hid⟩ :=
    placedBox_measured_origin measureFuel m.profile metric node shape x y parent box hm hp
  obtain ⟨original, ho, he, hpath⟩ :=
    decodeNode_descendant_parent_origin decodeFuel m source node descendant hs hd hn
  exact ⟨original, ho, hid.trans he, hpath⟩

/-- C3's local geometric obligation follows the executed placement address:
each internal parent is present in the same traversal and contains the child.
Only the traversal root leaves its caller's parent to the rule-fold invariant. -/
theorem PlacedBox.parent_contained {s : Shape} {x y : Int} {parent : String}
    {box : Box} (h : PlacedBox s x y parent box) (hg : Geometry s) :
    (box.parent = parent ∧ (shapeRect s x y).Contained box.rect) ∨
      ∃ enclosing, PlacedBox s x y parent enclosing ∧
        box.parent = enclosing.id ∧ enclosing.rect.Contained box.rect := by
  induction h with
  | root s x y parent =>
    exact Or.inl ⟨rfl, descendant_contained (.self s x y) hg⟩
  | @child s x y parent pair hp hn box hb ih =>
    rcases ih (hg.child pair hp) with ⟨hparent, hc⟩ | ⟨enclosing, he, hid, hc⟩
    · exact Or.inr ⟨Box.mk s.id (if leaf s.kind then "node" else "group")
        (shapeRect s x y) parent (leaf s.kind), .root s x y parent, hparent,
        Rect.Contained.trans (child_rect_contained s hg.inside x y pair hp) hc⟩
    · exact Or.inr ⟨enclosing, .child pair hp hn he, hid, hc⟩

theorem SourceDescendant.trans {m : Model} {a b c : ModelBox}
    (hab : SourceDescendant m a b) (hbc : SourceDescendant m b c) :
    SourceDescendant m a c := by
  induction hab with
  | root => exact hbc
  | child hc hp _ ih => exact .child hc hp (ih hbc)

theorem SourceDescendant.member {m : Model} {root box : ModelBox}
    (h : SourceDescendant m root box) (hr : root ∈ m.boxes) :
    box ∈ m.boxes := by
  revert hr
  induction h with
  | root => intro hr; exact hr
  | child hc _ _ ih => intro _; exact ih hc

/-- Transfer the internal-parent containment witness to boxes in the successful
state. Old boxes remain the caller's invariant; new boxes carry their executed
placement address and hence their actual enclosing frame. -/
theorem placeNode_new_parent_contained (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hg : Geometry s) (h : placeNode fuel p s x y parent initial = .ok final)
    (box : Box) (hb : box ∈ final.boxes) (hnew : box ∉ initial.boxes) :
    (box.parent = parent ∧ (shapeRect s x y).Contained box.rect) ∨
      ∃ enclosing, PlacedBox s x y parent enclosing ∧
        box.parent = enclosing.id ∧ enclosing.rect.Contained box.rect := by
  rcases placeNode_box_origin fuel p s x y parent initial final h box hb with
    hold | hplaced
  · exact False.elim (hnew hold)
  · exact hplaced.parent_contained hg

/-- Locate an actual recursive call in the child fold, retaining the suffix
extension needed to transport its box lookups into the completed state. -/
theorem foldlM_member_execution {α : Type}
    (f : State → α → Except LayoutError State)
    (hext : ∀ a before after, f before a = .ok after → ExtendsBoxes before after) :
    ∀ (xs : List α) (initial final : State),
      xs.foldlM f initial = .ok final →
      ∀ a ∈ xs, ∃ before after,
        f before a = .ok after ∧ ExtendsBoxes after final := by
  intro xs
  induction xs with
  | nil => intro initial final h a ha; cases ha
  | cons head tail ih =>
    intro initial final h a ha
    cases hh : f initial head with
    | error e => simp [List.foldlM_cons, hh, bind, Except.bind] at h
    | ok middle =>
      have ht : tail.foldlM f middle = .ok final := by
        simpa [List.foldlM_cons, hh, bind, Except.bind] using h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨initial, middle, hh,
          foldlM_boxes_extends f hext tail middle final ht⟩
      · exact ih middle final ht a ha

/-- Completeness of the execution-aware placement address. The nonleaf
condition on child addresses excludes subtrees the executable deliberately
does not visit. -/
theorem placeNode_address_mem :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      ∀ box, PlacedBox s x y parent box → box ∈ final.boxes := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final h box hb
    cases hb with
    | root => exact placeNode_root_mem (fuel+1) p s x y parent initial final h
    | child pair hp hn hbelow =>
      simp [placeNode, hn] at h
      obtain ⟨before, after, he, hext⟩ := foldlM_member_execution
        (fun acc (pair : Shape × Point) =>
          placeNode fuel p pair.1 (x+pair.2.x) (y+pair.2.y) s.id acc)
        (fun pair before after he =>
          placeNode_extends_boxes fuel p pair.1 _ _ s.id before after he)
        _ _ final h pair hp
      exact hext.mem box (ih p pair.1 _ _ s.id before after he box hbelow)

theorem placeNode_new_parent_member (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hg : Geometry s) (h : placeNode fuel p s x y parent initial = .ok final)
    (box : Box) (hb : box ∈ final.boxes) (hnew : box ∉ initial.boxes) :
    (box.parent = parent ∧ (shapeRect s x y).Contained box.rect) ∨
      ∃ enclosing ∈ final.boxes,
        box.parent = enclosing.id ∧ enclosing.rect.Contained box.rect := by
  rcases placeNode_new_parent_contained fuel p s x y parent initial final
      hg h box hb hnew with hroot | ⟨enclosing, he, hid, hc⟩
  · exact Or.inl hroot
  · exact Or.inr ⟨enclosing,
      placeNode_address_mem fuel p s x y parent initial final h enclosing he, hid, hc⟩

theorem pairwise_symmetric_members {α : Type} (R : α → α → Prop)
    (hsym : ∀ a b, R a b → R b a) :
    ∀ (xs : List α), xs.Pairwise R →
      ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → R a b := by
  intro xs
  induction xs with
  | nil => intro _ a ha; cases ha
  | cons head tail ih =>
    intro h a ha b hb hne
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with heA | haTail
    · subst a
      rcases List.mem_cons.mp hb with heB | hbTail
      · exact False.elim (hne heB.symm)
      · exact hhead b hbTail
    · rcases List.mem_cons.mp hb with heB | hbTail
      · subst b
        exact hsym _ _ (hhead a haTail)
      · exact ih htail a haTail b hbTail hne

theorem ChildrenSeparated.members {s : Shape} (h : ChildrenSeparated s)
    (a b : Shape × Point)
    (ha : a ∈ s.children.zip s.offsets) (hb : b ∈ s.children.zip s.offsets)
    (hne : a ≠ b) (x y : Int) :
    Disjoint (shapeRect a.1 (x+a.2.x) (y+a.2.y))
      (shapeRect b.1 (x+b.2.x) (y+b.2.y)) := by
  have hd := pairwise_symmetric_members
    (fun a b : Shape × Point =>
      Disjoint (shapeRect a.1 a.2.x a.2.y) (shapeRect b.1 b.2.x b.2.y))
    (by
      intro a b h
      unfold Disjoint Rect.meetsInterior at h ⊢
      omega)
    _ h a ha b hb hne
  unfold Disjoint Rect.meetsInterior shapeRect at hd ⊢
  dsimp only at hd ⊢
  omega

/-- Exclusive boxes emitted below one measured root either have the same
placement address or lie in separated child subtrees. Wrappers are never
exclusive, so the ancestor cases cannot overlap exclusive descendants. -/
theorem PlacedBox.exclusive_disjoint {s : Shape} {x y : Int} {parent : String}
    {boxA : Box} (hA : PlacedBox s x y parent boxA) :
    Geometry s → ∀ boxB, PlacedBox s x y parent boxB →
      boxA ≠ boxB → boxA.exclusive = true → boxB.exclusive = true →
      Disjoint boxA.rect boxB.rect := by
  induction hA with
  | root s x y parent =>
    intro hg boxB hB hne hAex hBex
    cases hB with
    | root => exact False.elim (hne rfl)
    | child pair hp hn hb => simp_all
  | @child s x y parent pair hp hn boxA hA ih =>
    intro hg boxB hB hne hAex hBex
    cases hB with
    | root => simp_all
    | child other ho _ hB =>
      by_cases he : pair = other
      · subst other
        exact ih (hg.child pair hp) boxB hB hne hAex hBex
      · have hs : ChildrenSeparated s := by
          cases hg with
          | node _ _ _ _ separated _ => exact separated
        exact placed_boxes_in_separated_children hg x y pair other hp ho
          s.id s.id boxA boxB hA hB (hs.members pair other hp ho he x y)

def ExclusiveSeparated (state : State) : Prop :=
  ∀ a ∈ state.boxes, ∀ b ∈ state.boxes, a ≠ b →
    a.exclusive = true → b.exclusive = true → Disjoint a.rect b.rect

theorem placeNode_exclusive_separated (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hg : Geometry s) (hi : ExclusiveSeparated initial)
    (hcross : ∀ old ∈ initial.boxes, old.exclusive = true → ∀ box,
      PlacedBox s x y parent box → Disjoint old.rect box.rect)
    (h : placeNode fuel p s x y parent initial = .ok final) :
    ExclusiveSeparated final := by
  intro a ha b hb hne hae hbe
  rcases placeNode_box_origin fuel p s x y parent initial final h a ha with ha | ha
  · rcases placeNode_box_origin fuel p s x y parent initial final h b hb with hb | hb
    · exact hi a ha b hb hne hae hbe
    · exact hcross a ha hae b hb
  · rcases placeNode_box_origin fuel p s x y parent initial final h b hb with hb | hb
    · have hd := hcross b hb hbe a ha
      unfold Disjoint Rect.meetsInterior at hd ⊢
      omega
    · exact ha.exclusive_disjoint hg b hb hne hae hbe

theorem addRule_exclusive_separated (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State)
    (hi : ExclusiveSeparated state) :
    ExclusiveSeparated (addRule p rule s g y state) := by
  unfold addRule
  split
  · exact hi
  · intro a ha b hb hne hae hbe
    simp only [List.mem_append, List.mem_singleton] at ha hb
    rcases ha with ha | rfl
    · rcases hb with hb | rfl
      · exact hi a ha b hb hne hae hbe
      · cases hbe
    · cases hae

/-- Earlier rules end at or above the next rule's origin. Thus all boxes in
the new definition subtree are separated from the previous stage, without
using source ids or assuming the completed scene is valid. -/
theorem previous_stage_definition_disjoint (p : Profile) (s : Shape)
    (title : Int) (before : RuleState) (parent : String)
    (hg : Geometry s) (ht : 0 ≤ title) (hi : StageBounds p before)
    (old : Box) (ho : old ∈ before.state.boxes) (box : Box)
    (hb : PlacedBox s
      (constant p "margin"+(ruleGeometry p s title).defX)
      (before.y+(ruleGeometry p s title).defY) parent box) :
    Disjoint old.rect box.rect := by
  have hOld := hi.2.2 old ho
  have hNew := Rect.Contained.trans
    (rule_contains_definition p s title before.y ht)
    (descendant_contained hb.descendant hg)
  unfold StageFrame Rect.Contained at hOld
  unfold ruleFrame Rect.Contained at hNew
  unfold Disjoint Rect.meetsInterior
  dsimp only at *
  omega

theorem placeRule_exclusive_separated (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : StageBounds m.profile before)
    (hsep : ExclusiveSeparated before.state)
    (h : placeRule m metric before rule = .ok after) :
    ExclusiveSeparated after.state := by
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
          have hplaced := placeNode_exclusive_separated _ _ _ _ _ _ _ _ hg
            (addRule_exclusive_separated _ _ _ _ _ _ hsep) ?_ hp
          · dsimp only [g] at hp
            simp only [hp, pure, Except.pure, Except.ok.injEq] at h
            subst after
            exact hplaced
          · intro old ho hex box hb
            unfold addRule at ho
            split at ho
            · exact previous_stage_definition_disjoint m.profile s title before
                rule.id hg hn hi old ho box hb
            · simp only [List.mem_append, List.mem_singleton] at ho
              rcases ho with ho | rfl
              · exact previous_stage_definition_disjoint m.profile s title before
                  rule.id hg hn hi old ho box hb
              · cases hex

theorem layout_exclusive_separated (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) : Validator.C2 scene.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hi : StageBounds m.profile
          ({y := constant m.profile "margin"} : RuleState) ∧
          ExclusiveSeparated
            ({y := constant m.profile "margin"} : RuleState).state :=
        ⟨initial_stage_bounds m.profile, by intro a ha; cases ha⟩
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => StageBounds m.profile state ∧ ExclusiveSeparated state.state)
        (fun rule before after hi he =>
          ⟨placeRule_stage_bounds m metric before after rule hi.1 he,
            placeRule_exclusive_separated m metric before after rule hi.1 hi.2 he⟩)
        rules _ result hi hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           intro a ha b hb hne hae hbe _
           exact hinv.2 a ha b hb
             (fun he => hne (congrArg Box.id he)) hae hbe)

theorem successful_adapter_origin (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    ∃ rules scene, Kinds.Railroad.lower m = .ok rules ∧
      layout m rules = .ok scene ∧ result.scene.layoutDump = scene.layoutDump := by
  by_cases hn : m.boxes.length > m.options.limits.maxNodes
  · simp [Kinds.Railroad.layout, hn, bind, Except.bind] at h
  by_cases he : m.routes.length > m.options.limits.maxEdges
  · simp [Kinds.Railroad.layout, hn, he, bind, Except.bind] at h
  by_cases ht : Kinds.Railroad.textBytes m > m.options.limits.maxTextBytes
  · simp [Kinds.Railroad.layout, hn, he, ht, bind, Except.bind] at h
  by_cases hc : (m.routes.any (fun r => m.boxes.any (fun b => b.id == r.id))) = true
  · simp [Kinds.Railroad.layout, hn, he, ht, hc, bind, Except.bind] at h
  simp only [Kinds.Railroad.layout, hn, he, ht, hc, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind] at h
  cases hl : Kinds.Railroad.lower m with
  | error e => simp [hl, Except.mapError] at h
  | ok rules =>
    cases hs : layout m rules with
    | error e => simp [hl, hs, Except.mapError] at h
    | ok scene =>
      simp only [hl, hs, Except.mapError, pure, Except.pure,
        Except.ok.injEq] at h
      subst result
      exact ⟨rules, scene, rfl, hs, Scene.projectCellAttachments_layoutDump _ _⟩

theorem railroad_canvas (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_canvas m rules scene hs

theorem railroad_exclusive_separated (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_exclusive_separated m rules scene hs

def ParentsContained (state : State) : Prop :=
  ∀ box ∈ state.boxes, box.parent ≠ "" →
    ∃ enclosing ∈ state.boxes, enclosing.id = box.parent ∧
      enclosing.rect.Contained box.rect

theorem placeNode_parents_contained (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hg : Geometry s) (hi : ParentsContained initial)
    (hparent : parent ≠ "" → ∃ enclosing ∈ initial.boxes,
      enclosing.id = parent ∧ enclosing.rect.Contained (shapeRect s x y))
    (h : placeNode fuel p s x y parent initial = .ok final) :
    ParentsContained final := by
  intro box hb hnonempty
  have hext := placeNode_extends_boxes fuel p s x y parent initial final h
  by_cases hold : box ∈ initial.boxes
  · obtain ⟨enclosing, he, hid, hc⟩ := hi box hold hnonempty
    exact ⟨enclosing, hext.mem enclosing he, hid, hc⟩
  · rcases placeNode_new_parent_member fuel p s x y parent initial final
        hg h box hb hold with ⟨hp, hc⟩ | ⟨enclosing, he, hid, hc⟩
    · obtain ⟨enclosing, he, hid, hroot⟩ :=
        hparent (by simpa only [← hp] using hnonempty)
      exact ⟨enclosing, hext.mem enclosing he, hid.trans hp.symm,
        Rect.Contained.trans hroot hc⟩
    · exact ⟨enclosing, he, hid.symm, hc⟩

theorem addRule_parents_contained (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State) (hi : ParentsContained state) :
    ParentsContained (addRule p rule s g y state) := by
  unfold addRule
  split
  · exact hi
  · intro box hb hn
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · obtain ⟨enclosing, he, hid, hc⟩ := hi box hb hn
      exact ⟨enclosing, List.mem_append_left _ he, hid, hc⟩
    · exact False.elim (hn rfl)

theorem placeRule_parents_contained (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : ParentsContained before.state)
    (h : placeRule m metric before rule = .ok after) :
    ParentsContained after.state := by
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
          have hplaced := placeNode_parents_contained _ _ _ _ _ _ _ _ hg
            (addRule_parents_contained _ _ _ _ _ _ hi) ?_ hp
          · dsimp only [g] at hp
            simp only [hp, pure, Except.pure, Except.ok.injEq] at h
            subst after
            exact hplaced
          · intro hne
            refine ⟨Box.mk rule.id "group" (ruleFrame m.profile g before.y) "" false,
              ?_, rfl, rule_contains_definition m.profile s title before.y hn⟩
            simp [addRule, hne]

theorem railroad_orthogonal (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C4 result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_orthogonal m rules scene hs

theorem layout_parent_witness (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) :
    ∀ box ∈ scene.boxes, box.parent ≠ "" →
      ∃ enclosing ∈ scene.boxes, enclosing.id = box.parent ∧
        enclosing.rect.Contained box.rect := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => ParentsContained state.state)
        (fun rule before after hi he =>
          placeRule_parents_contained m metric before after rule hi he)
        rules _ result (by intro box hb; cases hb) hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           exact hinv)

theorem ConsecutiveJoins.at (up gap : Int) :
    ∀ (pairs : List (Shape × Point)), ConsecutiveJoins up gap pairs →
      ∀ (i : Nat) (a b : Shape × Point),
        pairs[i]? = some a → pairs[i+1]? = some b → Joined up gap a b := by
  intro pairs
  induction pairs with
  | nil => intro _ i a b ha; simp at ha
  | cons first tail ih =>
    intro hj i a b ha hb
    cases tail with
    | nil =>
      cases i <;> simp at hb
    | cons second rest =>
      obtain ⟨hfirst, hrest⟩ := hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        simp only [Nat.zero_add, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.some.injEq] at hb
        subst a
        subst b
        exact hfirst
      | succ i =>
        exact ih hrest i a b ha hb

theorem Joined.endpoint_boundaries {up gap : Int} {a b : Shape × Point}
    (h : Joined up gap a b) (ha : Nonnegative a.1) (hb : Nonnegative b.1)
    (x y : Int) :
    Validator.onBoundary ⟨x+a.2.x+a.1.w,y+up⟩
        (shapeRect a.1 (x+a.2.x) (y+a.2.y)) ∧
      Validator.onBoundary ⟨x+b.2.x,y+up⟩
        (shapeRect b.1 (x+b.2.x) (y+b.2.y)) := by
  unfold Joined at h
  unfold Nonnegative at ha hb
  unfold Validator.onBoundary shapeRect Shape.height
  dsimp only at *
  constructor <;> omega

theorem sequenceLayout_endpoint_boundaries (p : Profile) (kids : List Shape)
    (hk : ∀ kid ∈ kids, Nonnegative kid)
    (i : Nat) (a b : Shape × Point)
    (ha : (kids.zip (sequenceLayout
      (kids.foldl (fun n kid => max n kid.up) 0) (constant p "hsep") 0 kids).2)[i]? =
        some a)
    (hb : (kids.zip (sequenceLayout
      (kids.foldl (fun n kid => max n kid.up) 0) (constant p "hsep") 0 kids).2)[i+1]? =
        some b)
    (x y : Int) :
    Validator.onBoundary
        ⟨x+a.2.x+a.1.w,y+kids.foldl (fun n kid => max n kid.up) 0⟩
        (shapeRect a.1 (x+a.2.x) (y+a.2.y)) ∧
      Validator.onBoundary
        ⟨x+b.2.x,y+kids.foldl (fun n kid => max n kid.up) 0⟩
        (shapeRect b.1 (x+b.2.x) (y+b.2.y)) := by
  have hj := ConsecutiveJoins.at _ _
    _ (sequence_all_rail_joins _ _ kids 0) i a b ha hb
  exact hj.endpoint_boundaries
    (hk a.1 (List.of_mem_zip (List.mem_of_getElem? ha)).1)
    (hk b.1 (List.of_mem_zip (List.mem_of_getElem? hb)).1) x y

def SequenceRoute (s : Shape) (x y : Int) (route : Route) : Prop :=
  ∃ i ∈ List.range (s.children.length-1),
    route.fromId = s.children[i]!.id ∧
    route.toId = s.children[i+1]!.id ∧
    route.points = [⟨x+s.offsets[i]!.x+s.children[i]!.w,y+s.up⟩,
      ⟨x+s.offsets[i+1]!.x,y+s.up⟩]

theorem foldl_preserves_members {α β : Type} (f : β → α → β) (P : β → Prop)
    (xs : List α)
    (step : ∀ a ∈ xs, ∀ before, P before → P (f before a))
    (initial : β) (hi : P initial) : P (xs.foldl f initial) := by
  induction xs generalizing initial with
  | nil => exact hi
  | cons a tail ih =>
    exact ih (fun b hb => step b (List.mem_cons_of_mem a hb))
      (f initial a) (step a List.mem_cons_self initial hi)

theorem sequenceJoins_route_origin (s : Shape) (x y : Int) (initial : State) :
    ∀ route ∈ (sequenceJoins s x y initial).routes,
      route ∈ initial.routes ∨ SequenceRoute s x y route := by
  unfold sequenceJoins
  apply foldl_preserves_members _ (fun state : State =>
    ∀ route ∈ state.routes, route ∈ initial.routes ∨ SequenceRoute s x y route)
  · intro i hi before hb route hr
    simp only [joinStep, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hb route hr
    · exact Or.inr ⟨i, hi, rfl, rfl, rfl⟩
  · intro route hr
    exact Or.inl hr

inductive PlacedRoute : Shape → Int → Int → Route → Prop where
  | sequence {s : Shape} {x y : Int} {route : Route}
      (hk : s.kind = "sequence") (hr : SequenceRoute s x y route) :
      PlacedRoute s x y route
  | child {s : Shape} {x y : Int} {route : Route}
      (pair : Shape × Point) (hp : pair ∈ s.children.zip s.offsets)
      (hn : leaf s.kind = false)
      (hr : PlacedRoute pair.1 (x+pair.2.x) (y+pair.2.y) route) :
      PlacedRoute s x y route

theorem placeNode_route_origin :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      ∀ route ∈ final.routes, route ∈ initial.routes ∨ PlacedRoute s x y route := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final h
    let P := fun state : State =>
      ∀ route ∈ state.routes, route ∈ initial.routes ∨ PlacedRoute s x y route
    simp only [placeNode] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst final
      intro route hr
      exact Or.inl hr
    · apply foldlM_preserves_mem _ P _ ?_ _ final ?_ h
      · intro pair hp before after hb he route hr
        rcases ih p pair.1 (x+pair.2.x) (y+pair.2.y) s.id before after he route hr with
          hold | hnew
        · exact hb route hold
        · exact Or.inr (.child pair hp (by simp_all) hnew)
      · split
        · intro route hr
          rcases sequenceJoins_route_origin s x y _ route hr with hold | hnew
          · exact Or.inl hold
          · exact Or.inr (.sequence (by simp_all) hnew)
        · intro route hr
          exact Or.inl hr

theorem SequenceRoute.sequence_endpoint_boxes (p : Profile) (node : Node)
    (kids : List Shape) (hk : ∀ kid ∈ kids, Nonnegative kid)
    (hkind : node.kind = "sequence") (x y : Int) (parent : String) (route : Route)
    (hr : SequenceRoute (sequenceShape p node kids) x y route) :
    ∃ a b, PlacedBox (sequenceShape p node kids) x y parent a ∧
      PlacedBox (sequenceShape p node kids) x y parent b ∧
      a.id = route.fromId ∧ b.id = route.toId ∧
      ∃ first last, route.points.head? = some first ∧
        route.points.getLast? = some last ∧
        Validator.onBoundary first a.rect ∧ Validator.onBoundary last b.rect := by
  obtain ⟨i, hi, hfrom, hto, hpoints⟩ := hr
  have hi' : i < kids.length-1 := by simpa [sequenceShape] using hi
  have hi0 : i < kids.length := by omega
  have hi1 : i+1 < kids.length := by omega
  let up := kids.foldl (fun n kid => max n kid.up) 0
  let offsets := (sequenceLayout up (constant p "hsep") 0 kids).2
  have hlen : offsets.length = kids.length := sequence_offsets_length _ _ _ _
  have ho0 : i < offsets.length := by omega
  have ho1 : i+1 < offsets.length := by omega
  have hget0 : kids[i]? = some kids[i]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi0]
  have hget1 : kids[i+1]? = some kids[i+1]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
  have hoff0 : offsets[i]? = some offsets[i]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ho0]
  have hoff1 : offsets[i+1]? = some offsets[i+1]! := by
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ho1]
  have hzip0 : (kids.zip offsets)[i]? = some (kids[i]!, offsets[i]!) :=
    List.getElem?_zip_eq_some.mpr ⟨hget0, hoff0⟩
  have hzip1 : (kids.zip offsets)[i+1]? = some (kids[i+1]!, offsets[i+1]!) :=
    List.getElem?_zip_eq_some.mpr ⟨hget1, hoff1⟩
  let a := Box.mk kids[i]!.id (if leaf kids[i]!.kind then "node" else "group")
    (shapeRect kids[i]! (x+offsets[i]!.x) (y+offsets[i]!.y))
    node.id (leaf kids[i]!.kind)
  let b := Box.mk kids[i+1]!.id (if leaf kids[i+1]!.kind then "node" else "group")
    (shapeRect kids[i+1]! (x+offsets[i+1]!.x) (y+offsets[i+1]!.y))
    node.id (leaf kids[i+1]!.kind)
  have hnonleaf : leaf (sequenceShape p node kids).kind = false := by
    simp [sequenceShape, hkind, leaf]
  have ha : PlacedBox (sequenceShape p node kids) x y parent a :=
    .child (kids[i]!,offsets[i]!)
      (List.mem_of_getElem? hzip0) hnonleaf (.root _ _ _ _)
  have hb : PlacedBox (sequenceShape p node kids) x y parent b :=
    .child (kids[i+1]!,offsets[i+1]!)
      (List.mem_of_getElem? hzip1) hnonleaf (.root _ _ _ _)
  have hbound := sequenceLayout_endpoint_boundaries p kids hk i _ _ hzip0 hzip1 x y
  refine ⟨a, b, ha, hb, hfrom.symm, hto.symm,
    ⟨x+offsets[i]!.x+kids[i]!.w,y+up⟩,
    ⟨x+offsets[i+1]!.x,y+up⟩, ?_, ?_, hbound.1, hbound.2⟩
  · simp [hpoints, sequenceShape, offsets, up]
  · simp [hpoints, sequenceShape, offsets, up]

theorem measure_sequence_shape (fuel : Nat) (p : Profile) (metric : Measure.Metric)
    (node : Node) (shape : Shape)
    (hm : measure (fuel+1) p metric node = .ok shape)
    (hk : shape.kind = "sequence") :
    ∃ kids, node.children.mapM (measure fuel p metric) = .ok kids ∧
      shape = sequenceShape p node kids ∧ node.kind = "sequence" := by
  simp only [measure] at hm
  cases hc : node.children.mapM (measure fuel p metric) with
  | error e => simp [hc, bind, Except.bind] at hm
  | ok kids =>
    simp only [hc, bind, Except.bind] at hm
    have hn : node.kind = "sequence" :=
      (size_metadata p metric node kids shape hm).2.1.symm.trans hk
    have hraw := size_raw_of_ok p metric node kids shape hm
    have he : shape = sequenceShape p node kids := by
      unfold sizeRaw at hraw
      simp [hn, leaf] at hraw
      split at hraw
      · cases hraw
      · exact (Except.ok.inj hraw).symm
    exact ⟨kids, rfl, he, hn⟩

theorem placedRoute_endpoint_boxes :
    ∀ (fuel : Nat) (p : Profile) (metric : Measure.Metric)
      (node : Node) (shape : Shape) (x y : Int) (parent : String) (route : Route),
      measure fuel p metric node = .ok shape →
      PlacedRoute shape x y route →
      ∃ a b, PlacedBox shape x y parent a ∧ PlacedBox shape x y parent b ∧
        a.id = route.fromId ∧ b.id = route.toId ∧
        ∃ first last, route.points.head? = some first ∧
          route.points.getLast? = some last ∧
          Validator.onBoundary first a.rect ∧ Validator.onBoundary last b.rect := by
  intro fuel
  induction fuel with
  | zero => intro p metric node shape x y parent route hm _; cases hm
  | succ fuel ih =>
    intro p metric node shape x y parent route hm hr
    cases hr with
    | sequence hk hr =>
      obtain ⟨kids, hc, he, hn⟩ :=
        measure_sequence_shape fuel p metric node shape hm hk
      have hkids := mapM_nonnegative (measure fuel p metric)
        (fun n s h => railroad_box_nonneg fuel p metric n s h)
        node.children kids hc
      subst shape
      exact SequenceRoute.sequence_endpoint_boxes p node kids hkids hn x y parent route hr
    | child pair hp hn hr =>
      obtain ⟨child, hc, hmchild⟩ :=
        measure_child_origin fuel p metric node shape pair.1 hm
          (List.of_mem_zip hp).1
      obtain ⟨a, b, ha, hb, hidA, hidB, first, last, hf, hl, hba, hbb⟩ :=
        ih p metric child pair.1 (x+pair.2.x) (y+pair.2.y) shape.id route hmchild hr
      exact ⟨a, b, .child pair hp hn ha, .child pair hp hn hb,
        hidA, hidB, first, last, hf, hl, hba, hbb⟩

theorem placeNode_new_route_endpoints (measureFuel placeFuel : Nat)
    (p : Profile) (metric : Measure.Metric) (node : Node) (shape : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hm : measure measureFuel p metric node = .ok shape)
    (hp : placeNode placeFuel p shape x y parent initial = .ok final)
    (route : Route) (hr : route ∈ final.routes) (hnew : route ∉ initial.routes) :
    ∃ a ∈ final.boxes, ∃ b ∈ final.boxes,
      a.id = route.fromId ∧ b.id = route.toId ∧
      ∃ first last, route.points.head? = some first ∧
        route.points.getLast? = some last ∧
        Validator.onBoundary first a.rect ∧ Validator.onBoundary last b.rect := by
  rcases placeNode_route_origin placeFuel p shape x y parent initial final hp route hr with
    hold | hplaced
  · exact False.elim (hnew hold)
  · obtain ⟨a, b, ha, hb, hidA, hidB, first, last, hf, hl, hba, hbb⟩ :=
      placedRoute_endpoint_boxes measureFuel p metric node shape x y parent route hm hplaced
    exact ⟨a, placeNode_address_mem placeFuel p shape x y parent initial final hp a ha,
      b, placeNode_address_mem placeFuel p shape x y parent initial final hp b hb,
      hidA, hidB, first, last, hf, hl, hba, hbb⟩

def EndpointsPresent (state : State) : Prop :=
  ∀ route ∈ state.routes, ∃ a ∈ state.boxes, ∃ b ∈ state.boxes,
    a.id = route.fromId ∧ b.id = route.toId ∧
    ∃ first last, route.points.head? = some first ∧
      route.points.getLast? = some last ∧
      Validator.onBoundary first a.rect ∧ Validator.onBoundary last b.rect

theorem placeNode_endpoints_present (measureFuel placeFuel : Nat)
    (p : Profile) (metric : Measure.Metric) (node : Node) (shape : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hm : measure measureFuel p metric node = .ok shape)
    (hp : placeNode placeFuel p shape x y parent initial = .ok final)
    (hi : EndpointsPresent initial) : EndpointsPresent final := by
  intro route hr
  by_cases hold : route ∈ initial.routes
  · obtain ⟨a, ha, b, hb, hidA, hidB, first, last, hf, hl, hba, hbb⟩ :=
      hi route hold
    have hext := placeNode_extends_boxes placeFuel p shape x y parent initial final hp
    exact ⟨a, hext.mem a ha, b, hext.mem b hb,
      hidA, hidB, first, last, hf, hl, hba, hbb⟩
  · exact placeNode_new_route_endpoints measureFuel placeFuel p metric node shape
      x y parent initial final hm hp route hr hold

theorem addRule_endpoints_present (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State) (hi : EndpointsPresent state) :
    EndpointsPresent (addRule p rule s g y state) := by
  unfold addRule
  split
  · exact hi
  · intro route hr
    obtain ⟨a, ha, b, hb, hidA, hidB, first, last, hf, hl, hba, hbb⟩ := hi route hr
    exact ⟨a, List.mem_append_left _ ha, b, List.mem_append_left _ hb,
      hidA, hidB, first, last, hf, hl, hba, hbb⟩

theorem placeRule_endpoints_present (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : EndpointsPresent before.state)
    (h : placeRule m metric before rule = .ok after) :
    EndpointsPresent after.state := by
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
          have hplaced := placeNode_endpoints_present _ _ _ _ _ _ _ _ _ _ _ hs hp
            (addRule_endpoints_present _ _ _ _ _ _ hi)
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          exact hplaced

theorem layout_endpoint_witnesses (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) :
    ∀ route ∈ scene.routes, ∃ a ∈ scene.boxes, ∃ b ∈ scene.boxes,
      a.id = route.fromId ∧ b.id = route.toId ∧
      ∃ first last, route.points.head? = some first ∧
        route.points.getLast? = some last ∧
        Validator.onBoundary first a.rect ∧ Validator.onBoundary last b.rect := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => EndpointsPresent state.state)
        (fun rule before after hi he =>
          placeRule_endpoints_present m metric before after rule hi he)
        rules _ result (by intro route hr; cases hr) hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           exact hinv)

theorem model_box_id_injective (m : Model) (hwf : WellFormed m) :
    ∀ a ∈ m.boxes, ∀ b ∈ m.boxes, a.id = b.id → a = b := by
  have hids := Model.boxIds_nodup hwf
  generalize m.boxes = boxes at *
  clear hwf m
  induction boxes with
  | nil => intro a ha; cases ha
  | cons head tail ih =>
    have hparts := List.nodup_cons.mp hids
    intro a ha b hb hid
    rcases List.mem_cons.mp ha with heA | haTail
    · subst a
      rcases List.mem_cons.mp hb with heB | hbTail
      · exact heB.symm
      · exact False.elim (hparts.1
          (by change head.id ∈ tail.map (·.id)
              rw [hid]
              exact List.mem_map_of_mem hbTail))
    · rcases List.mem_cons.mp hb with heB | hbTail
      · subst b
        exact False.elim (hparts.1
          (by change head.id ∈ tail.map (·.id)
              rw [← hid]
              exact List.mem_map_of_mem haTail))
      · exact ih hparts.2 a haTail b hbTail hid

theorem decodeNode_child_source (fuel : Nat) (m : Model) (hwf : WellFormed m)
    (source childSource : ModelBox) (node child : Node)
    (hchildSource : childSource ∈ m.boxes)
    (h : Kinds.Railroad.decodeNode (fuel+1) m source = .ok node)
    (hc : child ∈ node.children) (hid : child.id = childSource.id) :
    childSource.parent = source.id ∧
      Kinds.Railroad.decodeNode fuel m childSource = .ok child := by
  obtain ⟨original, ho, hp, he, hd⟩ :=
    decodeNode_child_origin fuel m source node child h hc
  have heq := model_box_id_injective m hwf original ho childSource hchildSource
    (he.symm.trans hid)
  subst original
  exact ⟨hp, hd⟩

theorem mapM_success_call {α β : Type} (f : α → Except LayoutError β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ∀ x ∈ xs, ∃ y, f x = .ok y := by
  intro xs
  induction xs with
  | nil => intro ys h x hx; cases hx
  | cons first tail ih =>
    intro ys h x hx
    cases hf : f first with
    | error e => simp [List.mapM_cons, hf, bind, Except.bind] at h
    | ok value =>
      cases ht : tail.mapM f with
      | error e => simp [List.mapM_cons, hf, ht, bind, Except.bind] at h
      | ok rest =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨value, hf⟩
        · exact ih rest ht x hx

theorem decodeNode_source_child_success (fuel : Nat) (m : Model)
    (source child : ModelBox) (node : Node)
    (h : Kinds.Railroad.decodeNode (fuel+1) m source = .ok node)
    (hc : child ∈ Kinds.Railroad.children m source.id) :
    ∃ decoded, Kinds.Railroad.decodeNode fuel m child = .ok decoded := by
  simp only [Kinds.Railroad.decodeNode] at h
  cases hk : (Kinds.Railroad.children m source.id).mapM
      (Kinds.Railroad.decodeNode fuel m) with
  | error e => simp [hk, bind, Except.bind] at h
  | ok kids => exact mapM_success_call _ _ _ hk child hc

/-- Finite successful decoding rules out a cycle in the source-parent graph.
The inductive step rotates the alleged cycle to the child whose decoder
actually ran with one less unit of fuel. No input-normalization premise or
independently postulated rank is needed. -/
theorem decodeNode_no_cycle :
    ∀ (fuel : Nat) (m : Model) (source : ModelBox) (node : Node),
      Kinds.Railroad.decodeNode fuel m source = .ok node →
      ∀ child ∈ Kinds.Railroad.children m source.id,
        SourceDescendant m child source → False := by
  intro fuel
  induction fuel with
  | zero => intro m source node h; cases h
  | succ fuel ih =>
    intro m source node h child hc hpath
    obtain ⟨decoded, hd⟩ := decodeNode_source_child_success fuel m source child node h hc
    cases hpath with
    | root =>
      exact ih m source decoded hd source hc (.root source)
    | @child _ next _ hn hp hrest =>
      have hnext : next ∈ Kinds.Railroad.children m child.id :=
        List.mem_filter.mpr ⟨hn, by simpa using hp⟩
      have hsourceChild := List.mem_filter.mp hc
      have hback : SourceDescendant m source child :=
        .child hsourceChild.1 (by simpa using hsourceChild.2) (.root child)
      exact ih m child decoded hd next hnext (hrest.trans hback)

theorem SourceDescendant.snoc {m : Model} {root previous child : ModelBox}
    (h : SourceDescendant m root previous) (hc : child ∈ m.boxes)
    (hp : child.parent = previous.id) : SourceDescendant m root child :=
  h.trans (.child hc hp (.root child))

theorem SourceDescendant.predecessor {m : Model} {root target : ModelBox}
    (h : SourceDescendant m root target) (hr : root ∈ m.boxes) :
    root = target ∨ ∃ previous ∈ m.boxes,
      SourceDescendant m root previous ∧ target.parent = previous.id := by
  revert hr
  induction h with
  | root => intro _; exact Or.inl rfl
  | @child root child target hc hp hd ih =>
    intro hr
    rcases ih hc with he | ⟨previous, hm, hpath, hparent⟩
    · subst target
      exact Or.inr ⟨root, hr, .root root, hp⟩
    · exact Or.inr ⟨previous, hm, .child hc hp hpath, hparent⟩

theorem SourceDescendant.reverse_induction {m : Model} {root target : ModelBox}
    (h : SourceDescendant m root target) (P : ModelBox → Prop)
    (base : P root)
    (step : ∀ previous child, child ∈ m.boxes →
      child.parent = previous.id → P previous → P child) : P target := by
  revert base
  induction h with
  | root => intro base; exact base
  | @child root child target hc hp hd ih =>
    intro base
    exact ih (step root child hc hp base)

/-- Distinct immediate source children cannot be ancestors of one another.
An alleged path's last parent is the common source by unique model ids, so
it would close a cycle already excluded by successful decoding. -/
theorem decodeNode_children_not_descendants (fuel : Nat) (m : Model)
    (hwf : WellFormed m) (source a b : ModelBox) (node : Node)
    (hs : source ∈ m.boxes)
    (h : Kinds.Railroad.decodeNode fuel m source = .ok node)
    (ha : a ∈ Kinds.Railroad.children m source.id)
    (hb : b ∈ Kinds.Railroad.children m source.id) (hne : a ≠ b) :
    ¬ SourceDescendant m a b := by
  intro hpath
  have hma := List.mem_filter.mp ha
  have hmb := List.mem_filter.mp hb
  rcases hpath.predecessor hma.1 with he | ⟨previous, hp, hprefix, hparent⟩
  · exact hne he
  · have hid : previous.id = source.id := by
      have hbp : b.parent = source.id := by simpa using hmb.2
      exact hparent.symm.trans hbp
    have heq := model_box_id_injective m hwf previous hp source hs hid
    subst previous
    exact decodeNode_no_cycle fuel m source node h a ha hprefix

theorem decodeNode_child_subtrees_disjoint (fuel : Nat) (m : Model)
    (hwf : WellFormed m) (source a b target : ModelBox) (node : Node)
    (hs : source ∈ m.boxes)
    (h : Kinds.Railroad.decodeNode fuel m source = .ok node)
    (ha : a ∈ Kinds.Railroad.children m source.id)
    (hb : b ∈ Kinds.Railroad.children m source.id) (hne : a ≠ b)
    (hA : SourceDescendant m a target) (hB : SourceDescendant m b target) : False := by
  have hma := (List.mem_filter.mp ha).1
  have hmb := (List.mem_filter.mp hb).1
  have hbase : ¬ SourceDescendant m b a :=
    decodeNode_children_not_descendants fuel m hwf source b a node hs h hb ha
      (Ne.symm hne)
  have hinv : SourceDescendant m a target ∧ ¬ SourceDescendant m b target := by
    apply hA.reverse_induction
      (fun current => SourceDescendant m a current ∧ ¬ SourceDescendant m b current)
      ⟨.root a, hbase⟩
    intro previous child hc hp hi
    have hnew := hi.1.snoc hc hp
    refine ⟨hnew, ?_⟩
    intro hother
    rcases hother.predecessor hmb with he | ⟨parent, hm, hprefix, hparent⟩
    · have hab : SourceDescendant m a b := by simpa only [← he] using hnew
      exact decodeNode_children_not_descendants fuel m hwf source a b node
        hs h ha hb hne hab
    · have heq := model_box_id_injective m hwf parent hm previous
        (hi.1.member hma) (hparent.symm.trans hp)
      subst parent
      exact hi.2 hprefix
  exact hinv.2 hB

theorem mapM_keys {α β κ : Type} (f : α → Except LayoutError β)
    (inputKey : α → κ) (outputKey : β → κ)
    (hkey : ∀ a b, f a = .ok b → outputKey b = inputKey a) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ys.map outputKey = xs.map inputKey := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst ys
    rfl
  | cons a tail ih =>
    intro ys h
    cases ha : f a with
    | error e => simp [List.mapM_cons, ha, bind, Except.bind] at h
    | ok b =>
      cases ht : tail.mapM f with
      | error e => simp [List.mapM_cons, ha, ht, bind, Except.bind] at h
      | ok rest =>
        simp only [List.mapM_cons, ha, ht, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq] at h
        subst ys
        simp only [List.map_cons, hkey a b ha, ih rest ht]

theorem decodeNode_children_ids (fuel : Nat) (m : Model) (source : ModelBox)
    (node : Node) (h : Kinds.Railroad.decodeNode (fuel+1) m source = .ok node) :
    node.children.map (·.id) = (Kinds.Railroad.children m source.id).map (·.id) := by
  simp only [Kinds.Railroad.decodeNode] at h
  cases hc : (Kinds.Railroad.children m source.id).mapM
      (Kinds.Railroad.decodeNode fuel m) with
  | error e => simp [hc, bind, Except.bind] at h
  | ok kids =>
    simp only [hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst node
    exact mapM_keys (Kinds.Railroad.decodeNode fuel m) (·.id) (·.id)
      (fun source node hd => (decodeNode_metadata fuel m source node hd).1) _ _ hc

theorem measure_id (fuel : Nat) (p : Profile) (metric : Measure.Metric)
    (node : Node) (shape : Shape) (h : measure fuel p metric node = .ok shape) :
    shape.id = node.id := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    simp only [measure] at h
    cases hc : node.children.mapM (measure fuel p metric) with
    | error e => simp [hc, bind, Except.bind] at h
    | ok kids =>
      simp only [hc, bind, Except.bind] at h
      exact (size_metadata p metric node kids shape h).1

theorem measure_children_ids (fuel : Nat) (p : Profile) (metric : Measure.Metric)
    (node : Node) (shape : Shape) (h : measure (fuel+1) p metric node = .ok shape) :
    shape.children.map (·.id) = node.children.map (·.id) := by
  simp only [measure] at h
  cases hc : node.children.mapM (measure fuel p metric) with
  | error e => simp [hc, bind, Except.bind] at h
  | ok kids =>
    simp only [hc, bind, Except.bind] at h
    rw [(size_metadata p metric node kids shape h).2.2]
    exact mapM_keys (measure fuel p metric) (·.id) (·.id)
      (fun node shape hm => measure_id fuel p metric node shape hm) _ _ hc

theorem measured_children_ids_nodup (decodeFuel measureFuel : Nat) (m : Model)
    (hwf : WellFormed m) (source : ModelBox) (node : Node) (shape : Shape)
    (metric : Measure.Metric)
    (hd : Kinds.Railroad.decodeNode decodeFuel m source = .ok node)
    (hm : measure measureFuel m.profile metric node = .ok shape) :
    (shape.children.map (·.id)).Nodup := by
  cases decodeFuel with
  | zero => cases hd
  | succ decodeFuel =>
    cases measureFuel with
    | zero => cases hm
    | succ measureFuel =>
      rw [measure_children_ids measureFuel m.profile metric node shape hm,
        decodeNode_children_ids decodeFuel m source node hd]
      exact List.Nodup.sublist
        (List.Sublist.map (fun b : ModelBox => b.id) List.filter_sublist)
        (Model.boxIds_nodup hwf)

theorem zipped_shape_id_injective :
    ∀ (kids : List Shape) (offsets : List Point),
      (kids.map (·.id)).Nodup →
      ∀ a ∈ kids.zip offsets, ∀ b ∈ kids.zip offsets,
        a.1.id = b.1.id → a = b := by
  intro kids
  induction kids with
  | nil => intro offsets h a ha; cases ha
  | cons first tail ih =>
    intro offsets h a ha b hb hid
    cases offsets with
    | nil => cases ha
    | cons offset rest =>
      have hparts := List.nodup_cons.mp h
      rcases List.mem_cons.mp ha with heA | haTail
      · subst a
        rcases List.mem_cons.mp hb with heB | hbTail
        · exact heB.symm
        · have hm := List.mem_map_of_mem (f := fun s : Shape => s.id)
            (List.of_mem_zip hbTail).1
          exact False.elim (hparts.1 (by
            change first.id ∈ tail.map (·.id)
            have he : first.id = b.1.id := hid
            rw [he]
            exact hm))
      · rcases List.mem_cons.mp hb with heB | hbTail
        · subst b
          have hm := List.mem_map_of_mem (f := fun s : Shape => s.id)
            (List.of_mem_zip haTail).1
          exact False.elim (hparts.1 (by simpa only [hid] using hm))
        · exact ih rest hparts.2 a haTail b hbTail hid

theorem measured_pair_source (decodeFuel measureFuel : Nat) (m : Model)
    (source : ModelBox) (node : Node) (shape : Shape) (metric : Measure.Metric)
    (hd : Kinds.Railroad.decodeNode (decodeFuel+1) m source = .ok node)
    (hm : measure (measureFuel+1) m.profile metric node = .ok shape)
    (pair : Shape × Point) (hp : pair ∈ shape.children.zip shape.offsets) :
    ∃ childSource ∈ Kinds.Railroad.children m source.id, ∃ childNode,
      Kinds.Railroad.decodeNode decodeFuel m childSource = .ok childNode ∧
      measure measureFuel m.profile metric childNode = .ok pair.1 := by
  obtain ⟨childNode, hc, hmeasure⟩ :=
    measure_child_origin measureFuel m.profile metric node shape pair.1 hm
      (List.of_mem_zip hp).1
  obtain ⟨childSource, hs, hparent, _, hdecode⟩ :=
    decodeNode_child_origin decodeFuel m source node childNode hd hc
  exact ⟨childSource, List.mem_filter.mpr ⟨hs, by simpa using hparent⟩,
    childNode, hdecode, hmeasure⟩

theorem measured_child_descendant_ne_root (decodeFuel measureFuel : Nat)
    (m : Model) (hwf : WellFormed m) (source : ModelBox) (node : Node)
    (shape : Shape) (metric : Measure.Metric) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeNode (decodeFuel+1) m source = .ok node)
    (hm : measure (measureFuel+1) m.profile metric node = .ok shape)
    (pair : Shape × Point) (hp : pair ∈ shape.children.zip shape.offsets)
    (x y : Int) (box : Box)
    (hb : PlacedBox pair.1 (x+pair.2.x) (y+pair.2.y) shape.id box) :
    box.id ≠ shape.id := by
  intro hid
  obtain ⟨childSource, hc, childNode, hdecode, hmeasure⟩ :=
    measured_pair_source decodeFuel measureFuel m source node shape metric hd hm pair hp
  have hchild := (List.mem_filter.mp hc).1
  obtain ⟨original, ho, he, hpath⟩ :=
    placedBox_decoded_parent_origin decodeFuel measureFuel m childSource childNode
      pair.1 metric _ _ shape.id box hchild hdecode hmeasure hb
  have hroot : shape.id = source.id :=
    (measure_id (measureFuel+1) m.profile metric node shape hm).trans
      (decodeNode_metadata (decodeFuel+1) m source node hd).1
  have heq := model_box_id_injective m hwf original ho source hs
    (he.symm.trans (hid.trans hroot))
  subst original
  exact decodeNode_no_cycle (decodeFuel+1) m source node hd childSource hc hpath

theorem placedBox_id_injective :
    ∀ (measureFuel decodeFuel : Nat) (m : Model) (_hwf : WellFormed m)
      (source : ModelBox) (node : Node) (shape : Shape) (metric : Measure.Metric)
      (x y : Int) (parent : String),
      source ∈ m.boxes →
      Kinds.Railroad.decodeNode decodeFuel m source = .ok node →
      measure measureFuel m.profile metric node = .ok shape →
      ∀ a b, PlacedBox shape x y parent a → PlacedBox shape x y parent b →
        a.id = b.id → a = b := by
  intro measureFuel
  induction measureFuel with
  | zero => intro decodeFuel m hwf source node shape metric x y parent hs hd hm; cases hm
  | succ measureFuel ih =>
    intro decodeFuel m hwf source node shape metric x y parent hs hd hm a b ha hb hid
    cases decodeFuel with
    | zero => cases hd
    | succ decodeFuel =>
      cases ha with
      | root =>
        cases hb with
        | root => rfl
        | child pair hp hn hb =>
          exact False.elim (measured_child_descendant_ne_root decodeFuel measureFuel
            m hwf source node shape metric hs hd hm pair hp x y b hb hid.symm)
      | child pairA hpA hnA ha =>
        cases hb with
        | root =>
          exact False.elim (measured_child_descendant_ne_root decodeFuel measureFuel
            m hwf source node shape metric hs hd hm pairA hpA x y a ha hid)
        | child pairB hpB hnB hb =>
          obtain ⟨sourceA, hsA, nodeA, hdA, hmA⟩ :=
            measured_pair_source decodeFuel measureFuel m source node shape metric hd hm pairA hpA
          obtain ⟨sourceB, hsB, nodeB, hdB, hmB⟩ :=
            measured_pair_source decodeFuel measureFuel m source node shape metric hd hm pairB hpB
          have hmemA := (List.mem_filter.mp hsA).1
          have hmemB := (List.mem_filter.mp hsB).1
          obtain ⟨originalA, hoA, heA, hpathA⟩ :=
            placedBox_decoded_parent_origin decodeFuel measureFuel m sourceA nodeA pairA.1
              metric _ _ shape.id a hmemA hdA hmA ha
          obtain ⟨originalB, hoB, heB, hpathB⟩ :=
            placedBox_decoded_parent_origin decodeFuel measureFuel m sourceB nodeB pairB.1
              metric _ _ shape.id b hmemB hdB hmB hb
          have heqOriginal := model_box_id_injective m hwf originalA hoA originalB hoB
            (heA.symm.trans (hid.trans heB))
          subst originalB
          have heqSource : sourceA = sourceB := by
            by_cases he : sourceA = sourceB
            · exact he
            · exact False.elim (decodeNode_child_subtrees_disjoint (decodeFuel+1) m hwf
                source sourceA sourceB originalA node hs hd hsA hsB he hpathA hpathB)
          subst sourceB
          have heqNode := Except.ok.inj (hdA.symm.trans hdB)
          subst nodeB
          have heqShape := Except.ok.inj (hmA.symm.trans hmB)
          have heqPair := zipped_shape_id_injective shape.children shape.offsets
            (measured_children_ids_nodup (decodeFuel+1) (measureFuel+1) m hwf
              source node shape metric hd hm)
            pairA hpA pairB hpB (congrArg Shape.id heqShape)
          subst pairB
          exact ih decodeFuel m hwf sourceA nodeA pairA.1 metric
            (x+pairA.2.x) (y+pairA.2.y) shape.id hmemA hdA hmA a b ha hb hid

theorem placeNode_new_id_injective (measureFuel decodeFuel placeFuel : Nat)
    (m : Model) (hwf : WellFormed m) (source : ModelBox) (node : Node)
    (shape : Shape) (metric : Measure.Metric) (x y : Int) (parent : String)
    (initial final : State) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeNode decodeFuel m source = .ok node)
    (hm : measure measureFuel m.profile metric node = .ok shape)
    (hp : placeNode placeFuel m.profile shape x y parent initial = .ok final)
    (a b : Box) (ha : a ∈ final.boxes) (hb : b ∈ final.boxes)
    (hna : a ∉ initial.boxes) (hnb : b ∉ initial.boxes)
    (hid : a.id = b.id) : a = b := by
  rcases placeNode_box_origin placeFuel m.profile shape x y parent initial final hp a ha with
    hold | hA
  · exact False.elim (hna hold)
  · rcases placeNode_box_origin placeFuel m.profile shape x y parent initial final hp b hb with
      hold | hB
    · exact False.elim (hnb hold)
    · exact placedBox_id_injective measureFuel decodeFuel m hwf source node shape metric
        x y parent hs hd hm a b hA hB hid

theorem decodeNode_source_descendant_success :
    ∀ (fuel : Nat) (m : Model) (source : ModelBox) (node : Node),
      Kinds.Railroad.decodeNode fuel m source = .ok node →
      ∀ target, SourceDescendant m source target →
        ∃ remaining decoded, Kinds.Railroad.decodeNode remaining m target = .ok decoded := by
  intro fuel
  induction fuel with
  | zero => intro m source node h; cases h
  | succ fuel ih =>
    intro m source node h target hpath
    cases hpath with
    | root => exact ⟨fuel+1, node, h⟩
    | @child _ child _ hc hp hrest =>
      have hchild : child ∈ Kinds.Railroad.children m source.id :=
        List.mem_filter.mpr ⟨hc, by simpa using hp⟩
      obtain ⟨decoded, hd⟩ :=
        decodeNode_source_child_success fuel m source child node h hchild
      exact ih m child decoded hd target hrest

theorem decodeNode_root_not_descendant (fuel : Nat) (m : Model)
    (a b : ModelBox) (node : Node) (ha : a ∈ m.boxes)
    (hpa : a.parent = "") (hpb : b.parent = "") (hne : a ≠ b)
    (hd : Kinds.Railroad.decodeNode fuel m a = .ok node) :
    ¬ SourceDescendant m a b := by
  intro hpath
  rcases hpath.predecessor ha with he | ⟨previous, hp, hprefix, hparent⟩
  · exact hne he
  · have hid : previous.id = "" := hparent.symm.trans hpb
    have hchild : a ∈ Kinds.Railroad.children m previous.id :=
      List.mem_filter.mpr ⟨ha, by simp [hpa, hid]⟩
    obtain ⟨remaining, decoded, hdecode⟩ :=
      decodeNode_source_descendant_success fuel m a node hd previous hprefix
    exact decodeNode_no_cycle remaining m previous decoded hdecode a hchild hprefix

theorem decodeNode_root_subtrees_disjoint (fuelA fuelB : Nat) (m : Model)
    (hwf : WellFormed m) (a b target : ModelBox) (nodeA nodeB : Node)
    (ha : a ∈ m.boxes) (hb : b ∈ m.boxes)
    (hpa : a.parent = "") (hpb : b.parent = "") (hne : a ≠ b)
    (hdA : Kinds.Railroad.decodeNode fuelA m a = .ok nodeA)
    (hdB : Kinds.Railroad.decodeNode fuelB m b = .ok nodeB)
    (hA : SourceDescendant m a target) (hB : SourceDescendant m b target) : False := by
  have hbase : ¬ SourceDescendant m b a :=
    decodeNode_root_not_descendant fuelB m b a nodeB hb hpb hpa (Ne.symm hne) hdB
  have hinv : SourceDescendant m a target ∧ ¬ SourceDescendant m b target := by
    apply hA.reverse_induction
      (fun current => SourceDescendant m a current ∧ ¬ SourceDescendant m b current)
      ⟨.root a, hbase⟩
    intro previous child hc hp hi
    have hnew := hi.1.snoc hc hp
    refine ⟨hnew, ?_⟩
    intro hother
    rcases hother.predecessor hb with he | ⟨parent, hm, hprefix, hparent⟩
    · have hab : SourceDescendant m a b := by simpa only [← he] using hnew
      exact decodeNode_root_not_descendant fuelA m a b nodeA ha hpa hpb hne hdA hab
    · have heq := model_box_id_injective m hwf parent hm previous
        (hi.1.member ha) (hparent.symm.trans hp)
      subst parent
      exact hi.2 hprefix
  exact hinv.2 hB

theorem placedBox_root_subtrees_id_disjoint
    (decodeFuelA decodeFuelB measureFuelA measureFuelB : Nat)
    (m : Model) (hwf : WellFormed m)
    (sourceA sourceB : ModelBox) (nodeA nodeB : Node)
    (shapeA shapeB : Shape) (metric : Measure.Metric)
    (xA yA xB yB : Int) (parentA parentB : String)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeNode decodeFuelA m sourceA = .ok nodeA)
    (hdB : Kinds.Railroad.decodeNode decodeFuelB m sourceB = .ok nodeB)
    (hmA : measure measureFuelA m.profile metric nodeA = .ok shapeA)
    (hmB : measure measureFuelB m.profile metric nodeB = .ok shapeB)
    (a b : Box)
    (hA : PlacedBox shapeA xA yA parentA a)
    (hB : PlacedBox shapeB xB yB parentB b) : a.id ≠ b.id := by
  intro hid
  obtain ⟨originalA, hoA, heA, hpathA⟩ :=
    placedBox_decoded_parent_origin decodeFuelA measureFuelA m sourceA nodeA
      shapeA metric xA yA parentA a ha hdA hmA hA
  obtain ⟨originalB, hoB, heB, hpathB⟩ :=
    placedBox_decoded_parent_origin decodeFuelB measureFuelB m sourceB nodeB
      shapeB metric xB yB parentB b hb hdB hmB hB
  have heq := model_box_id_injective m hwf originalA hoA originalB hoB
    (heA.symm.trans (hid.trans heB))
  subst originalB
  exact decodeNode_root_subtrees_disjoint decodeFuelA decodeFuelB m hwf
    sourceA sourceB originalA nodeA nodeB ha hb hpa hpb hne hdA hdB hpathA hpathB

theorem placeNode_new_root_subtrees_id_disjoint
    (decodeFuelA decodeFuelB measureFuelA measureFuelB placeFuelA placeFuelB : Nat)
    (m : Model) (hwf : WellFormed m)
    (sourceA sourceB : ModelBox) (nodeA nodeB : Node)
    (shapeA shapeB : Shape) (metric : Measure.Metric)
    (xA yA xB yB : Int) (parentA parentB : String)
    (initialA finalA initialB finalB : State)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeNode decodeFuelA m sourceA = .ok nodeA)
    (hdB : Kinds.Railroad.decodeNode decodeFuelB m sourceB = .ok nodeB)
    (hmA : measure measureFuelA m.profile metric nodeA = .ok shapeA)
    (hmB : measure measureFuelB m.profile metric nodeB = .ok shapeB)
    (hpA : placeNode placeFuelA m.profile shapeA xA yA parentA initialA = .ok finalA)
    (hpB : placeNode placeFuelB m.profile shapeB xB yB parentB initialB = .ok finalB)
    (a b : Box) (hA : a ∈ finalA.boxes) (hB : b ∈ finalB.boxes)
    (hnA : a ∉ initialA.boxes) (hnB : b ∉ initialB.boxes) : a.id ≠ b.id := by
  rcases placeNode_box_origin placeFuelA m.profile shapeA xA yA parentA
      initialA finalA hpA a hA with hold | hplacedA
  · exact False.elim (hnA hold)
  · rcases placeNode_box_origin placeFuelB m.profile shapeB xB yB parentB
        initialB finalB hpB b hB with hold | hplacedB
    · exact False.elim (hnB hold)
    · exact placedBox_root_subtrees_id_disjoint
        decodeFuelA decodeFuelB measureFuelA measureFuelB m hwf
        sourceA sourceB nodeA nodeB shapeA shapeB metric xA yA xB yB parentA parentB
        ha hb hpa hpb hne hdA hdB hmA hmB a b hplacedA hplacedB

theorem decodeRule_source_success (m : Model) (source : ModelBox) (rule : Rule)
    (h : Kinds.Railroad.decodeRule m source = .ok rule) :
    ∃ fuel node, Kinds.Railroad.decodeNode fuel m source = .ok node := by
  unfold Kinds.Railroad.decodeRule at h
  split at h
  · cases hc : Kinds.Railroad.children m source.id with
    | nil => simp [hc] at h
    | cons child rest =>
      cases rest with
      | cons next tail => simp [hc] at h
      | nil =>
        cases hd : Kinds.Railroad.decodeNode (m.boxes.length+1) m child with
        | error e => simp [hc, hd, bind, Except.bind] at h
        | ok node =>
          refine ⟨m.boxes.length+2,
            ⟨source.id,
              if ["terminal", "nonterminal", "special", "sequence", "choice",
                "optional", "zeroOrMore", "oneOrMore"].contains source.shape
              then source.shape else "terminal",
              Kinds.Railroad.display m source, [node]⟩, ?_⟩
          rw [Kinds.Railroad.decodeNode]
          simp [hc, List.mapM_cons, List.mapM_nil, hd, bind, Except.bind, pure, Except.pure]
  · cases hd : Kinds.Railroad.decodeNode (m.boxes.length+1) m source with
    | error e => simp [hd, bind, Except.bind] at h
    | ok node => exact ⟨m.boxes.length+1, node, hd⟩

theorem decoded_rule_subtrees_disjoint (m : Model) (hwf : WellFormed m)
    (sourceA sourceB target : ModelBox) (ruleA ruleB : Rule)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeRule m sourceA = .ok ruleA)
    (hdB : Kinds.Railroad.decodeRule m sourceB = .ok ruleB)
    (hA : SourceDescendant m sourceA target)
    (hB : SourceDescendant m sourceB target) : False := by
  obtain ⟨fuelA, nodeA, hsourceA⟩ := decodeRule_source_success m sourceA ruleA hdA
  obtain ⟨fuelB, nodeB, hsourceB⟩ := decodeRule_source_success m sourceB ruleB hdB
  exact decodeNode_root_subtrees_disjoint fuelA fuelB m hwf sourceA sourceB
    target nodeA nodeB ha hb hpa hpb hne hsourceA hsourceB hA hB

theorem decoded_rule_container_ne_descendant (m : Model) (source target : ModelBox)
    (rule : Rule)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hchild : target ∈ Kinds.Railroad.children m source.id)
    (hpath : SourceDescendant m target source) : False := by
  obtain ⟨fuel, node, hsource⟩ := decodeRule_source_success m source rule hd
  exact decodeNode_no_cycle fuel m source node hsource target hchild hpath

theorem decodeRule_definition_origin (m : Model) (source : ModelBox) (rule : Rule)
    (hs : source ∈ m.boxes)
    (h : Kinds.Railroad.decodeRule m source = .ok rule) :
    ∃ definition ∈ m.boxes,
      Kinds.Railroad.decodeNode (m.boxes.length+1) m definition = .ok rule.root ∧
      SourceDescendant m source definition ∧
      (rule.id = "" ∨ rule.id = source.id) := by
  unfold Kinds.Railroad.decodeRule at h
  split at h
  · cases hc : Kinds.Railroad.children m source.id with
    | nil => simp [hc] at h
    | cons child rest =>
      cases rest with
      | cons next tail => simp [hc] at h
      | nil =>
        have hchild : child ∈ Kinds.Railroad.children m source.id := by
          rw [hc]
          simp
        have hmem := (List.mem_filter.mp hchild).1
        have hparent : child.parent = source.id := by
          simpa using (List.mem_filter.mp hchild).2
        cases hd : Kinds.Railroad.decodeNode (m.boxes.length+1) m child with
        | error e => simp [hc, hd, bind, Except.bind] at h
        | ok node =>
          simp only [hc, hd, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at h
          subst rule
          exact ⟨child, hmem, hd, (SourceDescendant.root source).snoc hmem hparent,
            Or.inr rfl⟩
  · cases hd : Kinds.Railroad.decodeNode (m.boxes.length+1) m source with
    | error e => simp [hd, bind, Except.bind] at h
    | ok node =>
      simp only [hd, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst rule
      exact ⟨source, hs, hd, SourceDescendant.root source, Or.inl rfl⟩

theorem decoded_rule_descendant_ids_ne (m : Model) (hwf : WellFormed m)
    (sourceA sourceB targetA targetB : ModelBox) (ruleA ruleB : Rule)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeRule m sourceA = .ok ruleA)
    (hdB : Kinds.Railroad.decodeRule m sourceB = .ok ruleB)
    (hA : SourceDescendant m sourceA targetA)
    (hB : SourceDescendant m sourceB targetB) : targetA.id ≠ targetB.id := by
  intro hid
  have heq := model_box_id_injective m hwf targetA (hA.member ha)
    targetB (hB.member hb) hid
  subst targetB
  exact decoded_rule_subtrees_disjoint m hwf sourceA sourceB targetA ruleA ruleB
    ha hb hpa hpb hne hdA hdB hA hB

theorem decoded_rule_container_id_ne_descendant (m : Model) (hwf : WellFormed m)
    (source child target : ModelBox) (rule : Rule) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hc : child ∈ Kinds.Railroad.children m source.id)
    (hp : SourceDescendant m child target) : source.id ≠ target.id := by
  intro hid
  have heq := model_box_id_injective m hwf source hs target
    (hp.member (List.mem_filter.mp hc).1) hid
  subst target
  exact decoded_rule_container_ne_descendant m source child rule hd hc hp

theorem placedBox_decoded_rule_origin (measureFuel : Nat) (m : Model)
    (source : ModelBox) (rule : Rule) (shape : Shape) (metric : Measure.Metric)
    (x y : Int) (parent : String) (box : Box) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hm : measure measureFuel m.profile metric rule.root = .ok shape)
    (hp : PlacedBox shape x y parent box) :
    ∃ original ∈ m.boxes, box.id = original.id ∧
      SourceDescendant m source original := by
  obtain ⟨definition, hdef, hdecode, hpath, _⟩ :=
    decodeRule_definition_origin m source rule hs hd
  obtain ⟨original, ho, hid, hdesc⟩ :=
    placedBox_decoded_parent_origin (m.boxes.length+1) measureFuel m definition
      rule.root shape metric x y parent box hdef hdecode hm hp
  exact ⟨original, ho, hid, hpath.trans hdesc⟩

theorem placedBox_decoded_rules_id_disjoint
    (measureFuelA measureFuelB : Nat) (m : Model) (hwf : WellFormed m)
    (sourceA sourceB : ModelBox) (ruleA ruleB : Rule)
    (shapeA shapeB : Shape) (metric : Measure.Metric)
    (xA yA xB yB : Int) (parentA parentB : String) (a b : Box)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeRule m sourceA = .ok ruleA)
    (hdB : Kinds.Railroad.decodeRule m sourceB = .ok ruleB)
    (hmA : measure measureFuelA m.profile metric ruleA.root = .ok shapeA)
    (hmB : measure measureFuelB m.profile metric ruleB.root = .ok shapeB)
    (hA : PlacedBox shapeA xA yA parentA a)
    (hB : PlacedBox shapeB xB yB parentB b) : a.id ≠ b.id := by
  obtain ⟨originalA, _, hidA, hpathA⟩ :=
    placedBox_decoded_rule_origin measureFuelA m sourceA ruleA shapeA metric
      xA yA parentA a ha hdA hmA hA
  obtain ⟨originalB, _, hidB, hpathB⟩ :=
    placedBox_decoded_rule_origin measureFuelB m sourceB ruleB shapeB metric
      xB yB parentB b hb hdB hmB hB
  intro hid
  exact decoded_rule_descendant_ids_ne m hwf sourceA sourceB originalA originalB
    ruleA ruleB ha hb hpa hpb hne hdA hdB hpathA hpathB
    (hidA.symm.trans (hid.trans hidB))

theorem decoded_rule_root_ids_ne (m : Model) (hwf : WellFormed m)
    (sourceA sourceB : ModelBox) (ruleA ruleB : Rule)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeRule m sourceA = .ok ruleA)
    (hdB : Kinds.Railroad.decodeRule m sourceB = .ok ruleB) :
    ruleA.root.id ≠ ruleB.root.id := by
  obtain ⟨definitionA, _, hdecodeA, hpathA, _⟩ :=
    decodeRule_definition_origin m sourceA ruleA ha hdA
  obtain ⟨definitionB, _, hdecodeB, hpathB, _⟩ :=
    decodeRule_definition_origin m sourceB ruleB hb hdB
  have hidA := (decodeNode_metadata (m.boxes.length+1) m definitionA
    ruleA.root hdecodeA).1
  have hidB := (decodeNode_metadata (m.boxes.length+1) m definitionB
    ruleB.root hdecodeB).1
  intro hid
  exact decoded_rule_descendant_ids_ne m hwf sourceA sourceB definitionA definitionB
    ruleA ruleB ha hb hpa hpb hne hdA hdB hpathA hpathB
    (hidA.symm.trans (hid.trans hidB))

theorem decodeRules_root_ids_nodup (m : Model) (hwf : WellFormed m) :
    ∀ (sources : List ModelBox) (rules : List Rule),
      (sources.map (·.id)).Nodup →
      (∀ source ∈ sources, source ∈ m.boxes ∧ source.parent = "") →
      sources.mapM (Kinds.Railroad.decodeRule m) = .ok rules →
      (rules.map (fun rule => rule.root.id)).Nodup := by
  intro sources
  induction sources with
  | nil =>
    intro rules _ _ h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst rules
    exact List.nodup_nil
  | cons source tail ih =>
    intro rules hids hs h
    cases hd : Kinds.Railroad.decodeRule m source with
    | error e => simp [List.mapM_cons, hd, bind, Except.bind] at h
    | ok rule =>
      cases ht : tail.mapM (Kinds.Railroad.decodeRule m) with
      | error e => simp [List.mapM_cons, hd, ht, bind, Except.bind] at h
      | ok rest =>
        simp only [List.mapM_cons, hd, ht, bind, Except.bind,
          pure, Except.pure, Except.ok.injEq] at h
        subst rules
        have hparts := List.nodup_cons.mp hids
        have hsource := hs source (by simp)
        refine List.nodup_cons.mpr ⟨?_, ih rest hparts.2
          (fun b hb => hs b (List.mem_cons_of_mem source hb)) ht⟩
        intro hmem
        obtain ⟨other, ho, he⟩ := List.mem_map.mp hmem
        obtain ⟨origin, horigin, hdecode⟩ :=
          mapM_success_origin (Kinds.Railroad.decodeRule m) tail rest ht other ho
        have hother := hs origin (List.mem_cons_of_mem source horigin)
        have hne : source ≠ origin := by
          intro heq
          subst origin
          exact hparts.1 (List.mem_map_of_mem horigin)
        exact decoded_rule_root_ids_ne m hwf source origin rule other
          hsource.1 hother.1 hsource.2 hother.2 hne hd hdecode he.symm

theorem lower_root_ids_nodup (m : Model) (hwf : WellFormed m)
    (rules : List Rule) (h : Kinds.Railroad.lower m = .ok rules) :
    (rules.map (fun rule => rule.root.id)).Nodup := by
  apply decodeRules_root_ids_nodup m hwf (Kinds.Railroad.children m "") rules
  · exact List.Nodup.sublist
      (List.Sublist.map (fun b : ModelBox => b.id) List.filter_sublist)
      (Model.boxIds_nodup hwf)
  · intro source hs
    have hparts := List.mem_filter.mp hs
    exact ⟨hparts.1, by simpa using hparts.2⟩
  · exact h

theorem placeRule_box_source (m : Model) (metric : Measure.Metric)
    (source : ModelBox) (rule : Rule) (before after : RuleState)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : placeRule m metric before rule = .ok after) :
    ∀ box ∈ after.state.boxes, box ∈ before.state.boxes ∨
      ∃ original ∈ m.boxes, box.id = original.id ∧
        SourceDescendant m source original := by
  unfold placeRule at h
  cases hm : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hm, bind, Except.bind] at h
  | ok shape =>
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hm, ht, bind, Except.bind] at h
    | ok title =>
      let g := ruleGeometry m.profile shape title
      simp only [hm, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile shape
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule shape g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          intro box hb
          rcases placeNode_box_origin _ _ _ _ _ _ _ _ hp box hb with hold | hnew
          · unfold addRule at hold
            split at hold
            · exact Or.inl hold
            · simp only [List.mem_append, List.mem_singleton] at hold
              rcases hold with hold | heq
              · exact Or.inl hold
              · subst box
                obtain ⟨_, _, _, _, hkey⟩ :=
                  decodeRule_definition_origin m source rule hs hd
                rcases hkey with hempty | hid
                · simp [hempty] at *
                · exact Or.inr ⟨source, hs, hid, SourceDescendant.root source⟩
          · exact Or.inr (placedBox_decoded_rule_origin (m.boxes.length+1)
              m source rule shape metric
              (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id box
              hs hd hm hnew)

theorem placeRule_new_boxes_id_disjoint (m : Model) (hwf : WellFormed m)
    (metric : Measure.Metric) (sourceA sourceB : ModelBox) (ruleA ruleB : Rule)
    (beforeA afterA beforeB afterB : RuleState)
    (ha : sourceA ∈ m.boxes) (hb : sourceB ∈ m.boxes)
    (hpa : sourceA.parent = "") (hpb : sourceB.parent = "")
    (hne : sourceA ≠ sourceB)
    (hdA : Kinds.Railroad.decodeRule m sourceA = .ok ruleA)
    (hdB : Kinds.Railroad.decodeRule m sourceB = .ok ruleB)
    (hpA : placeRule m metric beforeA ruleA = .ok afterA)
    (hpB : placeRule m metric beforeB ruleB = .ok afterB)
    (a b : Box) (hA : a ∈ afterA.state.boxes) (hB : b ∈ afterB.state.boxes)
    (hnA : a ∉ beforeA.state.boxes) (hnB : b ∉ beforeB.state.boxes) :
    a.id ≠ b.id := by
  rcases placeRule_box_source m metric sourceA ruleA beforeA afterA ha hdA hpA
      a hA with hold | hnewA
  · exact False.elim (hnA hold)
  · rcases placeRule_box_source m metric sourceB ruleB beforeB afterB hb hdB hpB
        b hB with hold | hnewB
    · exact False.elim (hnB hold)
    · obtain ⟨originalA, _, hidA, hpathA⟩ := hnewA
      obtain ⟨originalB, _, hidB, hpathB⟩ := hnewB
      intro hid
      exact decoded_rule_descendant_ids_ne m hwf sourceA sourceB originalA originalB
        ruleA ruleB ha hb hpa hpb hne hdA hdB hpathA hpathB
        (hidA.symm.trans (hid.trans hidB))

theorem boxes_id_injective_of_nodup :
    ∀ (boxes : List Box), (boxes.map (·.id)).Nodup →
      ∀ a ∈ boxes, ∀ b ∈ boxes, a.id = b.id → a = b := by
  intro boxes
  induction boxes with
  | nil => intro _ a ha; cases ha
  | cons first rest ih =>
    intro hids a ha b hb hid
    have hparts := List.nodup_cons.mp hids
    rcases List.mem_cons.mp ha with heA | ha
    · subst a
      rcases List.mem_cons.mp hb with heB | hb
      · exact heB.symm
      · exact False.elim (hparts.1 (by
          change first.id ∈ rest.map (·.id)
          rw [hid]
          exact List.mem_map_of_mem hb))
    · rcases List.mem_cons.mp hb with heB | hb
      · subst b
        exact False.elim (hparts.1 (by
          change first.id ∈ rest.map (·.id)
          rw [← hid]
          exact List.mem_map_of_mem ha))
      · exact ih hparts.2 a ha b hb hid

theorem find_box_of_id_injective :
    ∀ (boxes : List Box),
      (∀ a ∈ boxes, ∀ b ∈ boxes, a.id = b.id → a = b) →
      ∀ box ∈ boxes, boxes.find? (fun b => b.id == box.id) = some box := by
  intro boxes
  induction boxes with
  | nil => intro _ box hb; cases hb
  | cons first rest ih =>
    intro hinj box hb
    rcases List.mem_cons.mp hb with he | hb
    · subst box
      simp
    · by_cases he : first.id = box.id
      · have heq := hinj first (by simp) box (List.mem_cons_of_mem first hb) he
        subst first
        simp
      · simp only [List.find?_cons, show (first.id == box.id) = false by
          simp [he]]
        exact ih (fun a ha b hb hid =>
          hinj a (List.mem_cons_of_mem first ha) b
            (List.mem_cons_of_mem first hb) hid) box hb

theorem layout_parent_lookup_of_id_injective (m : Model) (rules : List Rule)
    (scene : Scene) (h : layout m rules = .ok scene)
    (hinj : ∀ a ∈ scene.boxes, ∀ b ∈ scene.boxes, a.id = b.id → a = b) :
    Validator.C3 scene.layoutDump := by
  intro box hb hparent enclosing hlookup
  obtain ⟨parent, hp, hid, hcontained⟩ :=
    layout_parent_witness m rules scene h box hb hparent
  have hfind := find_box_of_id_injective scene.boxes hinj parent hp
  have hactual : scene.layoutDump.box? box.parent = some parent := by
    change scene.boxes.find? (fun b => b.id == box.parent) = some parent
    rw [← hid]
    exact hfind
  have heq := Option.some.inj (hactual.symm.trans hlookup)
  subst enclosing
  exact hcontained

theorem layout_endpoint_lookup_of_id_injective (m : Model) (rules : List Rule)
    (scene : Scene) (h : layout m rules = .ok scene)
    (hinj : ∀ a ∈ scene.boxes, ∀ b ∈ scene.boxes, a.id = b.id → a = b) :
    Validator.C5 scene.layoutDump := by
  intro route hr
  obtain ⟨a, ha, b, hb, hfrom, hto, first, last, hfirst, hlast, hba, hbb⟩ :=
    layout_endpoint_witnesses m rules scene h route hr
  refine ⟨first, last, a, b, hfirst, hlast, ?_, ?_, hba, hbb⟩
  · change scene.boxes.find? (fun b => b.id == route.fromId) = some a
    rw [← hfrom]
    exact find_box_of_id_injective scene.boxes hinj a ha
  · change scene.boxes.find? (fun b => b.id == route.toId) = some b
    rw [← hto]
    exact find_box_of_id_injective scene.boxes hinj b hb

theorem placedBox_decoded_rule_id_injective (measureFuel : Nat) (m : Model)
    (hwf : WellFormed m) (source : ModelBox) (rule : Rule) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hm : measure measureFuel m.profile metric rule.root = .ok shape)
    (a b : Box) (ha : PlacedBox shape x y parent a)
    (hb : PlacedBox shape x y parent b) (hid : a.id = b.id) : a = b := by
  obtain ⟨definition, hdef, hdecode, _, _⟩ :=
    decodeRule_definition_origin m source rule hs hd
  exact placedBox_id_injective measureFuel (m.boxes.length+1) m hwf
    definition rule.root shape metric x y parent hdef hdecode hm a b ha hb hid

theorem decoded_rule_frame_id_ne_placedBox (measureFuel : Nat) (m : Model)
    (hwf : WellFormed m) (source : ModelBox) (rule : Rule) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hne : rule.id ≠ "")
    (hm : measure measureFuel m.profile metric rule.root = .ok shape)
    (box : Box) (hb : PlacedBox shape x y parent box) : rule.id ≠ box.id := by
  have hsuccess := hd
  unfold Kinds.Railroad.decodeRule at hd
  split at hd
  · cases hc : Kinds.Railroad.children m source.id with
    | nil => simp [hc] at hd
    | cons child rest =>
      cases rest with
      | cons next tail => simp [hc] at hd
      | nil =>
        have hchild : child ∈ Kinds.Railroad.children m source.id := by
          rw [hc]
          simp
        cases hdecode : Kinds.Railroad.decodeNode (m.boxes.length+1) m child with
        | error e => simp [hc, hdecode, bind, Except.bind] at hd
        | ok node =>
          simp only [hc, hdecode, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] at hd
          subst rule
          obtain ⟨original, _, hid, hpath⟩ :=
            placedBox_decoded_parent_origin (m.boxes.length+1) measureFuel m child
              node shape metric x y parent box (List.mem_filter.mp hchild).1
              hdecode hm hb
          intro heq
          exact decoded_rule_container_id_ne_descendant m hwf source child original
            _ hs hsuccess hchild hpath (heq.trans hid)
  · cases hdecode : Kinds.Railroad.decodeNode (m.boxes.length+1) m source with
    | error e => simp [hdecode, bind, Except.bind] at hd
    | ok node =>
      simp only [hdecode, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at hd
      subst rule
      exact False.elim (hne rfl)

theorem decoded_rule_emitted_id_injective (measureFuel : Nat) (m : Model)
    (hwf : WellFormed m) (source : ModelBox) (rule : Rule) (shape : Shape)
    (metric : Measure.Metric) (x y : Int) (parent : String) (frame a b : Box)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (hm : measure measureFuel m.profile metric rule.root = .ok shape)
    (hframe : frame.id = rule.id)
    (ha : (rule.id ≠ "" ∧ a = frame) ∨ PlacedBox shape x y parent a)
    (hb : (rule.id ≠ "" ∧ b = frame) ∨ PlacedBox shape x y parent b)
    (hid : a.id = b.id) : a = b := by
  rcases ha with ⟨hne, rfl⟩ | ha
  · rcases hb with ⟨_, rfl⟩ | hb
    · rfl
    · exact False.elim
        (decoded_rule_frame_id_ne_placedBox measureFuel m hwf source rule shape
          metric x y parent hs hd hne hm b hb (hframe.symm.trans hid))
  · rcases hb with ⟨hne, rfl⟩ | hb
    · exact False.elim
        (decoded_rule_frame_id_ne_placedBox measureFuel m hwf source rule shape
          metric x y parent hs hd hne hm a ha (hframe.symm.trans hid.symm))
    · exact placedBox_decoded_rule_id_injective measureFuel m hwf source rule
        shape metric x y parent hs hd hm a b ha hb hid

theorem placeRule_new_id_injective (m : Model) (hwf : WellFormed m)
    (metric : Measure.Metric) (source : ModelBox) (rule : Rule)
    (before after : RuleState) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : placeRule m metric before rule = .ok after)
    (a b : Box) (ha : a ∈ after.state.boxes) (hb : b ∈ after.state.boxes)
    (hna : a ∉ before.state.boxes) (hnb : b ∉ before.state.boxes)
    (hid : a.id = b.id) : a = b := by
  unfold placeRule at h
  cases hm : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hm, bind, Except.bind] at h
  | ok shape =>
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hm, ht, bind, Except.bind] at h
    | ok title =>
      let g := ruleGeometry m.profile shape title
      simp only [hm, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hp : placeNode (m.boxes.length+1) m.profile shape
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule shape g before.y before.state) with
        | error e =>
          dsimp only [g] at hp
          simp only [hp] at h
          cases h
        | ok state =>
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          have origin : ∀ box ∈ state.boxes, box ∉ before.state.boxes →
              (rule.id ≠ "" ∧
                box = ⟨rule.id,"group",ruleFrame m.profile g before.y,"",false⟩) ∨
              PlacedBox shape (constant m.profile "margin"+g.defX)
                (before.y+g.defY) rule.id box := by
            intro box hbox hnew
            rcases placeNode_box_origin _ _ _ _ _ _ _ _ hp box hbox with hold | hplaced
            · unfold addRule at hold
              split at hold
              · exact False.elim (hnew hold)
              · rename_i hnonempty
                simp only [List.mem_append, List.mem_singleton] at hold
                rcases hold with hold | heq
                · exact False.elim (hnew hold)
                · exact Or.inl ⟨by simpa using hnonempty, heq⟩
            · exact Or.inr hplaced
          exact decoded_rule_emitted_id_injective (m.boxes.length+1) m hwf
            source rule shape metric _ _ rule.id
            ⟨rule.id,"group",ruleFrame m.profile g before.y,"",false⟩ a b
            hs hd hm rfl (origin a ha hna) (origin b hb hnb) hid

theorem layout_parent_lookup_of_ids_nodup (m : Model) (rules : List Rule)
    (scene : Scene) (h : layout m rules = .ok scene)
    (hids : (scene.boxes.map (·.id)).Nodup) :
    Validator.C3 scene.layoutDump :=
  layout_parent_lookup_of_id_injective m rules scene h
    (boxes_id_injective_of_nodup scene.boxes hids)

theorem layout_endpoint_lookup_of_ids_nodup (m : Model) (rules : List Rule)
    (scene : Scene) (h : layout m rules = .ok scene)
    (hids : (scene.boxes.map (·.id)).Nodup) :
    Validator.C5 scene.layoutDump :=
  layout_endpoint_lookup_of_id_injective m rules scene h
    (boxes_id_injective_of_nodup scene.boxes hids)

theorem placeRule_id_injective (m : Model) (hwf : WellFormed m)
    (metric : Measure.Metric) (source : ModelBox) (rule : Rule)
    (before after : RuleState) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : placeRule m metric before rule = .ok after)
    (hi : ∀ a ∈ before.state.boxes, ∀ b ∈ before.state.boxes,
      a.id = b.id → a = b)
    (hcross : ∀ old ∈ before.state.boxes, ∀ box ∈ after.state.boxes,
      box ∉ before.state.boxes → old.id ≠ box.id) :
    ∀ a ∈ after.state.boxes, ∀ b ∈ after.state.boxes,
      a.id = b.id → a = b := by
  intro a ha b hb hid
  by_cases hna : a ∈ before.state.boxes
  · by_cases hnb : b ∈ before.state.boxes
    · exact hi a hna b hnb hid
    · exact False.elim (hcross a hna b hb hnb hid)
  · by_cases hnb : b ∈ before.state.boxes
    · exact False.elim (hcross b hnb a ha hna hid.symm)
    · exact placeRule_new_id_injective m hwf metric source rule before after
        hs hd h a b ha hb hna hnb hid

theorem placeRule_empty_id_injective (m : Model) (hwf : WellFormed m)
    (metric : Measure.Metric) (source : ModelBox) (rule : Rule)
    (before after : RuleState) (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : placeRule m metric before rule = .ok after)
    (hempty : before.state.boxes = []) :
    ∀ a ∈ after.state.boxes, ∀ b ∈ after.state.boxes,
      a.id = b.id → a = b := by
  apply placeRule_id_injective m hwf metric source rule before after hs hd h
  · intro a ha
    rw [hempty] at ha
    cases ha
  · intro old hold
    rw [hempty] at hold
    cases hold

theorem layout_single_rule_id_injective (m : Model) (hwf : WellFormed m)
    (source : ModelBox) (rule : Rule) (scene : Scene)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : layout m [rule] = .ok scene) :
    ∀ a ∈ scene.boxes, ∀ b ∈ scene.boxes, a.id = b.id → a = b := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hp : placeRule m metric {y := constant m.profile "margin"} rule with
    | error e =>
      simp [hm, List.foldlM_cons, hp, bind, Except.bind] at h
    | ok result =>
      have hinj := placeRule_empty_id_injective m hwf metric source rule
        {y := constant m.profile "margin"} result hs hd hp rfl
      simp only [hm, List.foldlM_cons, hp, List.foldlM_nil, bind,
        Except.bind, pure, Except.pure] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [Except.ok.injEq] at h
           subst scene
           exact hinj)

theorem layout_single_rule_parent_lookup (m : Model) (hwf : WellFormed m)
    (source : ModelBox) (rule : Rule) (scene : Scene)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : layout m [rule] = .ok scene) :
    Validator.C3 scene.layoutDump :=
  layout_parent_lookup_of_id_injective m [rule] scene h
    (layout_single_rule_id_injective m hwf source rule scene hs hd h)

theorem layout_single_rule_endpoint_lookup (m : Model) (hwf : WellFormed m)
    (source : ModelBox) (rule : Rule) (scene : Scene)
    (hs : source ∈ m.boxes)
    (hd : Kinds.Railroad.decodeRule m source = .ok rule)
    (h : layout m [rule] = .ok scene) :
    Validator.C5 scene.layoutDump :=
  layout_endpoint_lookup_of_id_injective m [rule] scene h
    (layout_single_rule_id_injective m hwf source rule scene hs hd h)

theorem fold_decoded_rules_id_injective (m : Model) (hwf : WellFormed m)
    (metric : Measure.Metric) :
    ∀ (rules : List Rule) (before after : RuleState),
      (rules.map (fun rule => rule.root.id)).Nodup →
      (∀ rule ∈ rules, ∃ source ∈ m.boxes, source.parent = "" ∧
        Kinds.Railroad.decodeRule m source = .ok rule) →
      (∀ a ∈ before.state.boxes, ∀ b ∈ before.state.boxes,
        a.id = b.id → a = b) →
      (∀ old ∈ before.state.boxes, ∀ rule ∈ rules,
        ∀ source ∈ m.boxes, source.parent = "" →
        Kinds.Railroad.decodeRule m source = .ok rule →
        ∀ original, SourceDescendant m source original → old.id ≠ original.id) →
      rules.foldlM (placeRule m metric) before = .ok after →
      ∀ a ∈ after.state.boxes, ∀ b ∈ after.state.boxes,
        a.id = b.id → a = b := by
  intro rules
  induction rules with
  | nil =>
    intro before after _ _ hi _ h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst after
    exact hi
  | cons rule rest ih =>
    intro before after hids horigin hi havoid h
    obtain ⟨source, hs, hparent, hd⟩ := horigin rule (by simp)
    cases hp : placeRule m metric before rule with
    | error e => simp [List.foldlM_cons, hp, bind, Except.bind] at h
    | ok next =>
      simp only [List.foldlM_cons, hp, bind, Except.bind] at h
      have hparts := List.nodup_cons.mp hids
      have hnext : ∀ a ∈ next.state.boxes, ∀ b ∈ next.state.boxes,
          a.id = b.id → a = b := by
        apply placeRule_id_injective m hwf metric source rule before next hs hd hp hi
        intro old hold box hb hnew hid
        rcases placeRule_box_source m metric source rule before next hs hd hp
            box hb with holdBox | hsource
        · exact hnew holdBox
        · obtain ⟨original, _, hbox, hpath⟩ := hsource
          exact havoid old hold rule (by simp) source hs hparent hd
            original hpath (hid.trans hbox)
      apply ih next after hparts.2
        (fun other ho => horigin other (List.mem_cons_of_mem rule ho)) hnext
        ?_ h
      intro old hold other ho otherSource hos hop hod original hpath
      rcases placeRule_box_source m metric source rule before next hs hd hp
          old hold with hold | hnew
      · exact havoid old hold other (List.mem_cons_of_mem rule ho)
          otherSource hos hop hod original hpath
      · obtain ⟨oldSource, _, hid, oldPath⟩ := hnew
        have hne : source ≠ otherSource := by
          intro heq
          subst otherSource
          have he : rule = other := Except.ok.inj (hd.symm.trans hod)
          subst other
          exact hparts.1 (List.mem_map_of_mem ho)
        intro heq
        exact decoded_rule_descendant_ids_ne m hwf source otherSource
          oldSource original rule other hs hos hparent hop hne hd hod
          oldPath hpath (hid.symm.trans heq)

theorem layout_lowered_id_injective (m : Model) (hwf : WellFormed m)
    (rules : List Rule) (scene : Scene)
    (hl : Kinds.Railroad.lower m = .ok rules)
    (h : layout m rules = .ok scene) :
    ∀ a ∈ scene.boxes, ∀ b ∈ scene.boxes, a.id = b.id → a = b := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok state =>
      have hinj := fold_decoded_rules_id_injective m hwf metric rules
        {y := constant m.profile "margin"} state (lower_root_ids_nodup m hwf rules hl)
        (by
          intro rule hr
          obtain ⟨source, hs, hd⟩ :=
            mapM_success_origin (Kinds.Railroad.decodeRule m)
              (Kinds.Railroad.children m "") rules hl rule hr
          have hsource := List.mem_filter.mp hs
          exact ⟨source, hsource.1, by simpa using hsource.2, hd⟩)
        (by intro a ha; cases ha)
        (by intro old hold; cases hold) hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           exact hinj)

theorem railroad_parent_lookup (m : Model) (hwf : WellFormed m)
    (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C3 result.scene.layoutDump := by
  obtain ⟨rules, scene, hl, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_parent_lookup_of_id_injective m rules scene hs
    (layout_lowered_id_injective m hwf rules scene hl hs)

theorem railroad_endpoint_lookup (m : Model) (hwf : WellFormed m)
    (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C5 result.scene.layoutDump := by
  obtain ⟨rules, scene, hl, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_endpoint_lookup_of_id_injective m rules scene hs
    (layout_lowered_id_injective m hwf rules scene hl hs)

theorem previous_stage_avoids_horizontal (p : Profile) (state : RuleState)
    (hi : StageBounds p state) (box : Box) (hb : box ∈ state.state.boxes)
    (left right baseline : Int) (hy : state.y ≤ baseline) :
    ¬ Polyline.hitsRect [⟨left,baseline⟩,⟨right,baseline⟩] box.rect := by
  have hc := hi.2.2 box hb
  unfold StageFrame Rect.Contained at hc
  dsimp only at hc
  apply horizontal_route_avoids
  exact Or.inr (Or.inr (Or.inr (by omega)))

theorem previous_stage_disjoint_later_rect (p : Profile) (state : RuleState)
    (hi : StageBounds p state) (box : Box) (hb : box ∈ state.state.boxes)
    (rect : Rect) (hy : state.y ≤ rect.y) :
    Disjoint box.rect rect := by
  have hc := hi.2.2 box hb
  unfold StageFrame Rect.Contained at hc
  dsimp only at hc
  unfold Disjoint Rect.meetsInterior
  omega

theorem railroad_structural_constraints (m : Model) (hwf : WellFormed m)
    (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C1 result.scene.layoutDump ∧
      Validator.C2 result.scene.layoutDump ∧
      Validator.C3 result.scene.layoutDump ∧
      Validator.C4 result.scene.layoutDump ∧
      Validator.C5 result.scene.layoutDump :=
  ⟨railroad_canvas m result h, railroad_exclusive_separated m result h,
    railroad_parent_lookup m hwf result h, railroad_orthogonal m result h,
    railroad_endpoint_lookup m hwf result h⟩

theorem sequenceJoins_labels (s : Shape) (x y : Int) (state : State) :
    (sequenceJoins s x y state).labels = state.labels := by
  apply foldl_preserves (joinStep s x y) (fun acc => acc.labels = state.labels)
  · intro i acc h
    exact h
  · rfl

theorem placeNode_labels :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State), placeNode fuel p s x y parent initial = .ok final →
      final.labels = initial.labels := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final h
    simp only [placeNode] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst final
      rfl
    · apply foldlM_preserves _ (fun acc => acc.labels = initial.labels)
        (fun pair before after hb he =>
          (ih p pair.1 _ _ s.id before after he).trans hb) _ _ final ?_ h
      split
      · exact sequenceJoins_labels s x y _
      · rfl

theorem ruleLabel_vertical_bounds (p : Profile) (s : Shape) (title y : Int)
    (hs : Nonnegative s) :
    y ≤ (ruleLabelRect p (ruleGeometry p s title) y).y ∧
      (ruleLabelRect p (ruleGeometry p s title) y).y +
        (ruleLabelRect p (ruleGeometry p s title) y).h ≤
          y + (ruleGeometry p s title).height := by
  have hbase : Int.fdiv (constant p "line_height") 2 ≤
      constant p "rule_min_baseline" := by cases p <;> decide
  have hline : constant p "line_height" -
      Int.fdiv (constant p "line_height") 2 ≤ 2 * constant p "margin" := by
    cases p <;> decide
  have hb := Int.le_max_left (constant p "rule_min_baseline") s.up
  have hh := Int.le_max_right (constant p "rule_min_height")
    (max (constant p "rule_min_baseline") s.up - s.up +
      s.height + 2 * constant p "margin")
  unfold Nonnegative at hs
  dsimp only [ruleLabelRect, ruleGeometry, Shape.height]
  unfold Shape.height at hh
  constructor <;> omega

theorem ruleLabel_avoids_definition (p : Profile) (s : Shape)
    (title y : Int) (parent : String) (box : Box) (hg : Geometry s)
    (hb : PlacedBox s
      (constant p "margin" + (ruleGeometry p s title).defX)
      (y + (ruleGeometry p s title).defY) parent box) :
    Disjoint (ruleLabelRect p (ruleGeometry p s title) y) box.rect := by
  have hc := descendant_contained hb.descendant hg
  have hgap := (rule_spacing_nonnegative p).2.1
  unfold Rect.Contained shapeRect at hc
  unfold Disjoint Rect.meetsInterior
  dsimp only [ruleLabelRect, ruleGeometry] at *
  omega

theorem ruleLabel_strict_inside_frame (p : Profile) (s : Shape) (title y : Int)
    (hs : Nonnegative s) :
    (ruleFrame p (ruleGeometry p s title) y).StrictInside
      (ruleLabelRect p (ruleGeometry p s title) y) := by
  have hm : 0 < constant p "margin" := by cases p <;> decide
  have hgap := (rule_spacing_nonnegative p).2.1
  have hend := (rule_spacing_nonnegative p).2.2.1
  have hmarker := (rule_spacing_nonnegative p).2.2.2.1
  have hbase : Int.fdiv (constant p "line_height") 2 <
      constant p "rule_min_baseline" := by cases p <;> decide
  have hline : constant p "line_height" -
      Int.fdiv (constant p "line_height") 2 < 2 * constant p "margin" := by
    cases p <;> decide
  have hb := Int.le_max_left (constant p "rule_min_baseline") s.up
  have hh := Int.le_max_right (constant p "rule_min_height")
    (max (constant p "rule_min_baseline") s.up - s.up +
      s.height + 2 * constant p "margin")
  unfold Nonnegative at hs
  unfold Rect.StrictInside
  dsimp only [ruleFrame, ruleLabelRect, ruleGeometry, Shape.height] at *
  omega

def LabelsClear (state : State) : Prop :=
  ∀ label ∈ state.labels, ∀ box ∈ state.boxes, box.exclusive = true →
    Disjoint label.rect box.rect

def LabelsBefore (state : RuleState) : Prop :=
  ∀ label ∈ state.state.labels, label.rect.y + label.rect.h ≤ state.y

theorem addRule_exclusive_box_origin (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State) (box : Box)
    (hb : box ∈ (addRule p rule s g y state).boxes) (hex : box.exclusive = true) :
    box ∈ state.boxes := by
  unfold addRule at hb
  split at hb
  · exact hb
  · simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · exact hb
    · cases hex

theorem placeRule_labels_clear (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : StageBounds m.profile before)
    (hl : LabelsBefore before) (hc : LabelsClear before.state)
    (h : placeRule m metric before rule = .ok after) :
    LabelsBefore after ∧ LabelsClear after.state := by
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
      have hv := ruleLabel_vertical_bounds m.profile s title before.y hg.nonnegative
      have hheight := (ruleGeometry_nonnegative m.profile s title hg.nonnegative hn).2
      have hsep := (spacing_nonnegative m.profile).2.2.2.2.2
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
          have hlabels := placeNode_labels _ _ _ _ _ _ _ _ hp
          have hboxes := placeNode_box_origin _ _ _ _ _ _ _ _ hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          constructor
          · intro label hlabel
            change label ∈ state.labels at hlabel
            rw [hlabels] at hlabel
            unfold addRule at hlabel
            split at hlabel
            · have hb := hl label hlabel
              change label.rect.y + label.rect.h ≤ before.y + g.height +
                constant m.profile "vsep"
              dsimp only [g] at *
              omega
            · simp only [List.mem_append, List.mem_singleton] at hlabel
              rcases hlabel with hlabel | rfl
              · have hb := hl label hlabel
                change label.rect.y + label.rect.h ≤ before.y + g.height +
                  constant m.profile "vsep"
                dsimp only [g] at *
                omega
              · change (ruleLabelRect m.profile g before.y).y +
                    (ruleLabelRect m.profile g before.y).h ≤
                    before.y + g.height + constant m.profile "vsep"
                dsimp only [g] at *
                omega
          · intro label hlabel box hbox hex
            change label ∈ state.labels at hlabel
            change box ∈ state.boxes at hbox
            rw [hlabels] at hlabel
            rcases hboxes box hbox with hold | hnew
            · have hold' := addRule_exclusive_box_origin m.profile rule s g
                before.y before.state box hold hex
              unfold addRule at hlabel
              split at hlabel
              · exact hc label hlabel box hold' hex
              · simp only [List.mem_append, List.mem_singleton] at hlabel
                rcases hlabel with hlabel | rfl
                · exact hc label hlabel box hold' hex
                · have hb := hi.2.2 box hold'
                  unfold StageFrame Rect.Contained at hb
                  unfold Disjoint Rect.meetsInterior
                  dsimp only [g] at *
                  omega
            · have hb := Rect.Contained.trans
                (rule_contains_definition m.profile s title before.y hn)
                (descendant_contained hnew.descendant hg)
              unfold addRule at hlabel
              split at hlabel
              · have hbefore := hl label hlabel
                unfold ruleFrame Rect.Contained at hb
                unfold Disjoint Rect.meetsInterior
                dsimp only at *
                omega
              · simp only [List.mem_append, List.mem_singleton] at hlabel
                rcases hlabel with hlabel | rfl
                · have hbefore := hl label hlabel
                  unfold ruleFrame Rect.Contained at hb
                  unfold Disjoint Rect.meetsInterior
                  dsimp only at *
                  omega
                · exact ruleLabel_avoids_definition m.profile s title before.y
                    rule.id box hg hnew

theorem layout_labels_clear (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) : Validator.C7 scene.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => StageBounds m.profile state ∧ LabelsBefore state ∧
          LabelsClear state.state)
        (fun rule before after hi he => ⟨
          placeRule_stage_bounds m metric before after rule hi.1 he,
          placeRule_labels_clear m metric before after rule hi.1 hi.2.1 hi.2.2 he⟩)
        rules {y := constant m.profile "margin"} result
        ⟨initial_stage_bounds m.profile, (by intro label hl; cases hl),
          (by intro label hl; cases hl)⟩ hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           intro label hl box hb hex _
           obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
           exact hinv.2.2 source hs box hb hex)

theorem railroad_labels_clear (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C7 result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_labels_clear m rules scene hs

def FramesLabels (state : State) : Prop :=
  ∀ box ∈ state.boxes, ∀ label ∈ state.labels,
    Disjoint box.rect label.rect ∨ box.rect.StrictInside label.rect

theorem disjoint_symm {a b : Rect} (h : Disjoint a b) : Disjoint b a := by
  unfold Disjoint Rect.meetsInterior at *
  omega

theorem placeRule_frames_labels (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : StageBounds m.profile before) (hl : LabelsBefore before)
    (hc : FramesLabels before.state)
    (h : placeRule m metric before rule = .ok after) :
    FramesLabels after.state := by
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
      have hv := ruleLabel_vertical_bounds m.profile s title before.y hg.nonnegative
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
          have hlabels := placeNode_labels _ _ _ _ _ _ _ _ hp
          have hboxes := placeNode_box_origin _ _ _ _ _ _ _ _ hp
          dsimp only [g] at hp
          simp only [hp, pure, Except.pure, Except.ok.injEq] at h
          subst after
          intro box hbox label hlabel
          change label ∈ state.labels at hlabel
          change box ∈ state.boxes at hbox
          rw [hlabels] at hlabel
          rcases hboxes box hbox with hold | hnew
          · unfold addRule at hold hlabel
            split at hold
            · split at hlabel
              · exact hc box hold label hlabel
              · simp_all
            · simp only [List.mem_append, List.mem_singleton] at hold
              rcases hold with hold | rfl
              · split at hlabel
                · exact hc box hold label hlabel
                · simp only [List.mem_append, List.mem_singleton] at hlabel
                  rcases hlabel with hlabel | rfl
                  · exact hc box hold label hlabel
                  · apply Or.inl
                    have hb := hi.2.2 box hold
                    unfold StageFrame Rect.Contained at hb
                    unfold Disjoint Rect.meetsInterior
                    dsimp only [g] at *
                    omega
              · split at hlabel
                · apply Or.inl
                  have hb := hl label hlabel
                  unfold Disjoint Rect.meetsInterior
                  dsimp only [ruleFrame]
                  omega
                · simp only [List.mem_append, List.mem_singleton] at hlabel
                  rcases hlabel with hlabel | rfl
                  · apply Or.inl
                    have hb := hl label hlabel
                    unfold Disjoint Rect.meetsInterior
                    dsimp only [ruleFrame]
                    omega
                  · exact Or.inr (ruleLabel_strict_inside_frame
                      m.profile s title before.y hg.nonnegative)
          · have hb := Rect.Contained.trans
              (rule_contains_definition m.profile s title before.y hn)
              (descendant_contained hnew.descendant hg)
            unfold addRule at hlabel
            split at hlabel
            · apply Or.inl
              have hbefore := hl label hlabel
              unfold ruleFrame Rect.Contained at hb
              unfold Disjoint Rect.meetsInterior
              dsimp only at *
              omega
            · simp only [List.mem_append, List.mem_singleton] at hlabel
              rcases hlabel with hlabel | rfl
              · apply Or.inl
                have hbefore := hl label hlabel
                unfold ruleFrame Rect.Contained at hb
                unfold Disjoint Rect.meetsInterior
                dsimp only at *
                omega
              · exact Or.inl (disjoint_symm
                  (ruleLabel_avoids_definition m.profile s title before.y
                    rule.id box hg hnew))

theorem layout_frames_labels (m : Model) (rules : List Rule) (scene : Scene)
    (h : layout m rules = .ok scene) : Validator.C8b scene.layoutDump := by
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok result =>
      have hinv := foldlM_preserves (placeRule m metric)
        (fun state => StageBounds m.profile state ∧ LabelsBefore state ∧
          LabelsClear state.state ∧ FramesLabels state.state)
        (fun rule before after hi he => by
          have hl := placeRule_labels_clear m metric before after rule
            hi.1 hi.2.1 hi.2.2.1 he
          exact ⟨placeRule_stage_bounds m metric before after rule hi.1 he,
            hl.1, hl.2, placeRule_frames_labels m metric before after rule
              hi.1 hi.2.1 hi.2.2.2 he⟩)
        rules {y := constant m.profile "margin"} result
        ⟨initial_stage_bounds m.profile, (by intro label hl; cases hl),
          (by intro label hl; cases hl), (by intro box hb; cases hb)⟩ hf
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           intro box hb _ label hl
           obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
           exact hinv.2.2.2 box hb source hs)

theorem railroad_frames_labels (m : Model) (result : Layered.FamilyResult)
    (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C8b result.scene.layoutDump := by
  obtain ⟨rules, scene, _, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_frames_labels m rules scene hs

theorem PlacedRoute.horizontal_bounds {s : Shape} {x y : Int} {route : Route}
    (hr : PlacedRoute s x y route) (hg : Geometry s) :
    ∃ left right baseline, route.points = [⟨left, baseline⟩, ⟨right, baseline⟩] ∧
      y ≤ baseline ∧ baseline ≤ y + s.height := by
  induction hr with
  | sequence _ hr =>
    obtain ⟨i, _, _, _, hp⟩ := hr
    refine ⟨_, _, _, hp, ?_, ?_⟩
    · have hn := hg.nonnegative
      unfold Nonnegative at hn
      omega
    · have hn := hg.nonnegative
      unfold Nonnegative at hn
      unfold Shape.height
      omega
  | @child s x y route pair hp _ _ ih =>
    obtain ⟨left, right, baseline, he, hlo, hhi⟩ := ih (hg.child pair hp)
    have hc := child_rect_contained s hg.inside x y pair hp
    unfold Rect.Contained shapeRect at hc
    dsimp only at hc
    exact ⟨left, right, baseline, he, by omega, by omega⟩

theorem placed_route_avoids_previous_stage (p : Profile) (before : RuleState)
    (hi : StageBounds p before) (s : Shape) (x y : Int) (route : Route)
    (hg : Geometry s) (hr : PlacedRoute s x y route) (hy : before.y ≤ y)
    (box : Box) (hb : box ∈ before.state.boxes) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, he, hlo, _⟩ := hr.horizontal_bounds hg
  rw [he]
  exact previous_stage_avoids_horizontal p before hi box hb left right baseline
    (by omega)

theorem placed_route_avoids_later_box (s : Shape) (x y : Int) (route : Route)
    (hg : Geometry s) (hr : PlacedRoute s x y route) (box : Box)
    (hy : y + s.height ≤ box.rect.y) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, he, _, hhi⟩ := hr.horizontal_bounds hg
  rw [he]
  apply horizontal_route_avoids
  exact Or.inr (Or.inr (Or.inl (by omega)))

theorem placed_route_avoids_vertical_subtree
    {source target : Shape} {sx sy tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hs : Geometry source) (ht : Geometry target)
    (hr : PlacedRoute source sx sy route)
    (hb : PlacedBox target tx ty parent box)
    (hsep : sy + source.height ≤ ty ∨ ty + target.height ≤ sy) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨left, right, baseline, he, hlo, hhi⟩ := hr.horizontal_bounds hs
  have hc := descendant_contained hb.descendant ht
  unfold Rect.Contained shapeRect at hc
  dsimp only at hc
  rw [he]
  apply horizontal_route_avoids
  rcases hsep with hsep | hsep
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem placed_route_avoids_vertical_siblings
    {s : Shape} (hg : Geometry s) (x y : Int)
    (source target : Shape × Point)
    (hs : source ∈ s.children.zip s.offsets)
    (ht : target ∈ s.children.zip s.offsets)
    (parent : String) (route : Route) (box : Box)
    (hr : PlacedRoute source.1 (x+source.2.x) (y+source.2.y) route)
    (hb : PlacedBox target.1 (x+target.2.x) (y+target.2.y) parent box)
    (hsep : source.2.y + source.1.height ≤ target.2.y ∨
      target.2.y + target.1.height ≤ source.2.y) :
    ¬ Polyline.hitsRect route.points box.rect := by
  apply placed_route_avoids_vertical_subtree (hg.child source hs)
    (hg.child target ht) hr hb
  rcases hsep with hsep | hsep
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem SequenceRoute.avoids_subtree_of_corridor
    {s target : Shape} {x y tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hr : SequenceRoute s x y route) (ht : Geometry target)
    (hb : PlacedBox target tx ty parent box)
    (hc : ∀ i ∈ List.range (s.children.length-1),
      max (x+s.offsets[i]!.x+s.children[i]!.w)
          (x+s.offsets[i+1]!.x) ≤ tx ∨
      tx+target.w ≤ min (x+s.offsets[i]!.x+s.children[i]!.w)
          (x+s.offsets[i+1]!.x) ∨
      y+s.up ≤ ty ∨ ty+target.height ≤ y+s.up) :
    ¬ Polyline.hitsRect route.points box.rect := by
  obtain ⟨i, hi, _, _, hp⟩ := hr
  rw [hp]
  exact placed_box_avoids_separated_gap ht hb _ _ _ (hc i hi)

theorem SequenceRoute.avoids_left_subtree
    {s target : Shape} {x y tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hr : SequenceRoute s x y route) (ht : Geometry target)
    (hb : PlacedBox target tx ty parent box)
    (hc : ∀ i ∈ List.range (s.children.length-1),
      tx+target.w ≤ x+s.offsets[i]!.x+s.children[i]!.w ∧
      tx+target.w ≤ x+s.offsets[i+1]!.x) :
    ¬ Polyline.hitsRect route.points box.rect := by
  apply hr.avoids_subtree_of_corridor ht hb
  intro i hi
  exact Or.inr (Or.inl (Int.le_min.mpr ⟨(hc i hi).1, (hc i hi).2⟩))

theorem SequenceRoute.avoids_right_subtree
    {s target : Shape} {x y tx ty : Int} {parent : String}
    {route : Route} {box : Box}
    (hr : SequenceRoute s x y route) (ht : Geometry target)
    (hb : PlacedBox target tx ty parent box)
    (hc : ∀ i ∈ List.range (s.children.length-1),
      x+s.offsets[i]!.x+s.children[i]!.w ≤ tx ∧
      x+s.offsets[i+1]!.x ≤ tx) :
    ¬ Polyline.hitsRect route.points box.rect := by
  apply hr.avoids_subtree_of_corridor ht hb
  intro i hi
  exact Or.inl (Int.max_le.mpr ⟨(hc i hi).1, (hc i hi).2⟩)

theorem placeNode_new_route_avoids_previous_stage
    (fuel : Nat) (p : Profile) (s : Shape) (x y : Int)
    (parent : String) (before : RuleState) (final : State)
    (hi : StageBounds p before) (hg : Geometry s) (hy : before.y ≤ y)
    (h : placeNode fuel p s x y parent before.state = .ok final)
    (route : Route) (hr : route ∈ final.routes)
    (hnew : route ∉ before.state.routes)
    (box : Box) (hb : box ∈ before.state.boxes) :
    ¬ Polyline.hitsRect route.points box.rect := by
  rcases placeNode_route_origin fuel p s x y parent before.state final h
      route hr with hold | hplaced
  · exact False.elim (hnew hold)
  · exact placed_route_avoids_previous_stage p before hi s x y route
      hg hplaced hy box hb

theorem placeNode_new_route_avoids_later_box
    (fuel : Nat) (p : Profile) (s : Shape) (x y : Int)
    (parent : String) (initial final : State) (hg : Geometry s)
    (h : placeNode fuel p s x y parent initial = .ok final)
    (route : Route) (hr : route ∈ final.routes)
    (hnew : route ∉ initial.routes)
    (box : Box) (hy : y+s.height ≤ box.rect.y) :
    ¬ Polyline.hitsRect route.points box.rect := by
  rcases placeNode_route_origin fuel p s x y parent initial final h
      route hr with hold | hplaced
  · exact False.elim (hnew hold)
  · exact placed_route_avoids_later_box s x y route hg hplaced box hy

/-- The validator dump restricted to a state's boxes and routes, used to state
ancestor and scope facts at intermediate fold states. -/
def stateDump (state : State) : LayoutDump := ⟨⟨0, 0⟩, state.boxes, state.routes, []⟩

/-- The route scope of a route inside a state, mirroring `LayoutDump.routeScope`. -/
def routeScopeOf (state : State) (r : Route) : List String :=
  [r.fromId, r.toId] ++ (stateDump state).ancestors r.fromId ++
    (stateDump state).ancestors r.toId

/-- The index of the first box with id `id`, or the list length if none. -/
def boxIdx : List Box → String → Nat
  | [], _ => 0
  | b :: bs, id => if b.id == id then 0 else boxIdx bs id + 1

/-- Every non-root box's parent box occurs strictly earlier in the list. Parent walks
therefore visit each box at most once and `boxes.length` fuel never truncates them. -/
def ParentPrecedes (boxes : List Box) : Prop :=
  ∀ b ∈ boxes, b.parent ≠ "" → ∀ b' ∈ boxes, (b'.id == b.parent) = true →
    boxIdx boxes b.parent < boxIdx boxes b.id

/-- A state whose boxes have unique ids and earlier parents. Injectivity (rather
than `Nodup`) is exactly what `placeRule_id_injective` provides. -/
structure StateFacts (state : State) : Prop where
  inj : ∀ a ∈ state.boxes, ∀ b ∈ state.boxes, a.id = b.id → a = b
  pre : ParentPrecedes state.boxes

theorem stateFacts_empty : StateFacts ({boxes := [], routes := []} : State) := by
  constructor
  · intro a ha
    exact absurd ha (by simp)
  · intro b hb
    exact absurd hb (by simp)

theorem boxIdx_nil (id : String) : boxIdx [] id = 0 := rfl

theorem boxIdx_cons (b : Box) (bs : List Box) (id : String) :
    boxIdx (b :: bs) id = if b.id == id then 0 else boxIdx bs id + 1 := rfl

theorem boxIdx_lt_of_mem {boxes : List Box} {id : String}
    (h : ∃ b ∈ boxes, (b.id == id) = true) : boxIdx boxes id < boxes.length := by
  induction boxes with
  | nil => obtain ⟨b, hb, _⟩ := h; cases hb
  | cons b bs ih =>
    obtain ⟨b', hb', hbid⟩ := h
    rw [boxIdx_cons]
    split
    · next he =>
      simp only [List.length_cons]
      omega
    · next he =>
      have hmem : ∃ b'' ∈ bs, (b''.id == id) = true := by
        cases List.mem_cons.mp hb' with
        | inl hbeq =>
          subst hbeq
          exact absurd hbid he
        | inr hmem => exact ⟨_, hmem, hbid⟩
      have hlt := ih hmem
      have hlen : (b :: bs).length = bs.length + 1 := rfl
      omega

/-! Fuel monotonicity and irrelevance for `LayoutDump.ancestors.go`. -/

theorem ancestors_go_mono {boxes : List Box} :
    ∀ (k k' : Nat) (s : String), k ≤ k' →
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k s ⊆
        LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k' s := by
  intro k
  induction k with
  | zero =>
    intro k' s _ a ha
    simp only [LayoutDump.ancestors.go] at ha
    cases ha
  | succ k ih =>
    intro k' s hk
    cases k' with
    | zero => omega
    | succ k'' =>
      have hkk : k ≤ k'' := by omega
      simp only [LayoutDump.ancestors.go]
      cases hbox : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s with
      | none => intro a ha; exact ha
      | some b =>
        by_cases hpar : b.parent = ""
        · simp only [hpar, ↓reduceIte]
          intro a ha
          exact ha
        · simp only [hpar, ↓reduceIte]
          intro a ha
          simp only [List.mem_cons] at ha ⊢
          rcases ha with rfl | ha
          · exact Or.inl rfl
          · exact Or.inr (ih k'' b.parent hkk ha)

theorem ancestors_go_step_fuel {boxes : List Box}
    (hinj : ∀ a ∈ boxes, ∀ b ∈ boxes, a.id = b.id → a = b)
    (hpre : ParentPrecedes boxes) :
    ∀ (s : String) (k : Nat),
      (∀ b ∈ boxes, (b.id == s) = true → boxIdx boxes s + 1 ≤ k) →
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k + 1) s =
        LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k s := by
  -- strong induction on the index of s's box
  have key : ∀ (i : Nat) (s : String) (k : Nat),
      boxIdx boxes s = i → (∀ b ∈ boxes, (b.id == s) = true → i + 1 ≤ k) →
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k + 1) s =
        LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k s := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro s k hidx hside
      by_cases hmem : ∃ b ∈ boxes, (b.id == s) = true
      · obtain ⟨b, hbmem, hbid⟩ := hmem
        have hfind : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s = some b := by
          have heq : b.id = s := beq_iff_eq.mp hbid
          subst heq
          unfold LayoutDump.box?
          exact find_box_of_id_injective boxes hinj b hbmem
        have hk1 : i + 1 ≤ k := hside b hbmem hbid
        obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
        simp only [LayoutDump.ancestors.go]
        rw [hfind]
        by_cases hpar : b.parent = ""
        · simp [hpar]
        · simp only [hpar, ↓reduceIte]
          by_cases hpk : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? b.parent = none
          · cases k₀ with
            | zero => simp [LayoutDump.ancestors.go, hpk]
            | succ k₁ => simp [LayoutDump.ancestors.go, hpk]
          · obtain ⟨bp, hbp⟩ := Option.ne_none_iff_exists'.mp hpk
            have hfindp : boxes.find? (fun c => c.id == b.parent) = some bp := hbp
            have hbpmem : bp ∈ boxes := List.mem_of_find?_eq_some hfindp
            have hbpid : (bp.id == b.parent) = true := by
              simpa using List.find?_some hfindp
            have hlt : boxIdx boxes b.parent < i := by
              have hlt' := hpre b hbmem hpar bp hbpmem hbpid
              have heq : b.id = s := beq_iff_eq.mp hbid
              simpa only [heq, hidx] using hlt'
            have hi0 : i ≤ k₀ := by omega
            have hstep := ih (boxIdx boxes b.parent) hlt b.parent k₀
              rfl (by intro b'' hb'' hid''; omega)
            exact congrArg (b.parent :: ·) hstep
      · have hnone : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s = none := by
          cases h : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s with
          | none => rfl
          | some b =>
            have hfind : List.find? (fun b => b.id == s) boxes = some b := by
              unfold LayoutDump.box? at h
              exact h
            have hbmem := List.mem_of_find?_eq_some hfind
            have hbid := List.find?_some hfind
            exact absurd ⟨b, hbmem, hbid⟩ hmem
        by_cases hk0 : k = 0
        · subst hk0
          simp only [LayoutDump.ancestors.go, hnone]
        · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
          simp only [LayoutDump.ancestors.go, hnone]
  intro s k hside
  by_cases hmem : ∃ b ∈ boxes, (b.id == s) = true
  · obtain ⟨b, hbmem, hbid⟩ := hmem
    exact key (boxIdx boxes s) s k rfl
      (by intro b' hb' hid'; have := hside b' hb' hid'; omega)
  · have hnone : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s = none := by
      cases h : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? s with
      | none => rfl
      | some b =>
        have hfind : List.find? (fun b => b.id == s) boxes = some b := by
          unfold LayoutDump.box? at h
          exact h
        have hbmem := List.mem_of_find?_eq_some hfind
        have hbid := List.find?_some hfind
        exact absurd ⟨b, hbmem, hbid⟩ hmem
    by_cases hk0 : k = 0
    · subst hk0
      simp only [LayoutDump.ancestors.go, hnone]
    · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = k₀ + 1 := ⟨k - 1, by omega⟩
      simp only [LayoutDump.ancestors.go, hnone]
theorem ancestors_go_fuel_ge {boxes : List Box}
    (hinj : ∀ a ∈ boxes, ∀ b ∈ boxes, a.id = b.id → a = b)
    (hpre : ParentPrecedes boxes) (s : String)
    (hs : ∀ b ∈ boxes, (b.id == s) = true → boxIdx boxes s + 1 ≤ boxes.length) :
    ∀ (k : Nat), boxes.length ≤ k →
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k s =
        LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ boxes.length s := by
  have hsteps : ∀ n : Nat,
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (boxes.length + n) s =
        LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ boxes.length s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.add_succ]
      exact (ancestors_go_step_fuel hinj hpre s (boxes.length + n) (by
        intro b hb hbid
        have h := hs b hb hbid
        omega)).trans ih
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = boxes.length + n := ⟨k - boxes.length, by omega⟩
  exact hsteps n

theorem ancestors_go_trans {boxes : List Box} :
    ∀ (k₁ k₂ : Nat) (a b c : String),
      a ∈ LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k₁ b →
      b ∈ LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k₂ c →
      a ∈ LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k₁ + k₂) c := by
  intro k₁ k₂ a b c
  revert c
  revert b
  revert a
  revert k₁
  induction k₂ with
  | zero =>
    intro k₁ a b c ha hb
    simp only [LayoutDump.ancestors.go] at hb
    cases hb
  | succ k₂ ih =>
    intro k₁ a b c ha hb
    cases hbc : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? c with
    | none =>
      simp only [LayoutDump.ancestors.go, hbc] at hb
      cases hb
    | some bc =>
      have hgo : LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k₂ + 1) c =
          if bc.parent = "" then [] else bc.parent ::
            LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ k₂ bc.parent := by
        simp only [LayoutDump.ancestors.go, hbc]
      rw [hgo] at hb
      by_cases hpar : bc.parent = ""
      · simp only [hpar, ↓reduceIte] at hb
        cases hb
      · simp only [hpar, ↓reduceIte, List.mem_cons] at hb
        have hgoal : LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k₁ + (k₂ + 1)) c =
            bc.parent :: LayoutDump.ancestors.go ⟨⟨0, 0⟩, boxes, [], []⟩ (k₁ + k₂) bc.parent := by
          have heq : k₁ + (k₂ + 1) = (k₁ + k₂) + 1 := by omega
          rw [heq]
          simp only [LayoutDump.ancestors.go, hbc, hpar, ↓reduceIte]
        rw [hgoal]
        simp only [List.mem_cons]
        rcases hb with rfl | hb'
        · exact Or.inr (ancestors_go_mono k₁ (k₁ + k₂) _ (by omega) ha)
        · exact Or.inr (ih k₁ a b bc.parent ha hb')

theorem ancestors_trans' {boxes : List Box}
    (hinj : ∀ a ∈ boxes, ∀ b ∈ boxes, a.id = b.id → a = b)
    (hpre : ParentPrecedes boxes)
    {a b c : String}
    (ha : a ∈ (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).ancestors b)
    (hb : b ∈ (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).ancestors c) :
    a ∈ (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).ancestors c := by
  unfold LayoutDump.ancestors at ha hb ⊢
  have h := ancestors_go_trans boxes.length boxes.length a b c ha hb
  have hge := ancestors_go_fuel_ge hinj hpre c
    (by intro b' hb' hbid
        have := boxIdx_lt_of_mem (boxes := boxes) ⟨b', hb', hbid⟩
        omega)
    (boxes.length + boxes.length) (by omega)
  rw [hge] at h
  exact h

theorem ancestors_mem_parent {boxes : List Box} {id p : String} {b : Box}
    (hb : (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).box? id = some b)
    (hpar : b.parent = p) (hne : p ≠ "") :
    p ∈ (⟨⟨0, 0⟩, boxes, [], []⟩ : LayoutDump).ancestors id := by
  cases boxes with
  | nil => simp [LayoutDump.box?] at hb
  | cons c cs =>
    unfold LayoutDump.ancestors
    have hfuel : (⟨⟨0, 0⟩, c :: cs, [], []⟩ : LayoutDump).boxes.length =
        cs.length + 1 := rfl
    rw [hfuel]
    simp [LayoutDump.ancestors.go, hb, hpar, hne]

theorem ancestors_dump_congr {boxes : List Box} {c₁ c₂ : Size}
    {r₁ r₂ : List Route} {l₁ l₂ : List Label} :
    ∀ (k : Nat) (s : String),
      LayoutDump.ancestors.go ⟨c₁, boxes, r₁, l₁⟩ k s =
        LayoutDump.ancestors.go ⟨c₂, boxes, r₂, l₂⟩ k s := by
  intro k
  induction k with
  | zero => intro s; simp only [LayoutDump.ancestors.go]
  | succ k ih =>
    intro s
    simp only [LayoutDump.ancestors.go]
    have heq : (⟨c₁, boxes, r₁, l₁⟩ : LayoutDump).box? s =
        (⟨c₂, boxes, r₂, l₂⟩ : LayoutDump).box? s := rfl
    rw [heq]
    cases hbox : (⟨c₂, boxes, r₂, l₂⟩ : LayoutDump).box? s with
    | none => rfl
    | some b =>
      by_cases hpar : b.parent = ""
      · simp only [hpar, ↓reduceIte]
      · simp only [hpar, ↓reduceIte]
        exact congrArg (b.parent :: ·) (ih b.parent)

theorem routeScopeOf_eq (state : State) (r : Route) :
    routeScopeOf state r = (stateDump state).routeScope r := rfl

theorem boxIdx_append_left {xs ys : List Box} {id : String}
    (hmem : ∃ b ∈ xs, (b.id == id) = true) :
    boxIdx (xs ++ ys) id = boxIdx xs id := by
  induction xs with
  | nil => obtain ⟨b, hb, _⟩ := hmem; cases hb
  | cons x xs ih =>
    obtain ⟨b, hbmem, hbid⟩ := hmem
    have hcon : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
    rw [hcon, boxIdx_cons, boxIdx_cons]
    by_cases he : (x.id == id) = true
    · rw [ite_eq_left he, ite_eq_left he]
    · rw [ite_eq_right he, ite_eq_right he]
      have hmem' : ∃ b ∈ xs, (b.id == id) = true := by
        rcases List.mem_cons.mp hbmem with rfl | hb''
        · exact absurd hbid he
        · exact ⟨b, hb'', hbid⟩
      rw [ih hmem']
theorem mapM_elem_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β) (x : α),
      xs.mapM f = .ok ys → x ∈ xs → ∃ y, f x = .ok y := by
  intro xs
  induction xs with
  | nil => intro _ x _ hx; cases hx
  | cons a as ih =>
    intro ys x h hx
    cases hf : f a with
    | error e => simp [List.mapM_cons, hf, Bind.bind, Except.bind] at h
    | ok b =>
      cases has : as.mapM f with
      | error e => simp [List.mapM_cons, hf, has, Bind.bind, Except.bind] at h
      | ok bs =>
        rcases List.mem_cons.mp hx with hxx | hx'
        · subst x
          exact ⟨b, hf⟩
        · exact ih bs x has hx'

/-- Child link in the model box forest. -/
def ChildLink (m : Model) (p c : ModelBox) : Prop :=
  c ∈ m.boxes ∧ c.parent = p.id

/-- Reachability through child links with an explicit step count. -/
inductive ReachesLen (m : Model) : ModelBox → ModelBox → Nat → Prop where
  | refl (a : ModelBox) : ReachesLen m a a 0
  | step (a b c : ModelBox) (n : Nat) (h : ChildLink m a b)
      (t : ReachesLen m b c n) : ReachesLen m a c (n + 1)

theorem decodeNode_child_ok (F : Nat) (m : Model) (a c : ModelBox) (n : Node)
    (hc : ChildLink m a c)
    (h : Kinds.Railroad.decodeNode (F + 1) m a = .ok n) :
    ∃ n', Kinds.Railroad.decodeNode F m c = .ok n' := by
  obtain ⟨hcmem, hcpar⟩ := hc
  have hmem : c ∈ Kinds.Railroad.children m a.id := by
    unfold Kinds.Railroad.children
    simp only [List.mem_filter]
    refine ⟨hcmem, ?_⟩
    simp [hcpar]
  simp only [Kinds.Railroad.decodeNode] at h
  cases hmap : (Kinds.Railroad.children m a.id).mapM (Kinds.Railroad.decodeNode F m) with
  | error e => simp [hmap, Bind.bind, Except.bind] at h
  | ok kids => exact mapM_elem_ok _ _ _ _ hmap hmem

theorem ReachesLen_trans (m : Model) :
    ∀ (a b c : ModelBox) (L1 L2 : Nat),
      ReachesLen m a b L1 → ReachesLen m b c L2 → ReachesLen m a c (L1 + L2) := by
  intro a b c L1 L2 h1 h2
  revert h2
  revert c
  revert L2
  induction h1 with
  | refl a =>
    intro L2 c h2
    simpa using h2
  | step a b c' L h _ ih =>
    intro L2 c h2
    rw [Nat.add_right_comm]
    exact ReachesLen.step a b c (L + L2) h (ih L2 c h2)

theorem path_fuel (m : Model) :
    ∀ (F : Nat) (a b : ModelBox) (L : Nat), ReachesLen m a b L →
      ∀ (n : Node), Kinds.Railroad.decodeNode F m a = .ok n → L ≤ F →
        ∃ n', Kinds.Railroad.decodeNode (F - L) m b = .ok n' := by
  intro F a b L hr
  revert F
  induction hr with
  | refl a =>
    intro F n h _
    simp only [Nat.sub_zero]
    exact ⟨n, h⟩
  | step a b c L hlink _ ih =>
    intro F n h hle
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    obtain ⟨mid, hmid⟩ := decodeNode_child_ok F' m a b n hlink h
    have hle' : L ≤ F' := by omega
    obtain ⟨n'', hn''⟩ := ih F' mid hmid hle'
    have heq : F' + 1 - (L + 1) = F' - L := by omega
    rw [heq]
    exact ⟨n'', hn''⟩

theorem decode_fuel_ge_path (m : Model) :
    ∀ (F : Nat) (a b : ModelBox) (L : Nat), ReachesLen m a b L →
      ∀ (n : Node), Kinds.Railroad.decodeNode F m a = .ok n → L ≤ F := by
  intro F a b L hr
  revert F
  induction hr with
  | refl a =>
    intro F n _
    omega
  | step a b c L hlink _ ih =>
    intro F n h
    cases F with
    | zero => simp [Kinds.Railroad.decodeNode] at h
    | succ F' =>
      obtain ⟨mid, hmid⟩ := decodeNode_child_ok F' m a b n hlink h
      have := ih F' mid hmid
      omega

theorem cycle_fails (m : Model) (a b : ModelBox) (L1 L2 : Nat)
    (h1 : ReachesLen m a b L1) (h2 : ReachesLen m b a L2)
    (hpos : 0 < L1 + L2) :
    ∀ (F : Nat) (n : Node),
      Kinds.Railroad.decodeNode F m a = .ok n → False := by
  intro F
  induction F using Nat.strongRecOn with
  | _ F ih =>
    intro n h
    cases F with
    | zero => simp [Kinds.Railroad.decodeNode] at h
    | succ F' =>
      have hL1 := decode_fuel_ge_path m (F' + 1) a b L1 h1 n h
      obtain ⟨nb, hnb⟩ := path_fuel m (F' + 1) a b L1 h1 n h hL1
      have hL2 := decode_fuel_ge_path m (F' + 1 - L1) b a L2 h2 nb hnb
      obtain ⟨na, hna⟩ := path_fuel m (F' + 1 - L1) b a L2 h2 nb hnb hL2
      have hlt : F' + 1 - L1 - L2 < F' + 1 := by omega
      exact ih _ hlt na hna
theorem SourceDescendant_reaches (m : Model) :
    ∀ (a b : ModelBox), SourceDescendant m a b → ∃ L, ReachesLen m a b L := by
  intro a b h
  induction h with
  | root box => exact ⟨0, .refl box⟩
  | child hc hp _ ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L + 1, ReachesLen.step _ _ _ L ⟨hc, hp⟩ hL⟩

theorem nodeIn_model_path (m : Model) :
    ∀ (F : Nat) (S : ModelBox) (root node : Node),
      S ∈ m.boxes →
      Kinds.Railroad.decodeNode F m S = .ok root → NodeIn root node →
      ∃ (T : ModelBox) (L : Nat), T ∈ m.boxes ∧ node.id = T.id ∧
        ReachesLen m S T L ∧ L ≤ F := by
  intro F S root node hS h hn
  revert h
  revert hS
  revert S
  revert F
  induction hn with
  | root node =>
    intro F S hS h
    have hmeta := decodeNode_metadata F m S node h
    exact ⟨S, 0, hS, hmeta.1, .refl S, by omega⟩
  | @child outer child descendant hc _ ih =>
    intro F S hS h
    cases F with
    | zero => simp [Kinds.Railroad.decodeNode] at h
    | succ F' =>
      obtain ⟨source, hs, hpar, _, hd⟩ :=
        decodeNode_child_origin F' m S outer child h hc
      obtain ⟨T, L, hTmem, hTid, hreach, hle⟩ := ih F' source hs hd
      refine ⟨T, L + 1, hTmem, hTid, ?_, by omega⟩
      exact ReachesLen.step S source T L ⟨hs, hpar⟩ hreach

theorem rule_node_ne_empty (m : Model) (rules : List Rule)
    (hl : Kinds.Railroad.lower m = .ok rules) :
    ∀ (rule : Rule) (node : Node), rule ∈ rules → NodeIn rule.root node →
      node.id ≠ "" := by
  intro rule node hr hn hid
  unfold Kinds.Railroad.lower at hl
  obtain ⟨C, hCmem, hC⟩ := mapM_success_origin _ _ _ hl rule hr
  have hCbox : C ∈ m.boxes := (List.mem_filter.mp hCmem).1
  have hCpar : C.parent = "" := by simpa using (List.mem_filter.mp hCmem).2
  obtain ⟨D, hDmem, hDdec, hDpath, _⟩ :=
    decodeRule_definition_origin m C rule hCbox hC
  obtain ⟨T, L, _, hTid, hreach, _⟩ :=
    nodeIn_model_path m _ D rule.root node hDmem hDdec hn
  have hTid0 : T.id = "" := hTid.symm.trans hid
  have hTC : ReachesLen m T C 1 :=
    ReachesLen.step T C C 0 ⟨hCbox, by rw [hCpar]; exact hTid0.symm⟩ (.refl C)
  obtain ⟨Lk, hLk⟩ := SourceDescendant_reaches m C D hDpath
  have hDT : ReachesLen m D C (L + 1) :=
    ReachesLen_trans m D T C L 1 hreach hTC
  have hback : ReachesLen m D D (L + 1 + Lk) :=
    ReachesLen_trans m D C D (L + 1) Lk hDT hLk
  exact cycle_fails m D D (L + 1 + Lk) 0 hback (.refl D) (by omega)
    (m.boxes.length + 1) _ hDdec

theorem boxIdx_append_fresh (boxes : List Box) (box : Box)
    (hfresh : ∀ old ∈ boxes, old.id ≠ box.id) :
    boxIdx (boxes ++ [box]) box.id = boxes.length := by
  induction boxes with
  | nil => simp [boxIdx]
  | cons old rest ih =>
    have hne : (old.id == box.id) = false := by
      simp [hfresh old (by simp)]
    have htail : ∀ old ∈ rest, old.id ≠ box.id := by
      intro old hold
      exact hfresh old (List.mem_cons_of_mem _ hold)
    simp only [List.cons_append, boxIdx_cons, hne, Bool.false_eq_true,
      ↓reduceIte, List.length_cons]
    exact congrArg (· + 1) (ih htail)

theorem stateFacts_append_box (state : State) (box : Box)
    (hstate : StateFacts state)
    (hfresh : ∀ old ∈ state.boxes, old.id ≠ box.id)
    (hnotParent : ∀ old ∈ state.boxes, old.parent ≠ box.id)
    (hparent : box.parent ≠ "" →
      ∃ parent ∈ state.boxes, (parent.id == box.parent) = true) :
    StateFacts {state with boxes := state.boxes ++ [box]} := by
  constructor
  · intro a ha b hb hid
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp hb with hb | hb
      · exact hstate.inj a ha b hb hid
      · have hb : b = box := List.mem_singleton.mp hb
        subst b
        exact False.elim (hfresh a ha hid)
    · have ha : a = box := List.mem_singleton.mp ha
      subst a
      rcases List.mem_append.mp hb with hb | hb
      · exact False.elim (hfresh b hb hid.symm)
      · exact (List.mem_singleton.mp hb).symm
  · intro b hb hne parent hp hpid
    rcases List.mem_append.mp hb with hb | hb
    · have hbold : boxIdx (state.boxes ++ [box]) b.id =
          boxIdx state.boxes b.id :=
        boxIdx_append_left ⟨b, hb, by simp⟩
      rcases List.mem_append.mp hp with hp | hp
      · have hpold : boxIdx (state.boxes ++ [box]) b.parent =
            boxIdx state.boxes b.parent := boxIdx_append_left ⟨parent, hp, hpid⟩
        rw [hbold, hpold]
        exact hstate.pre b hb hne parent hp hpid
      · have hp : parent = box := List.mem_singleton.mp hp
        subst parent
        exact False.elim (hnotParent b hb (beq_iff_eq.mp hpid).symm)
    · have hb : b = box := List.mem_singleton.mp hb
      subst b
      obtain ⟨p, hp, hpid'⟩ := hparent hne
      have hpold : boxIdx (state.boxes ++ [box]) box.parent =
          boxIdx state.boxes box.parent := boxIdx_append_left ⟨p, hp, hpid'⟩
      rw [hpold, boxIdx_append_fresh state.boxes box hfresh]
      exact boxIdx_lt_of_mem ⟨p, hp, hpid'⟩
end Elegant.Railroad
