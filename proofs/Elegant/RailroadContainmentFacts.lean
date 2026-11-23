import Elegant.RailroadFrameFacts
import Elegant.RailroadClearanceFacts

set_option autoImplicit false

namespace Elegant.Railroad

 theorem stateFacts_append_injective (state : State) (box : Box)
    (hi : StateFacts state) (hp : ParentsPresent state)
    (hinj : ∀ a ∈ state.boxes ++ [box], ∀ b ∈ state.boxes ++ [box],
      a.id = b.id → a = b)
    (hparent : box.parent ≠ "" →
      ∃ parent ∈ state.boxes, parent.id = box.parent) :
    StateFacts {state with boxes := state.boxes ++ [box]} := by
  constructor
  · exact hinj
  · intro child hc hn enclosing he hid
    have hparentOld : ∃ parent ∈ state.boxes, parent.id = child.parent := by
      rcases List.mem_append.mp hc with hc | hc
      · exact hp child hc hn
      · have hchild : child = box := by simpa using hc
        subst child
        exact hparent hn
    obtain ⟨parent, hpm, hpid⟩ := hparentOld
    have hparentIdx : boxIdx (state.boxes ++ [box]) child.parent =
        boxIdx state.boxes child.parent :=
      boxIdx_append_left ⟨parent, hpm, by simp [hpid]⟩
    by_cases hchildOld : ∃ old ∈ state.boxes, old.id = child.id
    · obtain ⟨old, ho, hoid⟩ := hchildOld
      have heq : old = child := hinj old (List.mem_append_left _ ho) child hc hoid
      subst child
      rw [hparentIdx, boxIdx_append_left ⟨old, ho, by simp⟩]
      exact hi.pre old ho hn parent hpm (by simp [hpid])
    · have hfresh : ∀ old ∈ state.boxes, old.id ≠ box.id := by
        have hchild : child = box := by
          rcases List.mem_append.mp hc with hc | hc
          · exact False.elim (hchildOld ⟨child, hc, rfl⟩)
          · simpa using hc
        subst child
        intro old ho hid
        exact hchildOld ⟨old, ho, hid⟩
      have hchild : child = box := by
        rcases List.mem_append.mp hc with hc | hc
        · exact False.elim (hchildOld ⟨child, hc, rfl⟩)
        · simpa using hc
      subst child
      rw [hparentIdx, boxIdx_append_fresh state.boxes box hfresh]
      exact boxIdx_lt_of_mem ⟨parent, hpm, by simp [hpid]⟩

theorem foldlM_parent_order {α : Type}
    (f : State → α → Except LayoutError State) (root : Box)
    (hext : ∀ a before after, f before a = .ok after → ExtendsBoxes before after)
    (hstep : ∀ a before after, root ∈ before.boxes →
      StateFacts before → ParentsPresent before →
      (∀ b ∈ after.boxes, ∀ c ∈ after.boxes, b.id = c.id → b = c) →
      f before a = .ok after → StateFacts after ∧ ParentsPresent after) :
    ∀ (xs : List α) (initial final : State),
      root ∈ initial.boxes → StateFacts initial → ParentsPresent initial →
      (∀ b ∈ final.boxes, ∀ c ∈ final.boxes, b.id = c.id → b = c) →
      xs.foldlM f initial = .ok final → StateFacts final ∧ ParentsPresent final := by
  intro xs
  induction xs with
  | nil =>
    intro initial final hr hi hp hinj h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst final
    exact ⟨hi, hp⟩
  | cons head tail ih =>
    intro initial final hr hi hp hinj h
    cases hh : f initial head with
    | error e => simp [List.foldlM_cons, hh, bind, Except.bind] at h
    | ok middle =>
      have ht : tail.foldlM f middle = .ok final := by
        simpa [List.foldlM_cons, hh, bind, Except.bind] using h
      have hm := foldlM_boxes_extends f hext tail middle final ht
      have hmiddle := hstep head initial middle hr hi hp
        (fun b hb c hc hid => hinj b (hm.mem b hb) c (hm.mem c hc) hid) hh
      exact ih middle final ((hext head initial middle hh).mem root hr)
        hmiddle.1 hmiddle.2 hinj ht

theorem placeNode_stateFacts_of_injective :
    ∀ (fuel : Nat) (p : Profile) (s : Shape) (x y : Int) (parent : String)
      (initial final : State),
      StateFacts initial → ParentsPresent initial →
      (parent ≠ "" → ∃ enclosing ∈ initial.boxes, enclosing.id = parent) →
      (∀ a ∈ final.boxes, ∀ b ∈ final.boxes, a.id = b.id → a = b) →
      placeNode fuel p s x y parent initial = .ok final →
      StateFacts final ∧ ParentsPresent final := by
  intro fuel
  induction fuel with
  | zero => intro p s x y parent initial final hi hp hparent hinj h; cases h
  | succ fuel ih =>
    intro p s x y parent initial final hi hp hparent hinj h
    let root := Box.mk s.id (if leaf s.kind then "node" else "group")
      (shapeRect s x y) parent (leaf s.kind)
    let base : State := {initial with boxes := initial.boxes ++ [root]}
    have hbaseExt : ExtendsBoxes base final := by
      simp only [placeNode] at h
      split at h
      · rename_i hleaf
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst final
        exact ⟨[], by simp [base, root, hleaf]⟩
      · rename_i hleaf
        have hf := foldlM_boxes_extends
          (fun acc (pair : Shape × Point) =>
            placeNode fuel p pair.1 (x+pair.2.x) (y+pair.2.y) s.id acc)
          (fun pair before after he =>
            placeNode_extends_boxes fuel p pair.1 _ _ s.id before after he)
          _ _ final h
        apply ExtendsBoxes.trans (b := _) _ hf
        split
        · exact ⟨[], by simp [base, root, sequenceJoins_boxes, hleaf]⟩
        · exact ⟨[], by simp [base, root, hleaf]⟩
    have hbase : StateFacts base := stateFacts_append_injective initial root hi hp
      (fun a ha b hb hid => hinj a (hbaseExt.mem a ha) b (hbaseExt.mem b hb) hid)
      hparent
    have hbaseParents : ParentsPresent base :=
      parentsPresent_append_box initial root hp hparent
    simp only [placeNode] at h
    split at h
    · rename_i hleaf
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst final
      simp only [base, root, hleaf, ↓reduceIte] at hbase hbaseParents
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa only [hleaf] using hbase.inj
      · simpa only [hleaf] using hbase.pre
      · simpa only [ParentsPresent, hleaf] using hbaseParents
    · rename_i hleaf
      simp only [base, root, ite_eq_right hleaf] at hbase hbaseParents
      apply foldlM_parent_order
        (fun acc (pair : Shape × Point) =>
          placeNode fuel p pair.1 (x+pair.2.x) (y+pair.2.y) s.id acc)
        root
        (fun pair before after he =>
          placeNode_extends_boxes fuel p pair.1 _ _ s.id before after he)
        (fun pair before after hr hb hp hj he =>
          ih p pair.1 _ _ s.id before after hb hp
            (fun _ => ⟨root, hr, rfl⟩) hj he) _ _ final ?_ ?_ ?_ hinj h
      · split
        · simp [sequenceJoins_boxes, root, hleaf]
        · simp [root, hleaf]
      · split
        · apply sequenceJoins_stateFacts
          exact ⟨hbase.inj, hbase.pre⟩
        · exact ⟨hbase.inj, hbase.pre⟩
      · split
        · exact sequenceJoins_parentsPresent s x y _ hbaseParents
        · exact hbaseParents

theorem addRule_stateFacts_of_injective (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State)
    (hi : StateFacts state) (hp : ParentsPresent state)
    (hinj : ∀ a ∈ (addRule p rule s g y state).boxes,
      ∀ b ∈ (addRule p rule s g y state).boxes, a.id = b.id → a = b) :
    StateFacts (addRule p rule s g y state) ∧
      ParentsPresent (addRule p rule s g y state) := by
  unfold addRule at hinj ⊢
  by_cases hempty : (rule.id == "") = true
  · simp only [hempty, ↓reduceIte] at hinj ⊢
    exact ⟨hi, hp⟩
  · simp only [hempty] at hinj ⊢
    have hparent : (Box.mk rule.id "group" (ruleFrame p g y) "" false).parent ≠ "" →
        ∃ parent ∈ state.boxes, parent.id = "" := by
      intro h
      exact False.elim (h rfl)
    have hs := stateFacts_append_injective state
      ⟨rule.id, "group", ruleFrame p g y, "", false⟩ hi hp hinj hparent
    exact ⟨⟨hs.inj, hs.pre⟩,
      parentsPresent_append_box state
        ⟨rule.id, "group", ruleFrame p g y, "", false⟩ hp hparent⟩

theorem placeRule_stateFacts_of_injective (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (hi : StateFacts before.state) (hpresent : ParentsPresent before.state)
    (hinj : ∀ a ∈ after.state.boxes, ∀ b ∈ after.state.boxes,
      a.id = b.id → a = b)
    (h : placeRule m metric before rule = .ok after) :
    StateFacts after.state ∧ ParentsPresent after.state := by
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
      · cases hnode : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hnode
          simp only [hnode] at h
          cases h
        | ok state =>
          dsimp only [g] at hnode
          simp only [hnode, pure, Except.pure, Except.ok.injEq] at h
          subst after
          have hext := placeNode_extends_boxes _ _ _ _ _ _ _ _ hnode
          have hadd := addRule_stateFacts_of_injective m.profile rule s g
            before.y before.state hi hpresent
            (fun a ha b hb hid =>
              hinj a (hext.mem a ha) b (hext.mem b hb) hid)
          apply placeNode_stateFacts_of_injective _ _ _ _ _ _ _ _
            hadd.1 hadd.2 ?_ hinj hnode
          intro hne
          refine ⟨Box.mk rule.id "group" (ruleFrame m.profile g before.y) "" false,
            ?_, rfl⟩
          simp [addRule, hne]

theorem placeRule_extends_boxes (m : Model) (metric : Measure.Metric)
    (before after : RuleState) (rule : Rule)
    (h : placeRule m metric before rule = .ok after) :
    ExtendsBoxes before.state after.state := by
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
      · cases hn : placeNode (m.boxes.length+1) m.profile s
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule s g before.y before.state) with
        | error e =>
          dsimp only [g] at hn
          simp only [hn] at h
          cases h
        | ok state =>
          dsimp only [g] at hn
          simp only [hn, pure, Except.pure, Except.ok.injEq] at h
          subst after
          apply ExtendsBoxes.trans (b := addRule m.profile rule s g before.y before.state)
            ?_ (placeNode_extends_boxes _ _ _ _ _ _ _ _ hn)
          unfold addRule
          split
          · exact ExtendsBoxes.refl _
          · exact ⟨_, rfl⟩

theorem ruleFold_extends_boxes (m : Model) (metric : Measure.Metric) :
    ∀ (rules : List Rule) (before after : RuleState),
      rules.foldlM (placeRule m metric) before = .ok after →
      ExtendsBoxes before.state after.state := by
  intro rules
  induction rules with
  | nil =>
    intro before after h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst after
    exact ExtendsBoxes.refl _
  | cons rule rest ih =>
    intro before after h
    cases hr : placeRule m metric before rule with
    | error e => simp [List.foldlM_cons, hr, bind, Except.bind] at h
    | ok next =>
      have ht : rest.foldlM (placeRule m metric) next = .ok after := by
        simpa [List.foldlM_cons, hr, bind, Except.bind] using h
      exact (placeRule_extends_boxes m metric before next rule hr).trans
        (ih next after ht)

theorem ruleFold_stateFacts_of_injective (m : Model) (metric : Measure.Metric) :
    ∀ (rules : List Rule) (before after : RuleState),
      StateFacts before.state → ParentsPresent before.state →
      (∀ a ∈ after.state.boxes, ∀ b ∈ after.state.boxes, a.id = b.id → a = b) →
      rules.foldlM (placeRule m metric) before = .ok after →
      StateFacts after.state ∧ ParentsPresent after.state := by
  intro rules
  induction rules with
  | nil =>
    intro before after hi hp hinj h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst after
    exact ⟨hi, hp⟩
  | cons rule rest ih =>
    intro before after hi hp hinj h
    cases hr : placeRule m metric before rule with
    | error e => simp [List.foldlM_cons, hr, bind, Except.bind] at h
    | ok next =>
      have ht : rest.foldlM (placeRule m metric) next = .ok after := by
        simpa [List.foldlM_cons, hr, bind, Except.bind] using h
      have hext := ruleFold_extends_boxes m metric rest next after ht
      have hn := placeRule_stateFacts_of_injective m metric before next rule hi hp
        (fun a ha b hb hid => hinj a (hext.mem a ha) b (hext.mem b hb) hid) hr
      exact ih next after hn.1 hn.2 hinj ht

theorem layout_lowered_stateFacts (m : Model) (hwf : WellFormed m)
    (rules : List Rule) (scene : Scene)
    (hl : Kinds.Railroad.lower m = .ok rules)
    (h : layout m rules = .ok scene) :
    StateFacts ({boxes := scene.boxes, routes := scene.routes} : State) ∧
      ParentsPresent ({boxes := scene.boxes, routes := scene.routes} : State) := by
  have hinj := layout_lowered_id_injective m hwf rules scene hl h
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok final =>
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           have hs := ruleFold_stateFacts_of_injective m metric rules
             {y := constant m.profile "margin"} final stateFacts_empty
             parentsPresent_empty hinj hf
           exact ⟨⟨hs.1.inj, hs.1.pre⟩, hs.2⟩)

theorem PlacedBox.root_or_ancestor {s : Shape} {x y : Int} {parent : String}
    {box : Box} (hbox : PlacedBox s x y parent box) :
    ∀ (state : State), StateFacts state →
      (∀ b, PlacedBox s x y parent b → b.id ≠ "") →
      (∀ b, PlacedBox s x y parent b → b ∈ state.boxes) →
      box.id = s.id ∨ s.id ∈ (stateDump state).ancestors box.id := by
  induction hbox with
  | root s x y parent =>
    intro state hstate hnonempty hmem
    exact Or.inl rfl
  | @child s x y parent pair hp hn box hb ih =>
    intro state hstate hnonempty hmem
    have hchild := ih state hstate
      (fun b hb => hnonempty b (.child pair hp hn hb))
      (fun b hb => hmem b (.child pair hp hn hb))
    let enclosing := Box.mk s.id (if leaf s.kind then "node" else "group")
      (shapeRect s x y) parent (leaf s.kind)
    let childRoot := Box.mk pair.1.id
      (if leaf pair.1.kind then "node" else "group")
      (shapeRect pair.1 (x+pair.2.x) (y+pair.2.y)) s.id (leaf pair.1.kind)
    have hrootNe : s.id ≠ "" := hnonempty enclosing (.root s x y parent)
    have hchildRoot : childRoot ∈ state.boxes :=
      hmem childRoot (.child pair hp hn (.root pair.1 _ _ s.id))
    have hparent := stateDump_parent_ancestor state hstate childRoot hchildRoot hrootNe
    change s.id ∈ (stateDump state).ancestors pair.1.id at hparent
    apply Or.inr
    rcases hchild with hid | ha
    · simpa only [hid] using hparent
    · exact stateDump_ancestors_trans state hstate hparent ha

theorem PlacedBox.separated_or_ancestor {s : Shape} {x y : Int} {parent : String}
    {a : Box} (ha : PlacedBox s x y parent a) :
    ∀ (state : State), StateFacts state → Geometry s →
      (∀ b, PlacedBox s x y parent b → b.id ≠ "") →
      (∀ b, PlacedBox s x y parent b → b ∈ state.boxes) →
      ∀ b, PlacedBox s x y parent b →
      a.id = b.id ∨
        a.id ∈ (stateDump state).ancestors b.id ∨
        b.id ∈ (stateDump state).ancestors a.id ∨ Disjoint a.rect b.rect := by
  induction ha with
  | root s x y parent =>
    intro state hstate hg hnonempty hmem b hb
    rcases hb.root_or_ancestor state hstate hnonempty hmem with hid | hancestor
    · exact Or.inl hid.symm
    · exact Or.inr (Or.inl hancestor)
  | @child s x y parent pair hp hn a ha ih =>
    intro state hstate hg hnonempty hmem b hb
    cases hb with
    | root =>
      rcases (PlacedBox.child pair hp hn ha).root_or_ancestor
          state hstate hnonempty hmem with hid | hancestor
      · exact Or.inl hid
      · exact Or.inr (Or.inr (Or.inl hancestor))
    | child other ho hother hb =>
      by_cases he : pair = other
      · subst other
        exact ih state hstate (hg.child pair hp)
          (fun b hb => hnonempty b (.child pair hp hn hb))
          (fun b hb => hmem b (.child pair hp hn hb)) b hb
      · have hs : ChildrenSeparated s := by
          cases hg with
          | node _ _ _ _ separated _ => exact separated
        exact Or.inr (Or.inr (Or.inr
          (placed_boxes_in_separated_children hg x y pair other hp ho
            s.id s.id a b ha hb (hs.members pair other hp ho he x y))))

theorem placedBox_lowered_ne_empty (fuel : Nat) (m : Model) (rules : List Rule)
    (hl : Kinds.Railroad.lower m = .ok rules) (rule : Rule) (hr : rule ∈ rules)
    (metric : Measure.Metric) (shape : Shape)
    (hm : measure fuel m.profile metric rule.root = .ok shape)
    (x y : Int) (parent : String) (box : Box)
    (hb : PlacedBox shape x y parent box) : box.id ≠ "" := by
  obtain ⟨node, hn, hid⟩ :=
    placedBox_measured_origin fuel m.profile metric rule.root shape x y parent box hm hb
  rw [hid]
  exact rule_node_ne_empty m rules hl rule node hr hn

theorem PlacedBox.parent_ancestor {s : Shape} {x y : Int} {parent : String}
    {box : Box} (hb : PlacedBox s x y parent box)
    (state : State) (hstate : StateFacts state)
    (hnonempty : ∀ b, PlacedBox s x y parent b → b.id ≠ "")
    (hmem : ∀ b, PlacedBox s x y parent b → b ∈ state.boxes)
    (hparent : parent ≠ "") :
    parent ∈ (stateDump state).ancestors box.id := by
  let root := Box.mk s.id (if leaf s.kind then "node" else "group")
    (shapeRect s x y) parent (leaf s.kind)
  have hr := stateDump_parent_ancestor state hstate root
    (hmem root (.root s x y parent)) hparent
  change parent ∈ (stateDump state).ancestors s.id at hr
  rcases hb.root_or_ancestor state hstate hnonempty hmem with hid | ha
  · simpa only [hid] using hr
  · exact stateDump_ancestors_trans state hstate hr ha

theorem placed_boxes_frame_clear {s : Shape} {x y : Int} {parent : String}
    (state : State) (hstate : StateFacts state) (hg : Geometry s)
    (hnonempty : ∀ b, PlacedBox s x y parent b → b.id ≠ "")
    (hmem : ∀ b, PlacedBox s x y parent b → b ∈ state.boxes)
    (a b : Box) (ha : PlacedBox s x y parent a) (hb : PlacedBox s x y parent b)
    (hne : a.id ≠ b.id)
    (hab : a.id ∉ (stateDump state).ancestors b.id)
    (hba : b.id ∉ (stateDump state).ancestors a.id) :
    Disjoint a.rect b.rect := by
  rcases ha.separated_or_ancestor state hstate hg hnonempty hmem b hb with
    hid | ha | hb | hdisjoint
  · exact False.elim (hne hid)
  · exact False.elim (hab ha)
  · exact False.elim (hba hb)
  · exact hdisjoint

def FramePair (state : State) (a b : Box) : Prop :=
  a.id = b.id ∨ a.id ∈ (stateDump state).ancestors b.id ∨
    b.id ∈ (stateDump state).ancestors a.id ∨ Disjoint a.rect b.rect

theorem FramePair.symm {state : State} {a b : Box} (h : FramePair state a b) :
    FramePair state b a := by
  rcases h with hid | hab | hba | hd
  · exact Or.inl hid.symm
  · exact Or.inr (Or.inr (Or.inl hab))
  · exact Or.inr (Or.inl hba)
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    unfold Disjoint Rect.meetsInterior at hd ⊢
    omega

def FramePairs (state : State) (boxes : List Box) : Prop :=
  ∀ a ∈ boxes, ∀ b ∈ boxes, FramePair state a b

theorem placeRule_framePairs (m : Model) (rules : List Rule)
    (hl : Kinds.Railroad.lower m = .ok rules) (rule : Rule) (hr : rule ∈ rules)
    (metric : Measure.Metric) (before after : RuleState) (target : State)
    (htarget : StateFacts target) (hstage : StageBounds m.profile before)
    (hbefore : FramePairs target before.state.boxes)
    (hext : ExtendsBoxes after.state target)
    (h : placeRule m metric before rule = .ok after) :
    FramePairs target after.state.boxes := by
  unfold placeRule at h
  cases hm : measure (m.boxes.length+1) m.profile metric rule.root with
  | error e => simp [hm, bind, Except.bind] at h
  | ok shape =>
    have hg := measure_geometry _ _ _ _ _ hm
    cases ht : Measure.textWidth metric rule.title.toList with
    | error e => simp [hm, ht, bind, Except.bind] at h
    | ok title =>
      have htitle := Measure.textWidth_nonneg ht
      let g := ruleGeometry m.profile shape title
      simp only [hm, ht, bind, Except.bind] at h
      split at h
      · cases h
      · cases hn : placeNode (m.boxes.length+1) m.profile shape
          (constant m.profile "margin"+g.defX) (before.y+g.defY) rule.id
          (addRule m.profile rule shape g before.y before.state) with
        | error e =>
          dsimp only [g] at hn
          simp only [hn] at h
          cases h
        | ok state =>
          dsimp only [g] at hn
          simp only [hn, pure, Except.pure, Except.ok.injEq] at h
          subst after
          let frame := Box.mk rule.id "group" (ruleFrame m.profile g before.y) "" false
          let Placed := PlacedBox shape (constant m.profile "margin"+g.defX)
            (before.y+g.defY) rule.id
          have origin : ∀ box ∈ state.boxes, box ∈ before.state.boxes ∨
              (rule.id ≠ "" ∧ box = frame) ∨ Placed box := by
            intro box hb
            rcases placeNode_box_origin _ _ _ _ _ _ _ _ hn box hb with hold | hp
            · unfold addRule at hold
              split at hold
              · exact Or.inl hold
              · rename_i hne
                rcases List.mem_append.mp hold with hold | hframe
                · exact Or.inl hold
                · exact Or.inr (Or.inl ⟨by simpa using hne, by simpa [frame] using hframe⟩)
            · exact Or.inr (Or.inr hp)
          have hmem : ∀ box, Placed box → box ∈ target.boxes := by
            intro box hb
            exact hext.mem box (placeNode_address_mem _ _ _ _ _ _ _ _ hn box hb)
          have hnonempty : ∀ box, Placed box → box.id ≠ "" := by
            intro box hb
            exact placedBox_lowered_ne_empty (m.boxes.length+1) m rules hl rule hr
              metric shape hm _ _ rule.id box hb
          have hcross : ∀ old ∈ before.state.boxes, ∀ box,
              (rule.id ≠ "" ∧ box = frame) ∨ Placed box → Disjoint old.rect box.rect := by
            intro old ho box hb
            rcases hb with ⟨_, rfl⟩ | hp
            · exact previous_stage_disjoint_later_rect m.profile before hstage
                old ho frame.rect (by simp [frame, ruleFrame])
            · exact previous_stage_definition_disjoint m.profile shape title before
                rule.id hg htitle hstage old ho box hp
          have hnew : ∀ a b, ((rule.id ≠ "" ∧ a = frame) ∨ Placed a) →
              ((rule.id ≠ "" ∧ b = frame) ∨ Placed b) → FramePair target a b := by
            intro a b ha hb
            rcases ha with ⟨hne, rfl⟩ | ha
            · rcases hb with ⟨_, rfl⟩ | hb
              · exact Or.inl rfl
              · exact Or.inr (Or.inl
                  (hb.parent_ancestor target htarget hnonempty hmem hne))
            · rcases hb with ⟨hne, rfl⟩ | hb
              · exact Or.inr (Or.inr (Or.inl
                  (ha.parent_ancestor target htarget hnonempty hmem hne)))
              · exact ha.separated_or_ancestor target htarget hg hnonempty hmem b hb
          intro a ha b hb
          rcases origin a ha with hold | hnewA
          · rcases origin b hb with holdB | hnewB
            · exact hbefore a hold b holdB
            · exact Or.inr (Or.inr (Or.inr (hcross a hold b hnewB)))
          · rcases origin b hb with holdB | hnewB
            · exact (show FramePair target b a from
                Or.inr (Or.inr (Or.inr (hcross b holdB a hnewA)))).symm
            · exact hnew a b hnewA hnewB

theorem ruleFold_framePairs (m : Model) (rules : List Rule)
    (hl : Kinds.Railroad.lower m = .ok rules) (metric : Measure.Metric)
    (target : State) (htarget : StateFacts target) :
    ∀ (remaining : List Rule) (before after : RuleState),
      (∀ rule ∈ remaining, rule ∈ rules) →
      StageBounds m.profile before → FramePairs target before.state.boxes →
      ExtendsBoxes after.state target →
      remaining.foldlM (placeRule m metric) before = .ok after →
      FramePairs target after.state.boxes := by
  intro remaining
  induction remaining with
  | nil =>
    intro before after hsubset hstage hpairs hext h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst after
    exact hpairs
  | cons rule rest ih =>
    intro before after hsubset hstage hpairs hext h
    cases hr : placeRule m metric before rule with
    | error e => simp [List.foldlM_cons, hr, bind, Except.bind] at h
    | ok next =>
      have ht : rest.foldlM (placeRule m metric) next = .ok after := by
        simpa [List.foldlM_cons, hr, bind, Except.bind] using h
      have hnextExt := (ruleFold_extends_boxes m metric rest next after ht).trans hext
      have hnext := placeRule_framePairs m rules hl rule (hsubset rule (by simp))
        metric before next target htarget hstage hpairs hnextExt hr
      exact ih next after (fun other ho => hsubset other (List.mem_cons_of_mem rule ho))
        (placeRule_stage_bounds m metric before next rule hstage hr) hnext hext ht

theorem layout_lowered_frames_clear (m : Model) (hwf : WellFormed m)
    (rules : List Rule) (scene : Scene)
    (hl : Kinds.Railroad.lower m = .ok rules)
    (h : layout m rules = .ok scene) :
    Validator.C8a scene.layoutDump := by
  have hstate := (layout_lowered_stateFacts m hwf rules scene hl h).1
  have hanc := scene_ancestors_eq_stateDump scene
    ({boxes := scene.boxes, routes := scene.routes} : State) rfl
  unfold layout at h
  cases hm : metricFor m.profile m.options.fontFamily with
  | error e => simp [hm, bind, Except.bind] at h
  | ok metric =>
    cases hf : rules.foldlM (placeRule m metric)
        {y := constant m.profile "margin"} with
    | error e => simp [hm, hf, bind, Except.bind] at h
    | ok final =>
      simp only [hm, hf, bind, Except.bind] at h
      repeat' split at h
      all_goals first
        | (solve | cases h)
        | (simp only [pure, Except.pure, Except.ok.injEq] at h
           subst scene
           let target : State := {boxes := final.state.boxes, routes := final.state.routes}
           have hpairs := ruleFold_framePairs m rules hl metric target hstate
             rules {y := constant m.profile "margin"} final
             (fun rule hr => hr) (initial_stage_bounds m.profile)
             (by intro a ha; cases ha) (by exact ⟨[], by simp [target]⟩) hf
           intro group hg hrole box hb hne hab hba
           rw [hanc box.id] at hab
           rw [hanc group.id] at hba
           rcases hpairs group hg box hb with hid | ha | hb | hd
           · exact False.elim (hne hid.symm)
           · exact False.elim (hab ha)
           · exact False.elim (hba hb)
           · exact hd)

theorem railroad_frames_clear (m : Model) (hwf : WellFormed m)
    (result : Layered.FamilyResult) (h : Kinds.Railroad.layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  obtain ⟨rules, scene, hl, hs, hd⟩ := successful_adapter_origin m result h
  rw [hd]
  exact layout_lowered_frames_clear m hwf rules scene hl hs

theorem railroad_valid (m : Model) (hwf : WellFormed m) (_hlimits : WithinLimits m)
    (result : Layered.FamilyResult) (h : Kinds.Railroad.layout m = .ok result) :
    HardConstraints result.scene.layoutDump := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := railroad_structural_constraints m hwf result h
  exact ⟨h1, h2, h3, h4, h5, railroad_routes_exclusive_clear m result h,
    railroad_labels_clear m result h,
    railroad_frames_clear m hwf result h, railroad_frames_labels m result h⟩

end Elegant.Railroad
