import Elegant.RailroadAssemblyFacts

set_option autoImplicit false

namespace Elegant.Railroad

def ParentsPresent (state : State) : Prop :=
  ∀ box ∈ state.boxes, box.parent ≠ "" →
    ∃ parent ∈ state.boxes, parent.id = box.parent

theorem parentsPresent_empty : ParentsPresent ({boxes := [], routes := []} : State) := by
  intro box hb
  cases hb

theorem ParentsContained.parentsPresent {state : State}
    (h : ParentsContained state) : ParentsPresent state := by
  intro box hb hp
  obtain ⟨parent, hm, hid, _⟩ := h box hb hp
  exact ⟨parent, hm, hid⟩

theorem parentsPresent_append_box (state : State) (box : Box)
    (hstate : ParentsPresent state)
    (hparent : box.parent ≠ "" →
      ∃ parent ∈ state.boxes, parent.id = box.parent) :
    ParentsPresent {state with boxes := state.boxes ++ [box]} := by
  intro child hc hp
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨parent, hm, hid⟩ := hstate child hc hp
    exact ⟨parent, List.mem_append_left _ hm, hid⟩
  · have heq : child = box := List.mem_singleton.mp hc
    subst child
    obtain ⟨parent, hm, hid⟩ := hparent hp
    exact ⟨parent, List.mem_append_left _ hm, hid⟩

theorem stateFacts_append_present (state : State) (box : Box)
    (hstate : StateFacts state) (hpresent : ParentsPresent state)
    (hfresh : ∀ old ∈ state.boxes, old.id ≠ box.id)
    (hne : box.id ≠ "")
    (hparent : box.parent ≠ "" →
      ∃ parent ∈ state.boxes, parent.id = box.parent) :
    StateFacts {state with boxes := state.boxes ++ [box]} ∧
      ParentsPresent {state with boxes := state.boxes ++ [box]} := by
  constructor
  · apply stateFacts_append_box state box hstate hfresh
    · intro old hold heq
      have hneParent : old.parent ≠ "" := by
        intro hempty
        exact hne (heq.symm.trans hempty)
      obtain ⟨parent, hp, hid⟩ := hpresent old hold hneParent
      exact hfresh parent hp (hid.trans heq)
    · intro hp
      obtain ⟨parent, hm, hid⟩ := hparent hp
      exact ⟨parent, hm, by simp [hid]⟩
  · exact parentsPresent_append_box state box hpresent hparent

theorem sequenceJoins_stateFacts (s : Shape) (x y : Int) (state : State)
    (hstate : StateFacts state) : StateFacts (sequenceJoins s x y state) := by
  constructor
  · simpa only [sequenceJoins_boxes] using hstate.inj
  · simpa only [sequenceJoins_boxes] using hstate.pre

theorem sequenceJoins_parentsPresent (s : Shape) (x y : Int) (state : State)
    (hstate : ParentsPresent state) : ParentsPresent (sequenceJoins s x y state) := by
  simpa only [ParentsPresent, sequenceJoins_boxes] using hstate

theorem addRule_stateFacts (p : Profile) (rule : Rule) (s : Shape)
    (g : RuleGeometry) (y : Int) (state : State)
    (hstate : StateFacts state) (hpresent : ParentsPresent state)
    (hfresh : ∀ old ∈ state.boxes, old.id ≠ rule.id) :
    StateFacts (addRule p rule s g y state) ∧
      ParentsPresent (addRule p rule s g y state) := by
  unfold addRule
  split
  · exact ⟨hstate, hpresent⟩
  · rename_i hnonempty
    have hne : rule.id ≠ "" := by simpa using hnonempty
    have h := stateFacts_append_present state
      ⟨rule.id, "group", ruleFrame p g y, "", false⟩
      hstate hpresent hfresh hne (by intro h; exact False.elim (h rfl))
    exact ⟨⟨h.1.inj, h.1.pre⟩, h.2⟩

theorem foldlM_stateFacts {α : Type} (f : State → α → Except LayoutError State)
    (hf : ∀ a before after, StateFacts before → ParentsPresent before →
      f before a = .ok after → StateFacts after ∧ ParentsPresent after)
    (xs : List α) (initial final : State)
    (hi : StateFacts initial) (hp : ParentsPresent initial)
    (h : xs.foldlM f initial = .ok final) :
    StateFacts final ∧ ParentsPresent final := by
  exact foldlM_preserves f (fun state => StateFacts state ∧ ParentsPresent state)
    (fun a before after hin he => hf a before after hin.1 hin.2 he)
    xs initial final ⟨hi, hp⟩ h

theorem stateDump_go_eq (state : State) (fuel : Nat) (id : String) :
    LayoutDump.ancestors.go (stateDump state) fuel id =
      LayoutDump.ancestors.go ⟨⟨0, 0⟩, state.boxes, [], []⟩ fuel id :=
  ancestors_dump_congr fuel id

theorem stateDump_ancestors_eq (state : State) (id : String) :
    (stateDump state).ancestors id =
      (⟨⟨0, 0⟩, state.boxes, [], []⟩ : LayoutDump).ancestors id := by
  unfold LayoutDump.ancestors
  exact stateDump_go_eq state state.boxes.length id

theorem ancestors_go_extends (initial final : State)
    (hext : ExtendsBoxes initial final) (hi : StateFacts initial)
    (hp : ParentsPresent initial) :
    ∀ (fuel : Nat) (box : Box), box ∈ initial.boxes →
      LayoutDump.ancestors.go (stateDump final) fuel box.id =
        LayoutDump.ancestors.go (stateDump initial) fuel box.id := by
  intro fuel
  induction fuel with
  | zero => intro box hb; rfl
  | succ fuel ih =>
    intro box hb
    have hfind : initial.boxes.find? (fun b => b.id == box.id) = some box :=
      find_box_of_id_injective initial.boxes hi.inj box hb
    have hfinal := hext.find_preserved box.id box hfind
    simp only [LayoutDump.ancestors.go, LayoutDump.box?, stateDump, hfind, hfinal]
    by_cases hparent : box.parent = ""
    · simp only [hparent, ↓reduceIte]
    · simp only [hparent, ↓reduceIte]
      obtain ⟨parent, hm, hid⟩ := hp box hb hparent
      have hrec := ih parent hm
      rw [hid] at hrec
      exact congrArg (box.parent :: ·) hrec

theorem ancestors_extends (initial final : State)
    (hext : ExtendsBoxes initial final) (hi : StateFacts initial)
    (hp : ParentsPresent initial) (box : Box) (hb : box ∈ initial.boxes) :
    (stateDump final).ancestors box.id = (stateDump initial).ancestors box.id := by
  have hlen : initial.boxes.length ≤ final.boxes.length := by
    obtain ⟨suffix, hs⟩ := hext
    rw [hs, List.length_append]
    omega
  unfold LayoutDump.ancestors
  change LayoutDump.ancestors.go (stateDump final) final.boxes.length box.id =
    LayoutDump.ancestors.go (stateDump initial) initial.boxes.length box.id
  rw [ancestors_go_extends initial final hext hi hp final.boxes.length box hb]
  rw [stateDump_go_eq, stateDump_go_eq]
  exact ancestors_go_fuel_ge hi.inj hi.pre box.id
    (by
      intro old hold hid
      have hlt := boxIdx_lt_of_mem (boxes := initial.boxes) ⟨old, hold, hid⟩
      omega) final.boxes.length hlen

theorem placeNode_old_ancestors (fuel : Nat) (p : Profile) (s : Shape)
    (x y : Int) (parent : String) (initial final : State)
    (hi : StateFacts initial) (hp : ParentsPresent initial)
    (h : placeNode fuel p s x y parent initial = .ok final)
    (box : Box) (hb : box ∈ initial.boxes) :
    (stateDump final).ancestors box.id = (stateDump initial).ancestors box.id :=
  ancestors_extends initial final
    (placeNode_extends_boxes fuel p s x y parent initial final h) hi hp box hb

theorem stateDump_ancestors_trans (state : State) (hstate : StateFacts state)
    {a b c : String}
    (ha : a ∈ (stateDump state).ancestors b)
    (hb : b ∈ (stateDump state).ancestors c) :
    a ∈ (stateDump state).ancestors c := by
  rw [stateDump_ancestors_eq] at ha hb ⊢
  exact ancestors_trans' hstate.inj hstate.pre ha hb

theorem stateDump_parent_ancestor (state : State) (hstate : StateFacts state)
    (box : Box) (hb : box ∈ state.boxes) (hp : box.parent ≠ "") :
    box.parent ∈ (stateDump state).ancestors box.id := by
  rw [stateDump_ancestors_eq]
  apply ancestors_mem_parent (boxes := state.boxes) (id := box.id) (b := box)
  · exact find_box_of_id_injective state.boxes hstate.inj box hb
  · rfl
  · exact hp

theorem stateDump_ancestors_fuel (state : State) (hstate : StateFacts state)
    (id : String) (fuel : Nat) (hfuel : state.boxes.length ≤ fuel) :
    LayoutDump.ancestors.go (stateDump state) fuel id =
      (stateDump state).ancestors id := by
  unfold LayoutDump.ancestors
  change LayoutDump.ancestors.go (stateDump state) fuel id =
    LayoutDump.ancestors.go (stateDump state) state.boxes.length id
  rw [stateDump_go_eq, stateDump_go_eq]
  exact ancestors_go_fuel_ge hstate.inj hstate.pre id
    (by
      intro box hb hid
      have hlt := boxIdx_lt_of_mem (boxes := state.boxes) ⟨box, hb, hid⟩
      omega) fuel hfuel

theorem scene_ancestors_eq_stateDump (scene : Scene) (state : State)
    (hboxes : scene.boxes = state.boxes) (id : String) :
    scene.layoutDump.ancestors id = (stateDump state).ancestors id := by
  unfold LayoutDump.ancestors
  have hgo := ancestors_dump_congr
    (boxes := state.boxes) (c₁ := scene.canvas) (c₂ := ⟨0, 0⟩)
    (r₁ := scene.routes) (r₂ := state.routes)
    (l₁ := scene.labels.map (·.toLabel)) (l₂ := []) state.boxes.length id
  simpa [Scene.layoutDump, stateDump, hboxes] using hgo

end Elegant.Railroad
