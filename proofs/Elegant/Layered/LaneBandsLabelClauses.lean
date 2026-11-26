import Elegant.Layered.LaneBandsPhaseFacts
import Elegant.Layered.LaneBandsCoverage
import Elegant.DumpLaminar
set_option autoImplicit false
namespace Elegant.Layered.LaneBands
theorem meets_bool (outer inner : Rect) : meetsInterior outer inner = decide (outer.meetsInterior inner) := rfl
theorem strictly_bool (outer inner : Rect) : strictlyInside outer inner = decide (outer.StrictInside inner) := rfl
theorem overlaps_false_disjoint {frame : Box} {labelRect : Rect} (h : overlapsForeignFrame frame labelRect = false) (hrole : frame.role = "group") : Disjoint frame.rect labelRect ∨ frame.rect.StrictInside labelRect := by
  unfold overlapsForeignFrame at h
  simp only [hrole, beq_self_eq_true, Bool.true_and] at h
  have hmeets : meetsInterior frame.rect labelRect = decide (frame.rect.meetsInterior labelRect) := rfl
  have hstrict : strictlyInside frame.rect labelRect = decide (frame.rect.StrictInside labelRect) := rfl
  cases hm : meetsInterior frame.rect labelRect with
  | true =>
    cases hs : strictlyInside frame.rect labelRect with
    | false =>
      simp [hm, hs] at h
    | true =>
      exact Or.inr (of_decide_eq_true (by rw [← hstrict, hs]))
  | false =>
    exact Or.inl (of_decide_eq_false (by rw [← hmeets, hm]))
theorem hits_false_clear {node : Box} {l : SceneLabel} {anc : List String} (h : hitsUnrelatedNode node l anc = false) (hexcl : node.exclusive = true) (hne : node.id ≠ l.owner) (hmem : anc.contains node.id = false) : ¬ node.rect.meetsInterior l.rect := by
  unfold hitsUnrelatedNode at h
  simp only [hexcl, hmem, Bool.true_and] at h
  have hmeets : meetsInterior node.rect l.rect = decide (node.rect.meetsInterior l.rect) := rfl
  cases hm : meetsInterior node.rect l.rect with
  | true =>
    simp [hm] at h
    exact absurd h hne
  | false =>
    exact of_decide_eq_false (by rw [← hmeets, hm])
theorem needsRelocation_false_overlaps {s : Scene} {m : SceneLabel} (h : needsRelocation s m = false) {b : Box} (hmem : b ∈ s.boxes) : overlapsForeignFrame b m.rect = false := by
  unfold needsRelocation at h
  dsimp only at h
  have hall := List.any_eq_false.mp h b hmem
  have hall' : (overlapsForeignFrame b m.rect || hitsUnrelatedNode b m (ownerAncestors s m)) = false := by simpa using hall
  exact (Bool.or_eq_false_iff.mp hall').1
theorem needsRelocation_false_hits {s : Scene} {m : SceneLabel} (h : needsRelocation s m = false) {b : Box} (hmem : b ∈ s.boxes) : hitsUnrelatedNode b m (ownerAncestors s m) = false := by
  unfold needsRelocation at h
  dsimp only at h
  have hall := List.any_eq_false.mp h b hmem
  have hall' : (overlapsForeignFrame b m.rect || hitsUnrelatedNode b m (ownerAncestors s m)) = false := by simpa using hall
  exact (Bool.or_eq_false_iff.mp hall').2
theorem mem_le_foldl_max_aux (l : List Int) (init : Int) (x : Int) (hmem : x ∈ l) : x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil =>
    simp at hmem
  | cons hd tl ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with rfl | hmem
    · exact Int.le_trans (by omega) (le_foldl_max _ _)
    · exact ih (max init hd) hmem
theorem mem_le_bounds_hi {vs : List Int} {lo hi x : Int} (h : bounds vs = some (lo, hi)) (hmem : x ∈ vs) : x ≤ hi := by
  cases vs with
  | nil =>
    simp [bounds] at h
  | cons v rest =>
    simp only [bounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact le_foldl_max _ _
    · exact mem_le_foldl_max_aux rest _ x hmem
theorem highest_bounds {axis : Axis} {s : Scene} {v : Int} (hmem : v ∈ geometryValues axis true s) : v ≤ highest axis s := by
  unfold highest
  cases hbounds : bounds (geometryValues axis true s) with
  | none =>
    cases hgeom : geometryValues axis true s with
    | nil =>
      simp [hgeom] at hmem
    | cons hd tl =>
      rw [hgeom] at hbounds
      simp [bounds] at hbounds
  | some p =>
    cases p with
    | mk lo hi =>
      have hle : v ≤ hi := mem_le_bounds_hi hbounds hmem
      simp only [Option.map_some, Option.getD_some]
      omega
theorem box_start_mem {axis : Axis} {s : Scene} {g : Box} (hmem : g ∈ s.boxes) : axis.start g.rect ∈ geometryValues axis true s := by
  unfold geometryValues
  dsimp only
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  refine List.mem_flatMap.mpr ⟨g, hmem, ?_⟩
  simp
  unfold rectValues
  cases axis with
  | x =>
    simp only [Axis.start]
    exact List.mem_cons.mpr (Or.inl rfl)
  | y =>
    simp only [Axis.start]
    exact List.mem_cons.mpr (Or.inl rfl)
theorem box_far_mem {axis : Axis} {s : Scene} {g : Box} (hmem : g ∈ s.boxes) : axis.start g.rect + axis.length g.rect ∈ geometryValues axis true s := by
  unfold geometryValues
  dsimp only
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  refine List.mem_flatMap.mpr ⟨g, hmem, ?_⟩
  simp
  unfold rectValues
  cases axis with
  | x =>
    simp only [Axis.start, Axis.length]
    exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  | y =>
    simp only [Axis.start, Axis.length]
    exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
theorem spacing_slot_pos {o : Options} {sp : Spacing} (h : spacingOf o.profile = Except.ok sp) : 0 < sp.slot := by
  have hslot : sp.slot = LayoutConst.slot.get o.profile := by
    unfold spacingOf at h
    dsimp only at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  rw [hslot]
  cases o.profile with
  | vector =>
    decide
  | cell =>
    decide
theorem strip_disjoint {axis : Axis} {origin : Scene} {g : Box} (hg : g ∈ origin.boxes) {r' : Rect} {slot strip : Int} (hpos : 0 < slot) (hstrip : strip = highest axis origin + slot) (hle : strip ≤ axis.start r') : Disjoint g.rect r' := by
  have hlt : highest axis origin < axis.start r' := by omega
  cases axis with
  | x =>
    have hgStart : g.rect.x ≤ highest Axis.x origin := highest_bounds (box_start_mem (axis := Axis.x) hg)
    have hgFar : g.rect.x + g.rect.w ≤ highest Axis.x origin := highest_bounds (box_far_mem (axis := Axis.x) hg)
    simp only [Axis.start] at hlt
    unfold Disjoint Rect.meetsInterior
    intro hmeet
    omega
  | y =>
    have hgStart : g.rect.y ≤ highest Axis.y origin := highest_bounds (box_start_mem (axis := Axis.y) hg)
    have hgFar : g.rect.y + g.rect.h ≤ highest Axis.y origin := highest_bounds (box_far_mem (axis := Axis.y) hg)
    simp only [Axis.start] at hlt
    unfold Disjoint Rect.meetsInterior
    intro hmeet
    omega
theorem placeItem_text (place : Rect → Rect) (t : SceneText) : placeItem place (.text t) = .text t := rfl
theorem dump_ignores_items (s : Scene) : s.layoutDump.labels = s.labels.map (·.toLabel) := rfl
theorem c7_c8b_no_label_pair : ∃ (d : LayoutDump), (∃ l1 ∈ d.labels, ∃ l2 ∈ d.labels, l1.rect.meetsInterior l2.rect) ∧ Validator.C7 d ∧ Validator.C8b d := by
  refine ⟨⟨⟨0, 0⟩, [], [], [⟨"l1", "o1", ⟨0, 0, 5, 5⟩, []⟩, ⟨"l2", "o2", ⟨0, 0, 5, 5⟩, []⟩]⟩, ?_, ?_, ?_⟩
  · refine ⟨_, List.mem_cons.mpr (Or.inl rfl), _, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))), ?_⟩
    unfold Rect.meetsInterior
    decide
  · unfold Validator.C7
    intro l _ b hb
    simp at hb
  · unfold Validator.C8b
    intro g hg
    simp at hg
/-- The `pinBands` input scene has no empty box id and no box id equal to a route
id; `pinBands_transport` carries both facts to the output scene. -/
def LaneInputIdsClean (s : Scene) : Prop :=
  (∀ b ∈ s.boxes, b.id ≠ "") ∧ ∀ b ∈ s.boxes, ∀ rt ∈ s.routes, b.id ≠ rt.id
theorem pinBands_c8b {boxes : List ModelBox} {o : Options} {s r : Scene} (h : pinBands boxes o s = .ok r) (hin : Validator.C8b s.layoutDump) : Validator.C8b r.layoutDump := by
  have _keep := hin
  by_cases hempty : lanesOf boxes = []
  · have hr : r = s := by
      have h0 : pinBands boxes o s = .ok s := pinBands_no_lanes hempty
      rw [h0] at h
      cases h
      rfl
    subst hr
    exact hin
  · obtain ⟨sp, axis, _bands, _pinned, _routed, origin, strip, stripScene, hsp, _, _, _, _, _, hstripEq, hrelocEq, hgrow⟩ := pinBands_spec hempty h
    have hstrip : strip = highest axis origin + sp.slot := checked_value hstripEq
    have hslotPos : 0 < sp.slot := spacing_slot_pos hsp
    have hstripBoxes : stripScene.boxes = origin.boxes := relocateLabels_boxes hrelocEq
    have hstripRoutes : stripScene.routes = origin.routes := relocateLabels_routes hrelocEq
    obtain ⟨hgrowBoxes, hgrowRoutes, hgrowLabels⟩ := growCanvas_frame hgrow
    have hrBoxes : r.boxes = origin.boxes := by rw [hgrowBoxes, hstripBoxes]
    have hdBoxes : r.layoutDump.boxes = r.boxes := (pinBands_layoutDump (r := r)).1
    have hdLabels : r.layoutDump.labels = r.labels.map (·.toLabel) := (pinBands_layoutDump (r := r)).2.2.2
    unfold Validator.C8b
    intro g hg hrole l hl
    rw [hdLabels] at hl
    obtain ⟨sl, hslMem, hslEq⟩ := List.mem_map.mp hl
    have hslStrip : sl ∈ stripScene.labels := by rw [← hgrowLabels]; exact hslMem
    obtain ⟨m, hmMem, _hmid, _hmown, hstay, hmove⟩ := relocateLabels_labels hrelocEq hslStrip
    have hgR : g ∈ r.boxes := by rw [← hdBoxes]; exact hg
    have hgO : g ∈ origin.boxes := by rw [← hrBoxes]; exact hgR
    have hlRect : l.rect = sl.rect := by rw [← hslEq]
    by_cases hneed : needsRelocation origin m = false
    · have hover := needsRelocation_false_overlaps hneed hgO
      have hdisj := overlaps_false_disjoint hover hrole
      have hslRect : sl.rect = m.rect := hstay (by simp [hneed])
      rw [hlRect, hslRect]
      exact hdisj
    · have hneedT : needsRelocation origin m = true := by
        cases hnb : needsRelocation origin m with
        | true => rfl
        | false => exact absurd hnb hneed
      obtain ⟨hle, -, -, -⟩ := hmove hneedT
      have hdisj : Disjoint g.rect sl.rect := strip_disjoint hgO hslotPos hstrip hle
      rw [hlRect]
      exact Or.inl hdisj
-- `pinBands_c7` is stated and proved at the end of this file.

/-! ### Ancestor-walk bridges -/

/-- `go` depends on the dump only through its box list. -/
theorem go_congr_boxes {d e : LayoutDump} (h : d.boxes = e.boxes) :
    ∀ (k : Nat) (s : String),
      LayoutDump.ancestors.go d k s = LayoutDump.ancestors.go e k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [LayoutDump.ancestors.go]
    cases hd : d.box? s with
    | none =>
      have he : e.box? s = none := by
        unfold LayoutDump.box?
        rw [← h]
        exact hd
      simp only [he]
    | some b =>
      have he : e.box? s = some b := by
        unfold LayoutDump.box?
        rw [← h]
        exact hd
      simp only [he, ih]

/-- `ancestors` depends on the dump only through its box list. -/
theorem ancestors_congr_boxes {d e : LayoutDump} (h : d.boxes = e.boxes)
    (id : String) : d.ancestors id = e.ancestors id := by
  unfold LayoutDump.ancestors
  have hlen : d.boxes.length = e.boxes.length := by rw [h]
  rw [hlen]
  exact go_congr_boxes h _ _

/-- `labelOwnerAnc` depends on the dump only through its box and route lists, and on
the label only through its owner. -/
theorem labelOwnerAnc_congr_owner {d e : LayoutDump} {l₁ l₂ : Label}
    (hboxes : d.boxes = e.boxes) (hroutes : d.routes = e.routes)
    (hown : l₁.owner = l₂.owner) :
    d.labelOwnerAnc l₁ = e.labelOwnerAnc l₂ := by
  unfold LayoutDump.labelOwnerAnc
  have hfind : d.routes.find? (fun r => r.id == l₁.owner) =
      e.routes.find? (fun r => r.id == l₂.owner) := by
    rw [hroutes, hown]
  rw [hfind]
  cases hroute : e.routes.find? (fun r => r.id == l₂.owner) with
  | none =>
    show l₁.owner :: d.ancestors l₁.owner = l₂.owner :: e.ancestors l₂.owner
    rw [hown]
    congr 1
    exact ancestors_congr_boxes hboxes _
  | some r =>
    show d.ancestors r.fromId ++ d.ancestors r.toId =
      e.ancestors r.fromId ++ e.ancestors r.toId
    simp only [ancestors_congr_boxes hboxes]

/-- The dump-congruence bridge is a theorem, not a hypothesis. -/
theorem dumpAncCong (r origin : Scene) (sl m : SceneLabel)
    (hboxes : r.boxes = origin.boxes) (hroutes : r.routes = origin.routes)
    (hown : sl.owner = m.owner) :
    r.layoutDump.labelOwnerAnc sl.toLabel = origin.layoutDump.labelOwnerAnc m.toLabel := by
  apply labelOwnerAnc_congr_owner (l₁ := sl.toLabel) (l₂ := m.toLabel) hboxes hroutes
  show sl.toLabel.owner = m.toLabel.owner
  exact hown

/-- With no empty box id, the `go` walk from the sentinel id is empty. -/
theorem go_nil_of_empty_id {d : LayoutDump} (hEmpty : ∀ b ∈ d.boxes, b.id ≠ "") :
    ∀ (k : Nat), LayoutDump.ancestors.go d k "" = [] := by
  have hbox : d.box? "" = none := by
    unfold LayoutDump.box?
    rw [List.find?_eq_none]
    intro b hb
    have hbne := hEmpty b hb
    simp only [beq_iff_eq, hbne, not_false_eq_true]
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [LayoutDump.ancestors.go]
    rw [hbox]

/-- Every element the fuel-bounded `addAncestors` walk emits is either already in the
accumulator, the root sentinel `""`, or an element of the validator's `go` walk at the
same fuel. -/
theorem addAncestors_mem {d : LayoutDump} (hEmpty : ∀ b ∈ d.boxes, b.id ≠ "") :
    ∀ (F : Nat) (id : String) (acc : List String) (x : String),
      x ∈ addAncestors d.boxes F id acc →
      x ∈ acc ∨ x = "" ∨ x ∈ LayoutDump.ancestors.go d F id := by
  intro F
  induction F with
  | zero =>
    intro id acc x hx
    exact Or.inl hx
  | succ F ih =>
    intro id acc x hx
    have hstep : addAncestors d.boxes (F + 1) id acc =
        match d.boxes.find? (fun b => b.id == id) with
        | none => acc
        | some b =>
          if acc.contains b.parent then acc
          else addAncestors d.boxes F b.parent (b.parent :: acc) := rfl
    rw [hstep] at hx
    by_cases hfind : d.boxes.find? (fun b => b.id == id) = none
    · rw [hfind] at hx
      exact Or.inl hx
    · cases hfind' : d.boxes.find? (fun b => b.id == id) with
      | none => exact absurd hfind' hfind
      | some b =>
        simp only [hfind'] at hx
        by_cases hcont : acc.contains b.parent = true
        · rw [ite_eq_left hcont] at hx
          exact Or.inl hx
        · rw [ite_eq_right hcont] at hx
          have hboxI : d.box? id = some b := hfind'
          have hgo : LayoutDump.ancestors.go d (F + 1) id =
              if b.parent = "" then []
              else b.parent :: LayoutDump.ancestors.go d F b.parent := by
            simp only [LayoutDump.ancestors.go, hboxI]
          rcases ih b.parent (b.parent :: acc) x hx with hacc | hempty | hgo'
          · rcases List.mem_cons.mp hacc with rfl | haccIn
            · by_cases hp : b.parent = ""
              · exact Or.inr (Or.inl hp)
              · rw [hgo, ite_eq_right hp]
                exact Or.inr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            · exact Or.inl haccIn
          · exact Or.inr (Or.inl hempty)
          · by_cases hp : b.parent = ""
            · have hnil : LayoutDump.ancestors.go d F b.parent = [] := by
                rw [hp]
                exact go_nil_of_empty_id hEmpty F
              rw [hnil] at hgo'
              cases hgo'
            · rw [hgo, ite_eq_right hp]
              exact Or.inr (Or.inr (List.mem_cons_of_mem _ hgo'))

/-- Fuel stability of the validator's ancestor walk past the box count, for lane
scenes whose box ids are nonempty and whose parents are `""` or box ids. Every walk
element then names a box id, so any element past the box-count fuel repeats an earlier
one. This is the one remaining fact about `ancestors.go`. -/
def LaneAncFuelStableAll : Prop :=
  ∀ (d : LayoutDump),
    (∀ b ∈ d.boxes, b.id ≠ "") →
    (∀ b ∈ d.boxes, b.parent = "" ∨ b.parent ∈ d.boxIds) →
    ∀ (id x : String),
      x ∈ LayoutDump.ancestors.go d (d.boxes.length + 2) id →
      x ∈ LayoutDump.ancestors.go d d.boxes.length id

/-! ### Fuel stability of `ancestors.go` -/

/-- One parent step of the validator's ancestor walk, as a total function on ids. -/
private def ancStep (d : LayoutDump) (s : String) : String :=
  match d.box? s with
  | some b => b.parent
  | none => s

/-- `n` iterations of `ancStep`: the id reached after `n` parent steps. -/
private def ancIter (d : LayoutDump) : Nat → String → String
  | 0, s => s
  | n + 1, s => ancStep d (ancIter d n s)

private theorem ancIter_zero (d : LayoutDump) (s : String) :
    ancIter d 0 s = s := rfl

private theorem ancIter_step (d : LayoutDump) (m : Nat) (s : String) :
    ancIter d m (ancStep d s) = ancStep d (ancIter d m s) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show ancStep d (ancIter d m (ancStep d s)) = ancStep d (ancStep d (ancIter d m s))
    rw [ih]

private theorem ancIter_add (d : LayoutDump) (m : Nat) (n : Nat) :
    ∀ (s : String), ancIter d (m + n) s = ancIter d m (ancIter d n s) := by
  induction n with
  | zero =>
    intro s
    rfl
  | succ n ih =>
    intro s
    show ancStep d (ancIter d (m + n) s) = ancIter d m (ancStep d (ancIter d n s))
    rw [ih s, ancIter_step]

private theorem find?_some_spec {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rw [List.find?_cons] at h
    cases hpx : p x with
    | true =>
      simp only [hpx] at h
      cases h
      exact hpx
    | false =>
      simp only [hpx] at h
      exact ih h

private theorem find?_eq_some_of_exists {α : Type} {p : α → Bool} {l : List α}
    (h : ∃ a ∈ l, p a = true) : ∃ b, l.find? p = some b := by
  induction l with
  | nil =>
    obtain ⟨a, ha, _⟩ := h
    cases ha
  | cons x xs ih =>
    rw [List.find?_cons]
    cases hpx : p x with
    | true =>
      exact ⟨x, rfl⟩
    | false =>
      obtain ⟨a, ha, hpa⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp [hpa] at hpx
      · exact ih ⟨a, ha', hpa⟩

private theorem box?_mem {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b ∈ d.boxes := by
  unfold LayoutDump.box? at h
  exact List.mem_of_find?_eq_some h

private theorem box?_id_eq {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : b.id = s := by
  unfold LayoutDump.box? at h
  have hspec := find?_some_spec h
  exact beq_iff_eq.mp hspec

private theorem box?_eq_some_of_mem_boxIds {d : LayoutDump} {id : String}
    (h : id ∈ d.boxIds) : ∃ b, d.box? id = some b := by
  unfold LayoutDump.boxIds at h
  obtain ⟨b, hb, hbid⟩ := List.mem_map.mp h
  have hbeq : (b.id == id) = true := by rw [hbid]; exact beq_self_eq_true id
  show ∃ b, d.boxes.find? (fun b => b.id == id) = some b
  exact find?_eq_some_of_exists ⟨b, hb, hbeq⟩

private theorem ancStep_eq_some {d : LayoutDump} {s : String} {b : Box}
    (h : d.box? s = some b) : ancStep d s = b.parent := by
  simp [ancStep, h]

/-- Every element of the `go` walk is an iterate of `ancStep`, and every iterate up to
that position is a box id. -/
private theorem go_mem_iterate {d : LayoutDump}
    (hParent : ∀ b ∈ d.boxes, b.parent = "" ∨ b.parent ∈ d.boxIds) :
    ∀ (F : Nat) (id x : String),
      x ∈ LayoutDump.ancestors.go d F id →
      ∃ i : Nat, 1 ≤ i ∧ i ≤ F ∧ x = ancIter d i id ∧
        ∀ j : Nat, j ≤ i → ancIter d j id ∈ d.boxIds := by
  intro F
  induction F with
  | zero =>
    intro id x hx
    simp [LayoutDump.ancestors.go] at hx
  | succ F ih =>
    intro id x hx
    simp only [LayoutDump.ancestors.go] at hx
    cases hbox : d.box? id with
    | none =>
      simp only [hbox] at hx
      change x ∈ [] at hx
      simp at hx
    | some b =>
      simp only [hbox] at hx
      have hbmem : b ∈ d.boxes := box?_mem hbox
      have hbid : b.id = id := box?_id_eq hbox
      have hid : id ∈ d.boxIds := by
        show id ∈ d.boxes.map (·.id)
        exact List.mem_map.mpr ⟨b, hbmem, hbid⟩
      have hparent_b := hParent b hbmem
      by_cases hp : b.parent = ""
      · rw [ite_eq_left hp] at hx
        change x ∈ [] at hx
        simp at hx
      · rw [ite_eq_right hp] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨1, by omega, by omega, ?_, ?_⟩
          · show b.parent = ancStep d id
            exact (ancStep_eq_some hbox).symm
          · intro j hj
            have hj01 : j = 0 ∨ j = 1 := by omega
            rcases hj01 with rfl | rfl
            · show id ∈ d.boxIds
              exact hid
            · have hstep : ancIter d 1 id = b.parent := by
                show ancStep d id = b.parent
                exact ancStep_eq_some hbox
              rw [hstep]
              rcases hparent_b with he | hm
              · exact absurd he hp
              · exact hm
        · obtain ⟨i, hi1, hiF, hxeq, hilive⟩ := ih b.parent x hx
          refine ⟨i + 1, by omega, by omega, ?_, ?_⟩
          · have h1 : ancIter d (i + 1) id = ancIter d i (ancIter d 1 id) :=
              ancIter_add d i 1 id
            have h2 : ancIter d 1 id = b.parent := by
              show ancStep d id = b.parent
              exact ancStep_eq_some hbox
            rw [h1, h2]
            exact hxeq
          · intro j hj
            by_cases hj0 : j = 0
            · subst hj0
              show id ∈ d.boxIds
              exact hid
            · have hdecomp : ancIter d j id = ancIter d (j - 1) b.parent := by
                have h1 : ancIter d j id = ancIter d (j - 1) (ancIter d 1 id) := by
                  conv => lhs
                  rw [show j = (j - 1) + 1 by omega]
                  exact ancIter_add d (j - 1) 1 id
                rw [h1]
                have h2 : ancIter d 1 id = b.parent := by
                  show ancStep d id = b.parent
                  exact ancStep_eq_some hbox
                rw [h2]
              rw [hdecomp]
              exact hilive (j - 1) (by omega)

/-- Conversely, an iterate at a live position is an element of the `go` walk at any
fuel that reaches it. -/
private theorem mem_go_of_iterate {d : LayoutDump}
    (hEmpty : ∀ b ∈ d.boxes, b.id ≠ "") :
    ∀ (i F : Nat) (id : String),
      i + 1 ≤ F →
      (∀ j : Nat, j ≤ i + 1 → ancIter d j id ∈ d.boxIds) →
      ancIter d (i + 1) id ∈ LayoutDump.ancestors.go d F id := by
  intro i
  induction i with
  | zero =>
    intro F id hiF hlive
    obtain ⟨b', hb'⟩ := box?_eq_some_of_mem_boxIds (show id ∈ d.boxIds from hlive 0 (by omega))
    have hstep1 : ancIter d 1 id = b'.parent := by
      show ancStep d id = b'.parent
      exact ancStep_eq_some hb'
    have hpar_ne : b'.parent ≠ "" := by
      have hmem : b'.parent ∈ d.boxIds := by rw [← hstep1]; exact hlive 1 (by omega)
      intro he
      unfold LayoutDump.boxIds at hmem
      obtain ⟨b0, hb0, hb0id⟩ := List.mem_map.mp hmem
      rw [he] at hb0id
      exact absurd hb0id (hEmpty b0 hb0)
    have hF : F = (F - 1) + 1 := by omega
    rw [hF]
    simp only [LayoutDump.ancestors.go, hb']
    rw [ite_eq_right hpar_ne]
    apply List.mem_cons.mpr
    left
    exact hstep1
  | succ i ih =>
    intro F id hiF hlive
    obtain ⟨b', hb'⟩ := box?_eq_some_of_mem_boxIds (show id ∈ d.boxIds from hlive 0 (by omega))
    have hstep1 : ancIter d 1 id = b'.parent := by
      show ancStep d id = b'.parent
      exact ancStep_eq_some hb'
    have hpar_ne : b'.parent ≠ "" := by
      have hmem : b'.parent ∈ d.boxIds := by rw [← hstep1]; exact hlive 1 (by omega)
      intro he
      unfold LayoutDump.boxIds at hmem
      obtain ⟨b0, hb0, hb0id⟩ := List.mem_map.mp hmem
      rw [he] at hb0id
      exact absurd hb0id (hEmpty b0 hb0)
    have hlive' : ∀ j : Nat, j ≤ i + 1 → ancIter d j (ancIter d 1 id) ∈ d.boxIds := by
      intro j hj
      have hcast : ancIter d j (ancIter d 1 id) = ancIter d (j + 1) id :=
        (ancIter_add d j 1 id).symm
      rw [hcast]
      exact hlive (j + 1) (by omega)
    have hrec := ih (F - 1) (ancIter d 1 id) (by omega) hlive'
    rw [hstep1] at hrec
    have hF : F = (F - 1) + 1 := by omega
    rw [hF]
    simp only [LayoutDump.ancestors.go, hb']
    rw [ite_eq_right hpar_ne]
    apply List.mem_cons_of_mem
    have hcast : ancIter d (i + 1 + 1) id = ancIter d (i + 1) b'.parent := by
      show ancIter d ((i + 1) + 1) id = ancIter d (i + 1) b'.parent
      rw [ancIter_add d (i + 1) 1 id, hstep1]
    show ancIter d (i + 1 + 1) id ∈ LayoutDump.ancestors.go d (F - 1) b'.parent
    rw [hcast]
    exact hrec

/-- Pigeonhole: `n` values drawn from a list shorter than `n` cannot all be distinct. -/
private theorem injOn_length_le {α : Type} [BEq α] [LawfulBEq α] (f : Nat → α) {m : List α} (n : Nat) :
    (∀ i j : Nat, i < n → j < n → i ≠ j → f i ≠ f j) →
    (∀ j : Nat, j < n → f j ∈ m) → n ≤ m.length := by
  induction n generalizing m with
  | zero => intro _ _; exact Nat.zero_le _
  | succ n ih =>
    intro hinj hmem
    have hex : f n ∈ m := hmem n (Nat.lt_succ_self n)
    have hmem' : ∀ j : Nat, j < n → f j ∈ m.erase (f n) := by
      intro j hj
      have h1 : f j ∈ m := hmem j (Nat.lt_succ_of_lt hj)
      have h2 : f j ≠ f n := hinj j n (Nat.lt_succ_of_lt hj) (Nat.lt_succ_self n) (by omega)
      exact mem_erase_of_ne h1 h2
    have hle := ih (fun i j hi hj hij => hinj i j (by omega) (by omega) hij) hmem'
    rw [List.length_erase_of_mem hex] at hle
    have hpos := List.length_pos_of_mem hex
    omega

private theorem exists_pair_eq_of_forall_mem {α : Type} [BEq α] [LawfulBEq α] (f : Nat → α) {n : Nat}
    {m : List α} (hm : m.length < n) (hmem : ∀ j : Nat, j < n → f j ∈ m) :
    ∃ a b : Nat, a < n ∧ b < n ∧ a ≠ b ∧ f a = f b := by
  refine Classical.byContradiction ?_
  intro hcon
  have hinj : ∀ i j : Nat, i < n → j < n → i ≠ j → f i ≠ f j := by
    intro i j hi hj hij hEq
    exact hcon ⟨i, j, hi, hj, hij, hEq⟩
  have hle := injOn_length_le f n hinj hmem
  omega

/-- Periodicity of the orbit once two iterates coincide. -/
private theorem ancIter_period {d : LayoutDump} {a b : Nat} {id : String}
    (hab : a < b) (heq : ancIter d a id = ancIter d b id)
    {j : Nat} (hj : a ≤ j) :
    ancIter d (j + (b - a)) id = ancIter d j id := by
  have hfix : ancIter d (b - a) (ancIter d a id) = ancIter d a id := by
    have h1 : ancIter d ((b - a) + a) id = ancIter d (b - a) (ancIter d a id) :=
      ancIter_add d (b - a) a id
    have hba : (b - a) + a = a + (b - a) := Nat.add_comm _ _
    have h3 : a + (b - a) = b := by omega
    rw [hba, h3] at h1
    rw [← heq] at h1
    exact h1.symm
  have hdecomp : j + (b - a) = (j - a) + b := by omega
  rw [hdecomp]
  have e1 : ancIter d ((j - a) + b) id = ancIter d (j - a) (ancIter d b id) :=
    ancIter_add d (j - a) b id
  rw [e1, ← heq, ← ancIter_add d (j - a) a id]
  have hj2 : j - a + a = j := by omega
  rw [hj2]

/-- `k` periods of length `p` fix every point of the cycle. -/
private theorem ancIter_period_mul {d : LayoutDump} {p : Nat} {c : String}
    (hfix : ancIter d p c = c) :
    ∀ k : Nat, ancIter d (k * p) c = c := by
  intro k
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ k ih =>
    have hmul : (k + 1) * p = k * p + p := by
      rw [Nat.succ_mul]
    rw [hmul, ancIter_add d (k * p) p c, hfix, ih]

theorem laneAncFuelStableAll : LaneAncFuelStableAll := by
  intro d hEmpty hParent id x hx
  obtain ⟨i, hi1, hiF, hxeq, hilive⟩ := go_mem_iterate hParent _ _ _ hx
  by_cases hiL : i ≤ d.boxes.length
  · rw [hxeq]
    have hmem := mem_go_of_iterate hEmpty (i - 1) d.boxes.length id (by omega)
      (fun j hj => hilive j (by omega))
    have hidx : i - 1 + 1 = i := by omega
    rw [hidx] at hmem
    exact hmem
  · -- `i` is past the box count: pigeonhole on positions `1 … L+1`.
    have hiL1 : d.boxes.length + 1 ≤ i := by omega
    have hmem : ∀ j : Nat, j < d.boxes.length + 1 →
        ancIter d (j + 1) id ∈ d.boxIds := by
      intro j hj
      exact hilive (j + 1) (by omega)
    have hboxlen : d.boxIds.length = d.boxes.length := by
      unfold LayoutDump.boxIds
      rw [List.length_map]
    obtain ⟨a, b, ha, hb, hne, heq⟩ :=
      exists_pair_eq_of_forall_mem (fun k => ancIter d (k + 1) id)
        (by rw [hboxlen]; omega) hmem
    have hab : a + 1 < b + 1 ∨ b + 1 < a + 1 := by omega
    rcases hab with hlt | hlt
    · have hpair : ancIter d (a + 1) id = ancIter d (b + 1) id := heq
      have hpos : 0 < b - a := by omega
      have hi0 : i = ((i - (a + 1)) / (b - a)) * (b - a) +
          (a + 1 + (i - (a + 1)) % (b - a)) := by
        have hdm := Nat.div_add_mod (i - (a + 1)) (b - a)
        have hmul : ((i - (a + 1)) / (b - a)) * (b - a) =
            (b - a) * ((i - (a + 1)) / (b - a)) := Nat.mul_comm _ _
        have h2 : i = (i - (a + 1)) + (a + 1) := by omega
        omega
      have hfixAt : ∀ j' : Nat, a + 1 ≤ j' →
          ancIter d (b - a) (ancIter d j' id) = ancIter d j' id := by
        intro j' hj'
        have h1 := ancIter_period (d := d) (a := a + 1) (b := b + 1) (id := id)
          (by omega) hpair hj'
        have hsub : (b + 1) - (a + 1) = b - a := by omega
        rw [hsub] at h1
        have h2 : ancIter d (b - a) (ancIter d j' id) =
            ancIter d ((b - a) + j') id := (ancIter_add d (b - a) j' id).symm
        rw [h2, Nat.add_comm (b - a) j']
        exact h1
      have hcast : ∀ (K r : Nat),
          ancIter d (K * (b - a) + (a + 1 + r)) id = ancIter d (a + 1 + r) id := by
        intro K r
        rw [ancIter_add d (K * (b - a)) (a + 1 + r) id]
        exact ancIter_period_mul (hfixAt (a + 1 + r) (by omega)) K
      have hIter : ancIter d i id =
          ancIter d (a + 1 + (i - (a + 1)) % (b - a)) id :=
        (congrArg (fun t => ancIter d t id) hi0).trans (hcast _ _)
      have hrp : (i - (a + 1)) % (b - a) < b - a := Nat.mod_lt _ hpos
      have hi'le : a + 1 + (i - (a + 1)) % (b - a) ≤ d.boxes.length := by omega
      rw [hxeq, hIter]
      have hmem' := mem_go_of_iterate hEmpty
        (a + (i - (a + 1)) % (b - a)) d.boxes.length id (by omega)
        (fun j hj => hilive j (by omega))
      have hidx : (a + (i - (a + 1)) % (b - a)) + 1 =
          a + 1 + (i - (a + 1)) % (b - a) := by omega
      rw [hidx] at hmem'
      exact hmem'
    · have hpair : ancIter d (b + 1) id = ancIter d (a + 1) id := heq.symm
      have hpos : 0 < a - b := by omega
      have hi0 : i = ((i - (b + 1)) / (a - b)) * (a - b) +
          (b + 1 + (i - (b + 1)) % (a - b)) := by
        have hdm := Nat.div_add_mod (i - (b + 1)) (a - b)
        have hmul : ((i - (b + 1)) / (a - b)) * (a - b) =
            (a - b) * ((i - (b + 1)) / (a - b)) := Nat.mul_comm _ _
        have h2 : i = (i - (b + 1)) + (b + 1) := by omega
        omega
      have hfixAt : ∀ j' : Nat, b + 1 ≤ j' →
          ancIter d (a - b) (ancIter d j' id) = ancIter d j' id := by
        intro j' hj'
        have h1 := ancIter_period (d := d) (a := b + 1) (b := a + 1) (id := id)
          (by omega) hpair hj'
        have hsub : (a + 1) - (b + 1) = a - b := by omega
        rw [hsub] at h1
        have h2 : ancIter d (a - b) (ancIter d j' id) =
            ancIter d ((a - b) + j') id := (ancIter_add d (a - b) j' id).symm
        rw [h2, Nat.add_comm (a - b) j']
        exact h1
      have hcast : ∀ (K r : Nat),
          ancIter d (K * (a - b) + (b + 1 + r)) id = ancIter d (b + 1 + r) id := by
        intro K r
        rw [ancIter_add d (K * (a - b)) (b + 1 + r) id]
        exact ancIter_period_mul (hfixAt (b + 1 + r) (by omega)) K
      have hIter : ancIter d i id =
          ancIter d (b + 1 + (i - (b + 1)) % (a - b)) id :=
        (congrArg (fun t => ancIter d t id) hi0).trans (hcast _ _)
      have hrp : (i - (b + 1)) % (a - b) < a - b := Nat.mod_lt _ hpos
      have hi'le : b + 1 + (i - (b + 1)) % (a - b) ≤ d.boxes.length := by omega
      rw [hxeq, hIter]
      have hmem' := mem_go_of_iterate hEmpty
        (b + (i - (b + 1)) % (a - b)) d.boxes.length id (by omega)
        (fun j hj => hilive j (by omega))
      have hidx : (b + (i - (b + 1)) % (a - b)) + 1 =
          b + 1 + (i - (b + 1)) % (a - b) := by omega
      rw [hidx] at hmem'
      exact hmem'

/-- The shape hypothesis `LaneAncFuelStableAll` needs, on a scene. -/
def LaneSceneShape (s : Scene) : Prop :=
  (∀ b ∈ s.boxes, b.id ≠ "") ∧
  (∀ b ∈ s.boxes, b.parent = "" ∨ b.parent ∈ s.boxes.map (·.id))

-- `ownerAncestors` unfolded to its two fuel-bounded walks. -/
theorem ownerAncestors_eq (s : Scene) (l : SceneLabel) :
    ownerAncestors s l =
      match s.routes.find? (fun r => r.id == l.owner) with
      | some r => addAncestors s.boxes (s.boxes.length + 2) r.toId
          (addAncestors s.boxes (s.boxes.length + 2) r.fromId [])
      | none => addAncestors s.boxes (s.boxes.length + 2) l.owner [] := rfl
/-- The ancestor bridge for a relocated-label scene, proved from fuel stability. -/
theorem laneRelocAncBridge {origin stripScene : Scene} {axis : Axis} {strip gap : Int}
    (_hstrip : relocateLabels axis strip gap origin = .ok stripScene)
    (m : SceneLabel) (_hm : m ∈ origin.labels)
    (hshape : LaneSceneShape origin) (hstable : LaneAncFuelStableAll) :
    ∀ (id : String), id ∈ ownerAncestors origin m →
      id ∈ origin.layoutDump.labelOwnerAnc m.toLabel ∨ id = "" := by
  intro id hid
  rw [ownerAncestors_eq] at hid
  have hEmpty : ∀ b ∈ origin.layoutDump.boxes, b.id ≠ "" := hshape.1
  have hParent : ∀ b ∈ origin.layoutDump.boxes,
      b.parent = "" ∨ b.parent ∈ origin.layoutDump.boxIds := by
    intro b hb
    rcases hshape.2 b hb with he | hm
    · exact Or.inl he
    · exact Or.inr hm
  cases hroute : origin.routes.find? (fun r => r.id == m.owner) with
  | none =>
    simp only [hroute] at hid
    have hmem := addAncestors_mem (d := origin.layoutDump) hEmpty
      (origin.boxes.length + 2) m.owner [] id hid
    rcases hmem with hacc | hempty | hgo
    · cases hacc
    · exact Or.inr hempty
    · have hstab := hstable origin.layoutDump hEmpty hParent m.owner id hgo
      have hanc : id ∈ origin.layoutDump.ancestors m.owner := hstab
      left
      unfold LayoutDump.labelOwnerAnc
      have hfindNone : origin.layoutDump.routes.find? (fun r => r.id == m.toLabel.owner) = none := hroute
      rw [hfindNone]
      have hown : m.toLabel.owner = m.owner := rfl
      rw [hown]
      exact List.mem_cons_of_mem _ hanc
  | some r =>
    simp only [hroute] at hid
    have hmemO := addAncestors_mem (d := origin.layoutDump) hEmpty
      (origin.boxes.length + 2) r.toId _ id hid
    rcases hmemO with hacc | hempty | hgoTo
    · have hmemI := addAncestors_mem (d := origin.layoutDump) hEmpty
        (origin.boxes.length + 2) r.fromId [] id hacc
      rcases hmemI with hnil | hemptyI | hgoFrom
      · cases hnil
      · exact Or.inr hemptyI
      · have hstabF := hstable origin.layoutDump hEmpty hParent r.fromId id hgoFrom
        have hancF : id ∈ origin.layoutDump.ancestors r.fromId := hstabF
        left
        unfold LayoutDump.labelOwnerAnc
        have hfindSome : origin.layoutDump.routes.find? (fun r' => r'.id == m.toLabel.owner) = some r := hroute
        rw [hfindSome]
        exact List.mem_append_left _ hancF
    · exact Or.inr hempty
    · have hstabT := hstable origin.layoutDump hEmpty hParent r.toId id hgoTo
      have hancT : id ∈ origin.layoutDump.ancestors r.toId := hstabT
      left
      unfold LayoutDump.labelOwnerAnc
      have hfindSome : origin.layoutDump.routes.find? (fun r' => r'.id == m.toLabel.owner) = some r := hroute
      rw [hfindSome]
      exact List.mem_append_right _ hancT

/-- Local bind destructor (same shape as the clearance helper). -/
private theorem bind_ok2 {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [Bind.bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A uniform shift preserves box parents. -/
theorem shiftAll_boxes_parent {axis : Axis} {delta : Int} {s s' : Scene}
    (h : shiftAll axis delta s = .ok s') :
    s'.boxes.map (·.parent) = s.boxes.map (·.parent) := by
  unfold shiftAll at h
  obtain ⟨boxes', hboxes, h⟩ := bind_ok2 h
  obtain ⟨_labels, _hlabels, h⟩ := bind_ok2 h
  obtain ⟨_routes, _hroutes, h⟩ := bind_ok2 h
  obtain ⟨_items, _hitems, h⟩ := bind_ok2 h
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact (shiftBoxes_maps s.boxes axis delta _ hboxes).2.2.1

/-- Joint id/parent correspondence from equal id and parent maps. -/
private theorem boxCorr (l₁ l₂ : List Box)
    (hid : l₁.map (·.id) = l₂.map (·.id))
    (hpar : l₁.map (·.parent) = l₂.map (·.parent)) :
    ∀ b' ∈ l₂, ∃ b ∈ l₁, b'.id = b.id ∧ b'.parent = b.parent := by
  induction l₁ generalizing l₂ with
  | nil =>
    intro b' hb'
    have hm : l₂.map (·.id) = [] := by simpa using hid.symm
    cases l₂ with
    | nil => simp at hb'
    | cons c t => simp at hm
  | cons b₁ t₁ ih =>
    intro b' hb'
    have hne : l₂ ≠ [] := by
      intro he
      subst he
      simp at hid
    obtain ⟨b₂, t₂, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.map_cons, List.cons.injEq] at hid hpar
    obtain ⟨hid1, hid2⟩ := hid
    obtain ⟨hpar1, hpar2⟩ := hpar
    simp only [List.mem_cons] at hb'
    rcases hb' with rfl | hb'
    · exact ⟨b₁, List.mem_cons.mpr (Or.inl rfl), hid1.symm, hpar1.symm⟩
    · obtain ⟨b, hb, hidb, hparb⟩ := ih t₂ hid2 hpar2 b' hb'
      exact ⟨b, List.mem_cons.mpr (Or.inr hb), hidb, hparb⟩

/-- Per-element route id correspondence through `applyPin`'s route `mapM`. -/
private theorem pinRoutes_mem_id (l : List Route) (pin : Pin) (axis : Axis) :
    ∀ (l' : List Route),
    l.mapM (fun r : Route => match pin.route r.id with
      | none => (pure r : Except LayoutError Route)
      | some d => (do pure { r with points := ← r.points.mapM ((routeMove d).point axis) } : Except LayoutError Route)) = .ok l' →
    ∀ rt' ∈ l', ∃ rt ∈ l, rt'.id = rt.id := by
  induction l with
  | nil =>
    intro l' h rt' hb'
    have he : l' = [] := by
      simpa only [List.mapM_nil, Pure.pure, Except.pure, Except.ok.injEq] using h.symm
    subst he
    simp at hb'
  | cons head tail ih =>
    intro l' h rt' hb'
    rw [List.mapM_cons] at h
    obtain ⟨fstRt, hfirst, h⟩ := bind_ok2 h
    obtain ⟨rest, hrest, h⟩ := bind_ok2 h
    have he : fstRt :: rest = l' := by
      simpa only [Pure.pure, Except.pure, Except.ok.injEq] using h
    subst he
    simp only [List.mem_cons] at hb'
    rcases hb' with heq | hb'
    · rw [heq]
      have hid1 : fstRt.id = head.id := by
        cases hroute : pin.route head.id with
        | none =>
          simp only [hroute] at hfirst
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hfirst
          exact (congrArg (·.id) hfirst).symm
        | some d =>
          simp only [hroute] at hfirst
          obtain ⟨_pts, _hpts, hrfl⟩ := bind_ok2 hfirst
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrfl
          exact (congrArg (·.id) hrfl).symm
      exact ⟨head, List.mem_cons.mpr (Or.inl rfl), hid1⟩
    · obtain ⟨rt, hrt, hidr⟩ := ih _ hrest rt' hb'
      exact ⟨rt, List.mem_cons.mpr (Or.inr hrt), hidr⟩

-- Route id transport through the `pinBands` phase chain.
/-- One reroute step preserves the route id: every branch of the `rerouteBands`
match returns `r` or `{ r with points := ... }`. The match is copied verbatim
from `rerouteBands` (the `band` let is inlined). -/
private theorem reroutePair_id {axis : Axis} {sp : Spacing} {pin : Pin}
    {bands : List Band} {bend : Int} {s : Scene} {r old : Route} {y : Route}
    (h : ((match bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId),
        bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId),
        s.boxes.find? (·.id == r.fromId),
        s.boxes.find? (·.id == r.toId) with
      | some fi, some ti, some fb, some tb =>
        if fi == ti || old.points.length < 2 then (pure r : Except LayoutError Route)
        else do
          let ends ← routeEnds axis sp pin fb tb old.points
          let boxes := (s.boxes.filter (fun b => b.exclusive && b.id != r.fromId &&
            b.id != r.toId)).map (fun b => obstacleOf axis b.rect)
          let obs := boxes ++ textObstacles axis s
          pure { r with points := ← findRoute axis ends obs bend [sp.slot, 0] }
      | _, _, _, _ => (pure r : Except LayoutError Route)) : Except LayoutError Route) = .ok y) :
    y.id = r.id := by
  cases hfi : bands.findIdx? (fun b => b.id == r.fromId || b.members.contains r.fromId) with
  | none =>
    rw [hfi] at h
    dsimp only at h
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst h
    rfl
  | some fi =>
    cases hti : bands.findIdx? (fun b => b.id == r.toId || b.members.contains r.toId) with
    | none =>
      rw [hfi, hti] at h
      dsimp only at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
      subst h
      rfl
    | some ti =>
      cases hfb : s.boxes.find? (fun b => b.id == r.fromId) with
      | none =>
        rw [hfi, hti, hfb] at h
        dsimp only at h
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl
      | some fb =>
        cases htb : s.boxes.find? (fun b => b.id == r.toId) with
        | none =>
          rw [hfi, hti, hfb, htb] at h
          dsimp only at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          rfl
        | some tb =>
          rw [hfi, hti, hfb, htb] at h
          dsimp only at h
          by_cases hc : fi == ti || old.points.length < 2
          · simp [hc] at h
            simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
            subst h
            rfl
          · simp [hc] at h
            obtain ⟨ends, _, hy⟩ := bind_ok2 h
            obtain ⟨pts, _, hy2⟩ := bind_ok2 hy
            simp only [Except.ok.injEq] at hy2
            subst hy2
            rfl

/-- Every rerouted route comes from a pinned route with the same id. -/
private theorem rerouteRoutes_mem_id (axis : Axis) (sp : Spacing) (bend : Int)
    (bands : List Band) (pin : Pin) (original : List Route) (s routed : Scene)
    (h : rerouteBands axis sp bend bands pin original s = .ok routed) :
    ∀ r' ∈ routed.routes, ∃ r ∈ s.routes, r'.id = r.id := by
  unfold rerouteBands at h
  obtain ⟨routes, hmap, hcont⟩ := bind_ok2 h
  have hreq : routed.routes = routes := by
    dsimp only at hcont
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hcont
    rw [← hcont]
  rw [hreq]
  clear h hcont hreq
  obtain ⟨l, hl⟩ : ∃ l, s.routes = l := ⟨_, rfl⟩
  rw [hl] at hmap ⊢
  clear hl
  revert original routes hmap
  induction l with
  | nil =>
    intro original routes hmap r' hr'
    cases original with
    | nil =>
      have hempty : (([] : List Route).zip ([] : List Route)) = [] := rfl
      rw [hempty, List.mapM_nil] at hmap
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      exact absurd hr' (by simp)
    | cons o os =>
      have hempty : (([] : List Route).zip (o :: os)) = [] := rfl
      rw [hempty, List.mapM_nil] at hmap
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      exact absurd hr' (by simp)
  | cons hd tl ih =>
    intro original routes hmap r' hr'
    cases original with
    | nil =>
      have hempty : (hd :: tl).zip ([] : List Route) = [] := rfl
      rw [hempty, List.mapM_nil] at hmap
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hmap
      subst hmap
      exact absurd hr' (by simp)
    | cons o os =>
      have hzip : (hd :: tl).zip (o :: os) = (hd, o) :: (tl.zip os) := rfl
      rw [hzip, List.mapM_cons] at hmap
      obtain ⟨fst, hfst, hrest⟩ := bind_ok2 hmap
      obtain ⟨rest, hrestM, hcons⟩ := bind_ok2 hrest
      have hroutes : routes = fst :: rest := by
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hcons
        exact hcons.symm
      subst hroutes
      simp only [List.mem_cons] at hr'
      rcases hr' with heq | hr'
      · rw [heq]
        have hid : fst.id = hd.id := reroutePair_id hfst
        exact ⟨hd, List.mem_cons.mpr (Or.inl rfl), hid⟩
      · obtain ⟨r, hr, hid⟩ := ih os rest hrestM r' hr'
        exact ⟨r, List.mem_cons.mpr (Or.inr hr), hid⟩

/-- Element transport through the `pinBands` phase chain: the output scene shares
its boxes and routes with the restored origin scene, and every output box/route id
(and box parent) is witnessed by an input element. -/
theorem pinBands_transport {s r pinned routed origin : Scene} {sp : Spacing}
    {axis : Axis} {bands : List Band} {strip gap : Int} {stripScene : Scene} {bend : Int}
    (happ : applyPin (buildPin axis bands s) bands s = .ok pinned)
    (hroute : rerouteBands axis sp bend bands (buildPin axis bands s) s.routes pinned = .ok routed)
    (horig : restoreOrigin axis routed = .ok origin)
    (hrelocEq : relocateLabels axis strip gap origin = .ok stripScene)
    (hgrow : growCanvas axis s.canvas stripScene = .ok r) :
    r.boxes = origin.boxes ∧ r.routes = origin.routes ∧
      (∀ b' ∈ origin.boxes, ∃ b ∈ s.boxes, b'.id = b.id ∧ b'.parent = b.parent) ∧
      (∀ b ∈ s.boxes, ∃ b' ∈ origin.boxes, b.id = b'.id ∧ b.parent = b'.parent) ∧
      (∀ rt ∈ origin.routes, ∃ rt₀ ∈ s.routes, rt.id = rt₀.id) := by
  have hgrowF := growCanvas_frame hgrow
  have hboxesRO : r.boxes = origin.boxes := by rw [hgrowF.1, relocateLabels_boxes hrelocEq]
  have hroutesRO : r.routes = origin.routes := by rw [hgrowF.2.1, relocateLabels_routes hrelocEq]
  obtain ⟨shB, shL, shR, shI, hboxM, _hlabelM, hrouteM, _hitemM, hfold⟩ :=
    applyPin_shifted happ
  obtain ⟨_hlenSB, hidSB, hparSB, _hroleSB, _hexSB⟩ :=
    pinShiftBoxes_maps s.boxes _ _ shB hboxM
  obtain ⟨_hlenF, hidF, hparF, _hroleF, _hexF, _hlabF, hrtF, _hcanF⟩ :=
    foldReplaceFrame_all bands axis _ pinned hfold
  have hidFP : pinned.boxes.map (·.id) = shB.map (·.id) := hidF
  have hparFP : pinned.boxes.map (·.parent) = shB.map (·.parent) := hparF
  have hrtFP : pinned.routes = shR := hrtF
  have hfr := rerouteBands_frame hroute
  have hboxRid : routed.boxes.map (·.id) = pinned.boxes.map (·.id) :=
    congrArg (·.map (·.id)) hfr.1
  have hboxRpar : routed.boxes.map (·.parent) = pinned.boxes.map (·.parent) :=
    congrArg (·.map (·.parent)) hfr.1
  have hIDL : origin.boxes.map (·.id) = routed.boxes.map (·.id) ∧
      origin.boxes.map (·.parent) = routed.boxes.map (·.parent) ∧
      origin.routes.map (·.id) = routed.routes.map (·.id) := by
    rcases restoreOrigin_cases horig with heq | ⟨delta, _hpos, hshift⟩
    · subst heq
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨_hlenB, hidB, _⟩ :=
        shiftAll_boxes_labels (axis := axis) (delta := delta) (s := routed) (s' := origin) hshift
      have hparB :=
        shiftAll_boxes_parent (axis := axis) (delta := delta) (s := routed) (s' := origin) hshift
      obtain ⟨_hlenR, hidR, _hcanvas⟩ :=
        shiftAll_routes_canvas (axis := axis) (delta := delta) (s := routed) (s' := origin) hshift
      exact ⟨hidB, hparB, hidR⟩
  have hboxesIdSR : origin.boxes.map (·.id) = s.boxes.map (·.id) :=
    hIDL.1.trans (hboxRid.trans (hidFP.trans hidSB))
  have hboxesParSR : origin.boxes.map (·.parent) = s.boxes.map (·.parent) :=
    hIDL.2.1.trans (hboxRpar.trans (hparFP.trans hparSB))
  have hboxesFwd : ∀ b' ∈ origin.boxes, ∃ b ∈ s.boxes,
      b'.id = b.id ∧ b'.parent = b.parent :=
    boxCorr s.boxes origin.boxes hboxesIdSR.symm hboxesParSR.symm
  have hboxesBwd : ∀ b ∈ s.boxes, ∃ b' ∈ origin.boxes,
      b.id = b'.id ∧ b.parent = b'.parent :=
    boxCorr origin.boxes s.boxes hboxesIdSR hboxesParSR
  have hrtSR : ∀ rt ∈ origin.routes, ∃ rt₀ ∈ s.routes, rt.id = rt₀.id := by
    intro rt hrt
    have hmem : rt.id ∈ routed.routes.map (·.id) := by
      have hmem0 : rt.id ∈ origin.routes.map (·.id) := List.mem_map.mpr ⟨rt, hrt, rfl⟩
      rw [hIDL.2.2] at hmem0
      exact hmem0
    obtain ⟨rt', hrt', hrt'id⟩ := List.mem_map.mp hmem
    obtain ⟨rt'', hrt''p, hrt''id⟩ :=
      rerouteRoutes_mem_id axis sp bend bands
        (buildPin axis bands s) s.routes pinned routed hroute rt' hrt'
    have hrt''sh : rt'' ∈ shR := by
      rw [← hrtFP]
      exact hrt''p
    obtain ⟨rt₀, hrt₀, hrt₀eq⟩ :=
      pinRoutes_mem_id s.routes _ _ shR hrouteM rt'' hrt''sh
    exact ⟨rt₀, hrt₀, hrt'id.symm.trans (hrt''id.trans hrt₀eq)⟩
  exact ⟨hboxesRO, hroutesRO, hboxesFwd, hboxesBwd, hrtSR⟩

/-- `pinBands` preserves clause C7 for executed swimlane layouts: the input
scene supplies clean ids (`LaneInputIdsClean`) and the scene shape
(`LaneSceneShape`). Non-relocated labels keep their clearance by
`needsRelocation`; relocated labels move to a strip above all geometry; the
ancestor bridge (`laneRelocAncBridge` with the proved `laneAncFuelStableAll`)
and the dump congruence (`dumpAncCong`) carry the owner scope, and id transport
(`pinBands_transport`) carries box/route id disjointness to the output scene. -/
theorem pinBands_c7 {boxes : List ModelBox} {o : Options} {s r : Scene}
    (h : pinBands boxes o s = .ok r) (hin : Validator.C7 s.layoutDump)
    (hclean : LaneInputIdsClean s) (hshape : LaneSceneShape s) :
    Validator.C7 r.layoutDump := by
  have _keep := hin
  by_cases hempty : lanesOf boxes = []
  · have hr : r = s := by
      have h0 : pinBands boxes o s = .ok s := pinBands_no_lanes hempty
      rw [h0] at h
      cases h
      rfl
    subst hr
    exact hin
  · obtain ⟨sp, axis, _bands, _pinned, _routed, origin, strip, stripScene, hsp,
        _hax, _hbands, happ, hroute, horig, hstripEq, hrelocEq, hgrow⟩ :=
      pinBands_spec hempty h
    have hstrip : strip = highest axis origin + sp.slot := checked_value hstripEq
    have hslotPos : 0 < sp.slot := spacing_slot_pos hsp
    have hstripBoxes : stripScene.boxes = origin.boxes := relocateLabels_boxes hrelocEq
    have hstripRoutes : stripScene.routes = origin.routes := relocateLabels_routes hrelocEq
    obtain ⟨hgrowBoxes, hgrowRoutes, hgrowLabels⟩ := growCanvas_frame hgrow
    have hrBoxes : r.boxes = origin.boxes := by rw [hgrowBoxes, hstripBoxes]
    have hrRoutes : r.routes = origin.routes := by rw [hgrowRoutes, hstripRoutes]
    have hrLabels : r.labels = stripScene.labels := hgrowLabels
    have hdBoxes : r.layoutDump.boxes = r.boxes := (pinBands_layoutDump (r := r)).1
    have hdLabels : r.layoutDump.labels = r.labels.map (·.toLabel) :=
      (pinBands_layoutDump (r := r)).2.2.2
    obtain ⟨hnoEmptyS, hdisjS⟩ := hclean
    obtain ⟨_hbRO, _hrRO, hboxFwd, hboxBwd, hrtFwd⟩ :=
      pinBands_transport happ hroute horig hrelocEq hgrow
    have hnoEmpty : ∀ b ∈ r.boxes, b.id ≠ "" := by
      intro b hb
      have hbO : b ∈ origin.boxes := by rw [← hrBoxes]; exact hb
      obtain ⟨c, hc, hid, _hpar⟩ := hboxFwd b hbO
      rw [hid]
      exact hnoEmptyS c hc
    have hdisjIds : ∀ b ∈ r.boxes, ∀ rt ∈ r.routes, b.id ≠ rt.id := by
      intro b hb rt hrt
      have hbO : b ∈ origin.boxes := by rw [← hrBoxes]; exact hb
      have hrtO : rt ∈ origin.routes := by rw [← hrRoutes]; exact hrt
      obtain ⟨c, hc, hid, _hpar⟩ := hboxFwd b hbO
      obtain ⟨c₀, hc₀, hid₀⟩ := hrtFwd rt hrtO
      rw [hid, hid₀]
      exact hdisjS c hc c₀ hc₀
    have hshapeO : LaneSceneShape origin := by
      obtain ⟨hshEmpty, hshPar⟩ := hshape
      refine ⟨?_, ?_⟩
      · intro b hb
        obtain ⟨c, hc, hid, _hpar⟩ := hboxFwd b hb
        rw [hid]
        exact hshEmpty c hc
      · intro b hb
        obtain ⟨c, hc, hid, hpar⟩ := hboxFwd b hb
        rcases hshPar c hc with hparEmpty | hparMem
        · left
          rw [hpar, hparEmpty]
        · right
          obtain ⟨d, hd, hdid⟩ := List.mem_map.mp hparMem
          obtain ⟨d', hd', hdEq, _hparD⟩ := hboxBwd d hd
          apply List.mem_map.mpr
          refine ⟨d', hd', ?_⟩
          rw [hpar, ← hdid, hdEq]
    unfold Validator.C7
    intro l hl b hb hexcl hscope
    rw [hdLabels] at hl
    obtain ⟨sl, hslMem, hslEq⟩ := List.mem_map.mp hl
    have hslStrip : sl ∈ stripScene.labels := by rw [← hgrowLabels]; exact hslMem
    obtain ⟨m, hmMem, _hmid, hmown, hstay, hmove⟩ :=
      relocateLabels_labels hrelocEq hslStrip
    have hbR : b ∈ r.boxes := by rw [← hdBoxes]; exact hb
    have hbO : b ∈ origin.boxes := by rw [← hrBoxes]; exact hbR
    have hlRect : l.rect = sl.rect := by rw [← hslEq]
    have hbNe : b.id ≠ "" := hnoEmpty b hbR
    have hownSl : sl.owner = m.owner := hmown.symm
    have hancEq : r.layoutDump.labelOwnerAnc l =
        origin.layoutDump.labelOwnerAnc m.toLabel := by
      have hcongr := dumpAncCong r origin sl m hrBoxes hrRoutes hownSl
      rw [hslEq] at hcongr
      exact hcongr
    have hscopeO : b.id ∉ origin.layoutDump.labelOwnerAnc m.toLabel := by
      rw [← hancEq]; exact hscope
    by_cases hneed : needsRelocation origin m = false
    · have hhit := needsRelocation_false_hits hneed hbO
      have hne : b.id ≠ m.owner := by
        by_cases hroute : ∃ rt ∈ origin.routes, rt.id = m.owner
        · obtain ⟨rt, hrtMem, hrtEq⟩ := hroute
          have hrtR : rt ∈ r.routes := by rw [hrRoutes]; exact hrtMem
          have hbRt : b.id ≠ rt.id := hdisjIds b hbR rt hrtR
          rw [hrtEq] at hbRt
          exact hbRt
        · have hfindNone : origin.routes.find? (fun rt => rt.id == m.owner) = none := by
            rw [List.find?_eq_none]
            intro rt hrtMem
            have hneRt : rt.id ≠ m.owner := fun hEq => hroute ⟨rt, hrtMem, hEq⟩
            simp [hneRt]
          have hfindNoneDump :
              origin.layoutDump.routes.find? (fun rt => rt.id == m.owner) = none :=
            hfindNone
          have hmemScope : m.owner ∈ origin.layoutDump.labelOwnerAnc m.toLabel := by
            unfold LayoutDump.labelOwnerAnc
            rw [hfindNoneDump]
            simp
          intro hcontra
          rw [hcontra] at hscopeO
          exact hscopeO hmemScope
      have hbridge := laneRelocAncBridge hrelocEq m hmMem hshapeO laneAncFuelStableAll b.id
      have hnotContains : (ownerAncestors origin m).contains b.id = false := by
        rw [List.contains_eq_mem]
        simp only [decide_eq_false_iff_not]
        intro hmemAnc
        have hdisj := hbridge hmemAnc
        rcases hdisj with hmemScope | heqEmpty
        · exact hscopeO hmemScope
        · exact hbNe heqEmpty
      have hclear : ¬ b.rect.meetsInterior m.rect := by
        have hc := hits_false_clear (l := m) hhit hexcl hne hnotContains
        exact hc
      have hslRect : sl.rect = m.rect := hstay (by simp [hneed])
      have hgoal : ¬ l.rect.meetsInterior b.rect := by
        rw [hlRect, hslRect]
        rw [Rect.meetsInterior_comm]
        exact hclear
      exact hgoal
    · have hneedT : needsRelocation origin m = true := by
        cases hnb : needsRelocation origin m with
        | true => rfl
        | false => exact absurd hnb hneed
      obtain ⟨hle, -, -, -⟩ := hmove hneedT
      have hdisj : Disjoint b.rect sl.rect := strip_disjoint hbO hslotPos hstrip hle
      have hgoal : ¬ l.rect.meetsInterior b.rect := by
        rw [hlRect]
        have h1 : ¬ b.rect.meetsInterior sl.rect := hdisj
        rw [Rect.meetsInterior_comm]
        exact h1
      exact hgoal

end Elegant.Layered.LaneBands
