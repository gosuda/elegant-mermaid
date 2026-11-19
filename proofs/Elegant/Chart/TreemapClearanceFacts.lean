import Elegant.Chart.TreemapFacts
import Elegant.Kinds.Treemap

/-! Clearance facts for the treemap adapter: clause C8a (a group frame is
disjoint from every box that is neither its ancestor nor its descendant).

The proof carries a forest invariant through the `tileNodes` fold: every
assigned child tile is contained in its parent's tile, siblings receive
pairwise disjoint cells from `squarify`, and unrelated boxes end up in
disjoint sibling subtrees. -/

namespace Elegant.Treemap.Clearance

open Elegant.Treemap.CanvasC1

/-- The rectangle a node carries before the tiling fold reaches it: the root
keeps the canvas tile, every other node starts at the zero tile. This matches
`presetNode` exactly. -/
def seedRect (m : Model) (n : Node) : Tile :=
  if n.source.id == "root" then
    ⟨0, bandOf m, (constants m).width, bandOf m + (constants m).height⟩
  else ⟨0, 0, 0, 0⟩

/-- Every seeded node carries its seed rectangle. -/
theorem seeded_rect_eq_seedRect (m : Model) :
    ∀ n ∈ (assignSeries (aggregate (initialNodes m))).map
        (presetNode m (bandOf m)), n.rect = seedRect m n := by
  intro n hn
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hn
  have hsrc : ∀ w : Node, (presetNode m (bandOf m) w).source = w.source := by
    intro w
    unfold presetNode
    split <;> rfl
  unfold seedRect presetNode
  by_cases hid : w.source.id = "root"
  · rw [ite_eq_left (beq_iff_eq.mpr hid), ite_eq_left (beq_iff_eq.mpr hid)]
  · rw [ite_eq_right (by rw [beq_iff_eq]; exact hid),
      ite_eq_right (by rw [beq_iff_eq]; exact hid)]
    rw [assignSeries_aggregate_initial_rect m w hw]

/-- `Rect.Contained` transports disjointness inward: a rectangle contained in a
rectangle disjoint from `other` is itself disjoint from `other`. -/
theorem disjoint_of_contained_disjoint {outer inner other : Rect}
    (hcont : outer.Contained inner) (hdis : Disjoint outer other) :
    Disjoint inner other := by
  unfold Disjoint Rect.meetsInterior at *
  intro h
  obtain ⟨hx, hy⟩ := h
  apply hdis
  constructor <;> omega

/-- Tile-level version of `disjoint_of_contained_disjoint`. -/
theorem disjoint_tileRect_of_inside {p c o : Tile} (hc : c.Inside p)
    (hdis : Disjoint (tileRect p) (tileRect o)) :
    Disjoint (tileRect c) (tileRect o) :=
  disjoint_of_contained_disjoint (tile_inside_rect c p hc) hdis

/-- The ids of the nodes processed so far, read through the fixed reference
list `nodes0` (every fold state has the same sources, so the indices agree). -/
def processedIds (nodes0 : List Node) (done : List Nat) : List String :=
  done.filterMap fun i => (nodes0[i]?).map (·.source.id)

theorem processedIds_append (nodes0 : List Node) (d t : List Nat) :
    processedIds nodes0 (d ++ t) = processedIds nodes0 d ++ processedIds nodes0 t := by
  unfold processedIds
  rw [List.filterMap_append]

theorem processedIds_mono {nodes0 : List Node} {d₁ d₂ : List Nat}
    (h : d₁ <+: d₂) : processedIds nodes0 d₁ ⊆ processedIds nodes0 d₂ := by
  obtain ⟨t, rfl⟩ := h
  intro x hx
  rw [processedIds_append]
  exact List.mem_append.mpr (Or.inl hx)

/-- Every proper ancestor id of every node is a box id or `""`: the parent of a
box is `""` or another box id. -/
theorem parent_mem_boxIds (m : Model) (hwf : WellFormed m) (b : ModelBox)
    (hb : b ∈ m.boxes) : b.parent = "" ∨ b.parent ∈ m.boxes.map (fun x => x.id) := by
  have h := Elegant.parent_induction m hwf
    (fun id => id = "" ∨ id ∈ m.boxes.map (fun x => x.id))
    (Or.inl rfl)
    (fun c hmem _ => Or.inr (List.mem_map.mpr ⟨c, hmem, rfl⟩)) b hb
  exact h

/-- A node id occurs at most once: well-formedness gives nodup box ids and the
node sources are the box list. -/
theorem nodes_source_id_inj {nodes : List Node}
    (hnodup : (nodes.map (fun n => n.source.id)).Nodup) {a b : Node}
    (ha : a ∈ nodes) (hb : b ∈ nodes) (h : a.source.id = b.source.id) : a = b := by
  induction nodes generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.map_cons] at hnodup
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnodup
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd (List.mem_map.mpr ⟨b, hb, h.symm⟩) hx
    · exact absurd (List.mem_map.mpr ⟨a, ha, h⟩) hx
    · exact ih hxs ha hb h


namespace ClearanceContainment

theorem cfl_find_box_eq_map (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source) (id : String) :
    boxes.find? (fun b : ModelBox => b.id == id) =
      (nodes.find? (fun n : Node => n.source.id == id)).map Node.source := by
  rw [hboxes, List.find?_map]
  rfl

theorem cfl_parentChainEnds_mono (boxes : List ModelBox) :
    ∀ fuel n id, fuel ≤ n → parentChainEnds boxes fuel id = true →
      parentChainEnds boxes n id = true := by
  intro fuel n
  induction n generalizing fuel with
  | zero =>
    intro id hle h
    cases fuel with
    | zero => exact h
    | succ k => exact absurd hle (Nat.not_succ_le_zero k)
  | succ n ih =>
    intro id hle h
    by_cases he : id = ""
    · subst he; exact rfl
    · cases fuel with
      | zero =>
        have hfalse : parentChainEnds boxes 0 id = false := by
          rw [parentChainEnds.eq_2 boxes id (by intro h; exact he h)]
        rw [hfalse] at h
        exact absurd h (by decide)
      | succ k =>
        have hkle : k ≤ n := Nat.le_of_succ_le_succ hle
        cases hf : boxes.find? (fun b : ModelBox => b.id == id) with
        | none =>
          rw [parentChainEnds.eq_3 boxes id k he, hf] at h
          simp at h
          rw [parentChainEnds.eq_3 boxes id n he, hf]
        | some b =>
          rw [parentChainEnds.eq_3 boxes id k he, hf] at h
          have h' : parentChainEnds boxes k b.parent = true := h
          rw [parentChainEnds.eq_3 boxes id n he, hf]
          exact ih k b.parent hkle h'

theorem cfl_depthProfile_parentChainEnds (nodes : List Node) (boxes : List ModelBox)
    (hboxes : boxes = nodes.map Node.source) :
    ∀ (d : Nat) (id : String), CanvasC1.DepthProfile nodes id d →
      parentChainEnds boxes (d + 1) id = true := by
  intro d
  induction d with
  | zero =>
    intro id hprof
    by_cases hid : id = ""
    · subst id; rfl
    · cases hf : nodes.find? (fun x : Node => x.source.id == id) with
      | none =>
        have hcorr : boxes.find? (fun b : ModelBox => b.id == id) = none := by
          rw [cfl_find_box_eq_map nodes boxes hboxes id, hf]
          rfl
        rw [parentChainEnds.eq_3 boxes id 0 hid, hcorr]
      | some n =>
        have h2 := hprof 1
        simp [parentDepth, hf] at h2
  | succ d ih =>
    intro id hprof
    by_cases hid : id = ""
    · subst id; rfl
    · cases hf : nodes.find? (fun x : Node => x.source.id == id) with
      | none =>
        have hnez : parentDepth nodes (d + 1 + 1) id = d + 1 := by
          have := hprof (d + 1 + 1)
          simpa using this
        simp [parentDepth, hf] at hnez
      | some n =>
        have hstep : ∀ fuel, parentDepth nodes (fuel + 1) id =
            1 + parentDepth nodes fuel n.source.parent := by
          intro fuel
          simp [parentDepth, hf]
        have hprof' : CanvasC1.DepthProfile nodes n.source.parent d := by
          intro fuel
          have hs := hprof (fuel + 1)
          rw [hstep fuel] at hs
          omega
        have hcorr : boxes.find? (fun b : ModelBox => b.id == id) = some n.source := by
          rw [cfl_find_box_eq_map nodes boxes hboxes id, hf]
          rfl
        rw [parentChainEnds.eq_3 boxes id (d + 1) hid, hcorr]
        exact ih n.source.parent hprof'

theorem cfl_wellFormed_parentChainsEnd {m : Model} (hwf : WellFormed m) :
    parentChainsEnd m = true := by
  have hsrc : (initialNodes m).map Node.source = m.boxes :=
    CanvasC1.initialNodes_source m
  have hlenEq : (initialNodes m).length = m.boxes.length := by
    simpa using congrArg List.length hsrc
  unfold parentChainsEnd
  apply List.all_eq_true.mpr
  intro box hbox
  obtain ⟨depth, hprof⟩ :=
    CanvasC1.source_parent_depthProfile m hwf (initialNodes m) hsrc box hbox
  have hpos : 0 < m.boxes.length := List.length_pos_of_mem hbox
  have hk : m.boxes.length = m.boxes.length - 1 + 1 := by omega
  have hlt := CanvasC1.source_parent_depth_lt_length m hwf (initialNodes m) hsrc box hbox
  rw [hprof (initialNodes m).length, hlenEq] at hlt
  have hdepth : depth < m.boxes.length := by omega
  rw [hk]
  refine cfl_parentChainEnds_mono m.boxes (depth + 1) (m.boxes.length - 1 + 1) box.parent
    (by omega) ?_
  exact cfl_depthProfile_parentChainEnds (initialNodes m) m.boxes hsrc.symm depth box.parent hprof

end ClearanceContainment

namespace TileForestHelpers

open TileForest

/-- One step of `boxAncestors` at positive fuel, as an equation. -/
theorem boxAncestors_succ_eq (boxes : List ModelBox) (k : Nat) (id : String) :
    boxAncestors boxes (k + 1) id =
      match boxes.find? (fun b => b.id == id) with
      | none => []
      | some b =>
          if b.parent = "" then [] else b.parent :: boxAncestors boxes k b.parent := by
  rw [boxAncestors.eq_2]
  cases hfind : boxes.find? (fun b => b.id == id) <;> rfl

/-- One more unit of fuel can only append ancestors: the fuel-`k` ancestor list
is a prefix of the fuel-`(k+1)` list. -/
theorem boxAncestors_prefix_step (boxes : List ModelBox) :
    ∀ (k : Nat) (id : String),
      boxAncestors boxes k id <+: boxAncestors boxes (k + 1) id := by
  intro k id
  induction k generalizing id with
  | zero =>
    rw [boxAncestors.eq_1, boxAncestors_succ_eq boxes 0 id]
    cases hfind : boxes.find? (fun b => b.id == id) <;> simp
  | succ k ih =>
    rw [boxAncestors_succ_eq boxes (k + 1) id,
        boxAncestors_succ_eq boxes k id]
    cases hfind : boxes.find? (fun b => b.id == id) with
    | none => simp
    | some b =>
      show (if b.parent = "" then [] else b.parent :: boxAncestors boxes k b.parent) <+:
          (if b.parent = "" then [] else b.parent :: boxAncestors boxes (k + 1) b.parent)
      by_cases hp : b.parent = ""
      · rw [ite_eq_left hp, ite_eq_left hp]
        exact List.nil_prefix
      · rw [ite_eq_right hp, ite_eq_right hp, List.cons_prefix_cons]
        exact ⟨rfl, ih b.parent⟩

/-- More fuel gives a longer (prefix) ancestor list. -/
theorem boxAncestors_prefix (boxes : List ModelBox) {k₁ k₂ : Nat} (h : k₁ ≤ k₂)
    (id : String) : boxAncestors boxes k₁ id <+: boxAncestors boxes k₂ id := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  induction n with
  | zero => rw [Nat.add_zero]; exact List.prefix_rfl
  | succ n ih =>
    show boxAncestors boxes k₁ id <+: boxAncestors boxes (k₁ + n + 1) id
    exact (ih (Nat.le_add_right k₁ n)).trans (boxAncestors_prefix_step boxes (k₁ + n) id)

/-- The ancestor list never exceeds its fuel. -/
theorem boxAncestors_length_le (boxes : List ModelBox) :
    ∀ (k : Nat) (id : String), (boxAncestors boxes k id).length ≤ k := by
  intro k
  induction k with
  | zero =>
    intro id
    show (boxAncestors boxes 0 id).length ≤ 0
    rw [boxAncestors.eq_1]
    simp
  | succ k ih =>
    intro id
    rw [boxAncestors_succ_eq boxes k id]
    cases hfind : boxes.find? (fun b => b.id == id) with
    | none => simp
    | some b =>
      show (if b.parent = "" then [] else b.parent :: boxAncestors boxes k b.parent).length ≤ k + 1
      by_cases hp : b.parent = ""
      · rw [ite_eq_left hp]; simp
      · rw [ite_eq_right hp, List.length_cons]
        have := ih b.parent
        omega

/-- Once `parentChainEnds` certifies the parent walk terminates within `n+1`
steps, extra fuel cannot grow the ancestor list. -/
theorem boxAncestors_stable_of_ends (boxes : List ModelBox) :
    ∀ (n : Nat) (id : String), id ≠ "" →
      parentChainEnds boxes (n + 1) id = true →
      boxAncestors boxes (n + 2) id = boxAncestors boxes (n + 1) id := by
  intro n
  induction n with
  | zero =>
    intro id hne h
    show boxAncestors boxes (1 + 1) id = boxAncestors boxes (0 + 1) id
    rw [boxAncestors_succ_eq boxes 1 id, boxAncestors_succ_eq boxes 0 id]
    cases hf : boxes.find? (fun b => b.id == id) with
    | none => rfl
    | some b =>
      rw [parentChainEnds.eq_3 boxes id 0 hne, hf] at h
      show (if b.parent = "" then [] else b.parent :: boxAncestors boxes 1 b.parent) =
          (if b.parent = "" then [] else b.parent :: boxAncestors boxes 0 b.parent)
      by_cases hp : b.parent = ""
      · rw [ite_eq_left hp, ite_eq_left hp]
      · have h0 : parentChainEnds boxes 0 b.parent = true := h
        rw [parentChainEnds.eq_2 boxes b.parent hp] at h0
        simp at h0
  | succ n ih =>
    intro id hne h
    show boxAncestors boxes (n + 2 + 1) id = boxAncestors boxes (n + 1 + 1) id
    rw [boxAncestors_succ_eq boxes (n + 2) id, boxAncestors_succ_eq boxes (n + 1) id]
    cases hf : boxes.find? (fun b => b.id == id) with
    | none => rfl
    | some b =>
      rw [parentChainEnds.eq_3 boxes id (n + 1) hne, hf] at h
      have h' : parentChainEnds boxes (n + 1) b.parent = true := h
      show (if b.parent = "" then [] else b.parent :: boxAncestors boxes (n + 2) b.parent) =
          (if b.parent = "" then [] else b.parent :: boxAncestors boxes (n + 1) b.parent)
      by_cases hp : b.parent = ""
      · rw [ite_eq_left hp, ite_eq_left hp]
      · rw [ite_eq_right hp, ite_eq_right hp]
        exact congrArg (b.parent :: ·) (ih b.parent hp h')

/-- Under a terminating parent chain, the `(fuel+1)`-step ancestor list has
length at most `fuel`. -/
theorem anc_length_lt (boxes : List ModelBox) :
    ∀ (fuel : Nat) (id : String), id ≠ "" →
      parentChainEnds boxes fuel id = true →
      (boxAncestors boxes (fuel + 1) id).length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro id hid h
      rw [parentChainEnds.eq_2 boxes id hid] at h
      exact absurd h (by simp)
  | succ fuel ih =>
      intro id hid h
      rw [boxAncestors_succ_eq boxes (fuel + 1) id]
      cases hfind : boxes.find? (fun b => b.id == id) with
      | none => simp
      | some b =>
          show (if b.parent = "" then [] else
              b.parent :: boxAncestors boxes (fuel + 1) b.parent).length ≤ fuel + 1
          rw [parentChainEnds.eq_3 boxes id fuel hid, hfind] at h
          by_cases hb : b.parent = ""
          · rw [ite_eq_left hb]
            simp
          · rw [ite_eq_right hb, List.length_cons]
            have hih := ih b.parent hb h
            omega

end TileForestHelpers

end Elegant.Treemap.Clearance
