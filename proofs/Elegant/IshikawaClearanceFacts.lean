import Elegant.Ishikawa
import ElegantGeometry.Route
import Elegant.Chart.Scale
import Elegant.IshikawaSeparationFacts
import Elegant.ForInFacts
import Elegant.IshikawaFlattenParentFacts
import Elegant.IshikawaFlattenSizeFacts
import Elegant.IshikawaFlattenTemporalFacts
import Elegant.Kinds.IshikawaValid
import Elegant.Kinds.IshikawaSeparationFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

theorem place_empty_entries (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (cause : Tree.Node) (hcause : ns[r.cause]? = some cause)
    (hentries : r.entries = []) :
    place ns p spine r = .ok { r with pieces :=
      [(r.cause,
        (⟨-run p r.length - Int.fdiv cause.width 2,
          if r.upper then ordinate spine r.upper r.length - cause.height
          else ordinate spine r.upper r.length, cause.width, cause.height⟩ : Rect),
        [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩])] } := by
  simp [place, hcause, hentries, List.forIn_nil, pure, Except.pure, bind, Except.bind]

theorem cause_route_misses_right_box (p : Params) (spine : Int) (r : Rib)
    (dx dy : Int) (foreign : Rect)
    (hrun : 0 ≤ run p r.length) (hforeign : dx ≤ foreign.x) :
    ¬ Polyline.hitsRect
      [⟨dx, spine + dy⟩,
       ⟨-run p r.length + dx, ordinate spine r.upper r.length + dy⟩]
      foreign := by
  intro hhit
  apply hhit.2.2
  constructor
  · apply Or.inl
    change max dx (-run p r.length + dx) ≤ foreign.x
    omega
  · trivial

theorem placed_empty_entries_routes_miss_right_box
    (ns : List Tree.Node) (p : Params) (spine : Int) (r placed : Rib)
    (cause : Tree.Node) (foreign : Rect) (dx dy : Int)
    (hcause : ns[r.cause]? = some cause) (hentries : r.entries = [])
    (hrun : 0 ≤ run p r.length) (hforeign : dx ≤ foreign.x)
    (hplace : place ns p spine r = .ok placed) :
    ∀ piece ∈ placed.pieces,
      ¬ Polyline.hitsRect
        (piece.2.2.map (fun q => (⟨q.x + dx, q.y + dy⟩ : Point))) foreign := by
  rw [place_empty_entries ns p spine r cause hcause hentries] at hplace
  cases hplace
  intro piece hpiece
  simp only [List.mem_singleton] at hpiece
  subst piece
  simpa only [List.map_cons, List.map_nil, Int.zero_add] using
    cause_route_misses_right_box p spine r dx dy foreign hrun hforeign

theorem bone_route_misses_later_slot
    (spine x₀ x₁ t₀ t₁ foreignX foreignT foreignWidth foreignHeight heightBound : Int)
    (up : Bool) (dx dy : Int)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hgap₀ : t₀ + heightBound ≤ foreignT)
    (hgap₁ : t₁ + heightBound ≤ foreignT) :
    ¬ Polyline.hitsRect
      [⟨x₀ + dx, ordinate spine up t₀ + dy⟩,
       ⟨x₁ + dx, ordinate spine up t₁ + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  intro hhit
  apply hhit.2.2
  constructor
  · rw [Tree.fdiv2]
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte]
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      change max (spine + t₀ + dy) (spine + t₁ + dy) ≤
        spine + foreignT - foreignHeight / 2 + dy
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      change min (spine - t₀ + dy) (spine - t₁ + dy) ≥
        spine - foreignT - foreignHeight / 2 + dy + foreignHeight
      omega
  · trivial

theorem even_entry_route_misses_later_slot
    (p : Params) (par : Bone) (depth : Nat) (t count margin spine : Int)
    (up : Bool) (foreignX foreignT foreignWidth foreignHeight heightBound dx dy : Int)
    (heven : depth % 2 = 0)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hgap : t + heightBound ≤ foreignT) :
    let b := depthBone p par depth t count margin
    ¬ Polyline.hitsRect
      [⟨b.x0 + dx, ordinate spine up b.t0 + dy⟩,
       ⟨b.x1 + dx, ordinate spine up b.t1 + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  dsimp only
  have ht := depthBone_even_endpoints p par depth t count margin heven
  apply bone_route_misses_later_slot
  · exact hheight
  · exact hbound
  · simpa only [ht.1] using hgap
  · simpa only [ht.2.1] using hgap

theorem odd_entry_route_misses_later_slot
    (p : Params) (par : Bone) (depth : Nat) (t count margin spine : Int)
    (up : Bool) (foreignX foreignT foreignWidth foreignHeight heightBound dx dy : Int)
    (hodd : depth % 2 ≠ 0)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hparentGap : par.t0 + heightBound ≤ foreignT)
    (hentryGap : t + heightBound ≤ foreignT) :
    let b := depthBone p par depth t count margin
    ¬ Polyline.hitsRect
      [⟨b.x0 + dx, ordinate spine up b.t0 + dy⟩,
       ⟨b.x1 + dx, ordinate spine up b.t1 + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  dsimp only
  have ht := depthBone_odd_endpoints p par depth t count margin hodd
  apply bone_route_misses_later_slot
  · exact hheight
  · exact hbound
  · simpa only [ht.1] using hparentGap
  · simpa only [ht.2.1] using hentryGap

theorem entry_slot_lower_bound (length height : Int) (entries position : Nat)
    (hheight : 0 ≤ height)
    (hbudget : (entries + 1 : Nat) * height ≤ length) :
    height ≤ Int.fdiv (length * (position + 1 : Nat)) (entries + 1 : Nat) := by
  have hden : (0 : Int) < (entries + 1 : Nat) := by omega
  have hprod := Int.mul_nonneg (Int.le_of_lt hden) hheight
  have hlength : 0 ≤ length := by omega
  have hm := Int.mul_le_mul_of_nonneg_left
    (show (1 : Int) ≤ (position + 1 : Nat) by omega) hlength
  simp only [Int.mul_one] at hm
  exact Chart.le_fdiv_of_mul_le hden (Int.le_trans hbudget hm)

theorem even_entry_route_misses_later_ordered_slot
    (p : Params) (par : Bone) (depth : Nat)
    (length count margin spine : Int) (entries earlier later : Nat) (up : Bool)
    (foreignX foreignWidth foreignHeight heightBound dx dy : Int)
    (heven : depth % 2 = 0)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hbudget : (entries + 1 : Nat) * heightBound ≤ length)
    (horder : earlier < later) :
    let t := Int.fdiv (length * (earlier + 1 : Nat)) (entries + 1 : Nat)
    let foreignT := Int.fdiv (length * (later + 1 : Nat)) (entries + 1 : Nat)
    let b := depthBone p par depth t count margin
    ¬ Polyline.hitsRect
      [⟨b.x0 + dx, ordinate spine up b.t0 + dy⟩,
       ⟨b.x1 + dx, ordinate spine up b.t1 + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  apply even_entry_route_misses_later_slot
  · exact heven
  · exact hheight
  · exact hbound
  · exact ordinal_slots_gap length (entries + 1 : Nat) heightBound
      (earlier + 1 : Nat) (later + 1 : Nat) (by omega) (by omega) hbudget (by omega)

theorem bone_route_misses_opposite_ordered_slot
    (spine x₀ x₁ t₀ t₁ foreignX foreignWidth foreignHeight heightBound length : Int)
    (entries position : Nat) (up : Bool) (dx dy : Int)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hbudget : (entries + 1 : Nat) * heightBound ≤ length) :
    let foreignT := Int.fdiv (length * (position + 1 : Nat)) (entries + 1 : Nat)
    ¬ Polyline.hitsRect
      [⟨x₀ + dx, ordinate spine up t₀ + dy⟩,
       ⟨x₁ + dx, ordinate spine up t₁ + dy⟩]
      ⟨foreignX + dx, ordinate spine (!up) foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  have hslot := entry_slot_lower_bound length heightBound entries position
    (by omega) hbudget
  dsimp only
  intro hhit
  apply hhit.2.2
  constructor
  · rw [Tree.fdiv2]
    cases up <;> simp only [Bool.not_false, Bool.not_true, ordinate,
      Bool.false_eq_true, ↓reduceIte]
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      change min (spine + t₀ + dy) (spine + t₁ + dy) ≥
        spine - Int.fdiv (length * (position + 1 : Nat)) (entries + 1 : Nat) -
          foreignHeight / 2 + dy + foreignHeight
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      change max (spine - t₀ + dy) (spine - t₁ + dy) ≤
        spine + Int.fdiv (length * (position + 1 : Nat)) (entries + 1 : Nat) -
          foreignHeight / 2 + dy
      omega
  · trivial

theorem bone_route_misses_earlier_slot
    (spine x₀ x₁ t₀ t₁ foreignX foreignT foreignWidth foreignHeight heightBound : Int)
    (up : Bool) (dx dy : Int)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hgap₀ : foreignT + heightBound ≤ t₀)
    (hgap₁ : foreignT + heightBound ≤ t₁) :
    ¬ Polyline.hitsRect
      [⟨x₀ + dx, ordinate spine up t₀ + dy⟩,
       ⟨x₁ + dx, ordinate spine up t₁ + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  intro hhit
  apply hhit.2.2
  constructor
  · rw [Tree.fdiv2]
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte]
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      change min (spine + t₀ + dy) (spine + t₁ + dy) ≥
        spine + foreignT - foreignHeight / 2 + dy + foreignHeight
      omega
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      change max (spine - t₀ + dy) (spine - t₁ + dy) ≤
        spine - foreignT - foreignHeight / 2 + dy
      omega
  · trivial

theorem placed_foreign_entry_even_route_clearance
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (spine : Int) (r placed : Rib) (hplace : place ns p spine r = .ok placed)
    (hbudget : (r.entries.length + 1 : Nat) *
      r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤
        r.length)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ placed.pieces) (hforeign : i ≠ r.cause) :
    ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat),
      (e, idx) ∈ r.entries.zipIdx ∧
      r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧ i = e.node ∧
      ∀ (earlier : Nat) (par : Bone) (depth : Nat)
      (count margin dx dy : Int), depth % 2 = 0 → earlier < pos.2 →
      let t := Int.fdiv (r.length * (earlier + 1 : Nat)) (r.entries.length + 1 : Nat)
      let b := depthBone p par depth t count margin
      ¬ Polyline.hitsRect
        [⟨b.x0 + dx, ordinate spine r.upper b.t0 + dy⟩,
         ⟨b.x1 + dx, ordinate spine r.upper b.t1 + dy⟩]
        ⟨rect.x + dx, rect.y + dy, rect.w, rect.h⟩ := by
  have horigin := place_piece_placement ns p spine r placed hplace i rect points hmem
  rcases horigin with ⟨n, hn, hi, hrect⟩ | ⟨e, idx, pos, n, he, hpos, hi, hn, hw, hh, hy⟩
  · exact False.elim (hforeign hi)
  · refine ⟨e, idx, pos, he, hpos, hi, ?_⟩
    intro earlier par depth count margin dx dy heven horder
    have hdims := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
    have hbound := measured_entry_height_bound ns r.entries e
      (List.fst_mem_of_mem_zipIdx he) n hn
    dsimp only
    rw [hy, hh]
    refine even_entry_route_misses_later_ordered_slot p par depth
      r.length count margin spine r.entries.length earlier pos.2 r.upper
      rect.x rect.w n.height
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
      dx dy heven ?_ ?_ ?_ horder
    · exact Int.le_trans (by decide : (0 : Int) ≤ 1) hdims.2
    · exact hbound
    · exact hbudget

def PieceRouteOrigin (ns : List Tree.Node) (p : Params) (spine : Int) (r : Rib)
    (i : Nat) (points : List Point) : Prop :=
  (i = r.cause ∧ points =
    [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

private theorem clearance_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

inductive BoneGenealogy (ns : List Tree.Node) (p : Params) (r : Rib) : Bone → Prop
  | root : BoneGenealogy ns p r
      { x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length }
  | entry (par : Bone) (e : Entry) (idx : Nat) (pos : Nat × Nat)
      (hpar : BoneGenealogy ns p r par)
      (he : (e, idx) ∈ r.entries.zipIdx)
      (hpos : r.order.zipIdx.find? (fun v => v.1 == idx) = some pos) :
      BoneGenealogy ns p r (depthBone p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3))
  | draw (b : Bone) (hb : BoneGenealogy ns p r b) :
      BoneGenealogy ns p r { b with drawn := b.drawn + 1 }

theorem boneGenealogy_nonnegative_counters
    {ns : List Tree.Node} {p : Params} {r : Rib} {b : Bone}
    (h : BoneGenealogy ns p r b) : 0 ≤ b.count ∧ 0 ≤ b.drawn := by
  induction h with
  | root => simp
  | entry par e idx pos hpar he hpos ih =>
    unfold depthBone
    split <;> simp
  | draw b hb ih =>
    change 0 ≤ b.count ∧ 0 ≤ b.drawn + 1
    exact ⟨ih.1, Int.le_trans ih.2 (by omega)⟩

inductive IndexedBoneGenealogy (ns : List Tree.Node) (p : Params) (r : Rib) :
    Nat → Bone → Prop
  | root : IndexedBoneGenealogy ns p r 0
      { x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length }
  | entry (par : Bone) (e : Entry) (idx : Nat) (pos : Nat × Nat)
      (hpar : IndexedBoneGenealogy ns p r (e.parent + 1).toNat par)
      (he : (e, idx) ∈ r.entries.zipIdx)
      (hpos : r.order.zipIdx.find? (fun v => v.1 == idx) = some pos) :
      IndexedBoneGenealogy ns p r (idx + 1) (depthBone p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3))
  | draw (index : Nat) (b : Bone) (hb : IndexedBoneGenealogy ns p r index b) :
      IndexedBoneGenealogy ns p r index { b with drawn := b.drawn + 1 }

theorem indexedBoneGenealogy_erase
    {ns : List Tree.Node} {p : Params} {r : Rib} {index : Nat} {b : Bone}
    (h : IndexedBoneGenealogy ns p r index b) : BoneGenealogy ns p r b := by
  induction h with
  | root => exact BoneGenealogy.root
  | entry par e idx pos hpar he hpos ih =>
    exact BoneGenealogy.entry par e idx pos ih he hpos
  | draw index b hb ih => exact BoneGenealogy.draw b ih

theorem indexedBoneGenealogy_count_owner
    {ns : List Tree.Node} {p : Params} {r : Rib} {index : Nat} {b : Bone}
    (h : IndexedBoneGenealogy ns p r index b) :
    (index = 0 ∧ b.count = (children ns r.cause).length) ∨
      ∃ e idx, (e, idx) ∈ r.entries.zipIdx ∧ index = idx + 1 ∧
        b.count = (children ns e.node).length := by
  induction h with
  | root => exact Or.inl ⟨rfl, rfl⟩
  | entry par e idx pos hpar he hpos ih =>
    refine Or.inr ⟨e, idx, he, rfl, ?_⟩
    unfold depthBone
    split <;> rfl
  | draw index b hb ih => exact ih

theorem zipIdx_processed_index {α : Type} (xs : List α) (start : Nat)
    (done rest : List (α × Nat)) (a : α) (index : Nat)
    (h : xs.zipIdx start = done ++ (a, index) :: rest) :
    index = start + done.length := by
  induction xs generalizing start done with
  | nil => simp at h
  | cons first xs ih =>
    cases done with
    | nil =>
      simp only [List.zipIdx_cons, List.nil_append, List.cons.injEq,
        Prod.mk.injEq] at h
      simpa using h.1.2.symm
    | cons head done =>
      simp only [List.zipIdx_cons, List.cons_append, List.cons.injEq] at h
      have hi := ih (start + 1) done h.2
      simp only [List.length_cons]
      omega

def PieceRouteGenealogy (ns : List Tree.Node) (p : Params) (spine : Int) (r : Rib)
    (i : Nat) (points : List Point) : Prop :=
  (i = r.cause ∧ points =
    [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧ BoneGenealogy ns p r par ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

private theorem indexed_lookup_set {α : Type} (P : Nat → α → Prop)
    (xs : List α) (i : Nat) (replacement : α)
    (hold : ∀ j value, xs[j]? = some value → P j value)
    (hnew : P i replacement) :
    ∀ j value, (xs.set i replacement)[j]? = some value → P j value := by
  intro j value hvalue
  by_cases heq : i = j
  · subst j
    have hlt : i < xs.length := by
      simpa only [List.length_set] using (List.getElem?_eq_some_iff.mp hvalue).1
    rw [List.getElem?_set_self hlt] at hvalue
    cases hvalue
    exact hnew
  · rw [List.getElem?_set_ne heq] at hvalue
    exact hold j value hvalue

private theorem indexed_lookup_append_one {α : Type} (P : Nat → α → Prop)
    (xs : List α) (new : α)
    (hold : ∀ j value, xs[j]? = some value → P j value)
    (hnew : P xs.length new) :
    ∀ j value, (xs ++ [new])[j]? = some value → P j value := by
  intro j value hvalue
  by_cases hlt : j < xs.length
  · rw [List.getElem?_append_left hlt] at hvalue
    exact hold j value hvalue
  · have hbound := (List.getElem?_eq_some_iff.mp hvalue).1
    have heq : j = xs.length := by
      simp only [List.length_append, List.length_singleton] at hbound
      omega
    subst j
    rw [List.getElem?_append_right (Nat.le_refl xs.length)] at hvalue
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hvalue
    subst value
    exact hnew

def processedOddDraws (done : List (Entry × Nat)) (owner : Nat) : Int :=
  (done.filter (fun source =>
    (source.1.depth % 2 != 0) && ((source.1.parent + 1).toNat == owner))).length

theorem processedOddDraws_append_one (done : List (Entry × Nat))
    (e : Entry) (idx owner : Nat) :
    processedOddDraws (done ++ [(e, idx)]) owner =
      processedOddDraws done owner +
        if (e.depth % 2 != 0) && ((e.parent + 1).toNat == owner) then 1 else 0 := by
  unfold processedOddDraws
  rw [List.filter_append, List.length_append, Int.natCast_add]
  congr 1
  cases h : ((e.depth % 2 != 0) && ((e.parent + 1).toNat == owner)) <;>
    simp only [List.filter_cons, List.filter_nil, h] <;> rfl

theorem processedOddDraws_beyond_frontier (done : List (Entry × Nat)) (owner : Nat)
    (hfrontier : ∀ source ∈ done, (source.1.parent + 1).toNat < owner) :
    processedOddDraws done owner = 0 := by
  induction done with
  | nil => rfl
  | cons source rest ih =>
    have hlt := hfrontier source (List.mem_cons_self ..)
    have hne : ((source.1.parent + 1).toNat == owner) = false := by
      simp only [beq_eq_false_iff_ne]
      omega
    have hrest := ih (fun entry he => hfrontier entry (List.mem_cons_of_mem source he))
    simpa [processedOddDraws, hne] using hrest

theorem processedOddDraws_actual_set_append
    (done : List (Entry × Nat)) (e : Entry) (idx : Nat)
    (bones : List Bone) (par new : Bone)
    (hpar : bones[(e.parent + 1).toNat]? = some par)
    (haccount : ∀ owner b, bones[owner]? = some b →
      b.drawn = processedOddDraws done owner)
    (hfrontier : ∀ source ∈ done, (source.1.parent + 1).toNat < bones.length)
    (hnew : new.drawn = 0) :
    let next := if e.depth % 2 != 0 then
      bones.set (e.parent + 1).toNat { par with drawn := par.drawn + 1 } else bones
    ∀ owner b, (next ++ [new])[owner]? = some b →
      b.drawn = processedOddDraws (done ++ [(e, idx)]) owner := by
  let parent := (e.parent + 1).toNat
  have hparent : parent < bones.length := (List.getElem?_eq_some_iff.mp hpar).1
  have hparentDraw := haccount parent par hpar
  have hfresh : processedOddDraws (done ++ [(e, idx)]) bones.length = 0 := by
    apply processedOddDraws_beyond_frontier
    intro source hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · exact hfrontier source hs
    · exact hparent
  cases hodd : (e.depth % 2 != 0) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply indexed_lookup_append_one
      (fun owner (b : Bone) => b.drawn = processedOddDraws (done ++ [(e, idx)]) owner)
    · intro owner b hb
      simpa only [processedOddDraws_append_one, hodd, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, Int.add_zero] using haccount owner b hb
    · simpa only [hfresh] using hnew
  | true =>
    simp only [↓reduceIte]
    apply indexed_lookup_append_one
      (fun owner (b : Bone) => b.drawn = processedOddDraws (done ++ [(e, idx)]) owner)
    · intro owner b hb
      by_cases heq : parent = owner
      · subst owner
        rw [List.getElem?_set_self hparent] at hb
        cases hb
        simpa only [processedOddDraws_append_one, hodd, parent, beq_self_eq_true,
          Bool.true_and, ↓reduceIte] using congrArg (fun n : Int => n + 1) hparentDraw
      · rw [List.getElem?_set_ne heq] at hb
        have hne : ((e.parent + 1).toNat == owner) = false := by
          simpa only [beq_eq_false_iff_ne] using heq
        simpa only [processedOddDraws_append_one, hodd, hne, Bool.true_and,
          Bool.false_eq_true, ↓reduceIte, Int.add_zero] using haccount owner b hb
    · simpa only [List.length_set, hfresh] using hnew

def IndexedPieceRouteGenealogy (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (i : Nat) (points : List Point) : Prop :=
  (i = r.cause ∧ points =
    [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧
    IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

def AccountedPieceRouteGenealogy (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (i : Nat) (points : List Point) : Prop :=
  (i = r.cause ∧ points =
    [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node)
    (done rest : List (Entry × Nat)),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧
    IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧
    r.entries.zipIdx = done ++ (e, idx) :: rest ∧
    par.drawn = processedOddDraws done (e.parent + 1).toNat ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

def AccountedPieceGeometry (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (i : Nat) (rect : Rect) (points : List Point) : Prop :=
  (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
    rect = ⟨-run p r.length - Int.fdiv n.width 2,
      if r.upper then ordinate spine r.upper r.length - n.height
      else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
    points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node)
    (done rest : List (Entry × Nat)),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧
    IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧
    r.entries.zipIdx = done ++ (e, idx) :: rest ∧
    par.drawn = processedOddDraws done (e.parent + 1).toNat ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    rect = ⟨b.x1 - n.width, ordinate spine r.upper b.t1 - Int.fdiv n.height 2,
      n.width, n.height⟩ ∧
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

private def birthFrame (b : Bone) : Bone := { b with drawn := 0 }

private def BirthRecord (ns : List Tree.Node) (p : Params) (r : Rib)
    (frames : List Bone) (e : Entry) (idx : Nat) : Prop :=
  ∃ (pos : Nat × Nat) (parent born : Bone),
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    frames[(e.parent + 1).toNat]? = some parent ∧ frames[idx + 1]? = some born ∧
    born = depthBone p
      { parent with drawn := processedOddDraws (r.entries.zipIdx.take idx) (e.parent + 1).toNat }
      e.depth (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns e.node).length (run p r.heights + 3)

private def BirthPieceGeometry (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (frames : List Bone) (i : Nat) (rect : Rect) (points : List Point) : Prop :=
  (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
    rect = ⟨-run p r.length - Int.fdiv n.width 2,
      if r.upper then ordinate spine r.upper r.length - n.height
      else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
    points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (n : Tree.Node) (born : Bone),
    (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some n ∧
    frames[idx + 1]? = some born ∧
    rect = ⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
      n.width, n.height⟩ ∧
    points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
      ⟨born.x1, ordinate spine r.upper born.t1⟩]

private def BirthInvariant (ns : List Tree.Node) (p : Params) (spine : Int) (r : Rib)
    (done : List (Entry × Nat)) (pieces : List (Nat × Rect × List Point))
    (bones : List Bone) : Prop :=
  let frames := bones.map birthFrame
  frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) ∧
  (∀ e idx, (e, idx) ∈ done → BirthRecord ns p r frames e idx) ∧
  ∀ i rect points, (i, rect, points) ∈ pieces →
    BirthPieceGeometry ns p spine r frames i rect points

private theorem birth_lookup_append (frames : List Bone) (new : Bone) (i : Nat)
    (b : Bone) (h : frames[i]? = some b) : (frames ++ [new])[i]? = some b := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).choose]
  exact h

private theorem birthFrame_fixed (b : Bone) (h : b.drawn = 0) : birthFrame b = b := by
  cases b
  simp_all [birthFrame]

private theorem birthFrame_restore (b : Bone) (drawn : Int) (h : b.drawn = drawn) :
    { birthFrame b with drawn } = b := by
  cases b
  simp_all [birthFrame]

private theorem birth_frames_draw (bones : List Bone) (owner : Nat) (par : Bone)
    (hpar : bones[owner]? = some par) :
    (bones.set owner { par with drawn := par.drawn + 1 }).map birthFrame =
      bones.map birthFrame := by
  rw [List.map_set]
  change (bones.map birthFrame).set owner (birthFrame par) = bones.map birthFrame
  have hlookup : (bones.map birthFrame)[owner]? = some (birthFrame par) := by
    simp only [List.getElem?_map, hpar, Option.map_some]
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hlookup
  simpa only [hv] using (List.set_getElem_self hi)

private theorem birth_frames_set_append (bones : List Bone) (e : Entry)
    (par born : Bone) (hpar : bones[(e.parent + 1).toNat]? = some par)
    (hzero : born.drawn = 0) :
    ((if e.depth % 2 != 0 then
      bones.set (e.parent + 1).toNat { par with drawn := par.drawn + 1 } else bones) ++
        [born]).map birthFrame = bones.map birthFrame ++ [born] := by
  cases hodd : (e.depth % 2 != 0) with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.map_append,
      List.map_cons, List.map_nil, birthFrame_fixed born hzero]
  | true =>
    simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil,
      birthFrame_fixed born hzero, birth_frames_draw bones _ par hpar]

private theorem birth_record_append (ns : List Tree.Node) (p : Params) (r : Rib)
    (frames : List Bone) (new : Bone) (e : Entry) (idx : Nat)
    (h : BirthRecord ns p r frames e idx) :
    BirthRecord ns p r (frames ++ [new]) e idx := by
  obtain ⟨pos, parent, born, hpos, hparent, hborn, heq⟩ := h
  exact ⟨pos, parent, born, hpos,
    birth_lookup_append frames new _ parent hparent,
    birth_lookup_append frames new _ born hborn, heq⟩

private theorem birth_piece_append (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (frames : List Bone) (new : Bone) (i : Nat) (rect : Rect)
    (points : List Point) (h : BirthPieceGeometry ns p spine r frames i rect points) :
    BirthPieceGeometry ns p spine r (frames ++ [new]) i rect points := by
  rcases h with hroot | ⟨e, idx, n, born, he, hi, hn, hb, hr, hp⟩
  · exact Or.inl hroot
  · exact Or.inr ⟨e, idx, n, born, he, hi, hn,
      birth_lookup_append frames new _ born hb, hr, hp⟩

private theorem birthInvariant_set_append (ns : List Tree.Node) (p : Params)
    (spine : Int) (r : Rib) (done : List (Entry × Nat))
    (pieces : List (Nat × Rect × List Point)) (bones : List Bone)
    (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node)
    (born : Bone) (rest : List (Entry × Nat))
    (hprefix : r.entries.zipIdx = done ++ (e, idx) :: rest)
    (hidx : idx = done.length) (hlen : bones.length = done.length + 1)
    (hpar : bones[(e.parent + 1).toNat]? = some par)
    (hdrawn : par.drawn = processedOddDraws done (e.parent + 1).toNat)
    (hpos : r.order.zipIdx.find? (fun v => v.1 == idx) = some pos)
    (hn : ns[e.node]? = some n) (hzero : born.drawn = 0)
    (hborn : born = depthBone p par e.depth
      (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns e.node).length (run p r.heights + 3))
    (hold : BirthInvariant ns p spine r done pieces bones) :
    BirthInvariant ns p spine r (done ++ [(e, idx)])
      (pieces ++ [(e.node,
        (⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
          n.width, n.height⟩ : Rect),
        [⟨born.x0, ordinate spine r.upper born.t0⟩,
          ⟨born.x1, ordinate spine r.upper born.t1⟩])])
      ((if e.depth % 2 != 0 then
        bones.set (e.parent + 1).toNat { par with drawn := par.drawn + 1 } else bones) ++
          [born]) := by
  let frames := bones.map birthFrame
  have hframes := birth_frames_set_append bones e par born hpar hzero
  have hparent : frames[(e.parent + 1).toNat]? = some (birthFrame par) := by
    simp only [frames, List.getElem?_map, hpar, Option.map_some]
  have hframeLen : frames.length = idx + 1 := by
    simp only [frames, List.length_map]
    omega
  have hnew : (frames ++ [born])[idx + 1]? = some born := by
    rw [← hframeLen]
    simp
  have htake : r.entries.zipIdx.take idx = done := by
    rw [hprefix]
    exact List.take_left' hidx.symm
  have hrestore :
      { birthFrame par with
        drawn := processedOddDraws (r.entries.zipIdx.take idx) (e.parent + 1).toNat } = par := by
    rw [htake]
    exact birthFrame_restore par _ hdrawn
  have he : (e, idx) ∈ r.entries.zipIdx := by rw [hprefix]; simp
  unfold BirthInvariant
  rw [hframes]
  refine ⟨birth_lookup_append frames born 0 _ hold.1, ?_, ?_⟩
  · intro entry index hmem
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with hmem | ⟨rfl, rfl⟩
    · exact birth_record_append ns p r frames born entry index (hold.2.1 entry index hmem)
    · refine ⟨pos, birthFrame par, born, hpos,
        birth_lookup_append frames born _ _ hparent, hnew, ?_⟩
      rw [hrestore]
      exact hborn
  · intro i rect points hmem
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
    rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
    · exact birth_piece_append ns p spine r frames born i rect points (hold.2.2 i rect points hmem)
    · exact Or.inr ⟨e, idx, n, born, he, rfl, hn, hnew, rfl, rfl⟩

private theorem place_accounted_geometry_frames (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    (∀ i rect points, (i, rect, points) ∈ placed.pieces →
      AccountedPieceGeometry ns p spine r i rect points) ∧
    ∃ frames : List Bone, frames.length = r.entries.length + 1 ∧
      frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) ∧
      (∀ e idx, (e, idx) ∈ r.entries.zipIdx → BirthRecord ns p r frames e idx) ∧
      ∀ i rect points, (i, rect, points) ∈ placed.pieces →
        BirthPieceGeometry ns p spine r frames i rect points := by
  simp only [place] at hrun
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, hloop, hret⟩ := clearance_bind_ok hrun
    let P := fun (done : List (Entry × Nat))
        (st : List (Nat × Rect × List Point) × List Bone) =>
      st.2.length = done.length + 1 ∧
      (∀ j b, st.2[j]? = some b → IndexedBoneGenealogy ns p r j b) ∧
      (∀ owner b, st.2[owner]? = some b →
        b.drawn = processedOddDraws done owner) ∧
      (∀ source ∈ done, (source.1.parent + 1).toNat < st.2.length) ∧
      (∀ i rect points, (i, rect, points) ∈ st.1 →
        AccountedPieceGeometry ns p spine r i rect points) ∧
      BirthInvariant ns p spine r done st.1 st.2
    have hinv : P ([] ++ r.entries.zipIdx) mid := by
      refine Elegant.forIn_processed [] _ _ _ _ P ?_ ?_ hloop
      · constructor
        · rfl
        · constructor
          · intro j b hb
            cases j with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
              subst b
              exact IndexedBoneGenealogy.root
            | succ j => simp at hb
          · constructor
            · intro owner b hb
              cases owner with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
                subst b
                rfl
              | succ owner => simp at hb
            · constructor
              · intro source hs
                cases hs
              · constructor
                · intro i rect points hmem
                  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨rfl, rfl, rfl⟩
                  exact Or.inl ⟨cause, hcause, rfl, rfl, rfl⟩
                · refine ⟨rfl, ?_, ?_⟩
                  · intro e idx hm
                    cases hm
                  · intro i rect points hmem
                    simp only [List.mem_singleton, Prod.mk.injEq] at hmem
                    rcases hmem with ⟨rfl, rfl, rfl⟩
                    exact Or.inl ⟨cause, hcause, rfl, rfl, rfl⟩
      · intro done entry rest state next heq hi hstep
        obtain ⟨e, idx⟩ := entry
        have he : (e, idx) ∈ r.entries.zipIdx := by
          simp only [List.nil_append] at heq
          rw [heq]
          simp
        have hidx : idx = done.length := by
          have hz := zipIdx_processed_index r.entries 0 done rest e idx
            (by simpa only [List.nil_append] using heq)
          simpa only [Nat.zero_add] using hz
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          have hgene := hi.2.1 (e.parent + 1).toNat par hpar
          have hparentDraw := hi.2.2.1 (e.parent + 1).toNat par hpar
          have hparentBound := (List.getElem?_eq_some_iff.mp hpar).1
          have hdraw := indexed_lookup_set (IndexedBoneGenealogy ns p r)
            state.2 (e.parent + 1).toNat { par with drawn := par.drawn + 1 }
            hi.2.1 (IndexedBoneGenealogy.draw (e.parent + 1).toNat par hgene)
          cases hpos : r.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            let newBone := depthBone p par e.depth
              (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
              (children ns e.node).length (run p r.heights + 3)
            have hzero : newBone.drawn = 0 := by
              dsimp only [newBone]
              unfold depthBone
              split <;> rfl
            have haccountNext := processedOddDraws_actual_set_append done e idx
              state.2 par newBone hpar hi.2.2.1 hi.2.2.2.1 hzero
            by_cases hg : ((e.depth % 2 == 0) && decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep <;> rename_i hodd
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some n =>
                  have hbirthNext := birthInvariant_set_append ns p spine r done state.1 state.2
                    e idx pos par n newBone rest
                    (by simpa only [List.nil_append] using heq) hidx hi.1 hpar hparentDraw
                    hpos hn hzero rfl hi.2.2.2.2.2
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  refine ⟨_, rfl, ?_⟩
                  constructor
                  · simpa only [List.length_append, List.length_singleton,
                      List.length_set] using congrArg (fun n : Nat => n + 1) hi.1
                  · constructor
                    · have hnew := IndexedBoneGenealogy.entry par e idx pos hgene he hpos
                      first
                      | apply indexed_lookup_append_one (IndexedBoneGenealogy ns p r)
                          _ _ hdraw
                        simpa only [List.length_set, hi.1, hidx] using hnew
                      | apply indexed_lookup_append_one (IndexedBoneGenealogy ns p r)
                          _ _ hi.2.1
                        simpa only [hi.1, hidx] using hnew
                    · constructor
                      · first
                        | simpa only [hodd, ↓reduceIte] using haccountNext
                        | simpa only [hodd, Bool.false_eq_true, ↓reduceIte] using haccountNext
                      · constructor
                        · intro source hs
                          simp only [List.mem_append, List.mem_singleton] at hs
                          simp only [List.length_append, List.length_singleton,
                            List.length_set]
                          rcases hs with hs | rfl
                          · exact Nat.lt_trans (hi.2.2.2.1 source hs)
                              (Nat.lt_succ_self state.2.length)
                          · exact Nat.lt_trans hparentBound
                              (Nat.lt_succ_self state.2.length)
                        · constructor
                          · intro i rect points hmem
                            simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem
                            rcases hmem with hmem | ⟨rfl, rfl, rfl⟩
                            · exact hi.2.2.2.2.1 i rect points hmem
                            · exact Or.inr ⟨e, idx, pos, par, n, done, rest, he, hpos,
                                hn, rfl, hgene, by simpa only [List.nil_append] using heq,
                                hparentDraw, rfl, rfl⟩
                          · first
                            | simpa only [hodd, ↓reduceIte] using hbirthNext
                            | simpa only [hodd, Bool.false_eq_true, ↓reduceIte] using hbirthNext
    simp only [pure, Except.pure, Except.ok.injEq] at hret
    subst placed
    have hf := hinv.2.2.2.2.2
    refine ⟨hinv.2.2.2.2.1, ⟨mid.2.map birthFrame, ?_, hf.1, hf.2.1, hf.2.2⟩⟩
    simpa only [List.length_map, List.nil_append, List.length_zipIdx] using hinv.1

theorem place_piece_accounted_geometry (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      AccountedPieceGeometry ns p spine r i rect points :=
  (place_accounted_geometry_frames ns p spine r placed hrun).1

theorem place_common_birth_frames (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hplace : place ns p spine r = .ok placed) :
    ∃ frames : List Bone, frames.length = r.entries.length + 1 ∧
      frames[0]? = some ({ x1 := -run p r.length, t1 := r.length, count := (children ns r.cause).length } : Bone) ∧
      (∀ (done : List (Entry × Nat)) (e : Entry) (idx : Nat) (rest : List (Entry × Nat)),
        r.entries.zipIdx = done ++ (e, idx) :: rest →
        ∃ (pos : Nat × Nat) (parent born : Bone),
          r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
          frames[(e.parent + 1).toNat]? = some parent ∧ frames[idx + 1]? = some born ∧
          born = depthBone p
            { parent with drawn := processedOddDraws done (e.parent + 1).toNat }
            e.depth (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
            (children ns e.node).length (run p r.heights + 3)) ∧
      (∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv n.width 2,
            if r.upper then ordinate spine r.upper r.length - n.height
            else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (n : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some n ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
            n.width, n.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩]) := by
  obtain ⟨frames, hlength, hroot, hrecords, hpieces⟩ :=
    (place_accounted_geometry_frames ns p spine r placed hplace).2
  refine ⟨frames, hlength, hroot, ?_, hpieces⟩
  intro done e idx rest hprefix
  have he : (e, idx) ∈ r.entries.zipIdx := by rw [hprefix]; simp
  have hidx : idx = done.length := by
    have hi := zipIdx_processed_index r.entries 0 done rest e idx hprefix
    simpa only [Nat.zero_add] using hi
  have htake : r.entries.zipIdx.take idx = done := by
    rw [hprefix]
    exact List.take_left' hidx.symm
  have hrecord := hrecords e idx he
  simpa only [BirthRecord, htake] using hrecord

theorem place_piece_route_accounted_genealogy (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      AccountedPieceRouteGenealogy ns p spine r i points := by
  intro i rect points hmem
  have hg := place_piece_accounted_geometry ns p spine r placed hrun i rect points hmem
  rcases hg with ⟨n, hn, hi, hrect, hpoints⟩ |
    ⟨e, idx, pos, par, n, done, rest, he, hpos, hn, hi, hpar, hprefix, hdrawn, hrect, hpoints⟩
  · exact Or.inl ⟨hi, hpoints⟩
  · exact Or.inr ⟨e, idx, pos, par, n, done, rest, he, hpos, hn, hi, hpar,
      hprefix, hdrawn, hpoints⟩

theorem place_piece_route_indexed_genealogy (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      IndexedPieceRouteGenealogy ns p spine r i points := by
  intro i rect points hmem
  have hg := place_piece_route_accounted_genealogy ns p spine r placed hrun i rect points hmem
  rcases hg with hcause |
    ⟨e, idx, pos, par, n, done, rest, he, hpos, hn, hi, hpar, hprefix, hdrawn, hpoints⟩
  · exact Or.inl hcause
  · exact Or.inr ⟨e, idx, pos, par, n, he, hpos, hn, hi, hpar, hpoints⟩

theorem place_piece_route_genealogy (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      PieceRouteGenealogy ns p spine r i points := by
  intro i rect points hmem
  have hg := place_piece_route_indexed_genealogy ns p spine r placed hrun i rect points hmem
  rcases hg with hcause | ⟨e, idx, pos, par, n, he, hpos, hn, hi, hpar, hpoints⟩
  · exact Or.inl hcause
  · exact Or.inr ⟨e, idx, pos, par, n, he, hpos, hn, hi,
      indexedBoneGenealogy_erase hpar, hpoints⟩

theorem place_piece_route_origin (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib) (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      PieceRouteOrigin ns p spine r i points := by
  intro i rect points hmem
  have hg := place_piece_route_genealogy ns p spine r placed hrun i rect points hmem
  rcases hg with hcause | ⟨e, idx, pos, par, n, he, hpos, hn, hi, hpar, hpoints⟩
  · exact Or.inl hcause
  · exact Or.inr ⟨e, idx, pos, par, n, he, hpos, hn, hi, hpoints⟩


theorem placed_pieces_spine_clearance
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (spine : Int) (r placed : Rib) (hplace : place ns p spine r = .ok placed)
    (hlength : 0 ≤ r.length)
    (hbudget : (r.entries.length + 1 : Nat) *
      r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤
        r.length)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ placed.pieces) (x₀ x₁ dx dy : Int) :
    ¬ Polyline.hitsRect [⟨x₀, spine + dy⟩, ⟨x₁, spine + dy⟩]
      ⟨rect.x + dx, rect.y + dy, rect.w, rect.h⟩ := by
  have horigin := place_piece_placement ns p spine r placed hplace i rect points hmem
  rcases horigin with ⟨n, hn, hi, hrect⟩ |
    ⟨e, idx, pos, n, he, hpos, hi, hn, hw, hh, hy⟩
  · subst rect
    intro hhit
    apply hhit.2.2
    constructor
    · cases hup : r.upper <;>
        simp only [ordinate, Bool.false_eq_true, ↓reduceIte]
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        change max (spine + dy) (spine + dy) ≤ spine + r.length + dy
        omega
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        change min (spine + dy) (spine + dy) ≥
          spine - r.length - n.height + dy + n.height
        omega
    · trivial
  · have hdims := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
    have hbound := measured_entry_height_bound ns r.entries e
      (List.fst_mem_of_mem_zipIdx he) n hn
    have hnonnegative : 0 ≤
        r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
      entry_height_fold_initial ns r.entries 0
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    have hslot :
        r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ t :=
      entry_slot_lower_bound r.length _ r.entries.length pos.2 hnonnegative hbudget
    rw [hy, hh]
    intro hhit
    apply hhit.2.2
    constructor
    · rw [Tree.fdiv2]
      cases hup : r.upper <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte]
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        change max (spine + dy) (spine + dy) ≤ spine + t - n.height / 2 + dy
        omega
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        apply Or.inl
        change min (spine + dy) (spine + dy) ≥
          spine - t - n.height / 2 + dy + n.height
        omega
    · trivial

theorem generated_parent_drawn_le_count
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (owner : Nat) (par : Bone)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) owner par)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (hdrawn : par.drawn = processedOddDraws done owner) :
    par.drawn ≤ par.count := by
  have hcount := indexedBoneGenealogy_count_owner hgene
  rcases hcount with ⟨hroot, hcount⟩ | ⟨parentEntry, parentIdx, hentry, howner, hcount⟩
  · have hcfield :
        (effectivePlacedInput ns length (generatedRib ns (cause, k))).cause = cause :=
      (generated_rib_fields ns cause k).1
    rw [hcfield] at hcount
    have hnat := generated_prefix_odd_child_count_le ns cause k hlink hcause
      done rest hprefix owner cause (Or.inl ⟨hroot, rfl⟩)
    rw [hdrawn, hcount]
    unfold processedOddDraws
    omega
  · have hnat := generated_prefix_odd_child_count_le ns cause k hlink hcause
      done rest hprefix owner parentEntry.node
      (Or.inr ⟨parentEntry, parentIdx, hentry, howner, rfl⟩)
    rw [hdrawn, hcount]
    unfold processedOddDraws
    omega

def BoundedPieceRouteGenealogy (ns : List Tree.Node) (p : Params) (spine : Int)
    (r : Rib) (i : Nat) (points : List Point) : Prop :=
  (i = r.cause ∧ points =
    [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
  ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node),
    (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    ns[e.node]? = some n ∧ i = e.node ∧
    IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧
    par.drawn ≤ par.count ∧
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
      ⟨b.x1, ordinate spine r.upper b.t1⟩]

theorem generated_place_piece_parent_draw_bound
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) = .ok placed)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ placed.pieces) :
    BoundedPieceRouteGenealogy ns p spine
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) i points := by
  have hg := place_piece_route_accounted_genealogy ns p spine _ placed hplace i rect points hmem
  rcases hg with hcauseRoute |
    ⟨e, idx, pos, par, n, done, rest, he, hpos, hn, hi, hpar, hprefix, hdrawn, hpoints⟩
  · exact Or.inl hcauseRoute
  · have hbound := generated_parent_drawn_le_count ns p cause k length hlink hcause
      (e.parent + 1).toNat par hpar done ((e, idx) :: rest) hprefix hdrawn
    exact Or.inr ⟨e, idx, pos, par, n, he, hpos, hn, hi, hpar, hbound, hpoints⟩

theorem placed_rib_parent_draw_bound
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib) (length : Bool → Int) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r =>
      place ns p spine (effectivePlacedInput ns length r)) = .ok placed)
    (r : Rib) (hr : r ∈ placed)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ r.pieces) :
    ∃ source cause k, source ∈ ribs ∧ (cause, k) ∈ (children ns 0).zipIdx ∧
      source = generatedRib ns (cause, k) ∧
      BoundedPieceRouteGenealogy ns p spine (effectivePlacedInput ns length source) i points := by
  obtain ⟨source, cause, k, hsource, hcause, heq, hplace⟩ :=
    placed_rib_source ns p ribs placed length spine hg hplaces r hr
  refine ⟨source, cause, k, hsource, hcause, heq, ?_⟩
  rw [heq] at hplace ⊢
  exact generated_place_piece_parent_draw_bound ns p cause k length
    (Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun)
    (List.fst_mem_of_mem_zipIdx hcause) spine r hplace i rect points hmem

theorem entry_slot_upper_bound (length : Int) (entries position : Nat)
    (hlength : 0 ≤ length) (hposition : position < entries) :
    Int.fdiv (length * (position + 1 : Nat)) (entries + 1 : Nat) ≤ length := by
  apply Chart.fdiv_le_of_le_mul (by omega)
  have hmul := Int.mul_le_mul_of_nonneg_left
    (show ((position + 1 : Nat) : Int) ≤ (entries + 1 : Nat) by omega) hlength
  simpa only [Int.mul_comm length ((entries + 1 : Nat) : Int)] using hmul

theorem generated_bone_temporal_bounds
    (ns : List Tree.Node) (p : Params) (ribs : List Rib) (cause k : Nat)
    (hmin : 0 ≤ p.ribMin) (hbase : 0 ≤ p.spineBase) (b : Bone)
    (hgene : BoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) b) :
    let length := (effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k))).length
    0 ≤ b.t0 ∧ b.t0 ≤ length ∧ 0 ≤ b.t1 ∧ b.t1 ≤ length := by
  have hlength := effective_length_nonnegative ns p ribs (generatedRib ns (cause, k))
    hmin hbase
  dsimp only
  induction hgene with
  | root => exact ⟨Int.le_refl 0, hlength, hlength, Int.le_refl _⟩
  | entry par e idx pos hpar he hpos ih =>
    have hfields := (generated_rib_fields ns cause k).2.2.1
    have horder : (generatedRib ns (cause, k)).order =
        (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
      congrArg Prod.snd hfields
    have hentries : (generatedRib ns (cause, k)).entries =
        (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
      congrArg Prod.fst hfields
    simp only [effectivePlacedInput] at hpos
    rw [horder] at hpos
    have hfound := generated_rib_found_ordinal_lt ns cause k idx pos hpos
    have hord : pos.2 < (generatedRib ns (cause, k)).entries.length := by
      rw [hentries]
      exact hfound
    have hslotLo := entry_slot_lower_bound
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).length
      0 (generatedRib ns (cause, k)).entries.length pos.2 (Int.le_refl 0)
      (by simpa only [Int.mul_zero] using hlength)
    have hslotHi := entry_slot_upper_bound
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))).length
      (generatedRib ns (cause, k)).entries.length pos.2 hlength hord
    unfold depthBone
    split
    · exact ⟨ih.1, ih.2.1, hslotLo, hslotHi⟩
    · exact ⟨hslotLo, hslotHi, hslotLo, hslotHi⟩
  | draw index hb ih => exact ih

theorem nonpositive_interpolation_between (left right denominator weight : Int)
    (hspan : right ≤ left) (hden : 0 < denominator)
    (hweight : 0 ≤ weight) (hcap : weight ≤ denominator) :
    right ≤ left + Int.fdiv ((right - left) * weight) denominator ∧
      left + Int.fdiv ((right - left) * weight) denominator ≤ left := by
  have hdelta : right - left ≤ 0 := by omega
  have hlo := Int.mul_le_mul_of_nonpos_right hcap hdelta
  have hhi := Int.mul_le_mul_of_nonneg_right hdelta hweight
  have hquot := Chart.fdiv_between ((right - left) * weight) denominator
    (right - left) 0 hden
    (by simpa only [Int.mul_comm weight (right - left)] using hlo)
    (by simpa only [Int.zero_mul, Int.mul_zero] using hhi)
  omega

theorem generated_parent_odd_start_between
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (owner : Nat) (par : Bone)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) owner par)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (hdrawn : par.drawn = processedOddDraws done owner)
    (depth : Nat) (t count margin : Int) (hodd : depth % 2 ≠ 0)
    (hspan : par.x1 ≤ par.x0) :
    let b := depthBone p par depth t count margin
    par.x1 ≤ b.x0 ∧ b.x0 ≤ par.x0 := by
  have hnonnegative := boneGenealogy_nonnegative_counters (indexedBoneGenealogy_erase hgene)
  have hcap := generated_parent_drawn_le_count ns p cause k length hlink hcause
    owner par hgene done rest hprefix hdrawn
  have hstart := (depthBone_odd_endpoints p par depth t count margin hodd).2.2.1
  dsimp only
  rw [hstart]
  exact nonpositive_interpolation_between par.x0 par.x1 (par.count + 1)
    (par.count - par.drawn) hspan (by omega) (by omega) (by omega)

theorem indexedBoneGenealogy_temporal_origin
    {ns : List Tree.Node} {p : Params} {r : Rib} {index : Nat} {b : Bone}
    (hgene : IndexedBoneGenealogy ns p r index b) :
    (index = 0 ∧ b.t0 = 0 ∧ b.t1 = r.length) ∨
      ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone),
        (e, idx) ∈ r.entries.zipIdx ∧
        r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
        index = idx + 1 ∧
        IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧
        let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
        b.t1 = t ∧ (e.depth % 2 = 0 → b.t0 = t) ∧
          (e.depth % 2 ≠ 0 → b.t0 = par.t0) := by
  induction hgene with
  | root => exact Or.inl ⟨rfl, rfl, rfl⟩
  | entry par e idx pos hpar he hpos ih =>
    refine Or.inr ⟨e, idx, pos, par, he, hpos, rfl, hpar, ?_, ?_, ?_⟩
    · exact depthBone_endpoint_slot p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3)
    · intro heven
      exact (depthBone_even_endpoints p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3) heven).1
    · intro hodd
      exact (depthBone_odd_endpoints p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3) hodd).1
  | draw index b hb ih => exact ih

theorem sceneBoxOrigin_positive_lookup (m : Model) (normalized : Tree.Layout)
    (box : Box)
    (horigin : Elegant.Kinds.IshikawaSeparation.SceneBoxOrigin m normalized box)
    (hwidth : 0 < box.rect.w) (hheight : 0 < box.rect.h) :
    ∃ (i : Nat) (source : ModelBox), m.boxes[i]? = some source ∧
      box.id = source.id ∧ normalized.boxes[i]? = some box.rect := by
  obtain ⟨i, source, hsource, hid, hrect⟩ := horigin
  rcases hrect with hzero | hrect
  · rcases hzero with hw | hh
    · omega
    · omega
  · cases hlookup : normalized.boxes[i]? with
    | none =>
      simp only [hlookup, Option.getD_none] at hrect
      have hw := congrArg Rect.w hrect
      dsimp only at hw
      omega
    | some rect =>
      simp only [hlookup, Option.getD_some] at hrect
      refine ⟨i, source, hsource, hid, ?_⟩
      rw [hrect]
      exact hlookup

theorem successful_scene_positive_box_sources (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    ∃ (nodes : List Tree.Node) (raw normalized : Tree.Layout) (canvas : Size),
      layout nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
      Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
      ∀ box ∈ s.boxes, 0 < box.rect.w → 0 < box.rect.h →
        ∃ (i : Nat) (source : ModelBox), i < nodes.length ∧
          m.boxes[i]? = some source ∧ box.id = source.id ∧
          normalized.boxes[i]? = some box.rect ∧
          ∀ route : Route, box.id ∉ s.layoutDump.routeScope route →
            source.id ≠ route.fromId ∧ source.id ≠ route.toId := by
  obtain ⟨nodes, raw, normalized, canvas, hraw, hnormal, horigins⟩ :=
    Elegant.Kinds.IshikawaSeparation.successful_scene_box_origins m s hs
  have hlength := (Elegant.Kinds.IshikawaValid.successful_normalized_lengths nodes
    (Elegant.Kinds.Ishikawa.params m.profile) raw normalized
    (LayoutConst.canvas_margin.get m.profile) canvas hraw hnormal).1
  refine ⟨nodes, raw, normalized, canvas, hraw, hnormal, ?_⟩
  intro box hbox hw hh
  obtain ⟨i, source, hsource, hid, hlookup⟩ :=
    sceneBoxOrigin_positive_lookup m normalized box (horigins box hbox) hw hh
  have hindex := (List.getElem?_eq_some_iff.mp hlookup).1
  refine ⟨i, source, ?_, hsource, hid, hlookup, ?_⟩
  · simpa only [hlength] using hindex
  · intro route hscope
    constructor
    · intro heq
      apply hscope
      simp only [hid, heq]
      simp [LayoutDump.routeScope]
    · intro heq
      apply hscope
      simp only [hid, heq]
      simp [LayoutDump.routeScope]

private theorem parent_index_from_owner (parent : Int) (idx : Nat)
    (hlb : -1 ≤ parent) (howner : (parent + 1).toNat = idx + 1) :
    parent = (idx : Int) := by
  omega

theorem generated_indexed_bone_slot_origin
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (owner : Nat) (b : Bone)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) owner b) :
    let r := effectivePlacedInput ns length (generatedRib ns (cause, k))
    (owner = 0 ∧ b.t0 = 0 ∧ b.t1 = r.length) ∨
      ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat),
        (e, idx) ∈ r.entries.zipIdx ∧
        r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
        owner = idx + 1 ∧
        b.t1 = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) ∧
        ((e.depth % 2 = 0 ∧
          b.t0 = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) ∨
          (e.depth % 2 ≠ 0 ∧ ∃ (parent : Entry) (parentIdx : Nat) (parentPos : Nat × Nat),
            (parent, parentIdx) ∈ r.entries.zipIdx ∧
            r.order.zipIdx.find? (fun v => v.1 == parentIdx) = some parentPos ∧
            e.parent = (parentIdx : Int) ∧ parent.depth % 2 = 0 ∧
            b.t0 = Int.fdiv (r.length * (parentPos.2 + 1 : Nat))
              (r.entries.length + 1 : Nat))) := by
  dsimp only
  rcases indexedBoneGenealogy_temporal_origin hgene with hroot |
    ⟨e, idx, pos, par, he, hpos, howner, hpar, ht1, hteven, htodd⟩
  · exact Or.inl hroot
  · refine Or.inr ⟨e, idx, pos, he, hpos, howner, ht1, ?_⟩
    by_cases hd : e.depth % 2 = 0
    · exact Or.inl ⟨hd, hteven hd⟩
    · apply Or.inr
      refine ⟨hd, ?_⟩
      rcases indexedBoneGenealogy_temporal_origin hpar with hroot |
        ⟨parent, parentIdx, parentPos, grandparent, hp, hppos, hparentOwner,
          _, _, hparentEven, _⟩
      · have hlb := generated_entry_parent_lower_bound ns cause k e idx he
        have hepar : e.parent = -1 := by omega
        have hdepth := generated_root_depth ns cause k hlink hcause e idx he hepar
        omega
      · have hlb := generated_entry_parent_lower_bound ns cause k e idx he
        have hepar : e.parent = (parentIdx : Int) := by omega
        have hdepth := generated_parent_child_depth ns cause k hlink hcause
          parent e parentIdx idx hp he hepar
        have hmod := Nat.mod_lt parent.depth (by decide : 0 < 2)
        have hparentDepth : parent.depth % 2 = 0 := by omega
        exact ⟨parent, parentIdx, parentPos, hp, hppos, hepar, hparentDepth,
          (htodd hd).trans (hparentEven hparentDepth)⟩

private theorem generated_found_position_lt (ns : List Tree.Node) (cause k idx : Nat)
    (pos : Nat × Nat)
    (hpos : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idx) = some pos) :
    pos.2 < (generatedRib ns (cause, k)).entries.length := by
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have he : (generatedRib ns (cause, k)).entries =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).1 :=
    congrArg Prod.fst hfields
  have ho : (generatedRib ns (cause, k)).order =
      (flatten ns (upper k) 64 (children ns cause) (-1) 2 [] []).2 :=
    congrArg Prod.snd hfields
  rw [ho] at hpos
  rw [he]
  exact generated_rib_found_ordinal_lt ns cause k idx pos hpos

theorem generated_entry_parent_slot_gaps
    (ns : List Tree.Node) (p : Params) (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone)
    (he : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpos : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idx) = some pos)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (e.parent + 1).toNat par) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    (e.depth % 2 ≠ 0 → par.t0 + r.heights ≤ t) ∧
    (e.depth % 2 = 0 → par.t0 + r.heights ≤ t ∧ t + r.heights ≤ par.t1) := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  let slot := fun position : Nat =>
    Int.fdiv (r.length * (position + 1 : Nat)) (r.entries.length + 1 : Nat)
  have hne : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (e, idx) ∈ source.entries.zipIdx at he
      rw [hentries] at he
      simp at he
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hne
  have hheight : 0 ≤ source.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hgap : ∀ a b : Nat, a < b → slot a + r.heights ≤ slot b := by
    intro a b hab
    exact ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
      (a + 1 : Nat) (b + 1 : Nat) (by omega) hheight hbudget (by omega)
  have hbounds := ordinal_slot_inside r.length (r.entries.length + 1 : Nat) r.heights
    (pos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
    (by have hb := generated_found_position_lt ns cause k idx pos hpos; change pos.2 < r.entries.length at hb; omega)
  have horigin := generated_indexed_bone_slot_origin ns p cause k
    (measuredSideLength p ribs) hlink hcause (e.parent + 1).toNat par hgene
  rcases horigin with ⟨howner, ht0, ht1⟩ |
    ⟨parent, parentIdx, parentPos, hp, hppos, howner, ht1, hstart⟩
  · have hlb := generated_entry_parent_lower_bound ns cause k e idx he
    have hepar : e.parent = -1 := by omega
    have hdepth := generated_root_depth ns cause k hlink hcause e idx he hepar
    dsimp only
    refine ⟨?_, ?_⟩
    · intro hodd
      omega
    · intro _
      exact ⟨by simpa only [ht0, Int.zero_add] using hbounds.1,
        by simpa only [ht1] using hbounds.2⟩
  · have hlb := generated_entry_parent_lower_bound ns cause k e idx he
    have hepar : e.parent = (parentIdx : Int) :=
      parent_index_from_owner e.parent parentIdx hlb howner
    have hdepth := generated_parent_child_depth ns cause k hlink hcause
      parent e parentIdx idx hp he hepar
    have hmod := Nat.mod_lt parent.depth (by decide : 0 < 2)
    have horder := generated_parent_child_order ns cause k parent e parentIdx idx
      hp he hepar parentPos pos hppos hpos
    rcases hstart with ⟨hparentEven, ht0⟩ |
      ⟨hparentOdd, anchor, anchorIdx, anchorPos, ha, hapos, hparentPar, hanchorEven, ht0⟩
    · have hodd : e.depth % 2 ≠ 0 := by omega
      have hslot := hgap parentPos.2 pos.2 (horder.1 hparentEven)
      dsimp only
      refine ⟨?_, ?_⟩
      · intro _
        simpa only [ht0] using hslot
      · intro heven
        exact False.elim (hodd heven)
    · have heven : e.depth % 2 = 0 := by omega
      have hchain := IndexedAncestor.tail
        (IndexedAncestor.edge anchorIdx parentIdx parent
          (List.mem_zipIdx_iff_getElem?.mp hp) hparentPar)
        e (List.mem_zipIdx_iff_getElem?.mp he) hepar
      have hbefore := (generated_ancestor_order ns cause k anchor e anchorIdx idx
        ha he hchain anchorPos pos hapos hpos).1 hanchorEven
      have hlo := hgap anchorPos.2 pos.2 hbefore
      have hhi := hgap pos.2 parentPos.2 (horder.2 hparentOdd)
      dsimp only
      refine ⟨?_, ?_⟩
      · intro hodd
        exact False.elim (hodd heven)
      · intro _
        exact ⟨by simpa only [ht0] using hlo, by simpa only [ht1] using hhi⟩

private theorem positive_gap_lt (a b height : Int) (hh : 0 < height)
    (hgap : a + height ≤ b) : a < b := by
  omega

theorem generated_piece_strict_temporal_geometry
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0)
    (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ placed.pieces) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
      rect = ⟨-run p r.length - Int.fdiv n.width 2,
        if r.upper then ordinate spine r.upper r.length - n.height
        else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
      points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
    ∃ (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node),
      (e, idx) ∈ r.entries.zipIdx ∧
      r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
      ns[e.node]? = some n ∧ i = e.node ∧
      IndexedBoneGenealogy ns p r (e.parent + 1).toNat par ∧ par.drawn ≤ par.count ∧
      let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
      let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
      rect = ⟨b.x1 - n.width, ordinate spine r.upper b.t1 - Int.fdiv n.height 2,
        n.width, n.height⟩ ∧
      points = [⟨b.x0, ordinate spine r.upper b.t0⟩,
        ⟨b.x1, ordinate spine r.upper b.t1⟩] ∧
      (e.depth % 2 ≠ 0 → b.t0 < b.t1) ∧
      (e.depth % 2 = 0 → par.t0 < b.t0 ∧ b.t0 = b.t1 ∧ b.t1 < par.t1) := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have horigin := place_piece_accounted_geometry ns p spine r placed hplace i rect points hmem
  rcases horigin with hroot |
    ⟨e, idx, pos, par, n, done, rest, he, hpos, hn, hi, hgene, hprefix, hdrawn,
      hrect, hpoints⟩
  · exact Or.inl hroot
  · have hcount := generated_parent_drawn_le_count ns p cause k (measuredSideLength p ribs)
      hlink hcause (e.parent + 1).toNat par hgene done ((e, idx) :: rest) hprefix hdrawn
    have hdims := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
    have hmeasured := measured_entry_height_bound ns source.entries e
      (List.fst_mem_of_mem_zipIdx he) n hn
    have hheight : n.height ≤ r.heights := by
      change n.height ≤ (generatedRib ns (cause, k)).heights
      rw [(generated_rib_fields ns cause k).2.2.2]
      exact hmeasured
    have hpositive : 0 < r.heights :=
      Int.lt_of_lt_of_le (Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hdims.2) hheight
    have hgap := generated_entry_parent_slot_gaps ns p ribs hg cause k hsource hlink hcause
      e idx pos par he hpos hgene
    refine Or.inr ⟨e, idx, pos, par, n, he, hpos, hn, hi, hgene, hcount,
      hrect, hpoints, ?_, ?_⟩
    · intro hodd
      have hs := positive_gap_lt par.t0
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        r.heights hpositive (hgap.1 hodd)
      have ht := depthBone_odd_endpoints p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3) hodd
      calc
        _ = par.t0 := ht.1
        _ < Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := hs
        _ = _ := ht.2.1.symm
    · intro heven
      have hs := hgap.2 heven
      have hlo := positive_gap_lt par.t0
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        r.heights hpositive hs.1
      have hhi := positive_gap_lt
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        par.t1 r.heights hpositive hs.2
      have ht := depthBone_even_endpoints p par e.depth
        (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
        (children ns e.node).length (run p r.heights + 3) heven
      refine ⟨?_, ht.1.trans ht.2.1.symm, ?_⟩
      · calc
          par.t0 < Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := hlo
          _ = _ := ht.1.symm
      · calc
          _ = Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat) := ht.2.1
          _ < par.t1 := hhi

theorem successful_scene_foreign_native_indices (m : Model) (s : Scene)
    (hwf : WellFormed m) (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    ∃ (input : Elegant.Kinds.Ishikawa.Input) (raw normalized : Tree.Layout) (canvas : Size),
      Elegant.Kinds.Ishikawa.decode m = .ok input ∧
      layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
      Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
      ∀ route ∈ s.routes, ∀ box ∈ s.boxes,
        0 < box.rect.w → 0 < box.rect.h → box.id ∉ s.layoutDump.routeScope route →
        ∃ (targetIndex boxIndex : Nat) (target source : ModelBox),
          targetIndex < input.nodes.length ∧ boxIndex < input.nodes.length ∧
          m.boxes[targetIndex]? = some target ∧ target.id = route.toId ∧
          normalized.routes[targetIndex]? = some route.points ∧
          m.boxes[boxIndex]? = some source ∧ box.id = source.id ∧
          normalized.boxes[boxIndex]? = some box.rect ∧
          boxIndex ≠ targetIndex ∧ source.id ≠ route.fromId ∧ source.id ≠ route.toId := by
  obtain ⟨input, raw, normalized, canvas, hdecode, hraw, hnormal, hboxes, hroutes⟩ :=
    Elegant.Kinds.IshikawaSeparation.successful_scene_native_sources m s hwf hs
  have hlength := (Elegant.Kinds.IshikawaValid.successful_normalized_lengths input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) raw normalized
    (LayoutConst.canvas_margin.get m.profile) canvas hraw hnormal).1
  refine ⟨input, raw, normalized, canvas, hdecode, hraw, hnormal, ?_⟩
  intro route hroute box hbox hw hh hscope
  obtain ⟨targetIndex, target, htargetBound, htarget, htargetId, hroutePoints⟩ :=
    hroutes route hroute
  obtain ⟨boxIndex, source, hsource, hid, hrect⟩ :=
    sceneBoxOrigin_positive_lookup m normalized box (hboxes box hbox) hw hh
  have hboxBound : boxIndex < input.nodes.length := by
    have hb := (List.getElem?_eq_some_iff.mp hrect).choose
    simpa only [hlength] using hb
  have hfrom : source.id ≠ route.fromId := by
    intro heq
    apply hscope
    simp only [hid, heq]
    simp [LayoutDump.routeScope]
  have hto : source.id ≠ route.toId := by
    intro heq
    apply hscope
    simp only [hid, heq]
    simp [LayoutDump.routeScope]
  refine ⟨targetIndex, boxIndex, target, source, htargetBound, hboxBound,
    htarget, htargetId, hroutePoints, hsource, hid, hrect, ?_, hfrom, hto⟩
  intro heq
  subst boxIndex
  have hsame : source = target := Option.some.inj (hsource.symm.trans htarget)
  exact hto ((congrArg ModelBox.id hsame).trans htargetId)

theorem processedOddDraws_prefix (before after : List (Entry × Nat)) (owner : Nat)
    (hp : before <+: after) :
    processedOddDraws before owner ≤ processedOddDraws after owner := by
  rcases hp with ⟨rest, rfl⟩
  unfold processedOddDraws
  rw [List.filter_append, List.length_append, Int.natCast_add]
  omega

private theorem attachment_floor_gap (a b denominator margin : Int)
    (hden : 0 < denominator) (hgap : a + denominator * margin ≤ b) :
    Int.fdiv a denominator + margin ≤ Int.fdiv b denominator := by
  have hq := Int.mul_fdiv_add_fmod a denominator
  have hr := Int.fmod_nonneg_of_pos a hden
  apply Chart.le_fdiv_of_mul_le hden
  rw [Int.mul_add]
  omega

private theorem attachment_counter_gap (left right count margin firstDraw secondDraw : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hrank : firstDraw + 1 ≤ secondDraw) :
    left + Int.fdiv ((right - left) * (count - firstDraw)) (count + 1) + margin ≤
      left + Int.fdiv ((right - left) * (count - secondDraw)) (count + 1) := by
  have hnonnegative : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left
    (show (1 : Int) ≤ secondDraw - firstDraw by omega) hnonnegative
  simp only [Int.mul_one] at hmul
  have halgebra :
      (right - left) * (count - secondDraw) -
          (right - left) * (count - firstDraw) =
        (left - right) * (secondDraw - firstDraw) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hgap := attachment_floor_gap
    ((right - left) * (count - firstDraw))
    ((right - left) * (count - secondDraw)) (count + 1) margin hden (by omega)
  omega

private theorem successful_slope_parameters (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hne : ns ≠ []) (hrun : layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons head rest =>
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    split at hrun
    · simp only [bind, Except.bind] at hrun
      cases hrun
    · split at hrun
      · simp only [bind, Except.bind] at hrun
        cases hrun
      · rename_i hparameters
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hparameters
        omega

private theorem nonroot_parent_index (parent : Int) (hlb : -1 ≤ parent)
    (hne : parent ≠ -1) : ∃ i : Nat, parent = (i : Int) := by
  exact ⟨parent.toNat, by omega⟩

private theorem parent_depth_even (parent child : Nat) (hd : child = parent + 1)
    (hodd : child % 2 ≠ 0) : parent % 2 = 0 := by
  have hm := Nat.mod_lt parent (by decide : 0 < 2)
  omega

private theorem even_native_reservation (p : Params) (par : Bone) (depth : Nat)
    (t : Int) (count : Nat) (margin : Int) (hd : depth % 2 = 0) :
    let b := depthBone p par depth t count margin
    0 < b.count + 1 ∧ (b.count + 1) * margin ≤ b.x0 - b.x1 := by
  let b := depthBone p par depth t count margin
  have hc : b.count = (count : Int) := by
    unfold b depthBone
    split <;> rfl
  have he := (depthBone_even_endpoints p par depth t count margin hd).2.2
  have hr : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
    Int.le_max_right _ _
  constructor
  · rw [hc]
    omega
  · rw [hc]
    change ((count : Int) + 1) * margin ≤ b.x0 - b.x1
    change b.x1 = b.x0 - boneLength p count margin at he
    omega

theorem place_generated_odd_sibling_attachment_gap
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw) (cause k : Nat) (hcause : cause ∈ children ns 0)
    (length : Bool → Int) (spine : Int) (placed : Rib)
    (hplace : place ns p spine (effectivePlacedInput ns length (generatedRib ns (cause, k))) =
      .ok placed)
    (first second : Entry) (firstIdx secondIdx : Nat)
    (hfirst : (first, firstIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hsecond : (second, secondIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : first.depth % 2 ≠ 0) (hparent : first.parent = second.parent)
    (hindex : firstIdx < secondIdx) :
    let r := effectivePlacedInput ns length (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (firstBorn secondBorn : Bone),
      frames.length = r.entries.length + 1 ∧
      frames[firstIdx + 1]? = some firstBorn ∧ frames[secondIdx + 1]? = some secondBorn ∧
      firstBorn.x0 + (run p r.heights + 3) ≤ secondBorn.x0 ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv n.width 2,
            if r.upper then ordinate spine r.upper r.length - n.height
            else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (n : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some n ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
            n.width, n.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns length source
  let margin := run p r.heights + 3
  let owner := (first.parent + 1).toNat
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  obtain ⟨frames, hframesLength, _, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨firstDone, firstRest, hfirstPrefix, _⟩ := List.eq_append_cons_of_mem hfirst
  obtain ⟨secondDone, secondRest, hsecondPrefix, _⟩ := List.eq_append_cons_of_mem hsecond
  change r.entries.zipIdx = firstDone ++ (first, firstIdx) :: firstRest at hfirstPrefix
  change r.entries.zipIdx = secondDone ++ (second, secondIdx) :: secondRest at hsecondPrefix
  obtain ⟨firstPos, parentFrame, firstBorn, hfirstPos, hparentFrame, hfirstBorn, hfirstEquation⟩ :=
    hrecords firstDone first firstIdx firstRest hfirstPrefix
  obtain ⟨secondPos, secondParent, secondBorn, hsecondPos, hsecondParent, hsecondBorn, hsecondEquation⟩ :=
    hrecords secondDone second secondIdx secondRest hsecondPrefix
  change frames[owner]? = some parentFrame at hparentFrame
  have howner : (second.parent + 1).toNat = owner := by rw [← hparent]
  rw [howner] at hsecondParent hsecondEquation
  have hsameParent : secondParent = parentFrame :=
    Option.some.inj (hsecondParent.symm.trans hparentFrame)
  subst secondParent
  have hfirstIndex : firstIdx = firstDone.length := by
    simpa only [Nat.zero_add] using
      zipIdx_processed_index r.entries 0 firstDone firstRest first firstIdx hfirstPrefix
  have hsecondIndex : secondIdx = secondDone.length := by
    simpa only [Nat.zero_add] using
      zipIdx_processed_index r.entries 0 secondDone secondRest second secondIdx hsecondPrefix
  have hprefix1 : firstDone ++ [(first, firstIdx)] <+: r.entries.zipIdx :=
    ⟨firstRest, by simpa only [List.append_assoc, List.singleton_append] using hfirstPrefix.symm⟩
  have hprefix2 : secondDone <+: r.entries.zipIdx := ⟨_, hsecondPrefix.symm⟩
  have hprocessed : firstDone ++ [(first, firstIdx)] <+: secondDone :=
    List.prefix_of_prefix_length_le hprefix1 hprefix2 (by
      simp only [List.length_append, List.length_singleton]
      omega)
  have hmatches : ((first.depth % 2 != 0) && ((first.parent + 1).toNat == owner)) = true := by
    have hm := Nat.mod_lt first.depth (by decide : 0 < 2)
    simp [owner]
    omega
  have hrankStep := processedOddDraws_append_one firstDone first firstIdx owner
  rw [hmatches] at hrankStep
  have hrank : processedOddDraws firstDone owner + 1 ≤ processedOddDraws secondDone owner := by
    have hm := processedOddDraws_prefix _ _ owner hprocessed
    simpa only [hrankStep, ↓reduceIte] using hm
  have hrootFalse : first.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause first firstIdx hfirst heq
    exact hodd (by omega)
  obtain ⟨parentIdx, hparentIdx⟩ :=
    nonroot_parent_index first.parent
      (generated_entry_parent_lower_bound ns cause k first firstIdx hfirst) hrootFalse
  have hparentOwner : owner = parentIdx + 1 := by
    dsimp only [owner]
    rw [hparentIdx]
    omega
  have hparentBound : parentIdx < r.entries.length := by
    have hb := (List.getElem?_eq_some_iff.mp hparentFrame).choose
    change owner < frames.length at hb
    rw [hparentOwner, hframesLength] at hb
    omega
  let parentEntry := r.entries[parentIdx]'hparentBound
  have hparentLookup : r.entries[parentIdx]? = some parentEntry :=
    List.getElem?_eq_getElem hparentBound
  have hparentMem : (parentEntry, parentIdx) ∈ r.entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hparentLookup
  have hdepthFirst := generated_parent_child_depth ns cause k hlink hcause
    parentEntry first parentIdx firstIdx hparentMem hfirst hparentIdx
  have hdepthSecond := generated_parent_child_depth ns cause k hlink hcause
    parentEntry second parentIdx secondIdx hparentMem hsecond (hparent.symm.trans hparentIdx)
  have hparentEven := parent_depth_even parentEntry.depth first.depth hdepthFirst hodd
  have hsecondOdd : second.depth % 2 ≠ 0 := by
    have heq : second.depth = first.depth := hdepthSecond.trans hdepthFirst.symm
    simpa only [heq] using hodd
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ := List.eq_append_cons_of_mem hparentMem
  obtain ⟨parentPos, grandparent, parentBorn, hparentPos, hgrandparent,
    hparentBorn, hparentEquation⟩ :=
      hrecords parentDone parentEntry parentIdx parentRest hparentPrefix
  rw [hparentOwner] at hparentFrame
  have hsameBirth : parentBorn = parentFrame :=
    Option.some.inj (hparentBorn.symm.trans hparentFrame)
  have hparentFrameEquation := hsameBirth.symm.trans hparentEquation
  have hreserve := even_native_reservation p
    { grandparent with drawn := processedOddDraws parentDone (parentEntry.parent + 1).toNat }
    parentEntry.depth
    (Int.fdiv (r.length * (parentPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
    (children ns parentEntry.node).length margin hparentEven
  rw [← hparentFrameEquation] at hreserve
  have hne : ns ≠ [] := by
    intro hn
    simp [hn, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hrunHeight : 0 ≤ run p r.heights :=
    Int.fdiv_nonneg (Int.mul_nonneg hheight hparameters.1)
      (Int.le_trans (by decide : (0 : Int) ≤ 1) hparameters.2)
  have hmargin : 0 ≤ margin := Int.add_nonneg hrunHeight (by decide : (0 : Int) ≤ 3)
  have hfirstStart : firstBorn.x0 =
      parentFrame.x0 + Int.fdiv
        ((parentFrame.x1 - parentFrame.x0) *
          (parentFrame.count - processedOddDraws firstDone owner)) (parentFrame.count + 1) := by
    rw [hfirstEquation]
    exact (depthBone_odd_endpoints p
      { parentFrame with drawn := processedOddDraws firstDone owner } first.depth
      (Int.fdiv (r.length * (firstPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns first.node).length margin hodd).2.2.1
  have hsecondStart : secondBorn.x0 =
      parentFrame.x0 + Int.fdiv
        ((parentFrame.x1 - parentFrame.x0) *
          (parentFrame.count - processedOddDraws secondDone owner)) (parentFrame.count + 1) := by
    rw [hsecondEquation]
    exact (depthBone_odd_endpoints p
      { parentFrame with drawn := processedOddDraws secondDone owner } second.depth
      (Int.fdiv (r.length * (secondPos.2 + 1 : Nat)) (r.entries.length + 1 : Nat))
      (children ns second.node).length margin hsecondOdd).2.2.1
  refine ⟨frames, firstBorn, secondBorn, hframesLength, hfirstBorn, hsecondBorn, ?_, hpieces⟩
  rw [hfirstStart, hsecondStart]
  exact attachment_counter_gap parentFrame.x0 parentFrame.x1 parentFrame.count margin
    (processedOddDraws firstDone owner) (processedOddDraws secondDone owner)
    hreserve.1 hmargin hreserve.2 hrank

private theorem child_depth_even (parent child : Nat) (hd : child = parent + 1)
    (hodd : parent % 2 ≠ 0) : child % 2 = 0 := by
  have hm := Nat.mod_lt parent (by decide : 0 < 2)
  omega

private theorem boneLength_margin (p : Params) (count : Nat) (margin : Int)
    (hmargin : 0 ≤ margin) : margin ≤ boneLength p count margin := by
  have hcount : (1 : Int) ≤ (count : Int) + 1 := by omega
  have hmul := Int.mul_le_mul_of_nonneg_right hcount hmargin
  have hreserve : ((count : Int) + 1) * margin ≤ boneLength p count margin :=
    Int.le_max_right _ _
  exact Int.le_trans (by simpa only [Int.one_mul] using hmul) hreserve

theorem place_generated_even_child_interpolation_margin
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw) (cause k : Nat) (hcause : cause ∈ children ns 0)
    (length : Bool → Int) (spine : Int) (placed : Rib)
    (hplace : place ns p spine (effectivePlacedInput ns length (generatedRib ns (cause, k))) =
      .ok placed)
    (parent child : Entry) (parentIdx childIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : parent.depth % 2 ≠ 0) (hpar : child.parent = (parentIdx : Int)) :
    let r := effectivePlacedInput ns length (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (parentBorn childBorn : Bone),
      frames.length = r.entries.length + 1 ∧
      frames[parentIdx + 1]? = some parentBorn ∧ frames[childIdx + 1]? = some childBorn ∧
      childBorn.x1 + (run p r.heights + 3) ≤
        parentBorn.x0 + Int.fdiv
          ((parentBorn.x1 - parentBorn.x0) * (childBorn.t1 - parentBorn.t0))
          (parentBorn.t1 - parentBorn.t0) ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv n.width 2,
            if r.upper then ordinate spine r.upper r.length - n.height
            else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (n : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some n ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
            n.width, n.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns length source
  let margin := run p r.heights + 3
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hdepth := generated_parent_child_depth ns cause k hlink hcause
    parent child parentIdx childIdx hparent hchild hpar
  have heven := child_depth_even parent.depth child.depth hdepth hodd
  obtain ⟨frames, hlength, _, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨done, rest, hprefix, _⟩ := List.eq_append_cons_of_mem hchild
  change r.entries.zipIdx = done ++ (child, childIdx) :: rest at hprefix
  obtain ⟨pos, parentBorn, childBorn, hpos, hparentBorn, hchildBorn, hborn⟩ :=
    hrecords done child childIdx rest hprefix
  have howner : (child.parent + 1).toNat = parentIdx + 1 := by rw [hpar]; omega
  rw [howner] at hparentBorn
  have hne : ns ≠ [] := by
    intro hn
    simp [hn, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hrunHeight : 0 ≤ run p r.heights :=
    Int.fdiv_nonneg (Int.mul_nonneg hheight hparameters.1)
      (Int.le_trans (by decide : (0 : Int) ≤ 1) hparameters.2)
  have hmargin : 0 ≤ margin := Int.add_nonneg hrunHeight (by decide : (0 : Int) ≤ 3)
  have hreserve := boneLength_margin p (children ns child.node).length margin hmargin
  have hendpoint :
      childBorn.x1 =
        parentBorn.x0 + Int.fdiv
          ((parentBorn.x1 - parentBorn.x0) * (childBorn.t1 - parentBorn.t0))
          (parentBorn.t1 - parentBorn.t0) -
            boneLength p (children ns child.node).length margin := by
    rw [hborn]
    simp [depthBone, heven, margin]
  refine ⟨frames, parentBorn, childBorn, hlength, hparentBorn, hchildBorn, ?_, hpieces⟩
  rw [hendpoint]
  have hbound := Int.add_le_add_left hreserve
    (parentBorn.x0 + Int.fdiv
      ((parentBorn.x1 - parentBorn.x0) * (childBorn.t1 - parentBorn.t0))
      (parentBorn.t1 - parentBorn.t0) -
        boneLength p (children ns child.node).length margin)
  simpa only [Int.sub_add_cancel] using hbound

private theorem run_scaled_cross_bound (p : Params) (height span : Int)
    (hh : 0 ≤ height) (ht : 0 ≤ span) (hsin : 0 < p.sin) :
    height * run p span ≤ span * (run p height + 1) := by
  have hq := Int.mul_fdiv_add_fmod (span * p.cos) p.sin
  have hr := Int.fmod_nonneg_of_pos (span * p.cos) hsin
  have hlo : p.sin * run p span ≤ span * p.cos := by
    dsimp only [run]
    omega
  have hhi : height * p.cos ≤ p.sin * (run p height + 1) := by
    have h := Int.le_of_lt (Int.lt_fdiv_add_one_mul_self (height * p.cos) hsin)
    simpa only [run, Int.mul_comm] using h
  have hfirst := Int.mul_le_mul_of_nonneg_right hlo hh
  have hsecond := Int.mul_le_mul_of_nonneg_right hhi ht
  apply Int.le_of_mul_le_mul_left (a := p.sin) _ hsin
  calc
    p.sin * (height * run p span) = (p.sin * run p span) * height := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (span * p.cos) * height := hfirst
    _ = (height * p.cos) * span := by
      simp only [Int.mul_comm, Int.mul_left_comm]
    _ ≤ (p.sin * (run p height + 1)) * span := hsecond
    _ = p.sin * (span * (run p height + 1)) := by
      simp only [Int.mul_comm, Int.mul_left_comm]

private theorem interpolated_box_diagonal_miss
    (x0 x1 t0 t1 t width height reservation spine : Int) (up : Bool)
    (ht : t0 < t1) (hx : x1 ≤ x0) (hw : 0 ≤ width) (hh : 0 ≤ height)
    (hcoverage : (x0 - x1) * height ≤ (t1 - t0) * reservation) :
    ¬ Polyline.hitsRect
      [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
      ⟨x0 + Int.fdiv ((x1 - x0) * (t - t0)) (t1 - t0) - reservation - width,
        ordinate spine up t - Int.fdiv height 2, width, height⟩ := by
  let span := t1 - t0
  let fall := x0 - x1
  let q := Int.fdiv ((x1 - x0) * (t - t0)) span
  have hspan : 0 < span := by dsimp only [span]; omega
  have hfall : 0 ≤ fall := by dsimp only [fall]; omega
  have hnormalX : x1 - x0 = -fall := by dsimp only [fall]; omega
  have hfloor : span * q ≤ -(fall * t) + fall * t0 := by
    have hq := Int.mul_fdiv_add_fmod ((x1 - x0) * (t - t0)) span
    have hr := Int.fmod_nonneg_of_pos ((x1 - x0) * (t - t0)) hspan
    have hraw : span * q ≤ (x1 - x0) * (t - t0) := by
      dsimp only [q]
      omega
    rw [hnormalX] at hraw
    simp only [Int.mul_sub, Int.neg_mul] at hraw
    omega
  have hhalf : 0 ≤ Int.fdiv height 2 ∧ Int.fdiv height 2 ≤ height := by
    rw [Tree.fdiv2]
    omega
  have hwidthProduct := Int.mul_nonneg (Int.le_of_lt hspan) hw
  have hhalfProduct := Int.mul_nonneg hfall hhalf.1
  have hremainingProduct := Int.mul_nonneg hfall
    (show 0 ≤ height - Int.fdiv height 2 by omega)
  simp only [Int.mul_sub] at hremainingProduct
  change fall * height ≤ span * reservation at hcoverage
  change ¬ Polyline.hitsRect
    [⟨x0, ordinate spine up t0⟩, ⟨x1, ordinate spine up t1⟩]
    ⟨x0 + q - reservation - width, ordinate spine up t - Int.fdiv height 2,
      width, height⟩
  have hneq : (⟨x0, ordinate spine up t0⟩ : Point) ≠
      ⟨x1, ordinate spine up t1⟩ := by
    intro heq
    have hy := congrArg Point.y heq
    cases up <;> simp only [ordinate, Bool.false_eq_true, ↓reduceIte] at hy <;> omega
  intro hhit
  apply hhit.2.2
  constructor
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    refine ⟨hneq, ?_⟩
    cases up with
    | false =>
      apply Or.inl
      have hnormalY : (spine + t0) - (spine + t1) = -span := by
        dsimp only [span]
        omega
      simp only [Polyline.minCorner, Int.le_min]
      constructor <;> constructor
      all_goals
        simp only [ordinate, Bool.false_eq_true, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
    | true =>
      apply Or.inr
      have hnormalY : (spine - t0) - (spine - t1) = span := by
        dsimp only [span]
        omega
      simp only [Polyline.maxCorner, Int.max_le]
      constructor <;> constructor
      all_goals
        simp only [ordinate, ↓reduceIte, Polyline.dot]
        rw [hnormalY, hnormalX]
        simp only [Int.mul_add, Int.mul_sub, Int.neg_mul]
        omega
  · trivial

theorem place_generated_parent_diagonal_misses_even_child
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (parent child : Entry) (parentIdx childIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hchild : (child, childIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : parent.depth % 2 ≠ 0) (hpar : child.parent = (parentIdx : Int)) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (parentBorn childBorn : Bone) (n : Tree.Node),
      frames.length = r.entries.length + 1 ∧
      frames[parentIdx + 1]? = some parentBorn ∧ frames[childIdx + 1]? = some childBorn ∧
      ns[child.node]? = some n ∧
      ¬ Polyline.hitsRect
        [⟨parentBorn.x0, ordinate spine r.upper parentBorn.t0⟩,
          ⟨parentBorn.x1, ordinate spine r.upper parentBorn.t1⟩]
        ⟨childBorn.x1 - n.width, ordinate spine r.upper childBorn.t1 - Int.fdiv n.height 2,
          n.width, n.height⟩ ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ causeNode : Tree.Node, ns[r.cause]? = some causeNode ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv causeNode.width 2,
            if r.upper then ordinate spine r.upper r.length - causeNode.height
            else ordinate spine r.upper r.length, causeNode.width, causeNode.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (node : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some node ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - node.width, ordinate spine r.upper born.t1 - Int.fdiv node.height 2,
            node.width, node.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  let margin := run p r.heights + 3
  let reserve := boneLength p (children ns child.node).length margin
  let slot := fun position : Nat =>
    Int.fdiv (r.length * (position + 1 : Nat)) (r.entries.length + 1 : Nat)
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hdepth := generated_parent_child_depth ns cause k hlink hcause
    parent child parentIdx childIdx hparent hchild hpar
  have heven := child_depth_even parent.depth child.depth hdepth hodd
  have hchildNative := generated_parent_child_membership ns cause k
    parent child parentIdx childIdx hparent hchild hpar
  have hnodeBound : child.node < ns.length :=
    List.mem_range.mp (List.mem_filter.mp hchildNative).1
  let n := ns[child.node]'hnodeBound
  have hn : ns[child.node]? = some n := List.getElem?_eq_getElem hnodeBound
  have hdims := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
  have hmeasured := measured_entry_height_bound ns source.entries child
    (List.fst_mem_of_mem_zipIdx hchild) n hn
  have hheight : n.height ≤ r.heights := by
    change n.height ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact hmeasured
  have hpositive : 0 < r.heights :=
    Int.lt_of_lt_of_le (Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hdims.2) hheight
  have hneEntries : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (child, childIdx) ∈ source.entries.zipIdx at hchild
      rw [hentries] at hchild
      simp at hchild
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hneEntries
  have hgap : ∀ a b : Nat, a < b → slot a + r.heights ≤ slot b := by
    intro a b hab
    exact ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
      (a + 1 : Nat) (b + 1 : Nat) (by omega) (Int.le_of_lt hpositive) hbudget (by omega)
  obtain ⟨frames, hframesLength, _, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨parentDone, parentRest, hparentPrefix, _⟩ := List.eq_append_cons_of_mem hparent
  obtain ⟨childDone, childRest, hchildPrefix, _⟩ := List.eq_append_cons_of_mem hchild
  obtain ⟨parentPos, parentFrame, parentBorn, hparentPos, hparentFrame, hparentBorn,
    hparentEquation⟩ := hrecords parentDone parent parentIdx parentRest hparentPrefix
  obtain ⟨childPos, childParent, childBorn, hchildPos, hchildParent, hchildBorn,
    hchildEquation⟩ := hrecords childDone child childIdx childRest hchildPrefix
  have hchildOwner : (child.parent + 1).toNat = parentIdx + 1 := by rw [hpar]; omega
  rw [hchildOwner] at hchildParent
  have hsameParent : childParent = parentBorn :=
    Option.some.inj (hchildParent.symm.trans hparentBorn)
  rw [hsameParent] at hchildEquation
  have hrootFalse : parent.parent ≠ -1 := by
    intro heq
    have hd := generated_root_depth ns cause k hlink hcause parent parentIdx hparent heq
    exact hodd (by omega)
  obtain ⟨grandIdx, hgrandIdx⟩ :=
    nonroot_parent_index parent.parent
      (generated_entry_parent_lower_bound ns cause k parent parentIdx hparent) hrootFalse
  have hgrandOwner : (parent.parent + 1).toNat = grandIdx + 1 := by rw [hgrandIdx]; omega
  rw [hgrandOwner] at hparentFrame
  have hgrandBound : grandIdx < r.entries.length := by
    have hb := (List.getElem?_eq_some_iff.mp hparentFrame).choose
    rw [hframesLength] at hb
    omega
  let grandEntry := r.entries[grandIdx]'hgrandBound
  have hgrandLookup : r.entries[grandIdx]? = some grandEntry :=
    List.getElem?_eq_getElem hgrandBound
  have hgrandMem : (grandEntry, grandIdx) ∈ r.entries.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hgrandLookup
  have hgrandDepth := generated_parent_child_depth ns cause k hlink hcause
    grandEntry parent grandIdx parentIdx hgrandMem hparent hgrandIdx
  have hgrandEven := parent_depth_even grandEntry.depth parent.depth hgrandDepth hodd
  obtain ⟨grandDone, grandRest, hgrandPrefix, _⟩ := List.eq_append_cons_of_mem hgrandMem
  obtain ⟨grandPos, grandParent, grandBorn, hgrandPos, hgrandParent, hgrandBorn,
    hgrandEquation⟩ := hrecords grandDone grandEntry grandIdx grandRest hgrandPrefix
  have hsameGrand : grandBorn = parentFrame :=
    Option.some.inj (hgrandBorn.symm.trans hparentFrame)
  have hparentFrameEquation := hsameGrand.symm.trans hgrandEquation
  have hgrandTime : parentFrame.t0 = slot grandPos.2 := by
    rw [hparentFrameEquation]
    exact (depthBone_even_endpoints p
      { grandParent with drawn := processedOddDraws grandDone (grandEntry.parent + 1).toNat }
      grandEntry.depth (slot grandPos.2) (children ns grandEntry.node).length margin hgrandEven).1
  have hparentT0 : parentBorn.t0 = parentFrame.t0 := by
    rw [hparentEquation]
    exact (depthBone_odd_endpoints p
      { parentFrame with drawn := processedOddDraws parentDone (parent.parent + 1).toNat }
      parent.depth (slot parentPos.2) (children ns parent.node).length margin hodd).1
  have hparentT1 : parentBorn.t1 = slot parentPos.2 := by
    rw [hparentEquation]
    exact (depthBone_odd_endpoints p
      { parentFrame with drawn := processedOddDraws parentDone (parent.parent + 1).toNat }
      parent.depth (slot parentPos.2) (children ns parent.node).length margin hodd).2.1
  have hparentX : parentBorn.x1 =
      parentBorn.x0 - run p (parentBorn.t1 - parentBorn.t0) := by
    rw [hparentT1, hparentT0, hparentEquation]
    exact (depthBone_odd_endpoints p
      { parentFrame with drawn := processedOddDraws parentDone (parent.parent + 1).toNat }
      parent.depth (slot parentPos.2) (children ns parent.node).length margin hodd).2.2.2
  have hbefore := (generated_parent_child_order ns cause k grandEntry parent grandIdx parentIdx
    hgrandMem hparent hgrandIdx grandPos parentPos hgrandPos hparentPos).1 hgrandEven
  have hstrict := positive_gap_lt (slot grandPos.2) (slot parentPos.2)
    r.heights hpositive (hgap grandPos.2 parentPos.2 hbefore)
  have hspan : parentBorn.t0 < parentBorn.t1 := by
    calc
      parentBorn.t0 = slot grandPos.2 := hparentT0.trans hgrandTime
      _ < slot parentPos.2 := hstrict
      _ = parentBorn.t1 := hparentT1.symm
  have hspanPositive := Int.sub_pos_of_lt hspan
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hsin : 0 < p.sin := Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hparameters.2
  have hrunSpan : 0 ≤ run p (parentBorn.t1 - parentBorn.t0) :=
    Int.fdiv_nonneg (Int.mul_nonneg (Int.le_of_lt hspanPositive) hparameters.1)
      (Int.le_of_lt hsin)
  have hrunHeight : 0 ≤ run p r.heights :=
    Int.fdiv_nonneg (Int.mul_nonneg (Int.le_of_lt hpositive) hparameters.1)
      (Int.le_of_lt hsin)
  have hmargin : 0 ≤ margin := Int.add_nonneg hrunHeight (by decide : (0 : Int) ≤ 3)
  have hreserve := boneLength_margin p (children ns child.node).length margin hmargin
  have hmarginOne : run p r.heights + 1 ≤ margin :=
    Int.add_le_add_left (by decide : (1 : Int) ≤ 3) (run p r.heights)
  have hfall : parentBorn.x0 - parentBorn.x1 = run p (parentBorn.t1 - parentBorn.t0) := by
    rw [hparentX, Int.sub_sub_self]
  have hcoverage :
      (parentBorn.x0 - parentBorn.x1) * n.height ≤
        (parentBorn.t1 - parentBorn.t0) * reserve := by
    rw [hfall]
    calc
      run p (parentBorn.t1 - parentBorn.t0) * n.height =
          n.height * run p (parentBorn.t1 - parentBorn.t0) := Int.mul_comm _ _
      _ ≤ r.heights * run p (parentBorn.t1 - parentBorn.t0) :=
        Int.mul_le_mul_of_nonneg_right hheight hrunSpan
      _ ≤ (parentBorn.t1 - parentBorn.t0) * (run p r.heights + 1) :=
        run_scaled_cross_bound p r.heights (parentBorn.t1 - parentBorn.t0)
          (Int.le_of_lt hpositive) (Int.le_of_lt hspanPositive) hsin
      _ ≤ (parentBorn.t1 - parentBorn.t0) * margin :=
        Int.mul_le_mul_of_nonneg_left hmarginOne (Int.le_of_lt hspanPositive)
      _ ≤ (parentBorn.t1 - parentBorn.t0) * reserve :=
        Int.mul_le_mul_of_nonneg_left hreserve (Int.le_of_lt hspanPositive)
  have hchildTime : childBorn.t1 = slot childPos.2 := by
    rw [hchildEquation]
    exact (depthBone_even_endpoints p
      { parentBorn with drawn := processedOddDraws childDone (child.parent + 1).toNat }
      child.depth (slot childPos.2) (children ns child.node).length margin heven).2.1
  have hchildX : childBorn.x1 =
      parentBorn.x0 + Int.fdiv
        ((parentBorn.x1 - parentBorn.x0) * (slot childPos.2 - parentBorn.t0))
        (parentBorn.t1 - parentBorn.t0) - reserve := by
    rw [hchildEquation]
    simp [depthBone, heven, reserve, margin, slot]
  refine ⟨frames, parentBorn, childBorn, n, hframesLength, hparentBorn, hchildBorn,
    hn, ?_, hpieces⟩
  rw [hchildTime, hchildX]
  apply interpolated_box_diagonal_miss
  · exact hspan
  · apply Int.le_of_sub_nonneg
    rw [hfall]
    exact hrunSpan
  · exact Int.le_trans (by decide : (0 : Int) ≤ 1) hdims.1
  · exact Int.le_trans (by decide : (0 : Int) ≤ 1) hdims.2
  · exact hcoverage

theorem generated_current_odd_prefix_draw_bound
    (ns : List Tree.Node) (cause k : Nat) (hlink : Tree.link ns = true)
    (hcause : cause ∈ children ns 0)
    (done : List (Entry × Nat)) (e : Entry) (idx : Nat) (rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ (e, idx) :: rest)
    (parent : Entry) (parentIdx : Nat)
    (hparent : (parent, parentIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpar : e.parent = (parentIdx : Int)) (hodd : e.depth % 2 ≠ 0) :
    processedOddDraws done (parentIdx + 1) + 1 ≤ (children ns parent.node).length := by
  have hprefix' : (generatedRib ns (cause, k)).entries.zipIdx =
      (done ++ [(e, idx)]) ++ rest := by
    simpa only [List.append_assoc, List.singleton_append] using hprefix
  have hcount := generated_prefix_odd_child_count_le ns cause k hlink hcause
    (done ++ [(e, idx)]) rest hprefix' (parentIdx + 1) parent.node
    (Or.inr ⟨parent, parentIdx, hparent, rfl, rfl⟩)
  have howner : (e.parent + 1).toNat = parentIdx + 1 := by rw [hpar]; omega
  have hresidue : e.depth % 2 = 1 := by
    have hm := Nat.mod_lt e.depth (by decide : 0 < 2)
    omega
  have hmatches : ((e.depth % 2 != 0) &&
      ((e.parent + 1).toNat == parentIdx + 1)) = true := by
    simp [hresidue, howner]
  have hstep := processedOddDraws_append_one done e idx (parentIdx + 1)
  rw [hmatches] at hstep
  have hcountInt : processedOddDraws (done ++ [(e, idx)]) (parentIdx + 1) ≤
      (children ns parent.node).length := by
    unfold processedOddDraws
    omega
  rw [hstep] at hcountInt
  simpa only [↓reduceIte] using hcountInt

private theorem attachment_start_margin (left right count drawn margin : Int)
    (hden : 0 < count + 1) (hmargin : 0 ≤ margin)
    (hreserve : (count + 1) * margin ≤ left - right)
    (hdrawn : drawn + 1 ≤ count) :
    left + Int.fdiv ((right - left) * (count - drawn)) (count + 1) + margin ≤ left := by
  have hspan : 0 ≤ left - right :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hden) hmargin) hreserve
  have hmul := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ count - drawn by omega) hspan
  simp only [Int.mul_one] at hmul
  have halgebra : (right - left) * (count - drawn) =
      -((left - right) * (count - drawn)) := by
    simp only [Int.sub_mul]
    omega
  have hbound : (right - left) * (count - drawn) ≤ (count + 1) * (-margin) := by
    rw [Int.mul_neg]
    omega
  have hquot := Chart.fdiv_le_of_le_mul hden hbound
  omega

theorem place_generated_two_edge_descendant_envelope
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (ancestor middle descendant : Entry) (ancestorIdx middleIdx descendantIdx : Nat)
    (ha : (ancestor, ancestorIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hm : (middle, middleIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hd : (descendant, descendantIdx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hodd : ancestor.depth % 2 ≠ 0)
    (ham : middle.parent = (ancestorIdx : Int))
    (hmd : descendant.parent = (middleIdx : Int)) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    ∃ (frames : List Bone) (ancestorBorn middleBorn descendantBorn : Bone),
      frames.length = r.entries.length + 1 ∧
      frames[ancestorIdx + 1]? = some ancestorBorn ∧
      frames[middleIdx + 1]? = some middleBorn ∧
      frames[descendantIdx + 1]? = some descendantBorn ∧
      descendantBorn.t0 = middleBorn.t1 ∧
      middleBorn.t1 + r.heights ≤ descendantBorn.t1 ∧
      descendantBorn.x0 + (run p r.heights + 3) ≤ middleBorn.x0 ∧
      descendantBorn.x1 + (run p r.heights + 3) ≤
        ancestorBorn.x0 + Int.fdiv
          ((ancestorBorn.x1 - ancestorBorn.x0) * (middleBorn.t1 - ancestorBorn.t0))
          (ancestorBorn.t1 - ancestorBorn.t0) -
            run p (descendantBorn.t1 - middleBorn.t1) ∧
      ∀ (i : Nat) (rect : Rect) (points : List Point), (i, rect, points) ∈ placed.pieces →
        (∃ n : Tree.Node, ns[r.cause]? = some n ∧ i = r.cause ∧
          rect = ⟨-run p r.length - Int.fdiv n.width 2,
            if r.upper then ordinate spine r.upper r.length - n.height
            else ordinate spine r.upper r.length, n.width, n.height⟩ ∧
          points = [⟨0, spine⟩, ⟨-run p r.length, ordinate spine r.upper r.length⟩]) ∨
        ∃ (e : Entry) (idx : Nat) (n : Tree.Node) (born : Bone),
          (e, idx) ∈ r.entries.zipIdx ∧ i = e.node ∧ ns[e.node]? = some n ∧
          frames[idx + 1]? = some born ∧
          rect = ⟨born.x1 - n.width, ordinate spine r.upper born.t1 - Int.fdiv n.height 2,
            n.width, n.height⟩ ∧
          points = [⟨born.x0, ordinate spine r.upper born.t0⟩,
            ⟨born.x1, ordinate spine r.upper born.t1⟩] := by
  let source := generatedRib ns (cause, k)
  let r := effectivePlacedInput ns (measuredSideLength p ribs) source
  let margin := run p r.heights + 3
  let slot := fun position : Nat =>
    Int.fdiv (r.length * (position + 1 : Nat)) (r.entries.length + 1 : Nat)
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hmiddleDepth := generated_parent_child_depth ns cause k hlink hcause
    ancestor middle ancestorIdx middleIdx ha hm ham
  have hmiddleEven := child_depth_even ancestor.depth middle.depth hmiddleDepth hodd
  have hdescendantDepth := generated_parent_child_depth ns cause k hlink hcause
    middle descendant middleIdx descendantIdx hm hd hmd
  have hdescendantOdd : descendant.depth % 2 ≠ 0 := by
    have hmod := Nat.mod_lt middle.depth (by decide : 0 < 2)
    omega
  obtain ⟨frames, hlength, _, hrecords, hpieces⟩ :=
    place_common_birth_frames ns p spine r placed hplace
  obtain ⟨middleDone, middleRest, hmiddlePrefix, _⟩ := List.eq_append_cons_of_mem hm
  obtain ⟨descendantDone, descendantRest, hdescendantPrefix, _⟩ := List.eq_append_cons_of_mem hd
  obtain ⟨middlePos, ancestorBorn, middleBorn, hmiddlePos, hancestorBorn,
    hmiddleBorn, hmiddleEquation⟩ :=
      hrecords middleDone middle middleIdx middleRest hmiddlePrefix
  obtain ⟨descendantPos, descendantParent, descendantBorn, hdescendantPos,
    hdescendantParent, hdescendantBorn, hdescendantEquation⟩ :=
      hrecords descendantDone descendant descendantIdx descendantRest hdescendantPrefix
  have hmiddleOwner : (middle.parent + 1).toNat = ancestorIdx + 1 := by rw [ham]; omega
  have hdescendantOwner : (descendant.parent + 1).toNat = middleIdx + 1 := by rw [hmd]; omega
  rw [hmiddleOwner] at hancestorBorn
  rw [hdescendantOwner] at hdescendantParent hdescendantEquation
  have hsameMiddle : descendantParent = middleBorn :=
    Option.some.inj (hdescendantParent.symm.trans hmiddleBorn)
  rw [hsameMiddle] at hdescendantEquation
  have hdrawBound := generated_current_odd_prefix_draw_bound ns cause k hlink hcause
    descendantDone descendant descendantIdx descendantRest hdescendantPrefix
    middle middleIdx hm hmd hdescendantOdd
  have hcount : middleBorn.count = (children ns middle.node).length := by
    rw [hmiddleEquation]
    unfold depthBone
    split <;> rfl
  have hreserve := even_native_reservation p
    { ancestorBorn with drawn := processedOddDraws middleDone (middle.parent + 1).toNat }
    middle.depth (slot middlePos.2) (children ns middle.node).length margin hmiddleEven
  rw [← hmiddleEquation] at hreserve
  have hheight : 0 ≤ r.heights := by
    change 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hne : ns ≠ [] := by
    intro heq
    simp [heq, children] at hcause
  have hparameters := successful_slope_parameters ns p raw hne hrun
  have hrunHeight : 0 ≤ run p r.heights :=
    Int.fdiv_nonneg (Int.mul_nonneg hheight hparameters.1)
      (Int.le_trans (by decide : (0 : Int) ≤ 1) hparameters.2)
  have hmargin : 0 ≤ margin := Int.add_nonneg hrunHeight (by decide : (0 : Int) ≤ 3)
  have hstrictCount : processedOddDraws descendantDone (middleIdx + 1) + 1 ≤ middleBorn.count := by
    rw [hcount]
    exact hdrawBound
  have hstart : descendantBorn.x0 =
      middleBorn.x0 + Int.fdiv
        ((middleBorn.x1 - middleBorn.x0) *
          (middleBorn.count - processedOddDraws descendantDone (middleIdx + 1)))
        (middleBorn.count + 1) := by
    rw [hdescendantEquation]
    exact (depthBone_odd_endpoints p
      { middleBorn with drawn := processedOddDraws descendantDone (middleIdx + 1) }
      descendant.depth (slot descendantPos.2) (children ns descendant.node).length
      margin hdescendantOdd).2.2.1
  have hstartGap : descendantBorn.x0 + margin ≤ middleBorn.x0 := by
    rw [hstart]
    exact attachment_start_margin middleBorn.x0 middleBorn.x1 middleBorn.count
      (processedOddDraws descendantDone (middleIdx + 1)) margin
      hreserve.1 hmargin hreserve.2 hstrictCount
  have hmiddleTime : middleBorn.t0 = slot middlePos.2 ∧ middleBorn.t1 = slot middlePos.2 := by
    rw [hmiddleEquation]
    exact ⟨(depthBone_even_endpoints p
      { ancestorBorn with drawn := processedOddDraws middleDone (middle.parent + 1).toNat }
      middle.depth (slot middlePos.2) (children ns middle.node).length margin hmiddleEven).1,
      (depthBone_even_endpoints p
      { ancestorBorn with drawn := processedOddDraws middleDone (middle.parent + 1).toNat }
      middle.depth (slot middlePos.2) (children ns middle.node).length margin hmiddleEven).2.1⟩
  have hmiddleEqual : middleBorn.t1 = middleBorn.t0 :=
    hmiddleTime.2.trans hmiddleTime.1.symm
  have hmiddleX : middleBorn.x0 =
      ancestorBorn.x0 + Int.fdiv
        ((ancestorBorn.x1 - ancestorBorn.x0) * (middleBorn.t1 - ancestorBorn.t0))
        (ancestorBorn.t1 - ancestorBorn.t0) := by
    rw [hmiddleTime.2, hmiddleEquation]
    simp [depthBone, hmiddleEven, slot]
  have hdescendantTime : descendantBorn.t0 = middleBorn.t1 ∧
      descendantBorn.t1 = slot descendantPos.2 := by
    rw [hmiddleEqual, hdescendantEquation]
    exact ⟨(depthBone_odd_endpoints p
      { middleBorn with drawn := processedOddDraws descendantDone (middleIdx + 1) }
      descendant.depth (slot descendantPos.2) (children ns descendant.node).length
      margin hdescendantOdd).1,
      (depthBone_odd_endpoints p
      { middleBorn with drawn := processedOddDraws descendantDone (middleIdx + 1) }
      descendant.depth (slot descendantPos.2) (children ns descendant.node).length
      margin hdescendantOdd).2.1⟩
  have hdescendantX : descendantBorn.x1 =
      descendantBorn.x0 - run p (descendantBorn.t1 - middleBorn.t1) := by
    rw [hdescendantTime.2, hmiddleEqual, hdescendantEquation]
    exact (depthBone_odd_endpoints p
      { middleBorn with drawn := processedOddDraws descendantDone (middleIdx + 1) }
      descendant.depth (slot descendantPos.2) (children ns descendant.node).length
      margin hdescendantOdd).2.2.2
  have hnonempty : source.entries.isEmpty = false := by
    cases hentries : source.entries with
    | nil =>
      change (descendant, descendantIdx) ∈ source.entries.zipIdx at hd
      rw [hentries] at hd
      simp at hd
    | cons first rest => rfl
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  have horder := (generated_parent_child_order ns cause k middle descendant middleIdx descendantIdx
    hm hd hmd middlePos descendantPos hmiddlePos hdescendantPos).1 hmiddleEven
  have hslotGap := ordinal_slots_gap r.length (r.entries.length + 1 : Nat) r.heights
    (middlePos.2 + 1 : Nat) (descendantPos.2 + 1 : Nat) (by omega) hheight hbudget (by omega)
  refine ⟨frames, ancestorBorn, middleBorn, descendantBorn, hlength, hancestorBorn,
    hmiddleBorn, hdescendantBorn, hdescendantTime.1, ?_, hstartGap, ?_, hpieces⟩
  · calc
      middleBorn.t1 + r.heights = slot middlePos.2 + r.heights := by rw [hmiddleTime.2]
      _ ≤ slot descendantPos.2 := hslotGap
      _ = descendantBorn.t1 := hdescendantTime.2.symm
  · change descendantBorn.x1 + margin ≤
      ancestorBorn.x0 + Int.fdiv
        ((ancestorBorn.x1 - ancestorBorn.x0) * (middleBorn.t1 - ancestorBorn.t0))
        (ancestorBorn.t1 - ancestorBorn.t0) -
          run p (descendantBorn.t1 - middleBorn.t1)
    rw [hdescendantX, ← hmiddleX]
    have hshift := Int.sub_le_sub_right hstartGap (run p (descendantBorn.t1 - middleBorn.t1))
    calc
      _ = (descendantBorn.x0 + margin) -
          run p (descendantBorn.t1 - middleBorn.t1) := by omega
      _ ≤ _ := hshift


/-! ### Translation invariance of route-rectangle clearance -/

theorem point_translate_inj (dx dy : Int) (p q : Point) :
    (⟨p.x + dx, p.y + dy⟩ : Point) = ⟨q.x + dx, q.y + dy⟩ ↔ p = q := by
  constructor
  · intro h
    cases p with | mk px py =>
    cases q with | mk qx qy =>
    simp only [Point.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hpx : px = qx := by omega
    have hpy : py = qy := by omega
    subst hpx; subst hpy
    rfl
  · intro h; subst h; rfl

private theorem dot_translate (nx ny dx dy : Int) (p : Point) :
    Polyline.dot nx ny ⟨p.x + dx, p.y + dy⟩ =
      Polyline.dot nx ny p + (nx * dx + ny * dy) := by
  simp only [Polyline.dot, Int.mul_add]
  omega

private theorem minCorner_translate (nx ny dx dy : Int) (r : Rect) :
    Polyline.minCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.minCorner nx ny r + (nx * dx + ny * dy) := by
  simp only [Polyline.minCorner, Polyline.dot, Int.mul_add]
  omega

private theorem maxCorner_translate (nx ny dx dy : Int) (r : Rect) :
    Polyline.maxCorner nx ny ⟨r.x + dx, r.y + dy, r.w, r.h⟩ =
      Polyline.maxCorner nx ny r + (nx * dx + ny * dy) := by
  simp only [Polyline.maxCorner, Polyline.dot, Int.mul_add]
  omega

theorem segMisses_translate (dx dy : Int) (p q : Point) (r : Rect) :
    Polyline.segMisses (⟨p.x + dx, p.y + dy⟩) (⟨q.x + dx, q.y + dy⟩)
      ⟨r.x + dx, r.y + dy, r.w, r.h⟩ ↔ Polyline.segMisses p q r := by
  have hne : (⟨p.x + dx, p.y + dy⟩ : Point) ≠ ⟨q.x + dx, q.y + dy⟩ ↔ p ≠ q := by
    rw [ne_eq, ne_eq, point_translate_inj]
  show (max (p.x + dx) (q.x + dx) ≤ r.x + dx ∨
      min (p.x + dx) (q.x + dx) ≥ r.x + dx + r.w ∨
      max (p.y + dy) (q.y + dy) ≤ r.y + dy ∨
      min (p.y + dy) (q.y + dy) ≥ r.y + dy + r.h ∨
        ((⟨p.x + dx, p.y + dy⟩ : Point) ≠ ⟨q.x + dx, q.y + dy⟩ ∧
          (Polyline.dot ((p.y + dy) - (q.y + dy)) ((q.x + dx) - (p.x + dx))
              ⟨p.x + dx, p.y + dy⟩ ≤
            Polyline.minCorner ((p.y + dy) - (q.y + dy)) ((q.x + dx) - (p.x + dx))
              ⟨r.x + dx, r.y + dy, r.w, r.h⟩ ∨
           Polyline.dot ((p.y + dy) - (q.y + dy)) ((q.x + dx) - (p.x + dx))
              ⟨p.x + dx, p.y + dy⟩ ≥
            Polyline.maxCorner ((p.y + dy) - (q.y + dy)) ((q.x + dx) - (p.x + dx))
              ⟨r.x + dx, r.y + dy, r.w, r.h⟩))) ↔
    (max p.x q.x ≤ r.x ∨
      min p.x q.x ≥ r.x + r.w ∨
      max p.y q.y ≤ r.y ∨
      min p.y q.y ≥ r.y + r.h ∨
        (p ≠ q ∧
          (Polyline.dot (p.y - q.y) (q.x - p.x) p ≤
            Polyline.minCorner (p.y - q.y) (q.x - p.x) r ∨
           Polyline.dot (p.y - q.y) (q.x - p.x) p ≥
            Polyline.maxCorner (p.y - q.y) (q.x - p.x) r)))
  rw [hne]
  have hnx : (p.y + dy) - (q.y + dy) = p.y - q.y := by omega
  have hny : (q.x + dx) - (p.x + dx) = q.x - p.x := by omega
  rw [hnx, hny]
  constructor <;> intro h
  · rcases h with h | h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · rcases h with ⟨hne', hsat⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne', ?_⟩)))
      rcases hsat with hle | hge
      · left
        rw [dot_translate, minCorner_translate] at hle
        omega
      · right
        rw [dot_translate, maxCorner_translate] at hge
        omega
  · rcases h with h | h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; left; omega
    · rcases h with ⟨hne', hsat⟩
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne', ?_⟩)))
      rcases hsat with hle | hge
      · left
        rw [dot_translate, minCorner_translate]
        omega
      · right
        rw [dot_translate, maxCorner_translate]
        omega

theorem allSegsMiss_translate (dx dy : Int) (pts : List Point) (r : Rect) :
    Polyline.allSegsMiss (pts.map fun p => (⟨p.x + dx, p.y + dy⟩ : Point))
      ⟨r.x + dx, r.y + dy, r.w, r.h⟩ ↔ Polyline.allSegsMiss pts r := by
  induction pts generalizing r with
  | nil => exact Iff.rfl
  | cons p rest ih =>
    cases rest with
    | nil => exact Iff.rfl
    | cons q rest' =>
      simp only [List.map_cons, Polyline.allSegsMiss]
      constructor
      · intro h
        exact ⟨(segMisses_translate dx dy p q r).mp h.1,
          (ih r).mp h.2⟩
      · intro h
        exact ⟨(segMisses_translate dx dy p q r).mpr h.1,
          (ih r).mpr h.2⟩

theorem hitsRect_translate (dx dy : Int) (pts : List Point) (r : Rect) :
    Polyline.hitsRect (pts.map fun p => (⟨p.x + dx, p.y + dy⟩ : Point))
      ⟨r.x + dx, r.y + dy, r.w, r.h⟩ ↔ Polyline.hitsRect pts r := by
  unfold Polyline.hitsRect
  simp only [allSegsMiss_translate]

/-! ### Rib-local foreign-piece route clearance -/

private theorem distinct_order_find_positions {order : List Nat} {a b pa pb : Nat}
    (ha : order.zipIdx.find? (fun v => v.1 == a) = some (a, pa))
    (hb : order.zipIdx.find? (fun v => v.1 == b) = some (b, pb))
    (hab : a ≠ b) : pa ≠ pb := by
  intro h
  have hga : order[pa]? = some a := by
    have hm := List.mem_of_find?_eq_some ha
    have he := List.mem_zipIdx_iff_getElem?.mp hm
    exact he
  have hgb : order[pb]? = some b := by
    have hm := List.mem_of_find?_eq_some hb
    exact List.mem_zipIdx_iff_getElem?.mp hm
  rw [h] at hga
  exact hab (Option.some.inj (hga.symm.trans hgb))

theorem odd_entry_route_misses_earlier_slot
    (p : Params) (par : Bone) (depth : Nat) (t count margin spine : Int)
    (up : Bool) (foreignX foreignT foreignWidth foreignHeight heightBound dx dy : Int)
    (hodd : depth % 2 ≠ 0)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hparentGap : foreignT + heightBound ≤ par.t0)
    (hentryGap : foreignT + heightBound ≤ t) :
    let b := depthBone p par depth t count margin
    ¬ Polyline.hitsRect
      [⟨b.x0 + dx, ordinate spine up b.t0 + dy⟩,
       ⟨b.x1 + dx, ordinate spine up b.t1 + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  dsimp only
  have ht := depthBone_odd_endpoints p par depth t count margin hodd
  apply bone_route_misses_earlier_slot
  · exact hheight
  · exact hbound
  · simpa only [ht.1] using hparentGap
  · simpa only [ht.2.1] using hentryGap

theorem even_entry_route_misses_near_slot
    (p : Params) (par : Bone) (depth : Nat) (t count margin spine : Int)
    (up : Bool) (foreignX foreignT foreignWidth foreignHeight heightBound dx dy : Int)
    (heven : depth % 2 = 0)
    (hheight : 0 ≤ foreignHeight) (hbound : foreignHeight ≤ heightBound)
    (hlater : t + heightBound ≤ foreignT ∨ foreignT + heightBound ≤ t) :
    let b := depthBone p par depth t count margin
    ¬ Polyline.hitsRect
      [⟨b.x0 + dx, ordinate spine up b.t0 + dy⟩,
       ⟨b.x1 + dx, ordinate spine up b.t1 + dy⟩]
      ⟨foreignX + dx, ordinate spine up foreignT - Int.fdiv foreignHeight 2 + dy,
        foreignWidth, foreignHeight⟩ := by
  dsimp only
  have ht := depthBone_even_endpoints p par depth t count margin heven
  cases hlater with
  | inl hl =>
      apply bone_route_misses_later_slot
      · exact hheight
      · exact hbound
      · simpa only [ht.1, ht.2.1] using hl
      · simpa only [ht.1, ht.2.1] using hl
  | inr hl =>
      apply bone_route_misses_earlier_slot
      · exact hheight
      · exact hbound
      · simpa only [ht.1, ht.2.1] using hl
      · simpa only [ht.1, ht.2.1] using hl

theorem bone_route_misses_cause_box
    (spine x₀ x₁ t₀ t₁ L fx fw fh : Int) (up : Bool)
    (ht₀L : t₀ ≤ L) (ht₁L : t₁ ≤ L)
    (dx dy : Int) :
    ¬ Polyline.hitsRect
      [⟨x₀ + dx, ordinate spine up t₀ + dy⟩,
       ⟨x₁ + dx, ordinate spine up t₁ + dy⟩]
      ⟨fx + dx,
        (if up then ordinate spine up L - fh else ordinate spine up L) + dy,
        fw, fh⟩ := by
  intro hhit
  apply hhit.2.2
  constructor
  · cases up <;>
      simp only [ordinate, Bool.false_eq_true, ↓reduceIte]
    · apply Or.inr; apply Or.inr; apply Or.inl
      change max (spine + t₀ + dy) (spine + t₁ + dy) ≤ spine + L + dy
      omega
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      change min (spine - t₀ + dy) (spine - t₁ + dy) ≥
        (spine - L - fh) + dy + fh
      omega
  · trivial
theorem place_entry_route_misses_cause_box
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (_hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (_hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int) (placed : Rib)
    (_hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))) =
        .ok placed)
    (e : Entry) (idx : Nat) (pos : Nat × Nat) (par : Bone) (n : Tree.Node)
    (he : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hpos : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idx) = some pos)
    (_hn : ns[e.node]? = some n)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (e.parent + 1).toNat par)
    (cn : Tree.Node) (_hcn : ns[cause]? = some cn) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let b := depthBone p par e.depth t (children ns e.node).length (run p r.heights + 3)
    ¬ Polyline.hitsRect
      [⟨b.x0, ordinate spine r.upper b.t0⟩,
       ⟨b.x1, ordinate spine r.upper b.t1⟩]
      ⟨-run p r.length - Int.fdiv cn.width 2,
        (if r.upper then ordinate spine r.upper r.length - cn.height
          else ordinate spine r.upper r.length), cn.width, cn.height⟩ := by
  dsimp only
  have hne : ns ≠ [] := by
    intro hnil
    simp [hnil, children] at hcause
  obtain ⟨hmin, hbase⟩ := successful_nonempty_length_parameters ns p raw hne hrun
  have hbone : BoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k)))
      (depthBone p par e.depth
        (Int.fdiv ((effectivePlacedInput ns (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).length * (pos.2 + 1 : Nat))
          ((effectivePlacedInput ns (measuredSideLength p ribs)
            (generatedRib ns (cause, k))).entries.length + 1 : Nat))
        (children ns e.node).length
        (run p (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (cause, k))).heights + 3)) :=
    BoneGenealogy.entry par e idx pos (indexedBoneGenealogy_erase hgene) he hpos
  have htb := generated_bone_temporal_bounds ns p ribs cause k (by omega) (by omega) _ hbone
  simpa only [Int.add_zero] using
    bone_route_misses_cause_box spine _ _ _ _ _ _ _ _
      ((effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k))).upper)
      htb.2.1 htb.2.2.2 0 0



section IshikawaC6RibLocalLemmas
set_option maxHeartbeats 6000000
private theorem depthBone_t1_eq (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) :
    (depthBone p par depth t count margin).t1 = t := by
  unfold depthBone
  split <;> rfl

private theorem generated_entries_nonempty_of_mem {ns : List Tree.Node}
    {cause k : Nat} {e : Entry} {idx : Nat}
    (he : (e, idx) ∈ (generatedRib ns (cause, k)).entries.zipIdx) :
    (generatedRib ns (cause, k)).entries.isEmpty = false := by
  cases h : (generatedRib ns (cause, k)).entries with
  | nil =>
    rw [h] at he
    simp [List.zipIdx] at he
  | cons first rest => rfl

private theorem zipIdx_index_ne_of_node_ne {es : List Entry} {eI eJ : Entry}
    {idxI idxJ : Nat}
    (heI : (eI, idxI) ∈ es.zipIdx) (heJ : (eJ, idxJ) ∈ es.zipIdx)
    (hnode : eI.node ≠ eJ.node) : idxI ≠ idxJ := by
  intro hidx
  have gI := List.mem_zipIdx_iff_getElem?.mp heI
  have gJ := List.mem_zipIdx_iff_getElem?.mp heJ
  change es[idxI]? = some eI at gI
  change es[idxJ]? = some eJ at gJ
  rw [← hidx] at gJ
  have heq : eI = eJ := Option.some.inj (gI.symm.trans gJ)
  exact hnode (congrArg Entry.node heq)

private theorem order_positions_ne {order : List Nat} {idxI idxJ : Nat}
    {posI posJ : Nat × Nat}
    (hI : order.zipIdx.find? (fun v => v.1 == idxI) = some posI)
    (hJ : order.zipIdx.find? (fun v => v.1 == idxJ) = some posJ)
    (hidx : idxI ≠ idxJ) : posI.2 ≠ posJ.2 := by
  intro hpos
  have hIeq := List.find?_some hI
  have hJeq := List.find?_some hJ
  have hImem : posI ∈ order.zipIdx := List.mem_of_find?_eq_some hI
  have hJmem : posJ ∈ order.zipIdx := List.mem_of_find?_eq_some hJ
  have hI1 : posI.1 = idxI := by simpa only [beq_iff_eq] using hIeq
  have hJ1 : posJ.1 = idxJ := by simpa only [beq_iff_eq] using hJeq
  have gI := List.mem_zipIdx_iff_getElem?.mp hImem
  have gJ := List.mem_zipIdx_iff_getElem?.mp hJmem
  change order[posI.2]? = some posI.1 at gI
  change order[posJ.2]? = some posJ.1 at gJ
  rw [← hpos] at gJ
  have : posI.1 = posJ.1 := Option.some.inj (gI.symm.trans gJ)
  omega

theorem place_entry_route_misses_entry_box_even
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0) (spine : Int)
    (eI : Entry) (idxI : Nat) (posI : Nat × Nat) (parI : Bone) (nI : Tree.Node)
    (heI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hposI : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxI) = some posI)
    (_hgeneI : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (eI.parent + 1).toNat parI)
    (_hnI : ns[eI.node]? = some nI)
    (eJ : Entry) (idxJ : Nat) (posJ : Nat × Nat) (parJ : Bone) (nJ : Tree.Node)
    (heJ : (eJ, idxJ) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hposJ : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxJ) = some posJ)
    (_hgeneJ : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (eJ.parent + 1).toNat parJ)
    (hnJ : ns[eJ.node]? = some nJ)
    (hnode : eI.node ≠ eJ.node)
    (hevenI : eI.depth % 2 = 0) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    let tI := Int.fdiv (r.length * (posI.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bI := depthBone p parI eI.depth tI (children ns eI.node).length (run p r.heights + 3)
    let tJ := Int.fdiv (r.length * (posJ.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bJ := depthBone p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3)
    ¬ Polyline.hitsRect
      [⟨bI.x0, ordinate spine r.upper bI.t0⟩,
       ⟨bI.x1, ordinate spine r.upper bI.t1⟩]
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2,
        nJ.width, nJ.height⟩ := by
  intro r tI bI tJ bJ
  have hne : ns ≠ [] := by
    intro hnil
    simp [hnil, children] at hcause
  have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false :=
    generated_entries_nonempty_of_mem heI
  have hb := generated_reservation_budget ns p ribs hg
    (generatedRib ns (cause, k)) hsource hneEntries
  have hb' : ((generatedRib ns (cause, k)).entries.length + 1 : Nat) *
      (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length := by
    have hfields : (generatedRib ns (cause, k)).heights =
        (generatedRib ns (cause, k)).entries.foldl
          (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
      (generated_rib_fields ns cause k).2.2.2
    rw [hfields] at hb
    exact hb
  have hmaxH : 0 ≤ r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    entry_height_fold_initial ns _ 0
  have hbudget : (r.entries.length + 1 : Nat) * r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length := hb'
  have hdimsJ := successful_node_dimensions ns p raw hrun nJ (List.mem_of_getElem? hnJ)
  have hbound : nJ.height ≤ r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    measured_entry_height_bound ns r.entries eJ (List.fst_mem_of_mem_zipIdx heJ) nJ hnJ
  have hheight : 0 ≤ nJ.height := by omega
  have hidx : idxI ≠ idxJ := zipIdx_index_ne_of_node_ne heI heJ hnode
  have hpos : posI.2 ≠ posJ.2 := order_positions_ne hposI hposJ hidx
  have hbJ1 : bJ.t1 = tJ := by
    show (depthBone p parJ eJ.depth tJ (children ns eJ.node).length
      (run p r.heights + 3)).t1 = tJ
    exact depthBone_t1_eq p parJ eJ.depth tJ _ _
  rcases Nat.lt_or_gt_of_ne hpos with hlt | hgt
  · -- I earlier than J
    have hslot := ordinal_slots_gap r.length (r.entries.length + 1 : Nat)
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
      (posI.2 + 1 : Nat) (posJ.2 + 1 : Nat) (by omega) hmaxH hbudget (by omega)
    rw [hbJ1]
    intro hhit
    have hclear := even_entry_route_misses_later_ordered_slot p parI eI.depth
      r.length (children ns eI.node).length (run p r.heights + 3) spine
      r.entries.length posI.2 posJ.2 r.upper
      (bJ.x1 - nJ.width) nJ.width nJ.height
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
      0 0 hevenI hheight hbound hbudget (by omega)
    simp only [Int.add_zero] at hclear
    exact hclear hhit
  · -- J earlier than I
    have hslot := ordinal_slots_gap r.length (r.entries.length + 1 : Nat)
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
      (posJ.2 + 1 : Nat) (posI.2 + 1 : Nat) (by omega) hmaxH hbudget (by omega)
    have hteven := depthBone_even_endpoints p parI eI.depth tI
      (children ns eI.node).length (run p r.heights + 3) hevenI
    rw [hbJ1]
    intro hhit
    have hbI0' : bI.t0 = tI := hteven.1
    have hbI1' : bI.t1 = tI := hteven.2.1
    have hslot' : tJ +
        (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
        tI := hslot
    have hgap₀ : tJ +
        (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
        bI.t0 := by
      rw [hbI0']
      exact hslot'
    have hgap₁ : tJ +
        (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
        bI.t1 := by
      rw [hbI1']
      exact hslot'
    have hclear := bone_route_misses_earlier_slot spine bI.x0 bI.x1 bI.t0 bI.t1
      (bJ.x1 - nJ.width) tJ nJ.width nJ.height
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
      r.upper 0 0 hheight hbound hgap₀ hgap₁
    simp only [Int.add_zero] at hclear
    exact hclear hhit



theorem place_entry_route_misses_entry_box_odd_later
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (spine : Int)
    (eI : Entry) (idxI : Nat) (posI : Nat × Nat) (parI : Bone) (nI : Tree.Node)
    (heI : (eI, idxI) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (hposI : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxI) = some posI)
    (hgeneI : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (eI.parent + 1).toNat parI)
    (_hnI : ns[eI.node]? = some nI)
    (eJ : Entry) (idxJ : Nat) (posJ : Nat × Nat) (parJ : Bone) (nJ : Tree.Node)
    (heJ : (eJ, idxJ) ∈ (generatedRib ns (cause, k)).entries.zipIdx)
    (_hposJ : (generatedRib ns (cause, k)).order.zipIdx.find?
      (fun v => v.1 == idxJ) = some posJ)
    (_hgeneJ : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
      (eJ.parent + 1).toNat parJ)
    (hnJ : ns[eJ.node]? = some nJ)
    (_hnode : eI.node ≠ eJ.node)
    (hoddI : eI.depth % 2 ≠ 0)
    (_hlt : posI.2 < posJ.2) :
    let r := effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))
    let tI := Int.fdiv (r.length * (posI.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bI := depthBone p parI eI.depth tI (children ns eI.node).length (run p r.heights + 3)
    let tJ := Int.fdiv (r.length * (posJ.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    let bJ := depthBone p parJ eJ.depth tJ (children ns eJ.node).length (run p r.heights + 3)
    ¬ Polyline.hitsRect
      [⟨bI.x0, ordinate spine r.upper bI.t0⟩,
       ⟨bI.x1, ordinate spine r.upper bI.t1⟩]
      ⟨bJ.x1 - nJ.width, ordinate spine r.upper bJ.t1 - Int.fdiv nJ.height 2,
        nJ.width, nJ.height⟩ := by
  intro r tI bI tJ bJ
  have hneEntries : (generatedRib ns (cause, k)).entries.isEmpty = false :=
    generated_entries_nonempty_of_mem heI
  have hb := generated_reservation_budget ns p ribs hg
    (generatedRib ns (cause, k)) hsource hneEntries
  have hfields : (generatedRib ns (cause, k)).heights =
      (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    (generated_rib_fields ns cause k).2.2.2
  have hb' : ((generatedRib ns (cause, k)).entries.length + 1 : Nat) *
      (generatedRib ns (cause, k)).entries.foldl
        (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length := by
    rw [hfields] at hb
    exact hb
  have hmaxH : 0 ≤ r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    entry_height_fold_initial ns _ 0
  have hbudget : (r.entries.length + 1 : Nat) * r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length := hb'
  have hdimsJ := successful_node_dimensions ns p raw hrun nJ (List.mem_of_getElem? hnJ)
  have hbound : nJ.height ≤ r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 :=
    measured_entry_height_bound ns r.entries eJ (List.fst_mem_of_mem_zipIdx heJ) nJ hnJ
  have hheight : 0 ≤ nJ.height := by omega
  have hbJ1 : bJ.t1 = tJ := by
    show (depthBone p parJ eJ.depth tJ (children ns eJ.node).length
      (run p r.heights + 3)).t1 = tJ
    exact depthBone_t1_eq p parJ eJ.depth tJ _ _
  -- slot gap: tI + maxH ≤ tJ
  have hslot0 := ordinal_slots_gap r.length (r.entries.length + 1 : Nat)
    (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
    (posI.2 + 1 : Nat) (posJ.2 + 1 : Nat) (by omega) hmaxH hbudget (by omega)
  have hslot : tI +
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
      tJ := hslot0
  -- parent gap: parI.t0 + r.heights ≤ tI
  have hpgaps := generated_entry_parent_slot_gaps ns p ribs hg cause k hsource
    hlink hcause eI idxI posI parI heI hposI hgeneI
  have hpgaps' : parI.t0 + r.heights ≤ tI := hpgaps.1 hoddI
  have hrheights : r.heights = r.entries.foldl
      (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := hfields
  have hpgaps'' : parI.t0 +
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
      tI := by
    rw [hrheights] at hpgaps'
    exact hpgaps'
  have hoddEnds := depthBone_odd_endpoints p parI eI.depth tI
    (children ns eI.node).length (run p r.heights + 3) hoddI
  have hbI0 : bI.t0 = parI.t0 := hoddEnds.1
  have hbI1 : bI.t1 = tI := hoddEnds.2.1
  rw [hbJ1]
  intro hhit
  have hgap₀ : bI.t0 +
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
      tJ := by
    rw [hbI0]
    omega
  have hgap₁ : bI.t1 +
      (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0) ≤
      tJ := by
    rw [hbI1]
    exact hslot
  have hclear := bone_route_misses_later_slot spine bI.x0 bI.x1 bI.t0 bI.t1
    (bJ.x1 - nJ.width) tJ nJ.width nJ.height
    (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
    r.upper 0 0 hheight hbound hgap₀ hgap₁
  simp only [Int.add_zero] at hclear
  exact hclear hhit


end IshikawaC6RibLocalLemmas

end Elegant.Ishikawa
