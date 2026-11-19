import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.IshikawaFlattenSizeFacts
import Elegant.Kinds.IshikawaValid

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaSeparation

open Elegant.Ishikawa

theorem generated_place_entries_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (source : Rib) (hsource : source ∈ ribs) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) = .ok placed)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ placed.pieces)
    (hb : (j, b, pointsB) ∈ placed.pieces)
    (hi : i ≠ source.cause) (hj : j ≠ source.cause) (hne : i ≠ j) :
    Disjoint a b := by
  have hplacement := place_piece_placement ns p spine
    (effectivePlacedInput ns (measuredSideLength p ribs) source) placed hplace
    i a pointsA ha
  have hnonempty : source.entries.isEmpty = false := by
    rcases hplacement with ⟨n, _, hic, _⟩ |
      ⟨e, idx, pos, n, he, _⟩
    · exact False.elim (hi hic)
    · have hm : e ∈ source.entries :=
        List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
      cases hes : source.entries with
      | nil => simp only [hes, List.not_mem_nil] at hm
      | cons first rest => rfl
  obtain ⟨cause, k, _, hgenerated⟩ := generated_rib_source ns ribs hg source hsource
  have hheight : source.heights = source.entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
    rw [hgenerated]
    exact (generated_rib_fields ns cause k).2.2.2
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  rw [hheight] at hbudget
  exact placed_entries_disjoint ns p raw hrun spine
    (effectivePlacedInput ns (measuredSideLength p ribs) source) placed hplace
    hbudget i j a b pointsA pointsB ha hb hi hj hne

theorem found_entry_slot_bounds (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (r : Rib) (e : Entry) (idx : Nat) (pos : Nat × Nat) (n : Tree.Node)
    (he : (e, idx) ∈ r.entries.zipIdx)
    (hp : r.order.zipIdx.find? (fun v => v.1 == idx) = some pos)
    (hn : ns[e.node]? = some n)
    (horder : r.order.length ≤ r.entries.length)
    (hbudget : (r.entries.length + 1 : Nat) *
      r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length) :
    let t := Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)
    0 ≤ n.height ∧ n.height ≤ t ∧ t + n.height ≤ r.length := by
  have hmember : e ∈ r.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
  have hheight := measured_entry_height_bound ns r.entries e hmember n hn
  have hnonnegative := entry_height_fold_initial ns r.entries 0
  have hdims := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
  have hlookup := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hp)
  obtain ⟨hposbound, _⟩ := List.getElem?_eq_some_iff.mp hlookup
  have hpos : pos.2 < r.entries.length := Nat.lt_of_lt_of_le hposbound horder
  have hslot := ordinal_slot_inside r.length (r.entries.length + 1 : Nat)
    (r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0)
    (pos.2 + 1 : Nat) (by omega) hnonnegative hbudget (by omega) (by omega)
  dsimp only
  constructor
  · omega
  constructor <;> omega

theorem generated_effective_order_length_le (ns : List Tree.Node)
    (length : Bool → Int) (cause k : Nat) :
    (effectivePlacedInput ns length (generatedRib ns (cause, k))).order.length ≤
      (effectivePlacedInput ns length (generatedRib ns (cause, k))).entries.length := by
  have hfields := (generated_rib_fields ns cause k).2.2.1
  have hlength := generated_rib_order_length_le ns cause k
  rw [← hfields] at hlength
  exact hlength

theorem generated_found_entry_slot_bounds (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (source : Rib) (hsource : source ∈ ribs) :
    let input := effectivePlacedInput ns (measuredSideLength p ribs) source
    ∀ (e : Entry) (idx : Nat) (pos : Nat × Nat) (n : Tree.Node),
      (e, idx) ∈ input.entries.zipIdx →
      input.order.zipIdx.find? (fun v => v.1 == idx) = some pos →
      ns[e.node]? = some n →
      let t := Int.fdiv (input.length * (pos.2 + 1 : Nat))
        (input.entries.length + 1 : Nat)
      0 ≤ n.height ∧ n.height ≤ t ∧ t + n.height ≤ input.length := by
  dsimp only
  intro e idx pos n he hp hn
  have hm : e ∈ source.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he)
  have hnonempty : source.entries.isEmpty = false := by
    cases hes : source.entries with
    | nil => simp only [hes, List.not_mem_nil] at hm
    | cons first rest => rfl
  obtain ⟨cause, k, _, hgenerated⟩ := generated_rib_source ns ribs hg source hsource
  have hheight : source.heights = source.entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
    rw [hgenerated]
    exact (generated_rib_fields ns cause k).2.2.2
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  rw [hheight] at hbudget
  have horder : source.order.length ≤ source.entries.length := by
    rw [hgenerated]
    exact generated_effective_order_length_le ns (measuredSideLength p ribs) cause k
  exact found_entry_slot_bounds ns p raw hrun
    (effectivePlacedInput ns (measuredSideLength p ribs) source)
    e idx pos n he hp hn horder hbudget

theorem generated_cause_entry_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (source : Rib) (hsource : source ∈ ribs) (spine causeX causeW causeH entryX : Int) :
    let input := effectivePlacedInput ns (measuredSideLength p ribs) source
    ∀ (e : Entry) (idx : Nat) (pos : Nat × Nat) (n : Tree.Node),
      (e, idx) ∈ input.entries.zipIdx →
      input.order.zipIdx.find? (fun v => v.1 == idx) = some pos →
      ns[e.node]? = some n →
      Disjoint
        ⟨causeX, if input.upper then ordinate spine input.upper input.length - causeH
          else ordinate spine input.upper input.length, causeW, causeH⟩
        ⟨entryX, ordinate spine input.upper
          (Int.fdiv (input.length * (pos.2 + 1 : Nat)) (input.entries.length + 1 : Nat)) -
            Int.fdiv n.height 2, n.width, n.height⟩ := by
  dsimp only
  intro e idx pos n he hp hn
  have hslot := generated_found_entry_slot_bounds ns p raw hrun ribs hg source hsource
    e idx pos n he hp hn
  exact cause_entry_slots_disjoint spine _ _ n.height _ causeX causeW causeH entryX
    n.width n.height hslot.1 (Int.le_refl _) hslot.2.2

theorem generated_entries_geometry_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (source : Rib) (hsource : source ∈ ribs) (spine x₀ x₁ : Int) :
    let input := effectivePlacedInput ns (measuredSideLength p ribs) source
    ∀ (e₀ e₁ : Entry) (idx₀ idx₁ : Nat) (pos₀ pos₁ : Nat × Nat) (n₀ n₁ : Tree.Node),
      (e₀, idx₀) ∈ input.entries.zipIdx →
      (e₁, idx₁) ∈ input.entries.zipIdx →
      input.order.zipIdx.find? (fun v => v.1 == idx₀) = some pos₀ →
      input.order.zipIdx.find? (fun v => v.1 == idx₁) = some pos₁ →
      ns[e₀.node]? = some n₀ → ns[e₁.node]? = some n₁ → e₀.node ≠ e₁.node →
      Disjoint
        ⟨x₀, ordinate spine input.upper
          (Int.fdiv (input.length * (pos₀.2 + 1 : Nat)) (input.entries.length + 1 : Nat)) -
            Int.fdiv n₀.height 2, n₀.width, n₀.height⟩
        ⟨x₁, ordinate spine input.upper
          (Int.fdiv (input.length * (pos₁.2 + 1 : Nat)) (input.entries.length + 1 : Nat)) -
            Int.fdiv n₁.height 2, n₁.width, n₁.height⟩ := by
  dsimp only
  intro e₀ e₁ idx₀ idx₁ pos₀ pos₁ n₀ n₁ he₀ he₁ hp₀ hp₁ hn₀ hn₁ hnodes
  have hmem₀ : e₀ ∈ source.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he₀)
  have hmem₁ : e₁ ∈ source.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he₁)
  have hnonempty : source.entries.isEmpty = false := by
    cases hes : source.entries with
    | nil => simp only [hes, List.not_mem_nil] at hmem₀
    | cons first rest => rfl
  obtain ⟨cause, k, _, hgenerated⟩ := generated_rib_source ns ribs hg source hsource
  have hheight : source.heights = source.entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
    rw [hgenerated]
    exact (generated_rib_fields ns cause k).2.2.2
  have hbudget := generated_reservation_budget ns p ribs hg source hsource hnonempty
  rw [hheight] at hbudget
  have hindices := entry_occurrence_indices_distinct source.entries e₀ e₁ idx₀ idx₁
    he₀ he₁ hnodes
  have hpos := found_ordinal_injective source.order idx₀ idx₁ pos₀ pos₁ hp₀ hp₁ hindices
  by_cases horder : pos₀.2 < pos₁.2
  · exact measured_entry_slots_disjoint ns p raw hrun source.entries e₀ e₁
      hmem₀ hmem₁ n₀ n₁ hn₀ hn₁ spine _ (pos₀.2 + 1 : Nat)
      (pos₁.2 + 1 : Nat) x₀ x₁ source.upper (by omega) hbudget
  · apply (Disjoint.comm _ _).mpr
    exact measured_entry_slots_disjoint ns p raw hrun source.entries e₁ e₀
      hmem₁ hmem₀ n₁ n₀ hn₁ hn₀ spine _ (pos₁.2 + 1 : Nat)
      (pos₀.2 + 1 : Nat) x₁ x₀ source.upper (by omega) hbudget

theorem generated_place_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (source : Rib) (hsource : source ∈ ribs) (spine : Int) (placed : Rib)
    (hplace : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) = .ok placed)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ placed.pieces)
    (hb : (j, b, pointsB) ∈ placed.pieces) (hne : i ≠ j) : Disjoint a b := by
  let input := effectivePlacedInput ns (measuredSideLength p ribs) source
  have hpa := place_piece_placement ns p spine input placed hplace i a pointsA ha
  have hpb := place_piece_placement ns p spine input placed hplace j b pointsB hb
  rcases hpa with ⟨causeA, _, hi, hrectA⟩ |
    ⟨e₀, idx₀, pos₀, n₀, he₀, hp₀, hi₀, hn₀, haw, hah, hay⟩
  · rcases hpb with ⟨causeB, _, hj, _⟩ |
      ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, _, hn₁, hbw, hbh, hby⟩
    · exact False.elim (hne (hi.trans hj.symm))
    · have hsep := generated_cause_entry_disjoint ns p raw hrun ribs hg source hsource
        spine (-run p input.length - Int.fdiv causeA.width 2) causeA.width causeA.height
        b.x e₁ idx₁ pos₁ n₁ he₁ hp₁ hn₁
      rw [hrectA]
      simpa only [Disjoint, Rect.meetsInterior, hbw, hbh, hby] using hsep
  · rcases hpb with ⟨causeB, _, _, hrectB⟩ |
      ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, hj₁, hn₁, hbw, hbh, hby⟩
    · have hsep := generated_cause_entry_disjoint ns p raw hrun ribs hg source hsource
        spine (-run p input.length - Int.fdiv causeB.width 2) causeB.width causeB.height
        a.x e₀ idx₀ pos₀ n₀ he₀ hp₀ hn₀
      apply (Disjoint.comm _ _).mpr
      rw [hrectB]
      simpa only [Disjoint, Rect.meetsInterior, haw, hah, hay] using hsep
    · have hnodes : e₀.node ≠ e₁.node := by simpa only [hi₀, hj₁] using hne
      have hsep := generated_entries_geometry_disjoint ns p raw hrun ribs hg source hsource
        spine a.x b.x e₀ e₁ idx₀ idx₁ pos₀ pos₁ n₀ n₁
        he₀ he₁ hp₀ hp₁ hn₀ hn₁ hnodes
      simpa only [Disjoint, Rect.meetsInterior, haw, hah, hay, hbw, hbh, hby] using hsep

theorem generated_opposite_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs : List Rib) (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (sourceA sourceB : Rib) (hsourceA : sourceA ∈ ribs) (hsourceB : sourceB ∈ ribs)
    (hupper : sourceA.upper = true) (hlower : sourceB.upper = false)
    (spine : Int) (placedA placedB : Rib)
    (hplaceA : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) sourceA) = .ok placedA)
    (hplaceB : place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) sourceB) = .ok placedB)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ placedA.pieces)
    (hb : (j, b, pointsB) ∈ placedB.pieces) : Disjoint a b := by
  let inputA := effectivePlacedInput ns (measuredSideLength p ribs) sourceA
  let inputB := effectivePlacedInput ns (measuredSideLength p ribs) sourceB
  have hu : inputA.upper = true := hupper
  have hl : inputB.upper = false := hlower
  have hnonempty : ns ≠ [] := by
    intro he
    subst ns
    simp [place] at hplaceA
  have hlengthA := successful_nonempty_effective_length_nonnegative ns p raw hnonempty
    hrun ribs sourceA
  have hlengthB := successful_nonempty_effective_length_nonnegative ns p raw hnonempty
    hrun ribs sourceB
  have hpa := place_piece_placement ns p spine inputA placedA hplaceA i a pointsA ha
  have hpb := place_piece_placement ns p spine inputB placedB hplaceB j b pointsB hb
  rcases hpa with ⟨causeA, _, _, hrectA⟩ |
    ⟨e₀, idx₀, pos₀, n₀, he₀, hp₀, _, hn₀, haw, hah, hay⟩
  · rcases hpb with ⟨causeB, _, _, hrectB⟩ |
      ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, _, hn₁, hbw, hbh, hby⟩
    · have hsep := opposite_cause_slots_disjoint spine inputA.length inputB.length
        (-run p inputA.length - Int.fdiv causeA.width 2)
        (-run p inputB.length - Int.fdiv causeB.width 2)
        causeA.width causeB.width causeA.height causeB.height hlengthA hlengthB
      rw [hrectA, hrectB]
      simpa only [hu, hl, Bool.false_eq_true, ↓reduceIte] using hsep
    · have hslot := generated_found_entry_slot_bounds ns p raw hrun ribs hg
        sourceB hsourceB e₁ idx₁ pos₁ n₁ he₁ hp₁ hn₁
      have hsep := opposite_cause_entry_slots_disjoint spine inputA.length _ true
        (-run p inputA.length - Int.fdiv causeA.width 2) causeA.width causeA.height
        b.x n₁.width n₁.height hlengthA hslot.1 hslot.2.1
      rw [hrectA]
      simpa only [Disjoint, Rect.meetsInterior, hbw, hbh, hby, hu, hl,
        Bool.not_true, ↓reduceIte] using hsep
  · have hslotA := generated_found_entry_slot_bounds ns p raw hrun ribs hg
      sourceA hsourceA e₀ idx₀ pos₀ n₀ he₀ hp₀ hn₀
    rcases hpb with ⟨causeB, _, _, hrectB⟩ |
      ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, _, hn₁, hbw, hbh, hby⟩
    · have hsep := opposite_cause_entry_slots_disjoint spine inputB.length _ false
        (-run p inputB.length - Int.fdiv causeB.width 2) causeB.width causeB.height
        a.x n₀.width n₀.height hlengthB hslotA.1 hslotA.2.1
      apply (Disjoint.comm _ _).mpr
      rw [hrectB]
      simpa only [Disjoint, Rect.meetsInterior, haw, hah, hay, hu, hl,
        Bool.not_false, ↓reduceIte] using hsep
    · have hslotB := generated_found_entry_slot_bounds ns p raw hrun ribs hg
        sourceB hsourceB e₁ idx₁ pos₁ n₁ he₁ hp₁ hn₁
      have hsep := opposite_entry_slots_disjoint spine _ _ a.x n₀.width n₀.height
        b.x n₁.width n₁.height hslotA.1 hslotB.1 hslotA.2.1 hslotB.2.1
      simpa only [Disjoint, Rect.meetsInterior, haw, hah, hay, hbw, hbh, hby,
        hu, hl] using hsep

private theorem separation_bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem place_upper_eq (ns : List Tree.Node) (p : Params) (spine : Int)
    (input placed : Rib) (hrun : place ns p spine input = .ok placed) :
    placed.upper = input.upper := by
  simp only [place] at hrun
  cases hcause : ns[input.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, _, hret⟩ := separation_bind_ok hrun
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
    cases hret
    rfl

theorem placed_rib_index_upper (ns : List Tree.Node) (p : Params)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (k : Nat) (rib : Rib) (hrib : placed[k]? = some rib) :
    rib.upper = upper k := by
  obtain ⟨source, hsource, hplace⟩ :=
    (Elegant.Kinds.Gitgraph.mapM_index_record _ _ _ hplaces).2 k rib hrib
  rw [hg, List.getElem?_map, List.getElem?_zipIdx] at hsource
  cases hcause : (children ns 0)[k]? with
  | none =>
    simp only [hcause, Option.map_none] at hsource
    cases hsource
  | some cause =>
    simp only [hcause, Option.map_some, Nat.zero_add, Option.some.injEq] at hsource
    subst source
    exact (place_upper_eq ns p spine _ rib hplace).trans
      (generated_rib_fields ns cause k).2.1

theorem placed_adjacent_ribs_alternate (ns : List Tree.Node) (p : Params)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (k : Nat) (a b : Rib) (ha : placed[k]? = some a)
    (hb : placed[k + 1]? = some b) : b.upper = !a.upper := by
  rw [placed_rib_index_upper ns p ribs placed spine hg hplaces k a ha,
    placed_rib_index_upper ns p ribs placed spine hg hplaces (k + 1) b hb]
  exact ishikawa_causes_alternate_next k

theorem placed_opposite_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (ribA ribB : Rib) (hribA : ribA ∈ placed) (hribB : ribB ∈ placed)
    (hu : ribA.upper = true) (hl : ribB.upper = false)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ ribA.pieces)
    (hb : (j, b, pointsB) ∈ ribB.pieces) : Disjoint a b := by
  obtain ⟨sourceA, _, _, hsA, _, _, hpA⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces ribA hribA
  obtain ⟨sourceB, _, _, hsB, _, _, hpB⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces ribB hribB
  have huA : sourceA.upper = true := (place_upper_eq ns p spine _ ribA hpA).symm.trans hu
  have hlB : sourceB.upper = false := (place_upper_eq ns p spine _ ribB hpB).symm.trans hl
  exact generated_opposite_pieces_disjoint ns p raw hrun ribs hg sourceA sourceB
    hsA hsB huA hlB spine ribA ribB hpA hpB i j a b pointsA pointsB ha hb

theorem placed_same_rib_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (rib : Rib) (hrib : rib ∈ placed)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ rib.pieces)
    (hb : (j, b, pointsB) ∈ rib.pieces) (hne : i ≠ j) : Disjoint a b := by
  obtain ⟨source, _, _, hs, _, _, hp⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  exact generated_place_pieces_disjoint ns p raw hrun ribs hg source hs spine rib hp
    i j a b pointsA pointsB ha hb hne

theorem placed_different_side_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (ribA ribB : Rib) (hribA : ribA ∈ placed) (hribB : ribB ∈ placed)
    (hopposite : ribA.upper ≠ ribB.upper)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ ribA.pieces)
    (hb : (j, b, pointsB) ∈ ribB.pieces) : Disjoint a b := by
  cases hu : ribA.upper <;> cases hl : ribB.upper
  · exact False.elim (hopposite (hu.trans hl.symm))
  · apply (Disjoint.comm _ _).mpr
    exact placed_opposite_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
      ribB ribA hribB hribA hl hu j i b a pointsB pointsA hb ha
  · exact placed_opposite_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
      ribA ribB hribA hribB hu hl i j a b pointsA pointsB ha hb
  · exact False.elim (hopposite (hu.trans hl.symm))

theorem placed_current_pair_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (offset : Nat) (first : Rib) (rest : List Rib)
    (hsuffix : placed.drop offset = first :: rest)
    (ribA ribB : Rib) (hribA : ribA ∈ first :: rest.take 1)
    (hribB : ribB ∈ first :: rest.take 1)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ ribA.pieces)
    (hb : (j, b, pointsB) ∈ ribB.pieces) (hne : i ≠ j) : Disjoint a b := by
  have hfirst : placed[offset]? = some first := by
    have h : (placed.drop offset)[0]? = some first := by rw [hsuffix]; rfl
    simpa only [List.getElem?_drop, Nat.add_zero] using h
  have hmfirst := List.mem_of_getElem? hfirst
  cases rest with
  | nil =>
    have hA : ribA = first := by simpa using hribA
    have hB : ribB = first := by simpa using hribB
    subst ribA; subst ribB
    exact placed_same_rib_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
      first hmfirst i j a b pointsA pointsB ha hb hne
  | cons second tail =>
    have hsecond : placed[offset + 1]? = some second := by
      have h : (placed.drop offset)[1]? = some second := by rw [hsuffix]; rfl
      simpa only [List.getElem?_drop] using h
    have hmsecond := List.mem_of_getElem? hsecond
    have halt := placed_adjacent_ribs_alternate ns p ribs placed spine hg hplaces
      offset first second hfirst hsecond
    have hdiff : first.upper ≠ second.upper := by
      rw [halt]
      cases first.upper <;> decide
    have hA : ribA = first ∨ ribA = second := by simpa using hribA
    have hB : ribB = first ∨ ribB = second := by simpa using hribB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    all_goals
      rw [hA] at ha
      rw [hB] at hb
    · exact placed_same_rib_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
        first hmfirst i j a b pointsA pointsB ha hb hne
    · exact placed_different_side_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
        first second hmfirst hmsecond hdiff i j a b pointsA pointsB ha hb
    · exact placed_different_side_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
        second first hmsecond hmfirst (Ne.symm hdiff) i j a b pointsA pointsB ha hb
    · exact placed_same_rib_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
        second hmsecond i j a b pointsA pointsB ha hb hne

theorem placed_piece_nonnegative (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (rib : Rib) (hrib : rib ∈ placed)
    (piece : Nat × Rect × List Point) (hm : piece ∈ rib.pieces) :
    0 ≤ piece.2.1.w ∧ 0 ≤ piece.2.1.h := by
  obtain ⟨source, _, _, _, _, _, hp⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  apply Elegant.Ishikawa.placed_piece_nonnegative ns p spine _ rib ?_ hp piece hm
  intro n hn
  have hd := successful_node_dimensions ns p raw hrun n hn
  constructor <;> omega

theorem assembly_shift_cons_cases (first : Rib) (rest : List Rib)
    (ceiling previous : Int) (rib : Rib) (dx : Int)
    (h : AssemblyPairShift (first :: rest) ceiling previous rib dx) :
    (rib ∈ first :: rest.take 1 ∧
      dx = min ceiling (previous - (extent (first :: rest.take 1)).2)) ∨
    AssemblyPairShift (rest.drop 1)
      (min ceiling (previous - (extent (first :: rest.take 1)).2) +
        (extent (first :: rest.take 1)).1)
      (min ceiling (previous - (extent (first :: rest.take 1)).2) +
        (extent (first :: rest.take 1)).1) rib dx := by
  cases h with
  | current _ _ _ _ _ hm => exact Or.inl ⟨hm, rfl⟩
  | later _ _ _ _ _ _ ht => exact Or.inr ht

theorem assembly_shift_pieces_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    {rs : List Rib} {ceiling previous : Int} {ribA : Rib} {dxA : Int}
    (hshiftA : AssemblyPairShift rs ceiling previous ribA dxA) :
    ∀ (offset : Nat), placed.drop offset = rs →
    ∀ (ribB : Rib) (dxB : Int), AssemblyPairShift rs ceiling previous ribB dxB →
    ∀ (i j : Nat) (a b : Rect) (pointsA pointsB : List Point),
      (i, a, pointsA) ∈ ribA.pieces → (j, b, pointsB) ∈ ribB.pieces →
      i ≠ j →
      Disjoint { a with x := a.x + dxA } { b with x := b.x + dxB } := by
  induction hshiftA with
  | current first rest ceiling previous ribA hribA =>
    intro offset hsuffix ribB dxB hshiftB i j a b pointsA pointsB ha hb hne
    rcases assembly_shift_cons_cases first rest ceiling previous ribB dxB hshiftB with
      ⟨hribB, hdxB⟩ | htailB
    · have hsep := placed_current_pair_pieces_disjoint ns p raw hrun ribs placed spine
        hg hplaces offset first rest hsuffix ribA ribB hribA hribB
        i j a b pointsA pointsB ha hb hne
      rw [hdxB]
      simpa only [Rect.translateRaw, Int.add_zero] using
        Tree.disjoint_translate_raw hsep
          (min ceiling (previous - (extent (first :: rest.take 1)).2)) 0
    · have hsuffixTail : placed.drop (offset + 2) = rest.drop 1 := by
        rw [← List.drop_drop, hsuffix]
        rfl
      have hwidth : ∀ rib ∈ rest.drop 1, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
        intro rib hr q hq
        have hr' : rib ∈ placed := by
          apply List.mem_of_mem_drop
          rw [hsuffixTail]
          exact hr
        exact (placed_piece_nonnegative ns p raw hrun ribs placed spine hg hplaces
          rib hr' q hq).1
      have hright := assembly_shift_piece_right htailB hwidth (j, b, pointsB) hb
      have hleft := (extent_piece_bounds (first :: rest.take 1) (i, a, pointsA)
        (List.mem_flatMap.mpr ⟨ribA, hribA, ha⟩)).1
      dsimp only at hright hleft
      apply (Disjoint.comm _ _).mpr
      exact rib_piece_left_of_root b.x b.w dxB
        (min ceiling (previous - (extent (first :: rest.take 1)).2) +
          (extent (first :: rest.take 1)).1)
        (a.x + min ceiling (previous - (extent (first :: rest.take 1)).2)) a.w
        b.y b.h a.y a.h hright (by omega)
  | later first rest ceiling previous ribA dxA htailA ih =>
    intro offset hsuffix ribB dxB hshiftB i j a b pointsA pointsB ha hb hne
    have hsuffixTail : placed.drop (offset + 2) = rest.drop 1 := by
      rw [← List.drop_drop, hsuffix]
      rfl
    rcases assembly_shift_cons_cases first rest ceiling previous ribB dxB hshiftB with
      ⟨hribB, hdxB⟩ | htailB
    · have hwidth : ∀ rib ∈ rest.drop 1, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
        intro rib hr q hq
        have hr' : rib ∈ placed := by
          apply List.mem_of_mem_drop
          rw [hsuffixTail]
          exact hr
        exact (placed_piece_nonnegative ns p raw hrun ribs placed spine hg hplaces
          rib hr' q hq).1
      have hright := assembly_shift_piece_right htailA hwidth (i, a, pointsA) ha
      have hleft := (extent_piece_bounds (first :: rest.take 1) (j, b, pointsB)
        (List.mem_flatMap.mpr ⟨ribB, hribB, hb⟩)).1
      dsimp only at hright hleft
      rw [hdxB]
      exact rib_piece_left_of_root a.x a.w dxA
        (min ceiling (previous - (extent (first :: rest.take 1)).2) +
          (extent (first :: rest.take 1)).1)
        (b.x + min ceiling (previous - (extent (first :: rest.take 1)).2)) b.w
        a.y a.h b.y b.h hright (by omega)
    · exact ih (offset + 2) hsuffixTail ribB dxB htailB i j a b
        pointsA pointsB ha hb hne

theorem initial_box_cases (count k : Nat) (root box : Rect)
    (h : ((List.replicate count (⟨0, 0, 0, 0⟩ : Rect)).set 0 root)[k]? = some box) :
    (k = 0 ∧ box = root) ∨ box = ⟨0, 0, 0, 0⟩ := by
  cases count with
  | zero => simp at h
  | succ count =>
    cases k with
    | zero =>
      have he : root = box := by simpa using h
      exact Or.inl ⟨rfl, he.symm⟩
    | succ k =>
      change (List.replicate count (⟨0, 0, 0, 0⟩ : Rect))[k]? = some box at h
      exact Or.inr (by simpa using (List.mem_replicate.mp (List.mem_of_getElem? h)).2)

theorem successful_raw_boxes_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (i j : Nat) (a b : Rect) (ha : raw.boxes[i]? = some a)
    (hb : raw.boxes[j]? = some b) (hne : i ≠ j) : Disjoint a b := by
  rcases layout_origin ns p raw hrun with ⟨_, hraw⟩ | horigin
  · rw [hraw] at ha
    cases ha
  · rcases horigin with
      ⟨ribs, length, spine, placed, head, hg, hlength, _, hplaces, _, hassemble⟩
    subst length
    let root : Rect := ⟨0, spine - Int.fdiv head.height 2, head.width, head.height⟩
    let initial : Tree.Layout :=
      ⟨(List.replicate ns.length (⟨0, 0, 0, 0⟩ : Rect)).set 0 root,
        List.replicate ns.length []⟩
    have hwidth : ∀ rib ∈ placed, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
      intro rib hr q hq
      exact (placed_piece_nonnegative ns p raw hrun ribs placed spine hg hplaces
        rib hr q hq).1
    have hA := assemblePairs_box_origin spine placed (-p.inset) 0 initial raw
      hassemble i a ha
    have hB := assemblePairs_box_origin spine placed (-p.inset) 0 initial raw
      hassemble j b hb
    rcases hA with hinitA | ⟨ribA, originalA, pointsA, dxA, hshiftA, hmA, hrectA⟩
    · rcases initial_box_cases ns.length i root a hinitA with ⟨hi, hrootA⟩ | hzeroA
      · rcases hB with hinitB | ⟨ribB, originalB, pointsB, dxB, hshiftB, hmB, hrectB⟩
        · rcases initial_box_cases ns.length j root b hinitB with ⟨hj, _⟩ | hzeroB
          · exact False.elim (hne (hi.trans hj.symm))
          · rw [hzeroB]
            apply (Disjoint.comm _ _).mpr
            exact Elegant.Kinds.Gitgraph.disjoint_of_flat (Or.inl rfl)
        · rw [hrootA, hrectB]
          apply (Disjoint.comm _ _).mpr
          exact assembly_shift_piece_disjoint_root hshiftB hwidth
            (j, originalB, pointsB) hmB _ _ _
      · rw [hzeroA]
        exact Elegant.Kinds.Gitgraph.disjoint_of_flat (Or.inl rfl)
    · rcases hB with hinitB | ⟨ribB, originalB, pointsB, dxB, hshiftB, hmB, hrectB⟩
      · rcases initial_box_cases ns.length j root b hinitB with ⟨_, hrootB⟩ | hzeroB
        · rw [hrectA, hrootB]
          exact assembly_shift_piece_disjoint_root hshiftA hwidth
            (i, originalA, pointsA) hmA _ _ _
        · rw [hzeroB]
          apply (Disjoint.comm _ _).mpr
          exact Elegant.Kinds.Gitgraph.disjoint_of_flat (Or.inl rfl)
      · rw [hrectA, hrectB]
        exact assembly_shift_pieces_disjoint ns p raw hrun ribs placed spine hg hplaces
          hshiftA 0 rfl ribB dxB hshiftB i j originalA originalB pointsA pointsB hmA hmB hne

theorem successful_normalized_boxes_disjoint (ns : List Tree.Node) (p : Params)
    (raw normalized : Tree.Layout) (canvas : Size) (margin : Int)
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (hnormalize : Tree.normalize margin raw = .ok (canvas, normalized))
    (i j : Nat) (a b : Rect) (ha : normalized.boxes[i]? = some a)
    (hb : normalized.boxes[j]? = some b) (hne : i ≠ j) : Disjoint a b := by
  obtain ⟨dx, dy, hboxes, _⟩ := Tree.normalize_records hnormalize
  rw [hboxes, List.getElem?_map, Option.map_eq_some_iff] at ha hb
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  exact Tree.disjoint_translate_raw
    (successful_raw_boxes_disjoint ns p raw hrun i j a₀ b₀ ha₀ hb₀ hne) dx dy

def SceneBoxOrigin (m : Model) (normalized : Tree.Layout) (box : Box) : Prop :=
  ∃ (i : Nat) (source : ModelBox), m.boxes[i]? = some source ∧ box.id = source.id ∧
    ((box.rect.w = 0 ∨ box.rect.h = 0) ∨
      box.rect = (normalized.boxes[i]?).getD ⟨0, 0, 0, 0⟩)

theorem scene_origins_set (m : Model) (normalized : Tree.Layout)
    (boxes : List Box) (i : Nat) (replacement : Box)
    (hboxes : ∀ box ∈ boxes, SceneBoxOrigin m normalized box)
    (hrep : SceneBoxOrigin m normalized replacement) :
    ∀ box ∈ boxes.set i replacement, SceneBoxOrigin m normalized box := by
  induction boxes generalizing i with
  | nil => simp
  | cons first rest ih =>
    cases i with
    | zero =>
      intro box hb
      change box ∈ replacement :: rest at hb
      rcases List.mem_cons.mp hb with he | hb
      · subst box; exact hrep
      · exact hboxes box (List.mem_cons_of_mem first hb)
    | succ i =>
      intro box hb
      change box ∈ first :: rest.set i replacement at hb
      rcases List.mem_cons.mp hb with he | hb
      · subst box; exact hboxes first (List.mem_cons_self ..)
      · exact ih i (fun b hb => hboxes b (List.mem_cons_of_mem first hb)) box hb

theorem successful_scene_box_origins_decoded (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    ∃ (input : Elegant.Kinds.Ishikawa.Input) (raw normalized : Tree.Layout) (canvas : Size),
      Elegant.Kinds.Ishikawa.decode m = .ok input ∧
      Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
      Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
      ∀ box ∈ s.boxes, SceneBoxOrigin m normalized box := by
  unfold Elegant.Kinds.Ishikawa.scene at hs
  obtain ⟨input, hinput, hs⟩ := separation_bind_ok hs
  obtain ⟨raw, hraw, hs⟩ := separation_bind_ok hs
  obtain ⟨pair, hnormalize, hs⟩ := separation_bind_ok hs
  obtain ⟨boxes, hboxes, hs⟩ := separation_bind_ok hs
  have hinitial : ∀ box ∈ boxes, SceneBoxOrigin m pair.2 box := by
    apply Elegant.forIn_processed [] _ _ _ _
      (fun _ state => ∀ box ∈ state, SceneBoxOrigin m pair.2 box) (by simp) ?_ hboxes
    intro done entry rest state next hpartition hinv hstep
    rcases entry with ⟨source, i⟩
    have hmember : (source, i) ∈ m.boxes.zipIdx := by
      have heq : m.boxes.zipIdx = done ++ (source, i) :: rest := by simpa using hpartition
      simp [heq]
    have hlookup := List.mem_zipIdx_iff_getElem?.mp hmember
    simp only [pure, Except.pure, Except.ok.injEq] at hstep
    subst next
    refine ⟨_, rfl, ?_⟩
    intro box hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | hb
    · exact hinv box hb
    · subst box
      exact ⟨i, source, hlookup, rfl, Or.inr rfl⟩
  obtain ⟨triple, hloop, hrest⟩ := separation_bind_ok hs
  have hfinal : ∀ box ∈ triple.1, SceneBoxOrigin m pair.2 box := by
    apply Elegant.forIn_processed [] _ _ _ _
      (fun _ state => ∀ box ∈ state.1, SceneBoxOrigin m pair.2 box) hinitial ?_ hloop
    intro done entry rest state next _ hinv hstep
    rcases entry with ⟨route, j⟩
    cases hfind : (m.boxes.take input.nodes.length).findIdx? (·.id == route.toId) with
    | none => simp only [hfind, bind, Except.bind] at hstep; cases hstep
    | some k =>
      cases hdepth : input.depths[k]? with
      | none => simp only [hfind, hdepth, bind, Except.bind] at hstep; cases hstep
      | some depth =>
        by_cases horth : (!Elegant.Kinds.Ishikawa.consistentOrthogonal depth route.orthogonal) = true
        · simp only [hfind, hdepth, horth, bind, Except.bind, ite_true] at hstep
          cases hstep
        · cases hanchor : state.1[input.nodes.length + j]? with
          | none =>
            simp only [hfind, hdepth, horth, hanchor, bind, Except.bind] at hstep
            cases hstep
          | some anchor =>
            cases hpoints : pair.2.routes[k]? with
            | none =>
              simp only [hfind, hdepth, horth, hanchor, hpoints, bind, Except.bind] at hstep
              cases hstep
            | some points =>
              cases points with
              | nil =>
                simp only [hfind, hdepth, horth, hanchor, hpoints, bind, Except.bind] at hstep
                cases hstep
              | cons first tail =>
                cases tail with
                | nil =>
                  simp only [hfind, hdepth, horth, hanchor, hpoints, bind, Except.bind] at hstep
                  cases hstep
                | cons second remaining =>
                  by_cases hid : (anchor.id != route.fromId) = true
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      bind, Except.bind, ite_true] at hstep
                    cases hstep
                  · simp only [hfind, hdepth, horth, hanchor, hpoints, hid,
                      Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
                      Except.ok.injEq] at hstep
                    subst next
                    refine ⟨_, rfl, ?_⟩
                    apply scene_origins_set m pair.2 state.1 _ _ hinv
                    obtain ⟨i, source, hsource, hsid, _⟩ :=
                      hinv anchor (List.mem_of_getElem? hanchor)
                    exact ⟨i, source, hsource, hsid, Or.inl (Or.inl rfl)⟩
  obtain ⟨groups, _, hret⟩ := separation_bind_ok hrest
  simp only [pure, Except.pure, Except.ok.injEq] at hret
  subst s
  exact ⟨input, raw, pair.2, pair.1, hinput, hraw, hnormalize, hfinal⟩

theorem successful_scene_box_origins (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    ∃ (nodes : List Tree.Node) (raw normalized : Tree.Layout) (canvas : Size),
      Elegant.Ishikawa.layout nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
      Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
      ∀ box ∈ s.boxes, SceneBoxOrigin m normalized box := by
  obtain ⟨input, raw, normalized, canvas, hinput, hraw, hnormal, hboxes⟩ :=
    successful_scene_box_origins_decoded m s hs
  exact ⟨input.nodes, raw, normalized, canvas, hraw, hnormal, hboxes⟩

theorem successful_scene_native_sources (m : Model) (s : Scene) (hwf : WellFormed m)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) :
    ∃ (input : Elegant.Kinds.Ishikawa.Input) (raw normalized : Tree.Layout) (canvas : Size),
      Elegant.Kinds.Ishikawa.decode m = .ok input ∧
      Elegant.Ishikawa.layout input.nodes (Elegant.Kinds.Ishikawa.params m.profile) = .ok raw ∧
      Tree.normalize (LayoutConst.canvas_margin.get m.profile) raw = .ok (canvas, normalized) ∧
      (∀ box ∈ s.boxes, SceneBoxOrigin m normalized box) ∧
      (∀ route ∈ s.routes,
        Elegant.Kinds.IshikawaValid.SceneRouteNativeSource m input normalized route) := by
  obtain ⟨_, inputR, rawR, normalizedR, canvasR, hinputR, hrawR, hnormalR, hroutes⟩ :=
    Elegant.Kinds.IshikawaValid.successful_scene_c5_sources m s hwf hs
  obtain ⟨inputB, rawB, normalizedB, canvasB, hinputB, hrawB, hnormalB, hboxes⟩ :=
    successful_scene_box_origins_decoded m s hs
  have hinput : inputR = inputB := Except.ok.inj (hinputR.symm.trans hinputB)
  subst inputB
  have hraw : rawR = rawB := Except.ok.inj (hrawR.symm.trans hrawB)
  subst rawB
  have hpair : (canvasR, normalizedR) = (canvasB, normalizedB) :=
    Except.ok.inj (hnormalR.symm.trans hnormalB)
  have hcanvas : canvasR = canvasB := congrArg Prod.fst hpair
  have hnormalized : normalizedR = normalizedB := congrArg Prod.snd hpair
  subst canvasB
  subst normalizedB
  exact ⟨inputR, rawR, normalizedR, canvasR, hinputR, hrawR, hnormalR, hboxes, hroutes⟩

theorem successful_scene_boxes_disjoint (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s)
    (a : Box) (ha : a ∈ s.boxes) (b : Box) (hb : b ∈ s.boxes)
    (hne : a.id ≠ b.id) : Disjoint a.rect b.rect := by
  obtain ⟨nodes, raw, normalized, canvas, hraw, hnormalize, horigins⟩ :=
    successful_scene_box_origins m s hs
  obtain ⟨i, sourceA, hsourceA, hidA, hrectA⟩ := horigins a ha
  obtain ⟨j, sourceB, hsourceB, hidB, hrectB⟩ := horigins b hb
  rcases hrectA with hflatA | hrectA
  · exact Elegant.Kinds.Gitgraph.disjoint_of_flat hflatA
  rcases hrectB with hflatB | hrectB
  · exact (Disjoint.comm _ _).mpr (Elegant.Kinds.Gitgraph.disjoint_of_flat hflatB)
  have hindices : i ≠ j := by
    intro he
    subst j
    have hsource : sourceA = sourceB :=
      Option.some.inj (hsourceA.symm.trans hsourceB)
    exact hne (hidA.trans ((congrArg ModelBox.id hsource).trans hidB.symm))
  cases hlookupA : normalized.boxes[i]? with
  | none =>
    have hzero : a.rect = ⟨0, 0, 0, 0⟩ := by
      simpa only [hlookupA, Option.getD_none] using hrectA
    rw [hzero]
    exact Elegant.Kinds.Gitgraph.disjoint_of_flat (Or.inl rfl)
  | some rectA =>
    have heqA : a.rect = rectA := by
      simpa only [hlookupA, Option.getD_some] using hrectA
    cases hlookupB : normalized.boxes[j]? with
    | none =>
      have hzero : b.rect = ⟨0, 0, 0, 0⟩ := by
        simpa only [hlookupB, Option.getD_none] using hrectB
      rw [hzero]
      exact (Disjoint.comm _ _).mpr
        (Elegant.Kinds.Gitgraph.disjoint_of_flat (Or.inl rfl))
    | some rectB =>
      have heqB : b.rect = rectB := by
        simpa only [hlookupB, Option.getD_some] using hrectB
      rw [heqA, heqB]
      exact successful_normalized_boxes_disjoint nodes
        (Elegant.Kinds.Ishikawa.params m.profile) raw normalized canvas
        (LayoutConst.canvas_margin.get m.profile) hraw hnormalize
        i j rectA rectB hlookupA hlookupB hindices

theorem successful_scene_c2 (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) : Validator.C2 s.layoutDump := by
  intro a ha b hb hne _ _ _
  exact successful_scene_boxes_disjoint m s hs a ha b hb hne

theorem successful_scene_c8a (m : Model) (s : Scene)
    (hs : Elegant.Kinds.Ishikawa.scene m = .ok s) : Validator.C8a s.layoutDump := by
  intro group hg _ box hb hne _ _
  exact successful_scene_boxes_disjoint m s hs group hg box hb (Ne.symm hne)

theorem ishikawa_c2 (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (hlayout : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := Elegant.Kinds.Ishikawa.layout_success_scene m result hlayout
  rw [hdump]
  exact successful_scene_c2 m s hs

theorem ishikawa_c8a (m : Model) (result : Layered.FamilyResult)
    (_wf : WellFormed m) (_limits : WithinLimits m)
    (hlayout : Elegant.Kinds.Ishikawa.layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := Elegant.Kinds.Ishikawa.layout_success_scene m result hlayout
  rw [hdump]
  exact successful_scene_c8a m s hs

end Elegant.Kinds.IshikawaSeparation
