import Elegant.Ishikawa
import Elegant.ForInFacts
import Elegant.IshikawaAssemblyBoxFacts

set_option autoImplicit false

namespace Elegant.Ishikawa

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem place_piece_dimensions (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib)
    (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      ∃ n, ns[i]? = some n ∧ rect.w = n.width ∧ rect.h = n.height := by
  simp only [place] at hrun
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, hloop, hret⟩ := bind_ok hrun
    have hout : placed = { r with pieces := mid.1 } := by
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
      exact hret.symm
    have hinv : ∀ i rect points, (i, rect, points) ∈ mid.1 →
        ∃ n, ns[i]? = some n ∧ rect.w = n.width ∧ rect.h = n.height := by
      apply Elegant.forIn_processed [] _ _ _ _
        (fun _ st => ∀ i rect points, (i, rect, points) ∈ st.1 →
          ∃ n, ns[i]? = some n ∧ rect.w = n.width ∧ rect.h = n.height)
        ?_ ?_ hloop
      · intro i rect points hm
        simp at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        exact ⟨cause, hcause, rfl, rfl⟩
      · intro done a rest state next _ hi hstep
        obtain ⟨e, idx⟩ := a
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          cases hpos : r.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            by_cases hg : ((e.depth % 2 == 0) && decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some n =>
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  refine ⟨_, rfl, ?_⟩
                  intro i rect points hm
                  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
                  rcases hm with hm | ⟨rfl, rfl, rfl⟩
                  · exact hi i rect points hm
                  · exact ⟨n, hn, rfl, rfl⟩
    subst placed
    exact hinv

theorem placed_piece_nonnegative (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib)
    (hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height)
    (hrun : place ns p spine r = .ok placed)
    (piece : Nat × Rect × List Point) (hm : piece ∈ placed.pieces) :
    0 ≤ piece.2.1.w ∧ 0 ≤ piece.2.1.h := by
  obtain ⟨n, hn, hw, hh⟩ :=
    place_piece_dimensions ns p spine r placed hrun piece.1 piece.2.1 piece.2.2 hm
  obtain ⟨nw, nh⟩ := hdims n (List.mem_of_getElem? hn)
  simpa only [hw, hh] using And.intro nw nh

theorem extent_ordered (rs : List Rib)
    (hwidth : ∀ piece ∈ rs.flatMap (·.pieces), 0 ≤ piece.2.1.w) :
    (extent rs).1 ≤ (extent rs).2 := by
  cases he : rs.flatMap (·.pieces) with
  | nil => simp [extent, he]
  | cons piece rest =>
    have hm : piece ∈ rs.flatMap (·.pieces) := by rw [he]; exact List.mem_cons_self ..
    obtain ⟨hl, hr⟩ := extent_piece_bounds rs piece hm
    have hw := hwidth piece hm
    omega

theorem placed_extent_ordered (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib)
    (hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height)
    (hrun : place ns p spine r = .ok placed) :
    (extent [placed]).1 ≤ (extent [placed]).2 := by
  apply extent_ordered
  intro piece hm
  have hm' : piece ∈ placed.pieces := by simpa using hm
  exact (placed_piece_nonnegative ns p spine r placed hdims hrun piece hm').1

theorem pair_frontier_antitone (rs : List Rib) (ceiling previous : Int)
    (hwidth : ∀ piece ∈ rs.flatMap (·.pieces), 0 ≤ piece.2.1.w) :
    min ceiling (previous - (extent rs).2) + (extent rs).1 ≤ previous := by
  have horder := extent_ordered rs hwidth
  have hreach := pair_reach_before_previous ceiling previous (extent rs).2
  omega

theorem placed_pair_frontier_antitone (ns : List Tree.Node) (p : Params)
    (spine : Int) (a b placedA placedB : Rib)
    (hdims : ∀ n ∈ ns, 0 ≤ n.width ∧ 0 ≤ n.height)
    (ha : place ns p spine a = .ok placedA)
    (hb : place ns p spine b = .ok placedB)
    (ceiling previous : Int) :
    min ceiling (previous - (extent [placedA, placedB]).2) +
      (extent [placedA, placedB]).1 ≤ previous := by
  apply pair_frontier_antitone
  intro piece hm
  have hm' : piece ∈ placedA.pieces ∨ piece ∈ placedB.pieces := by
    simpa using hm
  rcases hm' with hm | hm
  · exact (placed_piece_nonnegative ns p spine a placedA hdims ha piece hm).1
  · exact (placed_piece_nonnegative ns p spine b placedB hdims hb piece hm).1

theorem successful_node_dimensions (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw) :
    ∀ n ∈ ns, 1 ≤ n.width ∧ 1 ≤ n.height := by
  cases ns with
  | nil => simp
  | cons first rest =>
    unfold layout at hrun
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hrun
    by_cases hbad : ((!Tree.link (first :: rest)) ||
        ((first :: rest).any fun n => n.width < 1 || n.height < 1)) = true
    · rw [ite_eq_left hbad] at hrun
      simp only [bind, Except.bind] at hrun
      cases hrun
    · intro n hn
      have hnot : ¬ (n.width < 1 ∨ n.height < 1) := by
        intro hnsmall
        apply hbad
        have hany : ((first :: rest).any fun n => n.width < 1 || n.height < 1) = true := by
          apply List.any_eq_true.mpr
          refine ⟨n, hn, ?_⟩
          simpa only [Bool.or_eq_true, decide_eq_true_eq] using hnsmall
        simp only [hany, Bool.or_true]
      omega

theorem successful_placed_piece_dimensions (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (spine : Int) (r placed : Rib) (hplace : place ns p spine r = .ok placed)
    (piece : Nat × Rect × List Point) (hm : piece ∈ placed.pieces) :
    1 ≤ piece.2.1.w ∧ 1 ≤ piece.2.1.h := by
  obtain ⟨n, hn, hw, hh⟩ :=
    place_piece_dimensions ns p spine r placed hplace piece.1 piece.2.1 piece.2.2 hm
  have hd := successful_node_dimensions ns p raw hrun n (List.mem_of_getElem? hn)
  simpa only [hw, hh] using hd

theorem entry_height_fold_initial (ns : List Tree.Node) (entries : List Entry)
    (initial : Int) :
    initial ≤ entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) initial := by
  induction entries generalizing initial with
  | nil => exact Int.le_refl _
  | cons e entries ih =>
    exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem entry_height_fold_bound (ns : List Tree.Node) (entries : List Entry)
    (initial : Int) (e : Entry) (he : e ∈ entries) :
    (((ns[e.node]?).map (·.height)).getD 0) ≤
      entries.foldl (fun h e =>
        max h (((ns[e.node]?).map (·.height)).getD 0)) initial := by
  induction entries generalizing initial with
  | nil => simp at he
  | cons first entries ih =>
    rcases List.mem_cons.mp he with hfirst | hrest
    · subst e
      exact Int.le_trans (Int.le_max_right _ _)
        (entry_height_fold_initial ns entries _)
    · exact ih _ hrest

theorem measured_entry_height_bound (ns : List Tree.Node) (entries : List Entry)
    (e : Entry) (he : e ∈ entries) (n : Tree.Node) (hn : ns[e.node]? = some n) :
    n.height ≤ entries.foldl (fun h e =>
      max h (((ns[e.node]?).map (·.height)).getD 0)) 0 := by
  have h := entry_height_fold_bound ns entries 0 e he
  simpa only [hn, Option.map_some, Option.getD_some] using h

theorem rib_length_fold_initial (rs : List Rib) (spacing initial : Int) :
    initial ≤ rs.foldl (fun l r =>
      if r.entries.isEmpty then l else
        max l (max ((r.entries.length : Int) * spacing)
          ((r.entries.length + 1 : Nat) * r.heights))) initial := by
  induction rs generalizing initial with
  | nil => exact Int.le_refl _
  | cons r rs ih =>
    by_cases he : r.entries.isEmpty = true
    · simpa only [List.foldl_cons, he, ↓reduceIte] using ih initial
    · simp only [List.foldl_cons, he, Bool.false_eq_true, ↓reduceIte]
      exact Int.le_trans (Int.le_max_left _ _) (ih _)

theorem measured_rib_length_bound (rs : List Rib) (spacing initial : Int)
    (r : Rib) (hr : r ∈ rs) (hne : r.entries.isEmpty = false) :
    (r.entries.length + 1 : Nat) * r.heights ≤
      rs.foldl (fun l r =>
        if r.entries.isEmpty then l else
          max l (max ((r.entries.length : Int) * spacing)
            ((r.entries.length + 1 : Nat) * r.heights))) initial := by
  induction rs generalizing initial with
  | nil => simp at hr
  | cons first rs ih =>
    rcases List.mem_cons.mp hr with hfirst | hrest
    · subst r
      simp only [List.foldl_cons, hne, Bool.false_eq_true, ↓reduceIte]
      exact Int.le_trans
        (Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _))
        (rib_length_fold_initial rs spacing _)
    · exact ih _ hrest

theorem ordinal_slots_gap (length denominator height i j : Int)
    (hd : 0 < denominator) (hh : 0 ≤ height)
    (hl : denominator * height ≤ length) (hij : i + 1 ≤ j) :
    Int.fdiv (length * i) denominator + height ≤
      Int.fdiv (length * j) denominator := by
  have hl0 : 0 ≤ length :=
    Int.le_trans (Int.mul_nonneg (Int.le_of_lt hd) hh) hl
  have hquot := Int.ediv_le_ediv hd hl
  have hheight : height ≤ length / denominator := by
    simpa [Int.mul_comm, Int.ne_of_gt hd] using hquot
  have hadd := Int.ediv_add_ediv_le_add_ediv
    (x := length * i) (y := length) hd
  have hmul := Int.mul_le_mul_of_nonneg_left hij hl0
  have hmono := Int.ediv_le_ediv hd hmul
  rw [Int.mul_add, Int.mul_one] at hmono
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hd),
    Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hd)]
  omega

theorem measured_entry_slots_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (entries : List Entry) (e₀ e₁ : Entry)
    (he₀ : e₀ ∈ entries) (he₁ : e₁ ∈ entries)
    (n₀ n₁ : Tree.Node) (hn₀ : ns[e₀.node]? = some n₀)
    (hn₁ : ns[e₁.node]? = some n₁)
    (spine length i j x₀ x₁ : Int) (up : Bool)
    (hij : i + 1 ≤ j)
    (hl : (entries.length + 1 : Nat) *
      entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ length) :
    Disjoint
      ⟨x₀, ordinate spine up
        (Int.fdiv (length * i) (entries.length + 1 : Nat)) - Int.fdiv n₀.height 2,
        n₀.width, n₀.height⟩
      ⟨x₁, ordinate spine up
        (Int.fdiv (length * j) (entries.length + 1 : Nat)) - Int.fdiv n₁.height 2,
        n₁.width, n₁.height⟩ := by
  have hd₀ := successful_node_dimensions ns p raw hrun n₀ (List.mem_of_getElem? hn₀)
  have hd₁ := successful_node_dimensions ns p raw hrun n₁ (List.mem_of_getElem? hn₁)
  apply subcause_slots_disjoint
  · omega
  · omega
  · exact measured_entry_height_bound ns entries e₀ he₀ n₀ hn₀
  · exact measured_entry_height_bound ns entries e₁ he₁ n₁ hn₁
  · apply ordinal_slots_gap _ _ _ _ _ (by omega) ?_ hl hij
    exact entry_height_fold_initial ns entries 0

theorem depthBone_endpoint_slot (p : Params) (par : Bone) (depth : Nat)
    (t count margin : Int) :
    (depthBone p par depth t count margin).t1 = t := by
  unfold depthBone
  split <;> rfl

def PiecePlacement (ns : List Tree.Node) (spine : Int) (p : Params) (r : Rib)
    (i : Nat) (rect : Rect) : Prop :=
  (∃ n, ns[r.cause]? = some n ∧ i = r.cause ∧
    rect = ⟨-run p r.length - Int.fdiv n.width 2,
      if r.upper then ordinate spine r.upper r.length - n.height
      else ordinate spine r.upper r.length, n.width, n.height⟩) ∨
  ∃ e idx pos n, (e, idx) ∈ r.entries.zipIdx ∧
    r.order.zipIdx.find? (fun v => v.1 == idx) = some pos ∧
    i = e.node ∧ ns[e.node]? = some n ∧
    rect.w = n.width ∧ rect.h = n.height ∧
    rect.y = ordinate spine r.upper
      (Int.fdiv (r.length * (pos.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) -
        Int.fdiv n.height 2

theorem place_piece_placement (ns : List Tree.Node) (p : Params)
    (spine : Int) (r placed : Rib)
    (hrun : place ns p spine r = .ok placed) :
    ∀ i rect points, (i, rect, points) ∈ placed.pieces →
      PiecePlacement ns spine p r i rect := by
  simp only [place] at hrun
  cases hcause : ns[r.cause]? with
  | none => simp only [hcause] at hrun; cases hrun
  | some cause =>
    simp only [hcause] at hrun
    obtain ⟨mid, hloop, hret⟩ := bind_ok hrun
    have hout : placed = { r with pieces := mid.1 } := by
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hret
      exact hret.symm
    have hinv : ∀ i rect points, (i, rect, points) ∈ mid.1 →
        PiecePlacement ns spine p r i rect := by
      apply Elegant.forIn_processed [] _ _ _ _
        (fun _ st => ∀ i rect points, (i, rect, points) ∈ st.1 →
          PiecePlacement ns spine p r i rect) ?_ ?_ hloop
      · intro i rect points hm
        simp at hm
        obtain ⟨rfl, rfl, rfl⟩ := hm
        exact Or.inl ⟨cause, hcause, rfl, rfl⟩
      · intro done a rest state next hpartition hi hstep
        obtain ⟨e, idx⟩ := a
        have hea : (e, idx) ∈ r.entries.zipIdx := by
          have heq : r.entries.zipIdx = done ++ (e, idx) :: rest := by
            simpa using hpartition
          simp [heq]
        cases hpar : state.2[(e.parent + 1).toNat]? with
        | none => simp only [hpar, bind, Except.bind] at hstep; cases hstep
        | some par =>
          cases hpos : r.order.zipIdx.find? (fun v => v.1 == idx) with
          | none => simp only [hpar, hpos, bind, Except.bind] at hstep; cases hstep
          | some pos =>
            by_cases hg : ((e.depth % 2 == 0) && decide (par.t1 ≤ par.t0)) = true
            · simp only [hpar, hpos, hg, ite_true, bind, Except.bind] at hstep
              cases hstep
            · simp only [hpar, hpos, hg, Bool.false_eq_true, ↓reduceIte,
                bind, Except.bind] at hstep
              split at hstep
              all_goals
                cases hn : ns[e.node]? with
                | none => simp only [hn] at hstep; cases hstep
                | some n =>
                  simp only [hn, pure, Except.pure, Except.ok.injEq] at hstep
                  subst next
                  refine ⟨_, rfl, ?_⟩
                  intro i rect points hm
                  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
                  rcases hm with hm | ⟨rfl, rfl, rfl⟩
                  · exact hi i rect points hm
                  · apply Or.inr
                    refine ⟨e, idx, pos, n, hea, hpos, rfl, hn, rfl, rfl, ?_⟩
                    simp only [depthBone_endpoint_slot]
    subst placed
    exact hinv

theorem found_ordinal_injective (order : List Nat) (i j : Nat)
    (a b : Nat × Nat)
    (ha : order.zipIdx.find? (fun v => v.1 == i) = some a)
    (hb : order.zipIdx.find? (fun v => v.1 == j) = some b)
    (hne : i ≠ j) : a.2 ≠ b.2 := by
  have hai : a.1 = i := by simpa using List.find?_some ha
  have hbj : b.1 = j := by simpa using List.find?_some hb
  have hlookupA := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some ha)
  have hlookupB := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hb)
  intro he
  rw [he] at hlookupA
  have hab := Option.some.inj (hlookupA.symm.trans hlookupB)
  exact hne (hai.symm.trans (hab.trans hbj))

theorem entry_occurrence_indices_distinct (entries : List Entry)
    (a b : Entry) (i j : Nat)
    (ha : (a, i) ∈ entries.zipIdx) (hb : (b, j) ∈ entries.zipIdx)
    (hne : a.node ≠ b.node) : i ≠ j := by
  have hlookupA := List.mem_zipIdx_iff_getElem?.mp ha
  have hlookupB := List.mem_zipIdx_iff_getElem?.mp hb
  intro he
  subst j
  have hab := Option.some.inj (hlookupA.symm.trans hlookupB)
  exact hne (congrArg Entry.node hab)

theorem placed_entry_ordinals_distinct (ns : List Tree.Node) (p : Params)
    (spine : Int) (r : Rib) (i j : Nat) (a b : Rect)
    (ha : PiecePlacement ns spine p r i a)
    (hb : PiecePlacement ns spine p r j b)
    (hi : i ≠ r.cause) (hj : j ≠ r.cause) (hne : i ≠ j) :
    ∃ e₀ e₁ idx₀ idx₁ pos₀ pos₁,
      (e₀, idx₀) ∈ r.entries.zipIdx ∧
      (e₁, idx₁) ∈ r.entries.zipIdx ∧
      r.order.zipIdx.find? (fun v => v.1 == idx₀) = some pos₀ ∧
      r.order.zipIdx.find? (fun v => v.1 == idx₁) = some pos₁ ∧
      i = e₀.node ∧ j = e₁.node ∧ pos₀.2 ≠ pos₁.2 := by
  rcases ha with ⟨n, _, hic, _⟩ | ⟨e₀, idx₀, pos₀, n₀, he₀, hp₀, hi₀, _⟩
  · exact False.elim (hi hic)
  rcases hb with ⟨n, _, hjc, _⟩ | ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, hj₁, _⟩
  · exact False.elim (hj hjc)
  have hnodes : e₀.node ≠ e₁.node := by simpa only [hi₀, hj₁] using hne
  have hindices := entry_occurrence_indices_distinct r.entries e₀ e₁ idx₀ idx₁ he₀ he₁ hnodes
  exact ⟨e₀, e₁, idx₀, idx₁, pos₀, pos₁, he₀, he₁, hp₀, hp₁,
    hi₀, hj₁, found_ordinal_injective r.order idx₀ idx₁ pos₀ pos₁ hp₀ hp₁ hindices⟩

theorem placed_entries_disjoint (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (spine : Int) (r placed : Rib) (hplace : place ns p spine r = .ok placed)
    (hl : (r.entries.length + 1 : Nat) *
      r.entries.foldl (fun h e => max h (((ns[e.node]?).map (·.height)).getD 0)) 0 ≤ r.length)
    (i j : Nat) (a b : Rect) (pointsA pointsB : List Point)
    (ha : (i, a, pointsA) ∈ placed.pieces)
    (hb : (j, b, pointsB) ∈ placed.pieces)
    (hi : i ≠ r.cause) (hj : j ≠ r.cause) (hne : i ≠ j) : Disjoint a b := by
  have hpa := place_piece_placement ns p spine r placed hplace i a pointsA ha
  have hpb := place_piece_placement ns p spine r placed hplace j b pointsB hb
  rcases hpa with ⟨n, _, hic, _⟩ |
    ⟨e₀, idx₀, pos₀, n₀, he₀, hp₀, hi₀, hn₀, haw, hah, hay⟩
  · exact False.elim (hi hic)
  rcases hpb with ⟨n, _, hjc, _⟩ |
    ⟨e₁, idx₁, pos₁, n₁, he₁, hp₁, hj₁, hn₁, hbw, hbh, hby⟩
  · exact False.elim (hj hjc)
  have hnodes : e₀.node ≠ e₁.node := by simpa only [hi₀, hj₁] using hne
  have hindices := entry_occurrence_indices_distinct r.entries e₀ e₁ idx₀ idx₁ he₀ he₁ hnodes
  have hpos := found_ordinal_injective r.order idx₀ idx₁ pos₀ pos₁ hp₀ hp₁ hindices
  have hmem₀ : e₀ ∈ r.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he₀)
  have hmem₁ : e₁ ∈ r.entries :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp he₁)
  have hrectA : a = ⟨a.x, ordinate spine r.upper
      (Int.fdiv (r.length * (pos₀.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) -
        Int.fdiv n₀.height 2, n₀.width, n₀.height⟩ := by
    cases a with
    | mk ax ay aw ah =>
      simp only at haw hah hay
      subst aw; subst ah; subst ay
      rfl
  have hrectB : b = ⟨b.x, ordinate spine r.upper
      (Int.fdiv (r.length * (pos₁.2 + 1 : Nat)) (r.entries.length + 1 : Nat)) -
        Int.fdiv n₁.height 2, n₁.width, n₁.height⟩ := by
    cases b with
    | mk bx byy bw bh =>
      simp only at hbw hbh hby
      subst bw; subst bh; subst byy
      rfl
  by_cases horder : pos₀.2 < pos₁.2
  · have hsep := measured_entry_slots_disjoint ns p raw hrun r.entries e₀ e₁
      hmem₀ hmem₁ n₀ n₁ hn₀ hn₁ spine r.length (pos₀.2 + 1 : Nat)
      (pos₁.2 + 1 : Nat) a.x b.x r.upper (by omega) hl
    rw [hrectA, hrectB]
    exact hsep
  · have hsep := measured_entry_slots_disjoint ns p raw hrun r.entries e₁ e₀
      hmem₁ hmem₀ n₁ n₀ hn₁ hn₀ spine r.length (pos₁.2 + 1 : Nat)
      (pos₀.2 + 1 : Nat) b.x a.x r.upper (by omega) hl
    exact (Disjoint.comm b a).mp (by rw [hrectB, hrectA]; exact hsep)

theorem assembly_shift_piece_right {rs : List Rib} {ceiling previous : Int}
    {r : Rib} {dx : Int}
    (hshift : AssemblyPairShift rs ceiling previous r dx) :
    (∀ rib ∈ rs, ∀ piece ∈ rib.pieces, 0 ≤ piece.2.1.w) →
    ∀ piece ∈ r.pieces, piece.2.1.x + dx + piece.2.1.w ≤ previous := by
  induction hshift with
  | current a rest ceiling previous r hr =>
    intro _ piece hm
    exact ishikawa_ribs_ordered (a :: rest.take 1) ceiling previous piece
      (List.mem_flatMap.mpr ⟨r, hr, hm⟩)
  | later a rest ceiling previous r dx h ih =>
    intro hwidth piece hm
    have htail : ∀ rib ∈ rest.drop 1, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
      intro rib hr q hq
      exact hwidth rib (List.mem_cons_of_mem a (List.mem_of_mem_drop hr)) q hq
    have hright := ih htail piece hm
    have hfrontier := pair_frontier_antitone (a :: rest.take 1) ceiling previous
      (by
        intro q hq
        obtain ⟨rib, hr, hq⟩ := List.mem_flatMap.mp hq
        have hr' : rib ∈ a :: rest := by
          rcases List.mem_cons.mp hr with he | hr
          · exact List.mem_cons.mpr (Or.inl he)
          · exact List.mem_cons_of_mem a (List.mem_of_mem_take hr)
        exact hwidth rib hr' q hq)
    exact Int.le_trans hright hfrontier

theorem assembly_shift_piece_disjoint_root {rs : List Rib} {ceiling : Int}
    {r : Rib} {dx : Int} (hshift : AssemblyPairShift rs ceiling 0 r dx)
    (hwidth : ∀ rib ∈ rs, ∀ piece ∈ rib.pieces, 0 ≤ piece.2.1.w)
    (piece : Nat × Rect × List Point) (hm : piece ∈ r.pieces)
    (rootY rootW rootH : Int) :
    Disjoint { piece.2.1 with x := piece.2.1.x + dx }
      ⟨0, rootY, rootW, rootH⟩ := by
  exact rib_piece_left_of_root piece.2.1.x piece.2.1.w dx 0 0 rootW
    piece.2.1.y piece.2.1.h rootY rootH
    (assembly_shift_piece_right hshift hwidth piece hm) (Int.le_refl 0)

theorem ordinal_slot_inside (length denominator height k : Int)
    (hd : 0 < denominator) (hh : 0 ≤ height)
    (hl : denominator * height ≤ length)
    (hk : 1 ≤ k) (hk' : k + 1 ≤ denominator) :
    height ≤ Int.fdiv (length * k) denominator ∧
      Int.fdiv (length * k) denominator + height ≤ length := by
  have hfirst := ordinal_slots_gap length denominator height 0 k hd hh hl (by omega)
  have hlast := ordinal_slots_gap length denominator height k denominator hd hh hl hk'
  constructor
  · simpa using hfirst
  · simpa [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hd),
      Int.ne_of_gt hd] using hlast

theorem cause_entry_slots_disjoint (spine length t heightBound : Int) (up : Bool)
    (causeX causeW causeH entryX entryW entryH : Int)
    (hh : 0 ≤ entryH) (hbound : entryH ≤ heightBound)
    (ht : t + heightBound ≤ length) :
    Disjoint
      ⟨causeX, if up then ordinate spine up length - causeH
        else ordinate spine up length, causeW, causeH⟩
      ⟨entryX, ordinate spine up t - Int.fdiv entryH 2, entryW, entryH⟩ := by
  rw [Tree.fdiv2]
  cases up <;> simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega

theorem opposite_entry_slots_disjoint (spine upperT lowerT : Int)
    (upperX upperW upperH lowerX lowerW lowerH : Int)
    (hu : 0 ≤ upperH) (hl : 0 ≤ lowerH)
    (hut : upperH ≤ upperT) (hlt : lowerH ≤ lowerT) :
    Disjoint
      ⟨upperX, ordinate spine true upperT - Int.fdiv upperH 2, upperW, upperH⟩
      ⟨lowerX, ordinate spine false lowerT - Int.fdiv lowerH 2, lowerW, lowerH⟩ := by
  rw [Tree.fdiv2, Tree.fdiv2]
  simp [Disjoint, Rect.meetsInterior, ordinate]
  omega

theorem opposite_cause_entry_slots_disjoint (spine length t : Int) (causeUp : Bool)
    (causeX causeW causeH entryX entryW entryH : Int)
    (hl : 0 ≤ length) (hh : 0 ≤ entryH) (ht : entryH ≤ t) :
    Disjoint
      ⟨causeX, if causeUp then ordinate spine causeUp length - causeH
        else ordinate spine causeUp length, causeW, causeH⟩
      ⟨entryX, ordinate spine (!causeUp) t - Int.fdiv entryH 2, entryW, entryH⟩ := by
  rw [Tree.fdiv2]
  cases causeUp <;> simp [Disjoint, Rect.meetsInterior, ordinate] <;> omega

end Elegant.Ishikawa
