import Elegant.Kinds.IshikawaRawClearance
import Elegant.Kinds.IshikawaSeparationFacts
import Elegant.IshikawaClearanceFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-- Residual (same side, cross rib): for the executed `assemblePairs` run, the
shifted route of a piece of one rib misses the shifted box of a piece of a
different rib on the SAME side of the spine.

This is one case of `IshikawaCrossRibPieceClearance` (the case
`rA.upper = rB.upper`); the opposite-side case is proved below from the rib
half-plane envelopes, which are insensitive to the horizontal shifts.
Same-side ribs always lie in different assembly pairs, so this case is the
shifted x-interval disjointness of distinct pairs. It held on every executed
layout in the raw-clearance probe (32 layouts, 4668 distinct-index
route/box pairs, no hits). -/
def IshikawaCrossRibSameSideClearance (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (rA rB : Rib) (dxA dxB : Int)
    (pieceA pieceB : Nat × Rect × List Point),
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rA dxA →
    AssemblyPairShift e.placed (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      rB dxB →
    rA ≠ rB → pieceA ∈ rA.pieces → pieceB ∈ rB.pieces →
    rA.upper = rB.upper → pieceA.1 ≠ pieceB.1 →
    ¬ Polyline.hitsRect
      (pieceA.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
      { pieceB.2.1 with x := pieceB.2.1.x + dxB }

/-- A segment weakly above a box misses its open interior. -/
theorem crossRib_segMisses_of_y_ge {p q : Point} {r : Rect}
    (h : r.y + r.h ≤ min p.y q.y) : Polyline.segMisses p q r :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem crossRib_route_le_of_upper (ns : List Tree.Node) (p : Params) (spine : Int)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r => place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) r)) = .ok placed)
    (hne : ns ≠ [])
    (rib : Rib) (hrib : rib ∈ placed) (hu : rib.upper = true)
    (i : Nat) (_rect : Rect) (points : List Point)
    (hmem : (i, _rect, points) ∈ rib.pieces) :
    ∀ q ∈ points, q.y ≤ spine := by
  obtain ⟨source, cause, k, _hs, _hi, heq, hplace⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  have hupper : (effectivePlacedInput ns (measuredSideLength p ribs) source).upper = true := by
    have h := Elegant.Kinds.IshikawaSeparation.place_upper_eq ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) rib hplace
    rw [hu] at h
    exact h.symm
  have hordT : ∀ t : Int, ordinate spine true t = spine - t := fun _ => rfl
  have hparams := successful_nonempty_length_parameters ns p raw hne hrun
  have hmin : 0 ≤ p.ribMin := by omega
  have hbase : 0 ≤ p.spineBase := by omega
  have hL : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) source).length :=
    effective_length_nonnegative ns p ribs source hmin hbase
  subst heq
  have horigin := place_piece_route_genealogy ns p spine
    (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
    rib hplace i _rect points hmem
  rcases horigin with ⟨_hic, hpoints⟩ | ⟨e, idx, pos, par, _n, he, hpos, _hn, _hi2, hgene, hpoints⟩
  · intro q hq
    rw [hpoints] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hnil
    · exact Int.le_refl _
    · rw [hupper, hordT]
      show spine - _ ≤ spine
      omega
    · cases hnil
  · dsimp only at hpoints
    have hentry := BoneGenealogy.entry par e idx pos hgene he hpos
    have htemp := generated_bone_temporal_bounds ns p ribs cause k hmin hbase _ hentry
    dsimp only at htemp
    obtain ⟨ht0, _ht0L, ht1, _ht1L⟩ := htemp
    intro q hq
    rw [hpoints] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hnil
    · rw [hupper, hordT]
      show spine - _ ≤ spine
      omega
    · rw [hupper, hordT]
      show spine - _ ≤ spine
      omega
    · cases hnil

theorem crossRib_box_le_of_upper (ns : List Tree.Node) (p : Params) (spine : Int)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r => place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) r)) = .ok placed)
    (hne : ns ≠ [])
    (rib : Rib) (hrib : rib ∈ placed) (hu : rib.upper = true)
    (i : Nat) (rect : Rect) (_points : List Point)
    (hmem : (i, rect, _points) ∈ rib.pieces) :
    rect.y + rect.h ≤ spine := by
  obtain ⟨source, _cause, _k, hsource, _hi, heq, hplace⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  have hupper : (effectivePlacedInput ns (measuredSideLength p ribs) source).upper = true := by
    have h := Elegant.Kinds.IshikawaSeparation.place_upper_eq ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) rib hplace
    rw [hu] at h
    exact h.symm
  have hordT : ∀ t : Int, ordinate spine true t = spine - t := fun _ => rfl
  have hparams := successful_nonempty_length_parameters ns p raw hne hrun
  have hmin : 0 ≤ p.ribMin := by omega
  have hbase : 0 ≤ p.spineBase := by omega
  have hL : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) source).length :=
    effective_length_nonnegative ns p ribs source hmin hbase
  subst heq
  have horigin := place_piece_placement ns p spine
    (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (_cause, _k)))
    rib hplace i rect _points hmem
  rcases horigin with ⟨n, _hn, _hic, hrect⟩
    | ⟨e, idx, pos, n, he, hpos, _hic, hn, _hw, hh, hy⟩
  · have e1 : rect.y = spine -
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).length - n.height := by
      simp [hrect, hupper, hordT]
    have e2 : rect.h = n.height := by rw [hrect]
    omega
  · have hslot := Elegant.Kinds.IshikawaSeparation.generated_found_entry_slot_bounds
        ns p raw hrun ribs hg (generatedRib ns (_cause, _k)) hsource
        e idx pos n he hpos hn
    dsimp only at hslot
    obtain ⟨_hh0, hht, _htL⟩ := hslot
    have e1 : rect.y = spine - Int.fdiv
        ((effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).length * (pos.2 + 1 : Nat))
        ((effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).entries.length + 1 : Nat)
        - Int.fdiv n.height 2 := by
      rw [hy, hupper, hordT]
    have e2 : rect.h = n.height := hh
    have hfd : 0 ≤ Int.fdiv n.height 2 := by
      rw [Elegant.Tree.fdiv2]
      omega
    omega

theorem crossRib_route_ge_of_lower (ns : List Tree.Node) (p : Params) (spine : Int)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r => place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) r)) = .ok placed)
    (hne : ns ≠ [])
    (rib : Rib) (hrib : rib ∈ placed) (hu : rib.upper = false)
    (i : Nat) (_rect : Rect) (points : List Point)
    (hmem : (i, _rect, points) ∈ rib.pieces) :
    ∀ q ∈ points, spine ≤ q.y := by
  obtain ⟨source, cause, k, _hs, _hi, heq, hplace⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  have hupper : (effectivePlacedInput ns (measuredSideLength p ribs) source).upper = false := by
    have h := Elegant.Kinds.IshikawaSeparation.place_upper_eq ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) rib hplace
    rw [hu] at h
    exact h.symm
  have hordF : ∀ t : Int, ordinate spine false t = spine + t := fun _ => rfl
  have hparams := successful_nonempty_length_parameters ns p raw hne hrun
  have hmin : 0 ≤ p.ribMin := by omega
  have hbase : 0 ≤ p.spineBase := by omega
  have hL : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) source).length :=
    effective_length_nonnegative ns p ribs source hmin hbase
  subst heq
  have horigin := place_piece_route_genealogy ns p spine
    (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k)))
    rib hplace i _rect points hmem
  rcases horigin with ⟨_hic, hpoints⟩ | ⟨e, idx, pos, par, _n, he, hpos, _hn, _hi2, hgene, hpoints⟩
  · intro q hq
    rw [hpoints] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hnil
    · exact Int.le_refl _
    · rw [hupper, hordF]
      show spine ≤ spine + _
      omega
    · cases hnil
  · dsimp only at hpoints
    have hentry := BoneGenealogy.entry par e idx pos hgene he hpos
    have htemp := generated_bone_temporal_bounds ns p ribs cause k hmin hbase _ hentry
    dsimp only at htemp
    obtain ⟨ht0, _ht0L, ht1, _ht1L⟩ := htemp
    intro q hq
    rw [hpoints] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | rfl | hnil
    · rw [hupper, hordF]
      show spine ≤ spine + _
      omega
    · rw [hupper, hordF]
      show spine ≤ spine + _
      omega
    · cases hnil

theorem crossRib_box_ge_of_lower (ns : List Tree.Node) (p : Params) (spine : Int)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r => place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) r)) = .ok placed)
    (hne : ns ≠ [])
    (rib : Rib) (hrib : rib ∈ placed) (hu : rib.upper = false)
    (i : Nat) (rect : Rect) (_points : List Point)
    (hmem : (i, rect, _points) ∈ rib.pieces) :
    spine ≤ rect.y := by
  obtain ⟨source, _cause, _k, hsource, _hi, heq, hplace⟩ :=
    placed_rib_source ns p ribs placed (measuredSideLength p ribs) spine hg hplaces rib hrib
  have hupper : (effectivePlacedInput ns (measuredSideLength p ribs) source).upper = false := by
    have h := Elegant.Kinds.IshikawaSeparation.place_upper_eq ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) source) rib hplace
    rw [hu] at h
    exact h.symm
  have hordF : ∀ t : Int, ordinate spine false t = spine + t := fun _ => rfl
  have hparams := successful_nonempty_length_parameters ns p raw hne hrun
  have hmin : 0 ≤ p.ribMin := by omega
  have hbase : 0 ≤ p.spineBase := by omega
  have hL : 0 ≤ (effectivePlacedInput ns (measuredSideLength p ribs) source).length :=
    effective_length_nonnegative ns p ribs source hmin hbase
  subst heq
  have horigin := place_piece_placement ns p spine
    (effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (_cause, _k)))
    rib hplace i rect _points hmem
  rcases horigin with ⟨n, _hn, _hic, hrect⟩
    | ⟨e, idx, pos, n, he, hpos, _hic, hn, _hw, hh, hy⟩
  · have e1 : rect.y = spine +
        (effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).length := by
      simp [hrect, hupper, hordF]
    omega
  · have hslot := Elegant.Kinds.IshikawaSeparation.generated_found_entry_slot_bounds
        ns p raw hrun ribs hg (generatedRib ns (_cause, _k)) hsource
        e idx pos n he hpos hn
    dsimp only at hslot
    obtain ⟨_hh0, hht, _htL⟩ := hslot
    have e1 : rect.y = spine + Int.fdiv
        ((effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).length * (pos.2 + 1 : Nat))
        ((effectivePlacedInput ns (measuredSideLength p ribs)
          (generatedRib ns (_cause, _k))).entries.length + 1 : Nat)
        - Int.fdiv n.height 2 := by
      rw [hy, hupper, hordF]
    have hfle : Int.fdiv n.height 2 ≤ n.height := by
      rw [Elegant.Tree.fdiv2]
      omega
    omega

theorem crossRib_opposite_miss (ns : List Tree.Node) (p : Params) (spine : Int)
    (raw : Tree.Layout) (hrun : layout ns p = .ok raw)
    (ribs placed : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun r => place ns p spine
      (effectivePlacedInput ns (measuredSideLength p ribs) r)) = .ok placed)
    (hne : ns ≠ [])
    (ribA ribB : Rib) (hribA : ribA ∈ placed) (hribB : ribB ∈ placed)
    (hopposite : ribA.upper ≠ ribB.upper)
    (pieceA pieceB : Nat × Rect × List Point)
    (hmemA : pieceA ∈ ribA.pieces) (hmemB : pieceB ∈ ribB.pieces)
    (dxA dxB : Int) :
    ¬ Polyline.hitsRect
      (pieceA.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
      { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
  have hA : (pieceA.1, pieceA.2.1, pieceA.2.2) ∈ ribA.pieces := hmemA
  have hB : (pieceB.1, pieceB.2.1, pieceB.2.2) ∈ ribB.pieces := hmemB
  cases _huA : ribA.upper <;> cases _huB : ribB.upper
  · rw [_huA, _huB] at hopposite
    exact False.elim (hopposite rfl)
  · have hroute := crossRib_route_ge_of_lower ns p spine raw hrun ribs placed hg hplaces hne
      ribA hribA _huA pieceA.1 pieceA.2.1 pieceA.2.2 hA
    have hbox := crossRib_box_le_of_upper ns p spine raw hrun ribs placed hg hplaces hne
      ribB hribB _huB pieceB.1 pieceB.2.1 pieceB.2.2 hB
    have hmiss : ∀ pts : List Point, (∀ q ∈ pts, spine ≤ q.y) →
        Polyline.allSegsMiss (pts.map fun q => ({ x := q.x + dxA, y := q.y } : Point))
          { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
      intro pts hpts
      induction pts with
      | nil => exact trivial
      | cons a rest ih =>
        cases rest with
        | nil => exact trivial
        | cons b rest' =>
          have ha := hpts a List.mem_cons_self
          have hb := hpts b (List.mem_cons_of_mem a List.mem_cons_self)
          have ih' := ih (fun q hq => hpts q (List.mem_cons_of_mem a hq))
          have hseg : Polyline.segMisses ({ x := a.x + dxA, y := a.y } : Point)
              ({ x := b.x + dxA, y := b.y } : Point)
              { pieceB.2.1 with x := pieceB.2.1.x + dxB } :=
            crossRib_segMisses_of_y_ge (by
              show pieceB.2.1.y + pieceB.2.1.h ≤ min a.y b.y
              omega)
          simp only [List.map_cons, Polyline.allSegsMiss]
          exact ⟨hseg, ih'⟩
    exact Polyline.not_hits_of_allMiss (hmiss _ hroute)
  · have hroute := crossRib_route_le_of_upper ns p spine raw hrun ribs placed hg hplaces hne
      ribA hribA _huA pieceA.1 pieceA.2.1 pieceA.2.2 hA
    have hbox := crossRib_box_ge_of_lower ns p spine raw hrun ribs placed hg hplaces hne
      ribB hribB _huB pieceB.1 pieceB.2.1 pieceB.2.2 hB
    have hmiss : ∀ pts : List Point, (∀ q ∈ pts, q.y ≤ spine) →
        Polyline.allSegsMiss (pts.map fun q => ({ x := q.x + dxA, y := q.y } : Point))
          { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
      intro pts hpts
      induction pts with
      | nil => exact trivial
      | cons a rest ih =>
        cases rest with
        | nil => exact trivial
        | cons b rest' =>
          have ha := hpts a List.mem_cons_self
          have hb := hpts b (List.mem_cons_of_mem a List.mem_cons_self)
          have ih' := ih (fun q hq => hpts q (List.mem_cons_of_mem a hq))
          have hseg : Polyline.segMisses ({ x := a.x + dxA, y := a.y } : Point)
              ({ x := b.x + dxA, y := b.y } : Point)
              { pieceB.2.1 with x := pieceB.2.1.x + dxB } :=
            Polyline.segMisses_of_y_le (by
              show max a.y b.y ≤ pieceB.2.1.y
              omega)
          simp only [List.map_cons, Polyline.allSegsMiss]
          exact ⟨hseg, ih'⟩
    exact Polyline.not_hits_of_allMiss (hmiss _ hroute)
  · rw [_huA, _huB] at hopposite
    exact False.elim (hopposite rfl)

theorem ishikawaCrossRibPieceClearance (m : Model)
    (hsame : IshikawaCrossRibSameSideClearance m) :
    IshikawaCrossRibPieceClearance m := by
  intro e rA rB dxA dxB pieceA pieceB hshiftA hshiftB hne hmemA hmemB hidx
  by_cases hside : rA.upper = rB.upper
  · exact hsame e rA rB dxA dxB pieceA pieceB hshiftA hshiftB hne hmemA hmemB hside hidx
  · have hribA : rA ∈ e.placed := assemblyPairShift_mem hshiftA
    have hribB : rB ∈ e.placed := assemblyPairShift_mem hshiftB
    have hne' : e.input.nodes ≠ [] :=
      List.ne_nil_of_mem (List.mem_of_getElem? e.hhead)
    have hplaces : e.ribs.mapM (fun r => place e.input.nodes
        (Elegant.Kinds.Ishikawa.params m.profile) e.spine
        (effectivePlacedInput e.input.nodes
          (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs) r)) =
        .ok e.placed := by
      rw [← e.hlength]
      exact e.hplaced
    exact crossRib_opposite_miss e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.spine e.raw e.hlayout e.ribs e.placed e.hribs hplaces hne'
      rA rB hribA hribB hside pieceA pieceB hmemA hmemB dxA dxB

end Elegant.Kinds.IshikawaFinal
