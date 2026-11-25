import Elegant.Kinds.IshikawaRawClearance
import Elegant.Kinds.IshikawaSeparationFacts
import Elegant.IshikawaSeparationFacts
import Elegant.IshikawaClearanceFacts
import Elegant.Kinds.IshikawaCrossRibClearance

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-- Residual (route x-envelope): for the executed `assemblePairs` run, every
route point of every placed rib piece lies in the pair's reserved x-interval
below the origin: at or left of `0` and at or right of the pair's box minimum.

Why this is true for executed layouts. The cause route is `[⟨0, spine⟩,
⟨-run, _⟩` with `run ≥ 0` from the executed nonnegativity of the rib length
and slope parameters, so both its points satisfy the bounds (the cause box
left edge sits left of `-run`). Every entry bone's `x1` is its own box right
edge, hence at or right of the pair minimum; an even bone's `x0` is `x1`
plus the positive `boneLength`; an odd bone's `x0` interpolates its parent
span, and its `x1` descends from `x0` by `run` of a nonnegative slot gap
(the slot-gap, drawn-count and executed parameter facts hold on executed
layouts). The raw-clearance probe saw no hits among 4668 distinct-index
route/box pairs on 32 executed layouts, consistent with this envelope:
same-side pairs can only clear in x.

This is strictly simpler than `IshikawaCrossRibPieceClearance`: a pure
per-piece x-bound with no shifts, no pair layout and no route/box
interaction. It is used once per segment below, in the pair-frontier
induction for same-side ribs. -/
def IshikawaRouteXEnvelope (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (P : List Rib) (r : Rib),
    r ∈ P → P ⊆ e.placed →
    ∀ (piece : Nat × Rect × List Point) (_hm : piece ∈ r.pieces)
      (q : Point) (_hq : q ∈ piece.2.2),
      (extent P).1 ≤ q.x ∧ q.x ≤ 0

/-- A segment weakly left of a box misses its open interior. -/
theorem crossRib_segMisses_of_x_ge {p q : Point} {r : Rect}
    (h : r.x + r.w ≤ min p.x q.x) : Polyline.segMisses p q r :=
  Or.inr (Or.inl h)

/-- The right edge of every pair extent is nonnegative (the fold starts at
`0` and only takes maxima). -/
theorem extent_right_nonneg (rs : List Rib) : 0 ≤ (extent rs).2 := by
  unfold extent
  have h : ∀ (ps : List (Nat × Rect × List Point)) (l : Int) (r : Int),
      0 ≤ r → 0 ≤ (ps.foldl (fun (l, right) v =>
        (min l v.2.1.x, max right (v.2.1.x + v.2.1.w))) (l, r)).2 := by
    intro ps
    induction ps with
    | nil => intro l r hr; simpa using hr
    | cons p ps ih => intro l r hr; exact ih _ _ (Int.le_trans hr (Int.le_max_left _ _))
  exact h _ _ _ (Int.le_refl 0)

/-- A shifted route point stays left of the shift frontier: the route point
is at or left of `0` while the shift is pinned by the pair reach. -/
theorem route_shift_piece_right {rs : List Rib} {ceiling previous : Int}
    {r : Rib} {dx : Int}
    (hshift : AssemblyPairShift rs ceiling previous r dx)
    (hx : ∀ piece ∈ r.pieces, ∀ q ∈ piece.2.2, q.x ≤ 0) :
    (∀ rib ∈ rs, ∀ piece ∈ rib.pieces, 0 ≤ piece.2.1.w) →
    ∀ piece ∈ r.pieces, ∀ q ∈ piece.2.2, q.x + dx ≤ previous := by
  induction hshift with
  | current a rest ceiling previous r hr =>
    intro _ piece hm q hq
    have hq0 : q.x ≤ 0 := hx piece hm q hq
    have hle : min ceiling (previous - (extent (a :: rest.take 1)).2) ≤
        previous - (extent (a :: rest.take 1)).2 :=
      Int.min_le_right _ _
    have hreach : 0 ≤ (extent (a :: rest.take 1)).2 := extent_right_nonneg _
    omega
  | later a rest ceiling previous r dx h ih =>
    intro hwidth piece hm q hq
    have htail : ∀ rib ∈ rest.drop 1, ∀ p ∈ rib.pieces, 0 ≤ p.2.1.w := by
      intro rib hr p hp
      exact hwidth rib (List.mem_cons_of_mem a (List.mem_of_mem_drop hr)) p hp
    have hright := ih hx htail piece hm q hq
    have hfrontier := pair_frontier_antitone (a :: rest.take 1) ceiling previous
      (by
        intro qq hqq
        obtain ⟨rib, hr, hqq⟩ := List.mem_flatMap.mp hqq
        have hr' : rib ∈ a :: rest := by
          rcases List.mem_cons.mp hr with he | hr
          · exact List.mem_cons.mpr (Or.inl he)
          · exact List.mem_cons_of_mem a (List.mem_of_mem_take hr)
        exact hwidth rib hr' qq hqq)
    omega

/-- A head pair of the executed assembly is contained in the placed ribs. -/
theorem pair_subset_placed (placed : List Rib) (offset : Nat) (a : Rib)
    (rest : List Rib) (hsuffix : placed.drop offset = a :: rest) :
    (a :: rest.take 1) ⊆ placed := by
  intro x hx
  have hx' : x ∈ placed.drop offset := by
    rw [hsuffix]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_of_mem_take hx))
  exact List.mem_of_mem_drop hx'

/-- Two distinct ribs of one assembly pair lie on opposite sides of the
spine, so they cannot satisfy the same-side hypothesis. -/
theorem same_pair_same_side_contra (ns : List Tree.Node) (p : Params)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (offset : Nat) (first : Rib) (rest : List Rib)
    (hsuffix : placed.drop offset = first :: rest)
    (rA rB : Rib) (hrA : rA ∈ first :: rest.take 1)
    (hrB : rB ∈ first :: rest.take 1)
    (hneRib : rA ≠ rB) (hside : rA.upper = rB.upper) : False := by
  have hfirst : placed[offset]? = some first := by
    have h : (placed.drop offset)[0]? = some first := by rw [hsuffix]; rfl
    simpa only [List.getElem?_drop, Nat.add_zero] using h
  cases rest with
  | nil =>
    have hA : rA = first := by simpa using hrA
    have hB : rB = first := by simpa using hrB
    exact hneRib (hA.trans hB.symm)
  | cons second tail =>
    have hsecond : placed[offset + 1]? = some second := by
      have h : (placed.drop offset)[1]? = some second := by rw [hsuffix]; rfl
      simpa only [List.getElem?_drop] using h
    have halt := Elegant.Kinds.IshikawaSeparation.placed_adjacent_ribs_alternate
      ns p ribs placed spine hg hplaces offset first second hfirst hsecond
    have hdiff : first.upper ≠ second.upper := by
      rw [halt]
      cases first.upper <;> decide
    have hA : rA = first ∨ rA = second := by simpa using hrA
    have hB : rB = first ∨ rB = second := by simpa using hrB
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact hneRib (hA.trans hB.symm)
    · rw [hA, hB] at hside
      exact hdiff hside
    · rw [hA, hB] at hside
      exact hdiff hside.symm
    · exact hneRib (hA.trans hB.symm)

/-- Same-side cross-rib clearance by pair-frontier induction, mirroring
`assembly_shift_pieces_disjoint`: same-pair shifts are contradictory, the
head route misses the tail box from the right via the pair minimum, and the
tail route misses the head box from the left via the nonpositive route
envelope. -/
theorem assembly_shift_same_side_miss (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hrun : Elegant.Ishikawa.layout ns p = .ok raw)
    (ribs placed : List Rib) (spine : Int)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (hplaces : ribs.mapM (fun source =>
      place ns p spine (effectivePlacedInput ns (measuredSideLength p ribs) source)) =
        .ok placed)
    (hxP : ∀ (P : List Rib) (r : Rib), r ∈ P → P ⊆ placed →
      ∀ (piece : Nat × Rect × List Point) (_hm : piece ∈ r.pieces)
        (q : Point) (_hq : q ∈ piece.2.2),
        (extent P).1 ≤ q.x ∧ q.x ≤ 0)
    {rs : List Rib} {ceiling previous : Int} {ribA : Rib} {dxA : Int}
    (hshiftA : AssemblyPairShift rs ceiling previous ribA dxA) :
    ∀ (offset : Nat), placed.drop offset = rs →
    ∀ (ribB : Rib) (dxB : Int), AssemblyPairShift rs ceiling previous ribB dxB →
    ∀ (pieceA pieceB : Nat × Rect × List Point),
      pieceA ∈ ribA.pieces → pieceB ∈ ribB.pieces →
      ribA ≠ ribB → ribA.upper = ribB.upper →
      ¬ Polyline.hitsRect
        (pieceA.2.2.map (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
        { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
  induction hshiftA with
  | current a rest ceiling previous ribA hrA =>
    intro offset hsuffix ribB dxB hshiftB pieceA pieceB hmA hmB hneRib hside
    rcases Elegant.Kinds.IshikawaSeparation.assembly_shift_cons_cases a rest ceiling previous ribB dxB hshiftB with
      ⟨hribB, _hdxB⟩ | htailB
    · exact False.elim (same_pair_same_side_contra ns p ribs placed spine hg hplaces
        offset a rest hsuffix ribA ribB hrA hribB hneRib hside)
    · have hsuffixTail : placed.drop (offset + 2) = rest.drop 1 := by
        rw [← List.drop_drop, hsuffix]
        rfl
      have hwidth : ∀ rib ∈ rest.drop 1, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
        intro rib hr q hq
        have hr' : rib ∈ placed := by
          apply List.mem_of_mem_drop
          rw [hsuffixTail]
          exact hr
        exact (Elegant.Kinds.IshikawaSeparation.placed_piece_nonnegative ns p raw hrun ribs placed spine hg hplaces
          rib hr' q hq).1
      have hBbox := assembly_shift_piece_right htailB hwidth pieceB hmB
      have hsub : (a :: rest.take 1) ⊆ placed :=
        pair_subset_placed placed offset a rest hsuffix
      have hroute : ∀ q ∈ pieceA.2.2,
          pieceB.2.1.x + dxB + pieceB.2.1.w ≤
            q.x + min ceiling (previous - (extent (a :: rest.take 1)).2) := by
        intro q hq
        have hlo := ((hxP (a :: rest.take 1) ribA hrA hsub) pieceA hmA q hq).1
        omega
      have hmiss : ∀ pts : List Point,
          (∀ q ∈ pts, pieceB.2.1.x + dxB + pieceB.2.1.w ≤
            q.x + min ceiling (previous - (extent (a :: rest.take 1)).2)) →
          Polyline.allSegsMiss (pts.map fun q => ({ x := q.x + min ceiling (previous - (extent (a :: rest.take 1)).2), y := q.y } : Point))
            { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
        intro pts hpts
        induction pts with
        | nil => exact trivial
        | cons a0 rest0 ih =>
          cases rest0 with
          | nil => exact trivial
          | cons b0 rest' =>
            have ha := hpts a0 List.mem_cons_self
            have hb := hpts b0 (List.mem_cons_of_mem a0 List.mem_cons_self)
            have ih' := ih (fun q hq => hpts q (List.mem_cons_of_mem a0 hq))
            have hseg : Polyline.segMisses
                ({ x := a0.x + min ceiling (previous - (extent (a :: rest.take 1)).2), y := a0.y } : Point)
                ({ x := b0.x + min ceiling (previous - (extent (a :: rest.take 1)).2), y := b0.y } : Point)
                { pieceB.2.1 with x := pieceB.2.1.x + dxB } :=
              crossRib_segMisses_of_x_ge (by
                show pieceB.2.1.x + dxB + pieceB.2.1.w ≤
                  min (a0.x + min ceiling (previous - (extent (a :: rest.take 1)).2))
                    (b0.x + min ceiling (previous - (extent (a :: rest.take 1)).2))
                omega)
            simp only [List.map_cons, Polyline.allSegsMiss]
            exact ⟨hseg, ih'⟩
      exact Polyline.not_hits_of_allMiss (hmiss _ hroute)
  | later a rest ceiling previous ribA dxA h ih =>
    intro offset hsuffix ribB dxB hshiftB pieceA pieceB hmA hmB hneRib hside
    have hsuffixTail : placed.drop (offset + 2) = rest.drop 1 := by
      rw [← List.drop_drop, hsuffix]
      rfl
    rcases Elegant.Kinds.IshikawaSeparation.assembly_shift_cons_cases a rest ceiling previous ribB dxB hshiftB with
      ⟨hribB, hdxB⟩ | htailB
    · have hwidth : ∀ rib ∈ rest.drop 1, ∀ q ∈ rib.pieces, 0 ≤ q.2.1.w := by
        intro rib hr q hq
        have hr' : rib ∈ placed := by
          apply List.mem_of_mem_drop
          rw [hsuffixTail]
          exact hr
        exact (Elegant.Kinds.IshikawaSeparation.placed_piece_nonnegative ns p raw hrun ribs placed spine hg hplaces
          rib hr' q hq).1
      have hmemTail : ribA ∈ rest.drop 1 := assemblyPairShift_mem h
      have hmemA' : ribA ∈ placed := by
        apply List.mem_of_mem_drop
        rw [hsuffixTail]
        exact hmemTail
      have hsubA : [ribA] ⊆ placed := by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        exact hmemA'
      have hxU : ∀ piece ∈ ribA.pieces, ∀ q ∈ piece.2.2, q.x ≤ 0 := by
        intro piece hm q hq
        exact ((hxP [ribA] ribA (by simp) hsubA) piece hm q hq).2
      have hroute : ∀ q ∈ pieceA.2.2, q.x + dxA ≤ dxB + pieceB.2.1.x := by
        intro q hq
        have hr := route_shift_piece_right h hxU hwidth pieceA hmA q hq
        have hleft := (extent_piece_bounds (a :: rest.take 1) pieceB
          (List.mem_flatMap.mpr ⟨ribB, hribB, hmB⟩)).1
        omega
      have hmiss : ∀ pts : List Point,
          (∀ q ∈ pts, q.x + dxA ≤ dxB + pieceB.2.1.x) →
          Polyline.allSegsMiss (pts.map fun q => ({ x := q.x + dxA, y := q.y } : Point))
            { pieceB.2.1 with x := pieceB.2.1.x + dxB } := by
        intro pts hpts
        induction pts with
        | nil => exact trivial
        | cons a0 rest0 ih =>
          cases rest0 with
          | nil => exact trivial
          | cons b0 rest' =>
            have ha := hpts a0 List.mem_cons_self
            have hb := hpts b0 (List.mem_cons_of_mem a0 List.mem_cons_self)
            have ih' := ih (fun q hq => hpts q (List.mem_cons_of_mem a0 hq))
            have hseg : Polyline.segMisses ({ x := a0.x + dxA, y := a0.y } : Point)
                ({ x := b0.x + dxA, y := b0.y } : Point)
                { pieceB.2.1 with x := pieceB.2.1.x + dxB } :=
              Polyline.segMisses_of_x_le (by
                show max (a0.x + dxA) (b0.x + dxA) ≤ pieceB.2.1.x + dxB
                omega)
            simp only [List.map_cons, Polyline.allSegsMiss]
            exact ⟨hseg, ih'⟩
      exact Polyline.not_hits_of_allMiss (hmiss _ hroute)
    · exact ih (offset + 2) hsuffixTail ribB dxB htailB pieceA pieceB hmA hmB hneRib hside

theorem ishikawaCrossRibSameSideClearance (m : Model) (hx : IshikawaRouteXEnvelope m) :
    IshikawaCrossRibSameSideClearance m := by
  intro e rA rB dxA dxB pieceA pieceB hshiftA hshiftB hneRib hmA hmB hside _hidx
  have hplaces : e.ribs.mapM (fun r => place e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.spine
      (effectivePlacedInput e.input.nodes
        (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs) r)) =
      .ok e.placed := by
    rw [← e.hlength]
    exact e.hplaced
  have hxP : ∀ (P : List Rib) (r : Rib), r ∈ P → P ⊆ e.placed →
      ∀ (piece : Nat × Rect × List Point) (hm : piece ∈ r.pieces)
        (q : Point) (hq : q ∈ piece.2.2),
        (extent P).1 ≤ q.x ∧ q.x ≤ 0 :=
    fun P r h1 h2 piece hm q hq => hx e P r h1 h2 piece hm q hq
  have hsuffix0 : e.placed.drop 0 = e.placed := by simp
  exact assembly_shift_same_side_miss e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
    e.raw e.hlayout e.ribs e.placed e.spine e.hribs hplaces hxP hshiftA 0 hsuffix0
    rB dxB hshiftB pieceA pieceB hmA hmB hneRib hside

theorem ishikawaCrossRibPieceClearance' (m : Model) (hx : IshikawaRouteXEnvelope m) :
    IshikawaCrossRibPieceClearance m := by
  intro e rA rB dxA dxB pieceA pieceB hshiftA hshiftB hne hmA hmB hidx
  by_cases hside : rA.upper = rB.upper
  · exact ishikawaCrossRibSameSideClearance m hx e rA rB dxA dxB pieceA pieceB
      hshiftA hshiftB hne hmA hmB hside hidx
  · exact ishikawaCrossRibPieceClearance m
      (ishikawaCrossRibSameSideClearance m hx) e rA rB dxA dxB pieceA pieceB
      hshiftA hshiftB hne hmA hmB hidx

end Elegant.Kinds.IshikawaFinal
