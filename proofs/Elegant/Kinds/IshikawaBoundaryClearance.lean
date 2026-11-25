import Elegant.Kinds.IshikawaRawClearance
import Elegant.IshikawaClearanceFacts
import Elegant.IshikawaLayoutProvenanceFacts
import Elegant.IshikawaAssemblyBoxFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! Boundary piece clearance.

`ishikawaBoundaryPieceClearance` discharges the two assembly-owned boundary
obligations of `IshikawaBoundaryPieceClearance`. Conjunct (1), the spine route
against every non-head raw box, is proved outright through
`placed_pieces_spine_clearance`: every placed rib piece lies strictly on its
side of the spine ordinate, so the horizontal spine segment never enters a
non-head box interior, for every start `a`. Conjunct (2), every shifted rib
route piece against the head box, follows from the nonpositivity of every
shifted route abscissa and of every assembly shift; the route bound is the
single named residual `IshikawaBoundaryRouteXNonpos`. -/

/-- Residual (route x-bound): in every executed layout, every route point of
every placed rib piece has nonpositive x. Rib bones interpolate from the rib
root at `x = 0` towards `-run p r.length ≤ 0`, so every bone end stays weakly
left of the spine; the remaining obligation is the induction over the placed
bones showing every interpolated x stays `≤ 0`. -/
def IshikawaBoundaryRouteXNonpos (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (rib : Rib),
    rib ∈ e.placed →
    ∀ (piece : Nat × Rect × List Point), piece ∈ rib.pieces →
      ∀ q ∈ piece.2.2, q.x ≤ 0

/-- A successful `getElem?` on a replicate list returns the replicated value. -/
private theorem boundary_replicate_getElem? {α : Type} (n : Nat) (a : α) :
    ∀ (k : Nat) (x : α), (List.replicate n a)[k]? = some x → x = a := by
  induction n with
  | zero => intro k x h; simp at h
  | succ n ih =>
    intro k x h
    cases k with
    | zero =>
      have h2 : some x = some a := by
        calc some x = (List.replicate (n + 1) a)[0]? := h.symm
        _ = some a := rfl
      exact Option.some_inj.mp h2
    | succ k => exact ih k x h

/-- Reading a nonzero index of a `set 0` list reads through to the original. -/
private theorem boundary_set_getElem_succ {α : Type} (l : List α) (hb : α)
    (k : Nat) (bx : α) (h : (l.set 0 hb)[k + 1]? = some bx) :
    l[k + 1]? = some bx := by
  cases l with
  | nil => exact h
  | cons a rest => exact h

/-- No route hits the zero rectangle at the origin. -/
private theorem boundary_hitsRect_zero (pts : List Point) :
    ¬ Polyline.hitsRect pts ⟨0, 0, 0, 0⟩ := by
  intro hhit
  obtain ⟨hrw, _, _⟩ := hhit
  exact absurd hrw (by decide)

/-- The slope and inset parameters of a successful nonempty layout. -/
private theorem boundary_param_facts (ns : List Tree.Node) (p : Params)
    (raw : Tree.Layout) (hne : ns ≠ [])
    (hrun : Elegant.Ishikawa.layout ns p = .ok raw) :
    0 ≤ p.cos ∧ 1 ≤ p.sin ∧ 0 ≤ p.inset := by
  cases ns with
  | nil => exact False.elim (hne rfl)
  | cons first rest =>
    unfold Elegant.Ishikawa.layout at hrun
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

/-- The executed input has a head node. -/
private theorem boundary_input_nonempty {m : Model} (e : IshikawaRawExecution m) :
    e.input.nodes ≠ [] := by
  intro hnil
  have hh := e.hhead
  rw [hnil] at hh
  simp at hh

/-- The reservation budget of a generated rib source, transported to the
executed `e.length` measurement. -/
private theorem boundary_placed_budget (m : Model) (e : IshikawaRawExecution m)
    (source : Rib) (cause k : Nat) (hsource : source ∈ e.ribs)
    (hgen : source = generatedRib e.input.nodes (cause, k)) :
    (source.entries.length + 1 : Nat) * source.entries.foldl
      (fun h en => max h
        (((e.input.nodes[en.node]?).map (·.height)).getD 0)) 0 ≤
    (effectivePlacedInput e.input.nodes e.length source).length := by
  have hne := boundary_input_nonempty e
  have hlen0 : 0 ≤ (effectivePlacedInput e.input.nodes e.length source).length := by
    have h := successful_nonempty_effective_length_nonnegative e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout e.ribs source
    rw [← e.hlength] at h
    exact h
  by_cases hEm : source.entries.isEmpty = true
  · have hnil : source.entries = [] := List.isEmpty_iff.mp hEm
    rw [hnil]
    simpa using hlen0
  · have hne2 : source.entries.isEmpty = false := by
      cases hb : source.entries.isEmpty with
      | true => exact absurd hb hEm
      | false => rfl
    have hbudget0 := generated_reservation_budget e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.ribs e.hribs source hsource hne2
    have hheight : source.heights = source.entries.foldl
        (fun h en => max h
          (((e.input.nodes[en.node]?).map (·.height)).getD 0)) 0 := by
      rw [hgen]
      exact (generated_rib_fields e.input.nodes cause k).2.2.2
    rw [hheight] at hbudget0
    rw [← e.hlength] at hbudget0
    exact hbudget0

/-- The spine route misses the assembly-shifted box of a placed rib piece. -/
private theorem boundary_placed_spine_clearance (m : Model)
    (e : IshikawaRawExecution m) (rib : Rib) (hrib : rib ∈ e.placed)
    (i : Nat) (rect : Rect) (points : List Point)
    (hmem : (i, rect, points) ∈ rib.pieces) (a dx dy : Int) :
    ¬ Polyline.hitsRect [⟨a, e.spine + dy⟩, ⟨0, e.spine + dy⟩]
      ⟨rect.x + dx, rect.y + dy, rect.w, rect.h⟩ := by
  obtain ⟨source, cause, k, hsource, hindex, hgen, hplace⟩ :=
    placed_rib_source e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.ribs e.placed e.length e.spine e.hribs e.hplaced rib hrib
  have hne := boundary_input_nonempty e
  have hlen0 : 0 ≤ (effectivePlacedInput e.input.nodes e.length source).length := by
    have h := successful_nonempty_effective_length_nonnegative e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout e.ribs source
    rw [← e.hlength] at h
    exact h
  have hbudget := boundary_placed_budget m e source cause k hsource hgen
  exact placed_pieces_spine_clearance e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.spine
    (effectivePlacedInput e.input.nodes e.length source) rib hplace
    hlen0 hbudget i rect points hmem a 0 dx dy

/-- Every placed rib piece rectangle has nonpositive x. -/
private theorem boundary_piece_rect_x_nonpos (m : Model)
    (hxb : IshikawaBoundaryRouteXNonpos m)
    (e : IshikawaRawExecution m) (rib : Rib) (hrib : rib ∈ e.placed)
    (piece : Nat × Rect × List Point) (hmem : piece ∈ rib.pieces) :
    piece.2.1.x ≤ 0 := by
  obtain ⟨source, cause, k, hsource, hindex, hgen, hplace⟩ :=
    placed_rib_source e.input.nodes (Elegant.Kinds.Ishikawa.params m.profile)
      e.ribs e.placed e.length e.spine e.hribs e.hplaced rib hrib
  have hne := boundary_input_nonempty e
  have hparam := boundary_param_facts e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
  have hlen0 : 0 ≤ (effectivePlacedInput e.input.nodes e.length source).length := by
    have h := successful_nonempty_effective_length_nonnegative e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout e.ribs source
    rw [← e.hlength] at h
    exact h
  obtain ⟨frames, hflen, hfroot, hfrec, hfpieces⟩ :=
    place_common_birth_frames e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.spine
      (effectivePlacedInput e.input.nodes e.length source) rib hplace
  have hgeom := hfpieces piece.1 piece.2.1 piece.2.2 hmem
  rcases hgeom with ⟨n, hn, hi, hrect, hpoints⟩ |
    ⟨en, idx, n, born, he, hi, hn, hborn, hrect, hpoints⟩
  · obtain ⟨hw, hh⟩ := successful_node_dimensions e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout n
      (List.mem_of_getElem? hn)
    have hrectx : piece.2.1.x =
        -run (Elegant.Kinds.Ishikawa.params m.profile)
          (effectivePlacedInput e.input.nodes e.length source).length -
          Int.fdiv n.width 2 := congrArg Rect.x hrect
    rw [hrectx]
    have hsin : 1 ≤ (Elegant.Kinds.Ishikawa.params m.profile).sin := hparam.2.1
    have hrun0 : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
        (effectivePlacedInput e.input.nodes e.length source).length := by
      show 0 ≤ Int.fdiv _ _
      exact Int.fdiv_nonneg (Int.mul_nonneg hlen0 hparam.1) (by omega)
    have hF : 0 ≤ Int.fdiv n.width 2 :=
      Int.fdiv_nonneg (by omega) (by omega)
    omega
  · obtain ⟨hw, hh⟩ := successful_node_dimensions e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout n
      (List.mem_of_getElem? hn)
    have hrectx : piece.2.1.x = born.x1 - n.width := congrArg Rect.x hrect
    rw [hrectx]
    have hP1mem : (⟨born.x1, ordinate e.spine
        (effectivePlacedInput e.input.nodes e.length source).upper born.t1⟩ : Point) ∈
        piece.2.2 := by
      rw [hpoints]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    have hx := hxb e rib hrib piece hmem _ hP1mem
    have hx1 : born.x1 ≤ 0 := hx
    omega

/-- If every piece rectangle of `pieces` has nonpositive x, the assembled
pair's left extent is nonpositive. -/
private theorem boundary_flatMap_left_nonpos
    (pieces : List (Nat × Rect × List Point))
    (hp : ∀ piece ∈ pieces, piece.2.1.x ≤ 0) :
    (pieces.foldl (fun (l, right) v =>
      (min l v.2.1.x, max right (v.2.1.x + v.2.1.w)))
      (((pieces.headD (0, ⟨0, 0, 0, 0⟩, [])).2.1.x), 0)).1 ≤ 0 := by
  by_cases hne : pieces = []
  · subst hne
    decide
  · obtain ⟨piece, hpmem⟩ := List.exists_mem_of_ne_nil _ hne
    have hx := hp piece hpmem
    have h1 := extent_fold_left pieces
      (((pieces.headD (0, ⟨0, 0, 0, 0⟩, [])).2.1.x), 0) piece hpmem
    exact Int.le_trans h1 hx

/-- The left extent of a rib pair whose pieces all start at nonpositive x is
nonpositive. -/
private theorem extent_left_nonpos {pair : List Rib}
    (hp : ∀ rib ∈ pair, ∀ piece ∈ rib.pieces, piece.2.1.x ≤ 0) :
    (extent pair).1 ≤ 0 := by
  have hflat : ∀ piece ∈ pair.flatMap (·.pieces), piece.2.1.x ≤ 0 := by
    intro piece hpmem
    obtain ⟨rib, hrib, hpiece⟩ := List.mem_flatMap.mp hpmem
    exact hp rib hrib piece hpiece
  exact boundary_flatMap_left_nonpos _ hflat

/-- Every assembly shift of a nonpositive-ceiling run is nonpositive, provided
every rib piece rectangle starts at nonpositive x. -/
private theorem assembly_shift_nonpos {rs : List Rib} {ceiling previous : Int}
    {r : Rib} {dx : Int}
    (hp : ∀ rib ∈ rs, ∀ piece ∈ rib.pieces, piece.2.1.x ≤ 0)
    (hc : ceiling ≤ 0)
    (h : AssemblyPairShift rs ceiling previous r dx) : dx ≤ 0 := by
  revert hp hc
  induction h
  · rename_i a rest ceiling previous r hr
    intro hp hc
    omega
  · rename_i a rest ceiling previous r dx h ih
    intro hp hc
    apply ih
    · intro rib hrib piece hpiece
      exact hp rib (List.mem_cons.mpr (Or.inr (List.mem_of_mem_drop hrib))) piece hpiece
    · have hpair : ∀ rib ∈ a :: rest.take 1, ∀ piece ∈ rib.pieces,
          piece.2.1.x ≤ 0 := by
        intro rib hrib piece hpiece
        refine hp rib ?_ piece hpiece
        rcases List.mem_cons.mp hrib with rfl | htake
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (List.mem_of_mem_take htake))
      have he1 := extent_left_nonpos hpair
      have hattach : min ceiling (previous - (extent (a :: rest.take 1)).2) ≤ 0 := by
        omega
      omega

/-- Every polyline whose points all lie at or left of `r.x` misses `r`. -/
private theorem allSegsMiss_of_x_nonpos {r : Rect} :
    ∀ pts : List Point, (∀ q ∈ pts, q.x ≤ r.x) → Polyline.allSegsMiss pts r := by
  intro pts
  induction pts with
  | nil => intro hx; trivial
  | cons p ps ih =>
    intro hx
    cases ps with
    | nil => trivial
    | cons q rest =>
      constructor
      · left
        have hpx := hx p (by simp)
        have hqx := hx q (by simp)
        omega
      · exact ih (fun s hs => hx s (List.mem_cons_of_mem _ hs))

/-- The boundary piece clearance theorem. -/
theorem ishikawaBoundaryPieceClearance (m : Model)
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (hxb : IshikawaBoundaryRouteXNonpos m) :
    IshikawaBoundaryPieceClearance m := by
  intro e
  have hne := boundary_input_nonempty e
  have hparam := boundary_param_facts e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
  constructor
  · intro a boxIndex rect hne0 hbox
    have hb := assemblePairs_box_origin e.spine e.placed
      (-(Elegant.Kinds.Ishikawa.params m.profile).inset) 0
      ⟨(List.replicate e.input.nodes.length (⟨0, 0, 0, 0⟩ : Rect)).set 0
        ⟨0, e.spine - Int.fdiv e.head.height 2, e.head.width, e.head.height⟩,
        List.replicate e.input.nodes.length []⟩ e.raw e.hassemble boxIndex rect hbox
    rcases hb with hBinit | ⟨rib, original, points, dx, hshift, hpiece, hrect⟩
    · cases boxIndex with
      | zero => exact False.elim (hne0 rfl)
      | succ j =>
        have h1 := boundary_set_getElem_succ _ _ j rect hBinit
        have h2 := boundary_replicate_getElem? _ _ _ _ h1
        rw [h2]
        exact boundary_hitsRect_zero _
    · intro hhit
      rw [hrect] at hhit
      have hrib : rib ∈ e.placed := assemblyPairShift_mem hshift
      have hsc := boundary_placed_spine_clearance m e rib hrib
        boxIndex original points hpiece a dx 0
      apply hsc
      simpa only [Int.add_zero] using hhit
  · intro rA dxA pieceR hshift hpieceR
    have hrA : rA ∈ e.placed := assemblyPairShift_mem hshift
    have hinset : 0 ≤ (Elegant.Kinds.Ishikawa.params m.profile).inset := hparam.2.2
    have hdx : dxA ≤ 0 :=
      assembly_shift_nonpos
        (fun rib hrib piece hpiece =>
          boundary_piece_rect_x_nonpos m hxb e rib hrib piece hpiece)
        (by omega) hshift
    have hx : ∀ q ∈ pieceR.2.2.map
        (fun q => ({ x := q.x + dxA, y := q.y } : Point)), q.x ≤ 0 := by
      intro q hq
      obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
      have hx0 := hxb e rA hrA pieceR hpieceR q0 hq0
      show q0.x + dxA ≤ 0
      omega
    have hmiss : Polyline.allSegsMiss (pieceR.2.2.map
        (fun q => ({ x := q.x + dxA, y := q.y } : Point)))
        ⟨0, e.spine - Int.fdiv e.head.height 2, e.head.width, e.head.height⟩ := by
      apply allSegsMiss_of_x_nonpos
      intro q hq
      exact hx q hq
    intro hhit
    exact hhit.2.2 hmiss

end Elegant.Kinds.IshikawaFinal
