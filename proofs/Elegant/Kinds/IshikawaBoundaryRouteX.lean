import Elegant.Kinds.IshikawaBoundaryClearance
import Elegant.IshikawaClearanceFacts

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-! Route x-bound for placed rib pieces.

`ishikawaBoundaryRouteXNonpos` discharges `IshikawaBoundaryRouteXNonpos`, the
residual of `ishikawaBoundaryPieceClearance`. The cause piece carries the
points `⟨0, spine⟩` and `⟨-run p length, …⟩`, both with `x ≤ 0`. An entry
piece carries the endpoints of its born bone; every bone satisfies `x0 ≤ 0`
and `x1 ≤ 0` by induction over `IndexedBoneGenealogy`: even-born bones
interpolate inside their parent's span (the even slot gap `t + r.heights ≤
par.t1` bounds the interpolation fraction, so no drawn-count control is
needed), odd-born bones take `x0 ≤ 0` from the residual
`IshikawaBoundaryOddBoneXNonpos` and fall by `run p (t - par.t0) ≥ 0`. The
residual is true because the `place` loop keeps every bone's drawn counter
`≤ count`; the pure genealogy admits draws beyond `count`, where the odd
interpolation overshoots, so exactly this class stays named. -/

/-- The executed measured rib instance of a generated cause. -/
def IshikawaBoundaryExecRib (ns : List Tree.Node) (p : Params) (ribs : List Rib)
    (cause k : Nat) : Rib :=
  effectivePlacedInput ns (measuredSideLength p ribs) (generatedRib ns (cause, k))

/-- Residual (odd-born bones): in every executed layout, every odd-depth born
bone of every generated rib source satisfies `x0 ≤ 0`. True because the
`place` loop keeps every bone's drawn counter `≤ count` (each draw records one
further odd child of the bone's node), which bounds the odd interpolation
handle `par.count - par.drawn`; the pure `IndexedBoneGenealogy` admits draws
beyond `count`, where the odd interpolation overshoots `par.x0`, so this
class needs the drawn-count loop invariant. -/
def IshikawaBoundaryOddBoneXNonpos (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (cause k : Nat)
    (_hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs)
    (parj : Bone) (ej : Entry) (j : Nat) (posj : Nat × Nat) (bj : Bone),
    IndexedBoneGenealogy e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile)
      (IshikawaBoundaryExecRib e.input.nodes
        (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k)
      (ej.parent + 1).toNat parj →
    (ej, j) ∈ (generatedRib e.input.nodes (cause, k)).entries.zipIdx →
    (generatedRib e.input.nodes (cause, k)).order.zipIdx.find?
      (fun v => v.1 == j) = some posj →
    ej.depth % 2 ≠ 0 →
    bj = depthBone (Elegant.Kinds.Ishikawa.params m.profile) parj ej.depth
      (Int.fdiv ((IshikawaBoundaryExecRib e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).length *
        (posj.2 + 1 : Nat))
        ((generatedRib e.input.nodes (cause, k)).entries.length + 1 : Nat))
      (children e.input.nodes ej.node).length
      (run (Elegant.Kinds.Ishikawa.params m.profile)
        (IshikawaBoundaryExecRib e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).heights + 3) →
    bj.x0 ≤ 0

/-- The slope and inset parameters of a successful nonempty layout. -/
private theorem routex_param_facts (ns : List Tree.Node) (p : Params)
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

/-- Every bone of a generated rib's genealogy satisfies `x0 ≤ 0` and `x1 ≤ 0`,
given the odd-born residual for the rib. -/
private theorem boundary_genealogy_x_nonpos_of_odd
    (ns : List Tree.Node) (p : Params) (raw : Tree.Layout)
    (hrun : layout ns p = .ok raw)
    (ribs : List Rib)
    (hg : ribs = (children ns 0).zipIdx.map (generatedRib ns))
    (cause k : Nat) (hsource : generatedRib ns (cause, k) ∈ ribs)
    (hcause : cause ∈ children ns 0)
    (hodd : ∀ (parj : Bone) (ej : Entry) (j : Nat) (posj : Nat × Nat) (bj : Bone),
      IndexedBoneGenealogy ns p (IshikawaBoundaryExecRib ns p ribs cause k)
        (ej.parent + 1).toNat parj →
      (ej, j) ∈ (generatedRib ns (cause, k)).entries.zipIdx →
      (generatedRib ns (cause, k)).order.zipIdx.find?
        (fun v => v.1 == j) = some posj →
      ej.depth % 2 ≠ 0 →
      bj = depthBone p parj ej.depth
        (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
          (posj.2 + 1 : Nat))
          ((generatedRib ns (cause, k)).entries.length + 1 : Nat))
        (children ns ej.node).length
        (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3) →
      bj.x0 ≤ 0)
    (b : Bone) (index : Nat)
    (hgene : IndexedBoneGenealogy ns p (IshikawaBoundaryExecRib ns p ribs cause k)
      index b) :
    b.x0 ≤ 0 ∧ b.x1 ≤ 0 := by
  have hlink := Elegant.Kinds.IshikawaValid.successful_link ns p raw hrun
  have hne : ns ≠ [] := by
    intro hnil
    have hc : children ns 0 = [] := by
      rw [hnil]
      rfl
    rw [hc] at hcause
    simp at hcause
  have hparam := routex_param_facts ns p raw hne hrun
  have hcos : 0 ≤ p.cos := hparam.1
  have hsin : 1 ≤ p.sin := hparam.2.1
  have hrL : 0 ≤ (IshikawaBoundaryExecRib ns p ribs cause k).length :=
    successful_nonempty_effective_length_nonnegative ns p raw hne hrun ribs
      (generatedRib ns (cause, k))
  have hh0 : 0 ≤ (IshikawaBoundaryExecRib ns p ribs cause k).heights := by
    show 0 ≤ (generatedRib ns (cause, k)).heights
    rw [(generated_rib_fields ns cause k).2.2.2]
    exact entry_height_fold_initial ns _ 0
  have hfold : effectivePlacedInput ns (measuredSideLength p ribs)
      (generatedRib ns (cause, k)) = IshikawaBoundaryExecRib ns p ribs cause k := rfl
  induction hgene with
  | root =>
    constructor
    · show (0 : Int) ≤ 0
      exact Int.le_refl 0
    · show -run p (IshikawaBoundaryExecRib ns p ribs cause k).length ≤ 0
      have hrun0 : 0 ≤ run p (IshikawaBoundaryExecRib ns p ribs cause k).length :=
        Int.fdiv_nonneg (Int.mul_nonneg hrL hcos) (by omega)
      omega
  | entry par ej idx pos hpar he hpos ih =>
    obtain ⟨hpx0, hpx1⟩ := ih
    have hgap := generated_entry_parent_slot_gaps ns p ribs hg cause k hsource
      hlink hcause ej idx pos par he hpos hpar
    by_cases hd : ej.depth % 2 = 0
    · -- even-born bone: interpolation inside the parent span, then a fall
      obtain ⟨hg1raw, hg2raw⟩ := hgap.2 hd
      rw [hfold] at hg1raw hg2raw
      have hg1 : par.t0 + (IshikawaBoundaryExecRib ns p ribs cause k).heights ≤
          Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) := hg1raw
      have hg2 : Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) +
          (IshikawaBoundaryExecRib ns p ribs cause k).heights ≤ par.t1 := hg2raw
      have hm0 : 0 ≤ Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0 := by
        omega
      have hmd : Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0 ≤
          par.t1 - par.t0 := by
        omega
      have hx0e : (depthBone p par ej.depth
            (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
              (pos.2 + 1 : Nat))
              ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat))
            (children ns ej.node).length
            (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3)).x0 =
          par.x0 + Int.fdiv
            ((par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
              (pos.2 + 1 : Nat))
              ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0))
            (par.t1 - par.t0) := by
        simp [depthBone, hd]
      have hends := depthBone_even_endpoints p par ej.depth
        (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
          (pos.2 + 1 : Nat))
          ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat))
        (children ns ej.node).length
        (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3) hd
      have hb0 : (depthBone p par ej.depth
            (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
              (pos.2 + 1 : Nat))
              ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat))
            (children ns ej.node).length
            (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3)).x0 ≤ 0 := by
        rw [hx0e]
        by_cases hd0 : par.t1 - par.t0 = 0
        · have hmz : Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
              (pos.2 + 1 : Nat))
              ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0 = 0 := by
            omega
          have hf : Int.fdiv
              ((par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                (pos.2 + 1 : Nat))
                ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0))
              (par.t1 - par.t0) = 0 := by
            rw [hd0, hmz, Int.mul_zero]
            rfl
          omega
        · have hd0' : 0 < par.t1 - par.t0 := by omega
          by_cases hpa : par.x1 - par.x0 ≤ 0
          · have hh : (par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                (pos.2 + 1 : Nat))
                ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0) ≤ 0 := by
              have h := Int.mul_le_mul_of_nonneg_right
                (show par.x1 - par.x0 ≤ 0 by omega) hm0
              simpa only [Int.zero_mul] using h
            have hf : Int.fdiv
                ((par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                  (pos.2 + 1 : Nat))
                  ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0))
                (par.t1 - par.t0) ≤ 0 :=
              Chart.fdiv_le_of_le_mul hd0' (by omega)
            omega
          · have hpa' : 0 < par.x1 - par.x0 := by omega
            have hm1 : (par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                  (pos.2 + 1 : Nat))
                  ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0) ≤
                (par.x1 - par.x0) * (par.t1 - par.t0) :=
              Int.mul_le_mul_of_nonneg_left hmd (by omega)
            have hm1' : (par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                  (pos.2 + 1 : Nat))
                  ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0) ≤
                (par.t1 - par.t0) * (par.x1 - par.x0) := by
              rw [Int.mul_comm (par.t1 - par.t0) (par.x1 - par.x0)]
              exact hm1
            have hf : Int.fdiv
                ((par.x1 - par.x0) * (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
                  (pos.2 + 1 : Nat))
                  ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0))
                (par.t1 - par.t0) ≤ par.x1 - par.x0 :=
              Chart.fdiv_le_of_le_mul hd0' hm1'
            omega
      constructor
      · exact hb0
      · rw [hends.2.2]
        have hmargin : 0 ≤ run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3 := by
          have h : 0 ≤ run p (IshikawaBoundaryExecRib ns p ribs cause k).heights :=
            Int.fdiv_nonneg (Int.mul_nonneg hh0 hcos) (by omega)
          omega
        have hbl : 0 ≤ boneLength p (children ns ej.node).length
            (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3) := by
          unfold boneLength
          exact Int.le_trans
            (Int.mul_nonneg (Int.natCast_nonneg _) hmargin) (Int.le_max_right _ _)
        omega
    · -- odd-born bone: residual start, then a fall by a nonnegative run
      have hoddgraw := hgap.1 hd
      rw [hfold] at hoddgraw
      have hoddg : par.t0 + (IshikawaBoundaryExecRib ns p ribs cause k).heights ≤
          Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) := hoddgraw
      have hb0 : (depthBone p par ej.depth
            (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
              (pos.2 + 1 : Nat))
              ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat))
            (children ns ej.node).length
            (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3)).x0 ≤ 0 :=
        hodd par ej idx pos _ hpar he hpos hd rfl
      have hends := depthBone_odd_endpoints p par ej.depth
        (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
          (pos.2 + 1 : Nat))
          ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat))
        (children ns ej.node).length
        (run p (IshikawaBoundaryExecRib ns p ribs cause k).heights + 3) hd
      have hrise : 0 ≤ Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0 := by
        omega
      have hrun0 : 0 ≤ run p
          (Int.fdiv ((IshikawaBoundaryExecRib ns p ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((IshikawaBoundaryExecRib ns p ribs cause k).entries.length + 1 : Nat) - par.t0) :=
        Int.fdiv_nonneg (Int.mul_nonneg hrise hcos) (by omega)
      constructor
      · exact hb0
      · rw [hends.2.2.2]
        omega
  | draw index b0 hb0 ih =>
    exact ih

/-- The boundary route-x residual, discharged modulo the odd-born-bone
residual. -/
theorem ishikawaBoundaryRouteXNonpos (m : Model)
    (_hwf : WellFormed m) (_hlimits : WithinLimits m)
    (hodd : IshikawaBoundaryOddBoneXNonpos m) :
    IshikawaBoundaryRouteXNonpos m := by
  intro e rib hrib piece hmem q hq
  obtain ⟨source, cause, k, hsource0, hcause0, heq, hbound⟩ :=
    placed_rib_parent_draw_bound e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout
      e.ribs e.placed e.length e.spine e.hribs e.hplaced rib hrib
      piece.1 piece.2.1 piece.2.2 hmem
  rw [e.hlength] at hbound
  rw [heq] at hbound
  have hsource : generatedRib e.input.nodes (cause, k) ∈ e.ribs := by
    rw [← heq]
    exact hsource0
  have hcause : cause ∈ children e.input.nodes 0 :=
    List.fst_mem_of_mem_zipIdx hcause0
  have hodd' := hodd e cause k hsource
  have hne : e.input.nodes ≠ [] := by
    intro hnil
    have hh := e.hhead
    rw [hnil] at hh
    simp at hh
  have hparam := routex_param_facts e.input.nodes
    (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout
  have hcos : 0 ≤ (Elegant.Kinds.Ishikawa.params m.profile).cos := hparam.1
  have hsin : 1 ≤ (Elegant.Kinds.Ishikawa.params m.profile).sin := hparam.2.1
  have hrL : 0 ≤ (IshikawaBoundaryExecRib e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).length :=
    successful_nonempty_effective_length_nonnegative e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw hne e.hlayout e.ribs
      (generatedRib e.input.nodes (cause, k))
  have hfoldE : effectivePlacedInput e.input.nodes
      (measuredSideLength (Elegant.Kinds.Ishikawa.params m.profile) e.ribs)
      (generatedRib e.input.nodes (cause, k)) =
      IshikawaBoundaryExecRib e.input.nodes
        (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k := rfl
  rcases hbound with hcauseR |
    ⟨en, idx, pos, par, n, he, hpos, hn, hi, hpar, hdrawnle, hpoints⟩
  · rw [hcauseR.2] at hq
    have hrun0 : 0 ≤ run (Elegant.Kinds.Ishikawa.params m.profile)
        (IshikawaBoundaryExecRib e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).length :=
      Int.fdiv_nonneg (Int.mul_nonneg hrL hcos) (by omega)
    rcases List.mem_cons.mp hq with rfl | hq'
    · show (0 : Int) ≤ 0
      exact Int.le_refl 0
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · show -run (Elegant.Kinds.Ishikawa.params m.profile)
          (IshikawaBoundaryExecRib e.input.nodes
            (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).length ≤ 0
        omega
      · exact absurd hq'' (by simp)
  · have hb : IndexedBoneGenealogy e.input.nodes
        (Elegant.Kinds.Ishikawa.params m.profile)
        (IshikawaBoundaryExecRib e.input.nodes
          (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k)
        (idx + 1)
        (depthBone (Elegant.Kinds.Ishikawa.params m.profile) par en.depth
          (Int.fdiv ((IshikawaBoundaryExecRib e.input.nodes
              (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).length *
            (pos.2 + 1 : Nat))
            ((generatedRib e.input.nodes (cause, k)).entries.length + 1 : Nat))
          (children e.input.nodes en.node).length
          (run (Elegant.Kinds.Ishikawa.params m.profile)
            (IshikawaBoundaryExecRib e.input.nodes
              (Elegant.Kinds.Ishikawa.params m.profile) e.ribs cause k).heights + 3)) :=
      IndexedBoneGenealogy.entry par en idx pos hpar he hpos
    have hxb := boundary_genealogy_x_nonpos_of_odd e.input.nodes
      (Elegant.Kinds.Ishikawa.params m.profile) e.raw e.hlayout e.ribs e.hribs
      cause k hsource hcause hodd' _ _ hb
    rw [hpoints] at hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hxb.1
    · rcases List.mem_cons.mp hq' with rfl | hq''
      · exact hxb.2
      · exact absurd hq'' (by simp)

/-- The boundary piece clearance without the original route-x hypothesis:
only the odd-born-bone residual remains. -/
theorem ishikawaBoundaryPieceClearance' (m : Model)
    (hwf : WellFormed m) (hlimits : WithinLimits m)
    (hodd : IshikawaBoundaryOddBoneXNonpos m) :
    IshikawaBoundaryPieceClearance m :=
  ishikawaBoundaryPieceClearance m hwf hlimits
    (ishikawaBoundaryRouteXNonpos m hwf hlimits hodd)

end Elegant.Kinds.IshikawaFinal
