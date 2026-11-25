import Elegant.Kinds.IshikawaBoundaryRouteX
import Elegant.Kinds.IshikawaCrossRibSameSide

set_option autoImplicit false

namespace Elegant.Kinds.IshikawaFinal

open Elegant.Ishikawa

/-!
# Place-loop drawn-count bound for Ishikawa ribs.

Target statements (exact):
* `place_drawn_le_count`: after any prefix of the `place` bone loop, every
  bone satisfies `drawn ≤ count` (real fields `Bone.drawn`, `Bone.count`).
* `accounted_odd_born_x0_nonpos` and `accounted_odd_born_x0_nonpos_of_prefix`:
  the true per-birth core of `IshikawaBoundaryOddBoneXNonpos`: an odd-depth
  born bone satisfies `x0 ≤ 0` once the parent's drawn counter, nonnegativity,
  span, and abscissa are supplied (the prefix corollary discharges the drawn
  half through the loop invariant).
* `IshikawaRouteXExtentLower`: the lower half of `IshikawaRouteXEnvelope`
  (every route point lies at or right of the pair's box minimum). It is used
  once, in `ishikawaRouteXEnvelope_of_lower_upper`, and through it in
  `ishikawaCrossRibPieceClearance''`.

Probe (copy of `proofs/wip/Probe/IshikawaRawProbe.lean` replay `birthBones`
plus per-piece route checks, 5 nested samples × vector/cell profiles,
10 successful layouts, 16 placed ribs, 78 birth-frame bones):
* `drawBad = 0`: every birth-frame bone satisfies `drawn ≤ count`.
* `oddBad = 0`: all 28 executed odd-born bones satisfy `x0 ≤ 0`.
* `upBad = loBad = extBad = 0`: all 156 placed route points satisfy
  `ownRect.x ≤ q.x ≤ 0` and the single-rib extent lower bound.

`IshikawaBoundaryOddBoneXNonpos` as stated is FALSE, so it is not proved here.
Its quantifier ranges over every `IndexedBoneGenealogy` derivation, and
`.draw` raises `drawn` without bound at a fixed index. Executed witness
(s06b vector profile, rib `(2, 1)`, first odd entry): the executed replay
parent is `x0 = -900, x1 = -5060, count = 1, drawn = 1` with born bone
`x0 = -2980`; the overdrawn variant `{ par with drawn := 2 }` (a valid
derivation at the same index by `.draw`) gives an odd-born bone with
`x0 = -900 + fdiv ((-5060 + 900) * (1 - 2)) 2 = 1180 > 0`
(the odd `x0` formula does not involve the slot `t`). Hence no proof of the
universal statement exists; the unconditional `ishikawaBoundaryPieceClearance''`
through it is blocked. The provable per-birth form is the two accounted
lemmas below; closing the unconditional route bound needs a birth-index
induction in the owning file, not a derivation induction (ancestor draws are
unbounded in the pure genealogy).
-/

/-- The executed rib input is the measured-length rib (used to tie the
counterexample witness to the executed genealogy rib). -/
theorem execrib_is_effective (ns : List Tree.Node) (p : Params) (ribs : List Rib)
    (cause k : Nat) :
    IshikawaBoundaryExecRib ns p ribs cause k =
      effectivePlacedInput ns (measuredSideLength p ribs)
        (generatedRib ns (cause, k)) := rfl

/-- Drawn-count invariant of the `place` bone loop: after any processed prefix
`done`, every bone accounted at its owner satisfies `drawn ≤ count`. The loop
records one further odd child of the bone's node per odd-depth draw, and the
odd-child count of any prefix is bounded by the node's child count
(`generated_prefix_odd_child_count_le`). -/
theorem place_drawn_le_count
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (owner : Nat) (par : Bone)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) owner par)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (hdrawn : par.drawn = processedOddDraws done owner) :
    par.drawn ≤ par.count :=
  generated_parent_drawn_le_count ns p cause k length hlink hcause
    owner par hgene done rest hprefix hdrawn

/-- Pure odd-birth bound: with the drawn counter inside its budget, the odd
interpolation handle `par.count - par.drawn` stays in `[0, par.count + 1]`,
so the interpolated end stays inside the parent span and below the origin. -/
theorem accounted_odd_born_x0_nonpos
    (p : Params) (par : Bone) (depth : Nat) (t nchild margin : Int)
    (hodd : depth % 2 ≠ 0)
    (hdrawn : par.drawn ≤ par.count)
    (hdrawn0 : 0 ≤ par.drawn)
    (hcount : 0 ≤ par.count)
    (hspan : par.x1 ≤ par.x0)
    (hpx0 : par.x0 ≤ 0) :
    (depthBone p par depth t nchild margin).x0 ≤ 0 := by
  have hends := depthBone_odd_endpoints p par depth t nchild margin hodd
  have hden : 0 < par.count + 1 := by omega
  have hweight : 0 ≤ par.count - par.drawn := by omega
  have hcap : par.count - par.drawn ≤ par.count + 1 := by omega
  have hb := nonpositive_interpolation_between par.x0 par.x1
    (par.count + 1) (par.count - par.drawn) hspan hden hweight hcap
  calc (depthBone p par depth t nchild margin).x0
      = par.x0 + Int.fdiv ((par.x1 - par.x0) * (par.count - par.drawn))
          (par.count + 1) := hends.2.2.1
    _ ≤ par.x0 := hb.2
    _ ≤ 0 := hpx0

/-- The loop invariant discharges the drawn half of the odd-birth bound for
every accounted parent of an executed `place` run. -/
theorem accounted_odd_born_x0_nonpos_of_prefix
    (ns : List Tree.Node) (p : Params) (cause k : Nat) (length : Bool → Int)
    (hlink : Tree.link ns = true) (hcause : cause ∈ children ns 0)
    (owner : Nat) (par : Bone)
    (hgene : IndexedBoneGenealogy ns p
      (effectivePlacedInput ns length (generatedRib ns (cause, k))) owner par)
    (done rest : List (Entry × Nat))
    (hprefix : (generatedRib ns (cause, k)).entries.zipIdx = done ++ rest)
    (hdrawn : par.drawn = processedOddDraws done owner)
    (depth : Nat) (t nchild margin : Int)
    (hodd : depth % 2 ≠ 0)
    (hspan : par.x1 ≤ par.x0)
    (hpx0 : par.x0 ≤ 0) :
    (depthBone p par depth t nchild margin).x0 ≤ 0 := by
  have hle := place_drawn_le_count ns p cause k length hlink hcause
    owner par hgene done rest hprefix hdrawn
  have hnn := boneGenealogy_nonnegative_counters (indexedBoneGenealogy_erase hgene)
  exact accounted_odd_born_x0_nonpos p par depth t nchild margin hodd
    hle hnn.2 hnn.1 hspan hpx0

/-- Residual (route x-envelope, lower half): for the executed `assemblePairs`
run, every route point of every placed rib piece lies at or right of the
pair's box minimum. The upper half (`q.x ≤ 0`) is the pre-existing
`IshikawaBoundaryRouteXNonpos` hypothesis. Probed with zero violations
(`loBad = extBad = 0` over 156 placed route points). -/
def IshikawaRouteXExtentLower (m : Model) : Prop :=
  ∀ (e : IshikawaRawExecution m) (P : List Rib) (r : Rib),
    r ∈ P → P ⊆ e.placed →
    ∀ (piece : Nat × Rect × List Point) (_hm : piece ∈ r.pieces)
      (q : Point) (_hq : q ∈ piece.2.2),
      (extent P).1 ≤ q.x

/-- The envelope splits into the lower residual and the upper hypothesis. -/
theorem ishikawaRouteXEnvelope_of_lower_upper (m : Model)
    (hlo : IshikawaRouteXExtentLower m)
    (hup : IshikawaBoundaryRouteXNonpos m) :
    IshikawaRouteXEnvelope m := by
  intro e P r hr hsub piece hm q hq
  exact ⟨hlo e P r hr hsub piece hm q hq, hup e r (hsub hr) piece hm q hq⟩

/-- The same-side cross-rib clearance conditional on the envelope halves:
the lower residual proved here and the upper route bound. -/
theorem ishikawaCrossRibPieceClearance'' (m : Model)
    (hlo : IshikawaRouteXExtentLower m)
    (hup : IshikawaBoundaryRouteXNonpos m) :
    IshikawaCrossRibPieceClearance m :=
  ishikawaCrossRibPieceClearance' m
    (ishikawaRouteXEnvelope_of_lower_upper m hlo hup)

end Elegant.Kinds.IshikawaFinal
