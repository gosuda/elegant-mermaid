import Elegant.Layered.ExactLoopEnvelopeReserveProof
import Elegant.Layered.ExactRunFrameNestingProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.Pipeline

set_option autoImplicit false

open Elegant Layered

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! Loop-envelope group overlap miss, W-form per-execution reduction.

Target leaf (`ExactLoopEnvelopeReserveProof.lean`): `XLEM_GroupOverlapMiss`
(the y-overlap half of `XLEM_GroupOwnerOtherRank`).

Probe truth (`proofs/wip/Probe/GroupOverlapMissTProbe.lean`,
`proofs/wip/Probe/GroupOverlapMissTNestedProbe.lean`, vector and cell
profiles, declaration order; `fp` is `loopFootprintExt` at the looping group
top, `yOvl`/`xOvl` are footprint-vs-box interval overlaps, `disj` is their
negation, `mem` is owner-decl membership in the box cluster path):

- `grp-1loop-big`, `grp-1loop-long`, `nest-1loop`, `unrelated-1loop`,
  `empty-nest`, `deep-nest`, `grp-cell`: every other-rank in-scope box has
  `yOvl=true`, `xOvl=false`, `disj=true`; members (`mem=true`) sit left of
  the footprint, foreign boxes (`mem=false`) sit right of it.
- `outer-loop`, `outer-loop-unrelated`, `outer-loop-longtitle` (looping
  outer group with a nested inner group): nested titles (`border 3`,
  `yOvl=true`) sit left of the footprint; side markers and proxy tops or
  bottoms (`border ±1`/`±2`) all have height zero, hence `yOvl=false`.
- `zero-sib` (zero-size fixed box), `selfloop-plain`, `dup-ill` (rejected at
  prep, no execution): degenerate inputs contribute no counterexample.
- Exact-owner check: `exactIds = ["g"]` on a looping group is rejected at
  `exactGraph` (no execution); a fixed-size group owner is demoted to a
  plain node. Every looping group top on an executed run has
  `run.exact.contains tail = false`.

What is proved: `XLEM_groupOverlapMiss_holds`, the per-execution W-form
reduction. For one executed exact run with local admission
(`WellFormed (inputModel inp o)`, `framedParents inp = true`), a looping
group top misses every other-rank in-scope real box that overlaps the
extended footprint vertically. The split is on plain membership: a plain
member (`border 0` candidate node whose path contains the owner decl) lies
in the owner frame by the proved `exactRunFrameNesting`, hence left of the
footprint origin; every other box (foreign boxes, nested titles and
markers, proxies) is covered by the single residual below.

What stays open: `XLEM_GroupOverlapForeignGap`, the x-gap for every
non-plain-member y-overlapping box (foreign boxes by the foreign cluster
rank spans with the loop extent counted in the sides separation; nested
titles by caption fit; proxies and markers hold vacuously since height
zero contradicts the y-overlap premise). It is strictly narrower than the
target (one extra non-membership premise) and true on every probe row
above (`xOvl=false` on all `yOvl=true` rows). The full `∀`-quantified
`XLEM_GroupOverlapMiss` assembles from this W-form reduction at use sites
that carry admission. All record literals are on one line. -/

/-- X-gap for non-plain-member y-overlapping boxes: a box that is not a
plain member of the looping group (no `border 0` candidate node with the
owner decl in its path) and overlaps the extended footprint vertically is
separated from it horizontally. Strictly narrower than
`XLEM_GroupOverlapMiss` (one extra non-membership premise); true on every
group probe row (foreign boxes, nested titles: `xOvl=false` on all
`yOvl=true` rows; proxies and markers hold vacuously). -/
def XLEM_GroupOverlapForeignGap (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    (cg.nodes.getD e.tail default).border = -2 →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h) →
    (¬ ∃ m : Node, cg.nodes[v]? = some m ∧ m.border = 0 ∧
      m.clusterPath.contains (((cg.nodes[e.tail]?).map (·.decl)).getD 0) = true) →
    (loopFootprintExt cg run execution.measured e.tail).x +
        (loopFootprintExt cg run execution.measured e.tail).w ≤
        (RouteImpl.boxRect run.proper run.xs run.ys v).x ∨
      (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
        (loopFootprintExt cg run execution.measured e.tail).x

/-- Group-owner other-rank miss in W form: on one executed exact run with
local admission, a looping group top misses every other-rank in-scope real
box overlapping the extended footprint vertically. Plain members follow
from `exactRunFrameNesting`; the rest is the residual above. -/
theorem XLEM_groupOverlapMiss_holds (exactIds : List String)
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (hgap : XLEM_GroupOverlapForeignGap exactIds) :
    ∀ (comp : List Nat) (candidate : Nat) (run : Run)
      (orderOptions : OrderOptions) (cg : Graph) (k : Nat) (e : Edge) (v : Nat),
    comp ∈ components execution.graph →
    cg = componentCandidate execution.graph comp candidate →
    componentRunX execution.params (exactDecls exactIds inp) cg execution.measured
      orderOptions = .ok run →
    cg.edges[k]? = some e →
    e.tail = e.head →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] →
    (rk run.coordinateProper.rank v).toNat ≠
      (rk run.coordinateProper.rank e.tail).toNat →
    (cg.nodes.getD e.tail default).border = -2 →
    max (loopFootprintExt cg run execution.measured e.tail).y
        (RouteImpl.boxRect run.proper run.xs run.ys v).y <
      min ((loopFootprintExt cg run execution.measured e.tail).y +
        (loopFootprintExt cg run execution.measured e.tail).h)
        ((RouteImpl.boxRect run.proper run.xs run.ys v).y +
          (RouteImpl.boxRect run.proper run.xs run.ys v).h) →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  intro comp candidate run orderOptions cg k e v hcomp hcg hrun hedge hself hv
    hreal hscope0 hscope1 hrank hbdr hyov
  subst hcg
  have hbd := sceneExecutionX_edges_bounded execution
  have hbnd := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd (List.mem_of_getElem? hedge)
  have htCG : e.tail <
      (componentCandidate execution.graph comp candidate).nodes.length := hbnd.1
  obtain ⟨nt, hnt⟩ : ∃ nt,
      (componentCandidate execution.graph comp candidate).nodes[e.tail]? =
        some nt :=
    ⟨_, List.getElem?_eq_getElem htCG⟩
  have htG : nt.border = -2 := by
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD
        e.tail default = nt := by
      simp only [List.getD_eq_getElem?_getD, hnt, Option.getD_some]
    rw [← hget]
    exact hbdr
  by_cases hpl : ∃ m : Node,
      (componentCandidate execution.graph comp candidate).nodes[v]? = some m ∧
      m.border = 0 ∧
      m.clusterPath.contains
        ((((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map
          (·.decl)).getD 0) = true
  · obtain ⟨m, hcgv, hb0, hmem⟩ := hpl
    have hdeclEq : ((((componentCandidate execution.graph comp candidate).nodes[e.tail]?).map
        (·.decl)).getD 0) = nt.decl := by
      simp only [hnt, Option.map_some, Option.getD_some]
    rw [hdeclEq] at hmem
    have hnest := exactRunFrameNesting execution hwf hframed
    have hcon := hnest.1 comp candidate run orderOptions hcomp hrun e.tail v
      nt m hnt htG hcgv hb0 hmem
    have hb0get : ((componentCandidate execution.graph comp candidate).nodes.getD
        v default).border = 0 := by
      simp only [List.getD_eq_getElem?_getD, hcgv, Option.getD_some]
      exact hb0
    have hcond : ((((componentCandidate execution.graph comp candidate).nodes.getD
        v default).border != -2)) = true := by
      rw [hb0get]
      decide
    have hfr : frameRect execution.params
        (componentCandidate execution.graph comp candidate) run v =
        nodeRect (componentCandidate execution.graph comp candidate) run v := by
      unfold frameRect
      simp only [hcond, ↓reduceIte]
    obtain ⟨nvp, hrec⟩ : ∃ nvp, run.proper.nodes[v]? = some nvp :=
      ⟨_, List.getElem?_eq_getElem hv⟩
    have hfb : frameRect execution.params
        (componentCandidate execution.graph comp candidate) run v =
        RouteImpl.boxRect run.proper run.xs run.ys v := by
      rw [hfr, nodeRect_of_record hrec]
      simp only [RouteImpl.boxRect, RouteImpl.leftOf, RouteImpl.xAt,
        RouteImpl.yAt, RouteImpl.nodeW, RouteImpl.nodeH, hrec]
    have hfx : (loopFootprintExt (componentCandidate execution.graph comp candidate)
        run execution.measured e.tail).x =
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run e.tail).x +
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run e.tail).w := rfl
    have hgapR : (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
        (loopFootprintExt (componentCandidate execution.graph comp candidate)
          run execution.measured e.tail).x := by
      rw [hfx, ← hfb]
      exact hcon.2.1
    have hgapOr : (loopFootprintExt (componentCandidate execution.graph comp candidate)
          run execution.measured e.tail).x +
        (loopFootprintExt (componentCandidate execution.graph comp candidate)
          run execution.measured e.tail).w ≤
        (RouteImpl.boxRect run.proper run.xs run.ys v).x ∨
      (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤
        (loopFootprintExt (componentCandidate execution.graph comp candidate)
          run execution.measured e.tail).x :=
      Or.inr hgapR
    exact rect_disjoint_of_x hgapOr
  · have hgapOr := hgap inp o res execution comp candidate run orderOptions
      (componentCandidate execution.graph comp candidate) k e v hcomp rfl hrun
      hedge hself hv hreal hscope0 hscope1 hrank hbdr hyov hpl
    exact rect_disjoint_of_x hgapOr

end PipelineImpl
end Layered
end Elegant
