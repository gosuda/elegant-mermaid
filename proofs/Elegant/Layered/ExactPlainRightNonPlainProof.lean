import Elegant.Layered.ExactLoopEnvelopeRightProof
import Elegant.Layered.ExactLoopEnvelopeSidesProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Right non-plain residual, narrowed by proper height.

Engine truth (`proofs/wip/Probe/PlainRightNonPlainTProbe.lean`, vector
profile, both candidates; `fp` is `loopFootprintExt` at the looping
border-0 owner, `rb` the later same-layer real box):
- `sib`, `zero`: layers `[[0],[1]]`, no same-layer owner/later pair.
- `empty-group`: comps `[0,3]` layers `[[3,0,2,4],[5,1,6]]` and `[1,2]`
  layers `[[0],[1]]`; no border-0 self-loop owner with a same-layer
  later real box.
- `nested`: owner `t = 2`, later `v = 23` and `v = 13`, both appended
  (`cg`-none), `proper` border `1`, `dummy = false`, `h = 0`, `w = 512`,
  `disj = true` on both candidates (`fpend = 8959`, `rx = 9982/11518`).
- `ill`: preparation fails with `LayoutError.domain`, vacuous.
- `exact-a`: owner `t = 0`, later `v = 1` is an original plain node
  (`cg` border `0`), already closed by `XLEM_plainRightMiss_holds`.
- `dummy` (long edge forcing chain nodes): layers `[[0],[1,2]]`, no
  same-layer pair.
So every executed in-scope same-layer later non-plain box has proper
height zero (proxy `±2`, side marker `±1`, appended marker); dummy chain
nodes are excluded by `IsReal` in any case. A height-zero box meets no
footprint interior (`max/min` emptiness). The only open sub-case is a
later non-plain box with nonzero proper height, which never occurs in
the probes.

Proved here:
- `xlem_plainRightNonPlain_holds (hPos : XLEM_PlainRightNonPlain_PosH _)`:
  reduction of `XLEM_PlainRightNonPlain` to the positive-height
  residual via the height-zero miss.
Open (one residual, strictly narrower by the height premise, vacuous on
all probes above):
- `XLEM_PlainRightNonPlain_PosH`.
-/

/-- Positive-height right non-plain residual: the right miss for a later
non-original-plain box with nonzero proper height. Strictly narrower
than `XLEM_PlainRightNonPlain` (extra height premise), vacuous on every
probe case (all executed in-scope same-layer non-plain later boxes have
proper height zero). -/
def XLEM_PlainRightNonPlain_PosH (exactIds : List String) : Prop :=
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
    (cg.nodes.getD e.tail default).border = 0 →
    (¬ ∃ nv, cg.nodes[v]? = some nv ∧ nv.border = 0) →
    RouteImpl.nodeH run.proper v ≠ 0 →
    ∀ {layer : List Nat}, layer ∈ run.layers →
    ∀ {pu pv : Nat}, layer[pu]? = some e.tail → layer[pv]? = some v → pu < pv →
    ¬ (loopFootprintExt cg run execution.measured e.tail).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- A height-zero box meets no footprint interior. -/
private theorem XLEMRNP_height_miss {run : Run} {cg : Graph}
    {labels : List MeasuredLabel} {t v : Nat}
    (hH : RouteImpl.nodeH run.proper v = 0) :
    ¬ (loopFootprintExt cg run labels t).meetsInterior
      (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  have hh : (RouteImpl.boxRect run.proper run.xs run.ys v).h = 0 := by
    simpa only [RouteImpl.boxRect] using hH
  intro hmeet
  obtain ⟨_, hy⟩ := hmeet
  omega

/-- Right non-plain reduction: the height-zero sub-case (proxies, side
markers, appended markers, and any zero-height dummy) misses by height;
the positive-height sub-case is the single residual. -/
theorem xlem_plainRightNonPlain_holds (exactIds : List String)
    (hPos : XLEM_PlainRightNonPlain_PosH exactIds) :
    XLEM_PlainRightNonPlain exactIds := by
  intro inp o res execution comp candidate run orderOptions cg k e v
    hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hOrig
    layer hlayer pu pv hpu hpv hlt
  by_cases hH : RouteImpl.nodeH run.proper v = 0
  · exact XLEMRNP_height_miss (labels := execution.measured) hH
  · exact hPos inp o res execution comp candidate run orderOptions cg k e v
      hcomp hcg hrun hk hloop hv hreal hscope0 hscope1 hB0 hOrig hH
      hlayer hpu hpv hlt

end PipelineImpl
end Layered
end Elegant
