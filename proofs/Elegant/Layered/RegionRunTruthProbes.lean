import Elegant.Layered.RegionActualParts
import Elegant.Scene
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region run truth probes: C2 / node-band (A) and C5 endpoints (B).

Decidable checkers over executed `componentRunR` / `layoutRIds` results.
Evaluations live in `proofs/wip/Probe/RegionC2C5ProbeT*.lean`.

## Evidence table (executed 2026-11-19 via `lake env lean wip/Probe/RegionC2C5ProbeT*.lean`)


Run-level `report` = `(nodeBand, disjoint, decls, swaps)` on the first
component; dump-level = `(c2, c5)` on `layoutRIds`. All runs `.ok`.

| input | run-level | dump C2/C5 | verdict |
|---|---|---|---|
| two regions side by side (`inpTwoSide`, rapProbe clone) | (true, true, true, 0) | (10 boxes, 3 routes) (true, true) | A+B hold; C2 vacuous (0 same-parent exclusive pairs) |
| two regions, paired members (`inpPair`) | (true, true, true, 0) | (11, 3) (true, true) | A+B hold; C2 non-vacuous (2 ordered pairs) |
| nested regions (`inpNested`) | (true, true, true, 0) | (7, 2) (true, true) | A+B hold; C2 non-vacuous |
| region with back edge (`inpBack`, d1->a1 cycle) | (true, true, true, 0) | (11, 4) (true, true) | A+B hold; no swap needed |
| region with self-loop (`inpSelf`, a1->a1) | (true, true, true, 0) | (11, 4) (true, true) | A+B hold |
| cross-region edge (`inpCross`, a1->x1 outside) | (true, true, true, 0) | (12, 4) (true, true) | A+B hold |
| region in group with long title (`inpTitle`) | (true, true, true, 0) | (11, 3) (true, true) | A+B hold |
| two-cycle (`inpFlip`, a1->c1 + c1->a1) | (true, true, true, 1) | (11, 3) (true, true) | A+B hold WITH a genuine rewrite |

Flip detail (`edgeSwapDetail`): input edge `(tail 9, head 6, decl 1)` becomes
`cg'` edge `(tail 6, head 9, decl 1, reversed)`; decl preserved, endpoints
swapped. Per-route dump endpoints (`routeEndpointReport`): every route has its
first point on its input `from` box and its last point on its input `to` box.

No clause failed on any input, so no witness minimization was needed. All
three `_fact` defs below hold on every probe as stated.

Endpoint-lookup verdict: per-edge input-graph endpoint order is stale for
rewritten edges (the flip input proves the swap happens while `decl` is
preserved). Endpoint lookup must go through the rewritten graph `cg'`
(final orientations, `decl` linkage); the dump-level C5 statement over the
input `from`/`to` boxes is true as stated because executed routes still run
from-box to to-box.
-/

/-- Every proper node of the run sits in its rank band. -/
def rrtpNodeBandOk (run : Run) : Bool :=
  (List.range run.proper.nodes.length).all fun q =>
    match run.proper.nodes[q]? with
    | none => true
    | some _ =>
      let r := (rk run.coordinateProper.rank q).toNat
      match run.layers[r]? with
      | none => false
      | some l =>
        decide (run.top.getD r 0 ≤ run.ys.getD q 0) &&
        decide (run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
          run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l)

/-- Placed rects of border-0 nodes of `g` are pairwise disjoint. -/
def rrtpDisjointOk (P : Params) (g : Graph) (run : Run) : Bool :=
  (List.range g.nodes.length).all fun u =>
    (List.range g.nodes.length).all fun v =>
      match g.nodes[u]?, g.nodes[v]? with
      | some nodeU, some nodeV =>
        if nodeU.border != 0 || nodeV.border != 0 || u == v then true
        else decide (Disjoint (frameRect P g run u) (frameRect P g run v))
      | _, _ => true

/-- Rank rewriting preserves edge declarations. -/
def rrtpDeclsOk (cg cg' : Graph) : Bool :=
  decide (cg'.edges.map (fun e => e.decl) = cg.edges.map (fun e => e.decl))

/-- Number of edges whose endpoints were swapped by the ranking rewrite. -/
def rrtpSwapCount (cg cg' : Graph) : Nat :=
  (List.zip cg.edges cg'.edges).foldl (fun n q =>
    if q.1.tail == q.2.head && q.1.head == q.2.tail &&
      q.1.tail != q.1.head then n + 1 else n) 0

/-- Validator C2 on an executed dump. -/
def rrtpC2Ok (d : LayoutDump) : Bool := Validator.c2 d

/-- Validator C5 on an executed dump. -/
def rrtpC5Ok (d : LayoutDump) : Bool := Validator.c5 d

/-- Region form of `componentRunX_node_band`: every proper node of a
successful `componentRunR` sits in its rank band (candidate true form;
probes decide). -/
def componentRunR_node_bandR_fact : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    ∀ {q : Nat} {nd : ProperNode}, run.proper.nodes[q]? = some nd →
    ∃ l : List Nat,
      run.layers[(rk run.coordinateProper.rank q).toNat]? = some l ∧
      run.top.getD (rk run.coordinateProper.rank q).toNat 0 ≤ run.ys.getD q 0 ∧
      run.ys.getD q 0 + RouteImpl.nodeH run.proper q ≤
        run.top.getD (rk run.coordinateProper.rank q).toNat 0 +
          CoordsImpl.layerHeight run.coordinateProper l

/-- Region form of run disjointness: placed rects of border-0 nodes are
pairwise disjoint (candidate true form; probes decide). -/
def componentRunR_positions_disjointR_fact : Prop :=
  ∀ {P : Params} {exact : List Nat} {spec : Option RegionSpec} {inp : Input}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions},
    componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run) →
    ∀ {u v : Nat} {nodeU nodeV : Node},
      cg'.nodes[u]? = some nodeU → cg'.nodes[v]? = some nodeV →
      nodeU.border = 0 → nodeV.border = 0 → u ≠ v →
      Disjoint (frameRect P cg' run u) (frameRect P cg' run v)

/-- Region flat C5 endpoints: every route of a successful `layoutRIds`
result has its ends on the boundary of the boxes named by the input
route's `from`/`to` (candidate true form; probes decide whether the
lookup must go through `cg'`). -/
def layoutRIds_c5_endpoints_fact : Prop :=
  ∀ {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult},
    layoutRIds exactIds idSets inp o = .ok res → Validator.C5 res.scene.layoutDump

/-- The C2 checker is the validator test. -/
theorem rrtpC2Ok_eq (d : LayoutDump) : rrtpC2Ok d = Validator.c2 d := rfl

/-- The C5 checker is the validator test. -/
theorem rrtpC5Ok_eq (d : LayoutDump) : rrtpC5Ok d = Validator.c5 d := rfl

/-- The decl checker unfolds to the declaration equality. -/
theorem rrtpDeclsOk_eq (cg cg' : Graph) :
    rrtpDeclsOk cg cg' = decide (cg'.edges.map (fun e => e.decl) =
      cg.edges.map (fun e => e.decl)) := rfl

end PipelineImpl
end Layered
end Elegant
