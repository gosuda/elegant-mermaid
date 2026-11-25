import Elegant.Layered.ExactFlatC5
import Elegant.Layered.RegionFlatC5
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionRunChainFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region executed C5 endpoints (`R_ExecutedC5EndpointsR`).

Replays the exact-twin endpoint establishment
(`ExactFlatC5.lean`, `ExactFlatC5Rank.lean`, `ExactFlatC5Bottom.lean`) over
`componentRunR_specR` for an executed `SceneExecutionR` with local
well-formedness and framed parents (`GroupEndpointInvariantMeasured inp
res.scene`).

Region differences from the exact twin: `rankEquivalentR` may reverse edges,
so oriented-edge endpoint lookup goes through the returned graph `cg'`,
keyed by `decl` (`rfc5_edges_decls`, `componentRunR_edges_declsR`); and for a
`some` spec the cross-coordinate step rewrites coordinates, so
`coordinateGraphR ... = run.coordinateProper` is false and no proof below
touches `run.coordinateProper`.

Split: route endpoint on the tail box (`R_TailLookupR`, proved), route
endpoint on the head box (`R_HeadLookupR`, proved next), group-boundary
attachment (`R_GroupBoundaryR`, the single narrower public residual, with
`#eval` evidence in `proofs/wip/Probe/RegionC5EndpointsTProbe.lean` on the
`RegionFlatC5TProbe` inputs). The closed `flatC5B_layoutRIds_closed` follows
from the two proved lookups plus the residual.
-/

/-- Executed-run tail lookup: every scene route of an executed region run on
a well-formed framed-parents input names an input box at its `fromId`. This
is the tail half of the box-existence part of `R_ExecutedC5EndpointsR`; it
needs no group machinery because scene routes carry input route ids
verbatim through `sceneOf`. -/
def R_TailLookupR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ out ∈ res.scene.routes, ∃ source ∈ inp.boxes, source.id = out.fromId

/-- The tail lookup holds for every executed region run. -/
theorem r_tailLookupR_holds (exactIds : List String) (idSets : List (String × List String)) :
    R_TailLookupR exactIds idSets := by
  intro inp o res execution hwf _hfp out hout
  have hcov : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length _ _ _ _ _ _
  obtain ⟨k, hkget⟩ := List.mem_iff_getElem?.mp hout
  have hk : k < inp.routes.length := by
    have hkk := (List.getElem?_eq_some_iff.mp hkget).1
    rwa [hlen] at hkk
  have hrec := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured k hk
  rw [← execution.scene_eq] at hrec
  have hfrom : out.fromId = (inp.routes[k]).fromId := by
    have hmap := congrArg (fun r : Option Route => r.map Route.fromId) (hkget.symm.trans hrec)
    simp only [Option.map_some, Option.some_inj] at hmap
    exact hmap
  have hkmem : inp.routes[k] ∈ inp.routes := List.getElem_mem hk
  obtain ⟨hfromCov, _⟩ := hcov _ hkmem
  obtain ⟨bf, hbf, hbfid⟩ := hfromCov
  exact ⟨bf, hbf, hbfid.trans hfrom.symm⟩

/-- Executed-run head lookup: every scene route of an executed region run on
a well-formed framed-parents input names an input box at its `toId`. This
is the head half of the box-existence part of `R_ExecutedC5EndpointsR`,
proved the same way as the tail half: scene routes carry input route ids
verbatim through `sceneOf`, and `RoutesCovered` supplies the target box. -/
def R_HeadLookupR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ out ∈ res.scene.routes, ∃ target ∈ inp.boxes, target.id = out.toId

/-- The head lookup holds for every executed region run. -/
theorem r_headLookupR_holds (exactIds : List String) (idSets : List (String × List String)) :
    R_HeadLookupR exactIds idSets := by
  intro inp o res execution hwf _hfp out hout
  have hcov : RoutesCovered inp := routesCovered_of_wellFormed hwf
  have hlen : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact sceneOf_routes_length _ _ _ _ _ _
  obtain ⟨k, hkget⟩ := List.mem_iff_getElem?.mp hout
  have hk : k < inp.routes.length := by
    have hkk := (List.getElem?_eq_some_iff.mp hkget).1
    rwa [hlen] at hkk
  have hrec := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured k hk
  rw [← execution.scene_eq] at hrec
  have hto : out.toId = (inp.routes[k]).toId := by
    have hmap := congrArg (fun r : Option Route => r.map Route.toId) (hkget.symm.trans hrec)
    simp only [Option.map_some, Option.some_inj] at hmap
    exact hmap
  have hkmem : inp.routes[k] ∈ inp.routes := List.getElem_mem hk
  obtain ⟨_, htoCov⟩ := hcov _ hkmem
  obtain ⟨bt, hbt, hbtid⟩ := htoCov
  exact ⟨bt, hbt, hbtid.trans hto.symm⟩

/-- Oriented-edge declaration range: every edge of the returned graph `cg'`
of a region run carries a declaration below `inp.routes.length`. The lookup
goes through `cg'` (not the input graph `cg`) because `rankEquivalentR` may
reverse edges; reversal keeps `decl` (`rfc5_map_decl_of_mem`), so the exact
declaration range transfers verbatim (`exactGraph_decl_rangeX`). -/
theorem r_orientedDeclRangeR_holds {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 cg : Graph} (h0 : measuredGraph P inp o lines = .ok graph0)
    (hX : exactGraph P exactIds inp o measured graph0 = .ok cg)
    {spec : Option RegionSpec} {cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hR : componentRunR P (exactDecls exactIds inp) spec inp cg labels orderOptions = .ok (cg', run))
    {i : Nat} (hi : i < cg'.edges.length) :
    (cg'.edges[i]'hi).decl < inp.routes.length := by
  have hdecls : cg'.edges.map (·.decl) = cg.edges.map (·.decl) :=
    componentRunR_edges_declsR hR
  have hrange : cg.edges.map (·.decl) = List.range' 0 inp.routes.length :=
    exactGraph_decl_rangeX h0 hX
  have hmem : (cg'.edges[i]'hi).decl ∈ cg.edges.map (·.decl) := by
    rw [← hdecls]
    exact List.mem_map.mpr ⟨cg'.edges[i]'hi, List.getElem_mem hi, rfl⟩
  rw [hrange, ← List.range_eq_range'] at hmem
  exact List.mem_range.mp hmem

/-- Group-boundary residual: for an executed region run on a well-formed
framed-parents input, every scene route carries endpoint points on the
boundary of its `from`/`to` dump boxes. This is the geometric half of
`R_ExecutedC5EndpointsR` (points plus dump-box boundary), strictly narrower
than the target because it does not assert the input-box existences proved
above. True on all eight `RegionFlatC5TProbe` inputs
(`proofs/wip/Probe/RegionFlatC5TProbe.lean`, `lake env lean`): their
`t5dump` reports are `(true, true)` for `Validator.c5` and `Validator.validate`. -/
def R_GroupBoundaryR (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (_execution : SceneExecutionR exactIds idSets inp o res),
    WellFormed (inputModel inp o) → framedParents inp = true →
    ∀ out ∈ res.scene.routes, ∃ (start finish : Point) (fromBox toBox : Box),
      out.points.head? = some start ∧ out.points.getLast? = some finish ∧
      res.scene.layoutDump.box? out.fromId = some fromBox ∧
      res.scene.layoutDump.box? out.toId = some toBox ∧
      Validator.onBoundary start fromBox.rect ∧ Validator.onBoundary finish toBox.rect

/-- Flat C5 for the region pipeline, closed modulo the group-boundary
residual: the proved tail/head lookups supply the input-box existences and
the residual supplies points plus dump-box boundary, which together are
exactly `R_ExecutedC5EndpointsR`. -/
theorem flatC5B_layoutRIds_closed (exactIds : List String) (idSets : List (String × List String))
    (hB : R_GroupBoundaryR exactIds idSets) : FlatC5B (layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp hb
  obtain ⟨execution⟩ := layoutRIds_sceneExecution hb
  have hids := RB_layout_ids hb
  have hT : R_TailLookupR exactIds idSets := r_tailLookupR_holds exactIds idSets
  have hH : R_HeadLookupR exactIds idSets := r_headLookupR_holds exactIds idSets
  refine ⟨hids.1, hids.2, ?_⟩
  intro out hout
  obtain ⟨source, hsmem, hsid⟩ := hT execution hwf hfp out hout
  obtain ⟨target, htmem, htid⟩ := hH execution hwf hfp out hout
  obtain ⟨start, finish, fromBox, toBox, h1, h2, h3, h4, h5, h6⟩ :=
    hB execution hwf hfp out hout
  exact ⟨source, hsmem, target, htmem, hsid, htid, start, finish, fromBox, toBox,
    h1, h2, h3, h4, h5, h6⟩


end PipelineImpl
end Layered
end Elegant
