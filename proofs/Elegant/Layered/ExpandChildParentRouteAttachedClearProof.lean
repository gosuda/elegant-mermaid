import Elegant.Layered.ExpandChildParentRouteRunProof
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.RecursiveFit
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.RecursiveC78
import Elegant.Model
import Elegant.Scene

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Attached-route clearance seam: self-loop endpoint residual.

`ExpandChildParentRouteAttachedClear` (`ExpandChildParentRouteRunProof.lean`) asks every parent route attached to the group to miss every rectangle strictly inside the group frame. Probe evidence (`proofs/wip/Probe/ParentRouteAttachedClearTProbe.lean`): edgeIntoTitled attached=1 viols=0, selfLoopGroup attached=1 selfLoops=1 boundViols=0, nestedCross attached=1 viols=0, noEdges attached=0, emptyGroup attached=0, fixedZero attached=0, betweenGroups calls=0 (cross-edge groups are not `Compound.independent`), illFormed TRACE-ERROR domain, cell variants attached=1 viols=0, parent c5=true c6=true throughout with frame excl=false. The statement is true on every executed call, but it does not follow from the call context alone: the context carries `layoutRecursive` successes, not validated `C5`/`C6`, and `C6` is vacuous here (frame non-exclusive, attached routes in scope), while `C5` pins only the boundary port, not the stub exterior or middle segments. The full miss therefore stays open.

 Advisory note (frame-level residual weighed, not kept): the attached frame miss also holds on the probe (`frameViols=0` on every call above) and would give the target by `hitsRect` monotonicity, but it is not kept: it implies the target so it is a strengthening, no proved clause gives it, and bridging needs the private `segMisses` chain with no public bridge. The self-loop endpoint below is strictly weaker, proved outright, and needs no copies.
 -/

/-- The parent sub-input is well-formed (copy of the private lemma in `ExpandChildParentFrameProof.lean`; `inputModel` ignores the fixed side tables). -/
private theorem prac_parentInput_wellFormed {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int} {parent child res : FamilyResult} (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res) : WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact inputModel_wellFormed_fixed_congr _ _ _ (selectInput_wellFormed inp o (fun box => !Elegant.Layered.Compound.inside inp.boxes group.id box.id) "" hctx.1 (fun c hc hkept => keepOutside_close (group := group.id) (inputFacts_of_wellFormed hctx.1) hc hkept) o)

/-- Sub-case of `ExpandChildParentRouteAttachedClear`: attached self-loop routes meet the group frame on its boundary. Strictly weaker (self-loops only, boundary only, no inner-rect quantifier); the boundary half of the endpoint-attachment content. -/
def ExpandChildParentRouteAttachedSelfEndpoint (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box), parent.scene.boxes.find? (fun box => box.id == group.id) = some frame → ∀ pr ∈ parent.scene.routes, pr.fromId = group.id → pr.toId = group.id → ∃ p q, pr.points.head? = some p ∧ pr.points.getLast? = some q ∧ Validator.onBoundary p frame.rect ∧ Validator.onBoundary q frame.rect

/-- The self-loop endpoint residual holds on every executed `expandChild` call, from the proved self-endpoint invariant at the parent sub-input. -/
theorem parentRouteAttachedSelfEndpoint_holds (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult) (hexpand : expandChild P inp o group titleHeight parent child = .ok res) (hframed : framedParents inp = true) (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res) (_hparams : ExpandChildCallParams P inp o group titleLines titleHeight) : ExpandChildParentRouteAttachedSelfEndpoint group parent := by
  have _hex := hexpand
  have _hfr := hframed
  intro frame hfind pr hmem hfrom hto
  have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent := hctx.2.2.2.2.1
  have hwfParent : WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := prac_parentInput_wellFormed hctx
  have hids : ((parentSubInput inp group P titleLines child).boxes.map (fun b => b.id)).Nodup := Model.boxIds_nodup hwfParent
  have hcovered : RoutesCovered (parentSubInput inp group P titleLines child) := routesCovered_of_wellFormed hwfParent
  have hself : pr.fromId = pr.toId := hfrom.trans hto.symm
  obtain ⟨p, q, fromBox, toBox, hp, hq, hboxFrom, hboxTo, hbFrom, hbTo⟩ := layoutRecursive_self_endpoint_c5 fuel hids hcovered hparent hmem hself
  have hboxGroup : parent.scene.layoutDump.box? group.id = some frame := by
    have h : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame := hfind
    simpa [Scene.layoutDump, LayoutDump.box?] using h
  have h1 : parent.scene.layoutDump.box? group.id = some fromBox := by
    rw [← hfrom]
    exact hboxFrom
  have h2 : parent.scene.layoutDump.box? group.id = some toBox := by
    rw [← hto]
    exact hboxTo
  have hfromBox : fromBox = frame := by
    have hEq : some fromBox = some frame := h1.symm.trans hboxGroup
    cases hEq
    rfl
  have htoBox : toBox = frame := by
    have hEq : some toBox = some frame := h2.symm.trans hboxGroup
    cases hEq
    rfl
  exact ⟨p, q, hp, hq, hfromBox ▸ hbFrom, htoBox ▸ hbTo⟩

end Elegant.Layered.PipelineImpl
