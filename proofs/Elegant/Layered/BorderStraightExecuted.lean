import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ForeignBorderDivergeFramedProof
import Elegant.Layered.ForeignSideChainShapeProof

set_option autoImplicit false
set_option warningAsError true

namespace Elegant.Layered.PipelineImpl

/-- The represented side markers of a declaration have equal cross-axis
coordinates before proxy projection in a successful framed component run. -/
theorem border_chain_straight_executed {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {decl : Nat} {side : Int} (hside : side = -1 ∨ side = 1)
    {a b : Nat} {na nb : ProperNode}
    (ha : run.coordinateProper.nodes[a]? = some na)
    (hb : run.coordinateProper.nodes[b]? = some nb)
    (hsideA : na.node.border = side) (hsideB : nb.node.border = side)
    (hownerA : na.node.clusterPath.getLast? = some decl)
    (hownerB : nb.node.clusterPath.getLast? = some decl) :
    run.coordinateXs[a]! = run.coordinateXs[b]! := by
  obtain ⟨labeled, hcoord, hready⟩ := componentRun_titled_border_ready hgraph hcomp hrun
  have hwidth {v : Nat} {n : ProperNode}
      (hv : run.coordinateProper.nodes[v]? = some n) (hborder : n.node.border = side) :
      n.node.w = P.clusterBorderW := by
    have hs : n.node.border = -1 ∨ n.node.border = 1 := by
      rw [hborder]
      exact hside
    have hlookup : (coordinateGraph P labeled).nodes[v]? = some n := by
      rw [hcoord]
      exact hv
    exact shape_side_width _ _ hready (coordinateGraph_side_original hready hlookup hs) hs
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨pos, hchecked, _⟩ := Elegant.Layered.crossCoordsClusterWith_ok hcross
  let chain := sideChainNodes P run side decl
  have hmem (v : Nat) : v ∈ chain ↔
      ∃ n : ProperNode, run.coordinateProper.nodes[v]? = some n ∧
        n.node.border = side ∧ n.node.w = P.clusterBorderW ∧
        n.node.clusterPath.getLast? = some decl :=
    mem_sideChainNodes (P := P) (run := run) (side := side) (decl := decl)
      (pos := pos) (a := v) hchecked
  have haChain : a ∈ chain := (hmem a).mpr ⟨na, ha, hsideA, hwidth ha hsideA, hownerA⟩
  have hbChain : b ∈ chain := (hmem b).mpr ⟨nb, hb, hsideB, hwidth hb hsideB, hownerB⟩
  have hbounds : ∀ v ∈ chain, v < run.coordinateProper.nodes.length := by
    intro v hv
    obtain ⟨_, hlookup, _, _, _⟩ := (hmem v).mp hv
    exact (List.getElem?_eq_some_iff.mp hlookup).1
  refine Elegant.Layered.border_chain_straight hcross hbounds ?_ a haChain b hbChain
  intro passPos hpassPos k hk
  have hL := (Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad)
    (p := CoordsImpl.borderAlignment run.coordinateProper run.layers) (layers := run.layers)
    (marked := CoordsImpl.typeOneConflicts
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) passPos)
    (k := k) hpassPos).1
  obtain ⟨passChain, hpassMem, hblock⟩ :=
    foreignBorderSideBlocked (decl := decl) (side := side)
      (foreignBorderSideUps_closed foreignBorderDivergeStable_framed)
      hgraph hlines hwf hframed hcomp hrun hside hk hpassPos hL
  have hinPass (v : Nat) : v ∈ chain ↔ v ∈ passChain :=
    (hmem v).trans (hpassMem v).symm
  obtain ⟨r, hr, hroot, hrLayer, hall⟩ :=
    hblock (List.ne_nil_of_mem ((hinPass a).mp haChain))
  exact ⟨r, (hinPass r).mpr hr, hroot, hrLayer,
    fun v hv => hall v ((hinPass v).mp hv)⟩

end Elegant.Layered.PipelineImpl
