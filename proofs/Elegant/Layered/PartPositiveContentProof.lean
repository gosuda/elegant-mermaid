import Elegant.Layered.Pipeline
import Elegant.Layered.FlatC6ScopeResidualsProof
import Elegant.Layered.FlatC6ScopeBridgeProof
import Elegant.Layered.PartFrameWitnessProof
import Elegant.Layered.LoopRectRealQProof
import Elegant.Layered.LabelRunBridgeFacts
import Elegant.Layered.RunStageChainKeysResiduals
import Elegant.Layered.SizingFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.RouteProxyStart
import Elegant.Layered.LoopFootprintFactsProof
import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CgShape
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.LoopFootprintGeneralOrder
import Elegant.Layered.CoordGraph
import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Positive content without the false witness

Consumer analysis: `partFrameWitness` (`LayeredSeams.partFrameWitness`,
`FamilyAssembly.lean:96-98`) is consumed at exactly two use sites,
`FamilyAssembly.lean:170` and `FamilyAssemblyB.lean:221`, both of the form
`flatC6_closed S.partFrameWitness ...`. Inside `flatC6_closed`
(`FlatC6ClosedProof.lean:40-43,69-70`) the witness is used only once, via
`partPositiveContent'`, to build `hcontent : PartPositiveContent inp o res`,
which is then consumed by `routePartShelfPositive_of_content`
(`FlatC6ClosedProof.lean:78`) to supply the shelf positivity the chain and
loop cases need. So the weakest conclusion the consumer needs is the existing
`PartPositiveContent` (`FlatC6ScopeResidualsProof.lean:97-105`): every placed
part with a route has a positive-width rect and (a positive-height rect or a
route y-span). This file does not redefine it.

Truth (executed probe): `proofs/wip/Probe/PartPositiveContent2TProbe.lean`
evaluates the exact `PartPositiveContent` conclusion per routed part on twelve
executed layouts (double fixed-zero TB/LR, single fixed-zero self-loop TB/LR,
group-with-zero TB/LR, normal TB/LR, double negative-fixed TB/LR, negative
self-loop TB/LR). Every layout elaborates `ok` and every routed part reports
`CONTENT=true`. The two degenerate fixed pairs satisfy it only through the
route y-span disjunct (`wpos=true hpos=false yspan=true`, points
`[(512,0),(512,3072)]` in both TB and LR); the self-loops satisfy it through a
positive-height rect from the loop floors (`hpos=true`). The unconditional
statement is therefore true, and the premise below is NOT a truth narrowing.

Not yet proved (honest gap): nothing. The unconditional theorem
`partPositiveContent_holds` is proved below by cases: a live part goes through
the existing frame-positive route (`partPositiveContent_of_node`); otherwise
every candidate node is border-0 (group tops are live, bottom markers rejoin
their top by `componentRun_cg_top_of_bottom`), width comes from
`runProperFloor`, and the height-or-span disjunct is discharged by the two
named branch lemmas `partContent_route_yspan` (a non-loop edge spans a
positive y distance by chain endpoints, route endpoints, and strict band
separation) and `partContent_selfLoop_yspan` (a self-loop-only part inherits
the `centre ± slot` span of its `Loops.placement`). The corollary
`routePartShelfPositive_holds` feeds the existing shelf bridge.

Seam-owner status: the `partFrameWitness` field (`FamilyAssembly.lean:96-98`)
can now be deleted from the seam record. Its replacement is the unconditional
`partPositiveContent_holds inp o res hwf hframed`, consumed at
`FlatC6ClosedProof.lean:69-70` in place of `partPositiveContent'`, and
`routePartShelfPositive_holds inp o res hwf hframed` delivers exactly what the
old witness's downstream consumer needed. `partPositiveContent_executed` and
`PartLiveWitness` remain as narrow-premise facts but are no longer on the
cutover path.
-/

/-- `portGap` is positive in both profiles (mirrors `nodeMinW_pos`). -/
theorem portGap_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.portGap := by
  obtain ⟨B, hb, rfl⟩ := checkedParams_some h
  have hP : (B.forKind profile kind).portGap = B.portGap := rfl
  have hB : B.portGap = LayoutConst.port_gap.get profile := by
    unfold baseParams at hb
    have heq := Option.some.inj hb
    have hcon := congrArg Params.portGap heq
    simpa using hcon.symm
  rw [hP, hB]
  cases profile <;> decide

/-- Port sizing floors every plain anchor at `portGap`: a non-dummy border-0
proper node keeps its edge/border/dummy and gains `w ≥ portGap`, `h`
unchanged. The `+1` makes the bound unconditional (no incident edge needed). -/
theorem sizeProperPorts_floor {P : Params} (hpg : 0 < P.portGap) {p : Proper}
    {v : Nat} {nd : ProperNode} (hn : p.nodes[v]? = some nd)
    (hnd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ sized, (sizeProperPorts P p).nodes[v]? = some sized ∧
      sized.edge = nd.edge ∧ sized.node.border = 0 ∧ sized.dummy = false ∧
      P.portGap ≤ sized.node.w ∧ sized.node.h = nd.node.h ∧
      nd.node.w ≤ sized.node.w := by
  unfold sizeProperPorts
  simp only [List.getElem?_map, List.getElem?_zipIdx, hn, Option.map_some]
  split
  · next h => simp [hnd, hb] at h
  · refine ⟨_, rfl, rfl, hb, hnd, ?_, rfl, ?_⟩
    · apply Int.le_trans _ (Int.le_max_right _ _)
      have hk : (1 : Int) ≤
          (((max ((p.edges.filter fun edge => edge.head == 0 + v).map (·.tail)).eraseDups.length
            ((p.edges.filter fun edge => edge.tail == 0 + v).map (·.head)).eraseDups.length
            + 1 : Nat)) : Int) := by
        have h0 : (0 : Int) ≤
            (((max ((p.edges.filter fun edge => edge.head == 0 + v).map (·.tail)).eraseDups.length
            ((p.edges.filter fun edge => edge.tail == 0 + v).map (·.head)).eraseDups.length
            : Nat)) : Int) := Int.natCast_nonneg _
        omega
      calc P.portGap = 1 * P.portGap := (Int.one_mul _).symm
        _ ≤ _ * P.portGap := Int.mul_le_mul_of_nonneg_right hk (Int.le_of_lt hpg)
    · exact Int.le_max_left _ _

/-- The sizing floor survives title reservation, border insertion, and
display-path materialization: none shrinks a plain anchor's measured stack
(mirrors `coordinateGraph_plain_anchor_dims` with the floor carried). -/
theorem coordinateGraph_floor {P : Params} (hpg : 0 < P.portGap) {p : Proper}
    {v : Nat} {nd : ProperNode} (hp : p.nodes[v]? = some nd)
    (hnd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[v]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧ out.dummy = false ∧
      P.portGap ≤ out.node.w ∧ out.node.h = nd.node.h ∧
      nd.node.w ≤ out.node.w := by
  obtain ⟨sized, hs, he, hb', hd, hfloor, hh, hw⟩ :=
    sizeProperPorts_floor hpg hp hnd hb
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[v]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[v]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[v]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · next h => simp [hd] at h
  · exact ⟨_, rfl, he, hb', hd, hfloor, hh, hw⟩

/-- Executed-run width floor at a plain candidate index: the proper node
above a border-0 candidate node is at least `portGap` wide. Index-preserving
stages (`normalize`, label nodes, proxy widths, title drop) carry the
coordinate floor to `run.proper`. -/
theorem runProperFloor {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) (hpg : 0 < P.portGap)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node)
    (hb : node.border = 0) :
    ∃ out, run.proper.nodes[v]? = some out ∧ out.node.border = 0 ∧
      P.portGap ≤ out.node.w := by
  obtain ⟨_ranks, p0, labeled, _q0, hn, hl, hc, _, _, _hproxy, _hdrop, _, _, _, _, _⟩ :=
    componentRun_spec h
  have hp0 : p0.nodes[v]? = some ⟨node, false, none, false⟩ :=
    normalize_node_record hn hnode
  have hlabeled : labeled.nodes[v]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hl hp0 rfl
  obtain ⟨out, hout, _hedge, hbout, _hdout, hfloor, _hhout, _hwout⟩ :=
    coordinateGraph_floor hpg hlabeled rfl hb
  rw [hc] at hout
  have hproper : run.proper.nodes[v]? = some out :=
    componentRun_plain_node_dims h hout hbout
  exact ⟨out, hproper, hbout, hfloor⟩
/-- Narrow premise replacing the false `PartFrameWitness`: every routed part
either holds an unfixed node-role box whose candidate node is border-0, or
has a group-top (border -2) candidate node. Both cases carry proved frame
positivity (`exclusiveBox_frame_pos`, `top_frame_pos`). This excludes the
degenerate all-fixed routed pair (zero/negative witness inputs), where
content holds only via the route y-span; that derivation stays open. -/
def PartLiveWitness (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {part : List Nat × Part}, part ∈ execution.componentsAcc.parts →
      part.1 = comp → part.2.routes ≠ [] →
      (∃ (w key : Nat) (box : ModelBox) (ls : List Measure.Line) (nodeW : Node),
        comp[w]? = some key ∧ inp.boxes[key]? = some box ∧
        execution.lines[key]? = some ls ∧ box.role = .node ∧
        inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false ∧
        (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW ∧
        nodeW.border = 0)
      ∨ (∃ (v : Nat) (node : Node),
        (componentCandidate execution.graph comp candidate).nodes[v]? = some node ∧
        node.border = -2)

/-- Per-part core: an explicit positive-frame candidate node supplies the
`PartPositiveContent` conclusion for that part (its shifted rect is a member
with positive width and positive height). This is the body of
`partPositiveContent_of_witness` with the witness call replaced by explicit
node evidence. -/
private theorem partPositiveContent_of_node {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {part : List Nat × Part}
    {index : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    (hrectsEq : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph part.1 index).nodes[v]? = some node)
    (hpos : 0 < (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run v).w ∧
      0 < (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run v).h) :
    (∃ r : Rect, r ∈ part.2.rects ∧ 0 < r.w) ∧
    ((∃ r : Rect, r ∈ part.2.rects ∧ 0 < r.h) ∨
      (∃ pts : List Point, ∃ p₁ p₂ : Point,
        (∃ decl : Nat, (decl, pts) ∈ part.2.routes) ∧
        p₁ ∈ pts ∧ p₂ ∈ pts ∧ p₁.y ≠ p₂.y)) := by
  have hi : v < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hget := placeComponent_rects_get_copy execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops hi
  have hmem : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v) ∈
      part.2.rects := by
    rw [hrectsEq]
    exact List.mem_of_getElem? hget
  have hw : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).w := hpos.1
  have hh : 0 < (shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run v)).h := hpos.2
  exact ⟨⟨_, hmem, hw⟩, Or.inl ⟨_, hmem, hh⟩⟩

/-- Executed-run replacement for the false seam field: under the narrow live
premise, every routed part satisfies `PartPositiveContent`. The
well-formedness hypotheses are kept (unused) so the statement drops into the
seam site unchanged. -/
theorem partPositiveContent_executed {inp : Input} {o : Options}
    {res : FamilyResult} (_hwf : WellFormed (inputModel inp o))
    (_hfp : framedParents inp = true) (hlive : PartLiveWitness inp o res) :
    PartPositiveContent inp o res := by
  intro execution part hpart hroutes
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  have hrectsEq : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects := by rw [heq]
  rcases hlive execution part.1 index run hcomp hrun hpart rfl hroutes with
    ⟨w, key, box, ls, nodeW, hkey, hbox, hline, hrole, hnf, hnodeW, hbW⟩ |
    ⟨v, node, hnode, hb⟩
  · obtain ⟨hposW, hposH⟩ :=
      exclusiveBox_frame_pos execution hrun hnodeW hbW hkey hbox hline hrole hnf
    exact partPositiveContent_of_node execution hrectsEq hnodeW ⟨hposW, hposH⟩
  · obtain ⟨hposW, hposH⟩ :=
      top_frame_pos execution hcomp hrun hnode hb
    exact partPositiveContent_of_node execution hrectsEq hnode ⟨hposW, hposH⟩

/-- Bridge for the seam owner: positive content delivers exactly what the old
witness's downstream consumer needed (shelf positivity for the chain and loop
cases). This does not rebuild the false `PartFrameWitness`; it replaces its
use-site value. At the `partFrameWitness` use site, replace
`routePartShelfPositive_of_content (partPositiveContent' ... (hwit ...))` with
`partFrameWitness_of_positiveContent (partPositiveContent_holds ...)` once the
seam carries no witness premise. -/
theorem partFrameWitness_of_positiveContent {inp : Input} {o : Options}
    {res : FamilyResult} (hcontent : PartPositiveContent inp o res) :
    RoutePartShelfPositive inp o res :=
  routePartShelfPositive_of_content hcontent

/-- Executed lines cover every box (local copy of the private scene fact). -/
private theorem partContent_lines_len {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := (mapM_getElem? _ _ _ execution.lines_eq).1
  simpa only [List.length_zipIdx] using h

/-- Uniform band bounds for an executed proper position: the placed y sits in
its rank band and the node stays inside it. Plain nodes use the band lemma;
anchors use zero height and band nonnegativity. -/
private theorem partContent_ys_band {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} (hvP : v < run.proper.nodes.length) :
    ∃ r l, run.layers[r]? = some l ∧ v ∈ l ∧
      run.top.getD r 0 ≤ run.ys.getD v 0 ∧
      run.ys.getD v 0 + RouteImpl.nodeH run.proper v ≤
        run.top.getD r 0 + CoordsImpl.layerHeight run.coordinateProper l := by
  obtain ⟨_, _, labeled, _, _, _, hcoord, _, _, hproxy, hdropEq, hroute, _, hry, hys, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdropEq]; exact (proxyWidths_rel hproxy).2.2.1
  have hrankEq : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdropEq]; exact (proxyWidths_rel hproxy).2.1
  have hok := (RouteImpl.routeWithLanes_geometry hroute).1
  have hspecL := RouteImpl.layersOk_spec hok
  obtain ⟨_, _, _, hcov, _⟩ := hspecL
  obtain ⟨l, hl, hmem, hnn⟩ := hcov v hvP
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hrec : run.proper.nodes[v]? = some (run.proper.nodes[v]'hvP) :=
    List.getElem?_eq_getElem hvP
  obtain ⟨nvc, hnc, _, hhEq, _⟩ := fbs_coordinate_record hrun hrec
  rw [hrankEq] at hl hnn
  have hrkC : rk run.coordinateProper.rank v =
      ((rk run.coordinateProper.rank v).toNat : Int) := by omega
  have hband := CoordsImpl.rankAxis_node_in_band hry hl hmem hvC hrkC
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
    rw [hy]; simp
  have hvY : v < run.coordinateYs.length := by omega
  have hysEq := proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs hnc hvY
  rw [hys] at hysEq
  have hnHc : CoordsImpl.nodeH run.coordinateProper v = nvc.node.h := by
    simp only [CoordsImpl.nodeH, hnc]
  have hnodeH : RouteImpl.nodeH run.proper v = nvc.node.h := by
    simp only [RouteImpl.nodeH, hrec, ← hhEq]
  have hLHnn : 0 ≤ CoordsImpl.layerHeight run.coordinateProper l :=
    CoordsImpl.layerHeight_nonneg _ _
  rw [hnHc] at hband
  by_cases hb2 : nvc.node.border = -2 ∨ nvc.node.border = 2
  · have hzero : nvc.node.h = 0 := by
      have hnc' : (coordinateGraph P labeled).nodes[v]? = some nvc := by
        rw [hcoord]; exact hnc
      exact pc_frame_flat hnc' hb2
    rcases hb2 with hb | hb
    · have e1 : (nvc.node.border == -2) = true := by rw [hb]; simp
      simp [e1] at hysEq
      simp only [← List.getD_eq_getElem?_getD] at hysEq
      refine ⟨_, _, hl, hmem, ?_, ?_⟩
      · rw [hysEq]; exact Int.le_refl _
      · rw [hysEq, hnodeH, hzero]; omega
    · have e1 : (nvc.node.border == -2) = false := by rw [hb]; simp
      have e2 : (nvc.node.border == 2) = true := by rw [hb]; simp
      simp [e1, e2] at hysEq
      simp only [← List.getD_eq_getElem?_getD] at hysEq
      have hlyD : run.layers.getD (rk run.coordinateProper.rank v).toNat [] = l := by
        rw [List.getD_eq_getElem?_getD, hl, Option.getD_some]
      have hLH2 : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
          (run.layers.getD (rk run.coordinateProper.rank v).toNat []) :=
        CoordsImpl.layerHeight_nonneg _ _
      refine ⟨_, _, hl, hmem, ?_, ?_⟩
      · rw [hysEq]; omega
      · rw [hysEq, hnodeH, hzero, hlyD]; omega
  · have f1 : (nvc.node.border == -2) = false := by
      cases hc : nvc.node.border == -2 with
      | true => exact absurd (Or.inl (beq_iff_eq.mp hc)) hb2
      | false => rfl
    have f2 : (nvc.node.border == 2) = false := by
      cases hc : nvc.node.border == 2 with
      | true => exact absurd (Or.inr (beq_iff_eq.mp hc)) hb2
      | false => rfl
    simp [f1, f2] at hysEq
    simp only [← List.getD_eq_getElem?_getD] at hysEq
    refine ⟨_, _, hl, hmem, ?_, ?_⟩
    · rw [hysEq]; exact hband.1
    · rw [hysEq, hnodeH]; exact hband.2
/-- Bottom markers rejoin their top: in a part with no border -2 node, no
candidate node is border 2. -/
private theorem partContent_no_bottom {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat}
    (hcomp : part.1 ∈ components execution.graph)
    (hno2 : ∀ (v : Nat) (node : Node),
      (componentCandidate execution.graph part.1 index).nodes[v]? = some node →
      node.border ≠ -2)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph part.1 index).nodes[v]? = some node)
    (hb : node.border = 2) : False := by
  obtain ⟨t, htfind⟩ := componentRun_cg_top_of_bottom execution.graph_eq
    (partContent_lines_len execution) hcomp hnode hb
  have htmem := List.mem_of_find?_eq_some htfind
  have hpred := List.find?_some htfind
  have hbeq : (t.1.border == -2) = true := by
    apply Classical.byContradiction
    intro hcon
    have hff : (t.1.border == -2) = false := by
      cases hbb : (t.1.border == -2) with
      | true => exact absurd hbb hcon
      | false => rfl
    simp [hff] at hpred
  have htz := List.mem_zipIdx_iff_getElem?.mp htmem
  exact hno2 t.2 t.1 htz (beq_iff_eq.mp hbeq)

/-- Successful plain loop placements are the mapped `Loops.placement` list
(local copy of the private `loops_ok_map`). -/
private theorem partContent_loops_ok_map {node : Rect} {slot : Int} {sizes : List LoopLabel}
    {placements : List LoopPlacement}
    (h : Loops.loops node slot sizes = .ok placements) :
    placements = (sizes.zipIdx.map fun q =>
      Loops.placement node slot (Loops.band slot sizes) sizes.length q.2 q.1) := by
  unfold Loops.loops at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h
        · cases h; rfl
        · contradiction

/-- A plain loop placement spans `2 * slot` in y between points of its list. -/
private theorem partContent_placement_yspan (node : Rect) (slot band : Int)
    (count index : Nat) (label : LoopLabel) :
    ∃ p₁ p₂ : Point, p₁ ∈ (Loops.placement node slot band count index label).points ∧
      p₂ ∈ (Loops.placement node slot band count index label).points ∧
      p₁.y + slot + slot = p₂.y := by
  refine ⟨⟨node.x + node.w, node.y + (index : Int) * band + Int.fdiv band 2 - slot⟩,
    ⟨node.x + node.w, node.y + (index : Int) * band + Int.fdiv band 2 + slot⟩, ?_, ?_, ?_⟩
  · simp [Loops.placement]
  · simp [Loops.placement]
  · dsimp only
    omega

/-- Shifted points keep membership and y-distinctness. -/
private theorem partContent_shift_yspan {pts : List Point} {p₁ p₂ : Point}
    (hm1 : p₁ ∈ pts) (hm2 : p₂ ∈ pts) {dx dy : Int} (hne : p₁.y ≠ p₂.y) :
    shiftPoint dx dy p₁ ∈ pts.map (shiftPoint dx dy) ∧
    shiftPoint dx dy p₂ ∈ pts.map (shiftPoint dx dy) ∧
    (shiftPoint dx dy p₁).y ≠ (shiftPoint dx dy p₂).y := by
  refine ⟨List.mem_map.mpr ⟨_, hm1, rfl⟩, List.mem_map.mpr ⟨_, hm2, rfl⟩, ?_⟩
  have e1 : (shiftPoint dx dy p₁).y = p₁.y + dy := rfl
  have e2 : (shiftPoint dx dy p₂).y = p₂.y + dy := rfl
  omega

/-- Candidate edges keep both endpoints below the component length (public
re-export of the general bounds theorem, specialized to the node count). -/
private theorem partContent_edge_bounded {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hcomp : part.1 ∈ components execution.graph)
    {index : Nat} {edge : Edge}
    (hedge : edge ∈ (componentCandidate execution.graph part.1 index).edges) :
    edge.tail < (componentCandidate execution.graph part.1 index).nodes.length ∧
      edge.head < (componentCandidate execution.graph part.1 index).nodes.length :=
  candidate_edge_endpoints_bounded_general execution.graph part.1 index hcomp
    (sceneExecution_edges_bounded execution) hedge

/-- Executed parts carry their component, run, and loop placements. This keeps
the `componentLoops` success that `execution_part_run` drops, so the branch
lemmas below can exclude ordinary declarations and emit self-loop routes. -/
private theorem partContent_run_loops {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {part : List Nat × Part}
    (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (run : Run) (loops : List (Nat × LoopPlacement)) (area : Int),
      part.1 ∈ components execution.graph ∧
      componentRun execution.params (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      componentLoops execution.params (componentCandidate execution.graph part.1 index)
        run execution.measured = .ok loops ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometry hempty execution.components_eq
  obtain ⟨index, chosen, run, loops, area, _, _, _, hrun, hloops, heq⟩ :=
    hall part hpart
  refine ⟨index, run, loops, area, ?_, hrun, hloops, heq⟩
  rw [← hm]
  exact List.mem_map_of_mem hpart
private theorem partContent_tops_step_aux (hs : List Int) :
    ∀ (ss : List Int) (t : Int) (r : Nat) (a b h s : Int)
      (_ha : (CoordsImpl.topsFrom 0 1 t hs ss)[r]? = some a)
      (_hb : (CoordsImpl.topsFrom 0 1 t hs ss)[r + 1]? = some b)
      (_hh : hs[r]? = some h) (_hss : ss[r]? = some s),
      b = a + h + s := by
  induction hs with
  | nil =>
    intro ss t r a b h s ha hb hh hss
    simp [CoordsImpl.topsFrom] at ha
  | cons x xs' ih =>
    intro ss t r a b h s ha hb hh hss
    cases ss with
    | nil =>
      cases xs' with
      | nil =>
        simp [CoordsImpl.topsFrom] at hb
      | cons x2 xs'' =>
        simp [CoordsImpl.topsFrom] at ha
    | cons y ys' =>
      cases r with
      | zero =>
        cases xs' with
        | nil =>
          cases ys' with
          | nil =>
            simp [CoordsImpl.topsFrom] at hb
          | cons y2 ys'' =>
            simp [CoordsImpl.topsFrom] at hb
        | cons x2 xs'' =>
          cases ys' with
          | nil =>
            cases xs'' with
            | nil =>
              simp only [CoordsImpl.topsFrom, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.some.injEq] at ha hb hh hss
              omega
            | cons x3 xs3 =>
              simp [CoordsImpl.topsFrom] at hb
          | cons y2 ys'' =>
            simp only [CoordsImpl.topsFrom, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.some.injEq] at ha hb hh hss
            omega
      | succ r1 =>
        cases xs' with
        | nil =>
          cases ys' with
          | nil =>
            simp [CoordsImpl.topsFrom] at ha
          | cons y2 ys'' =>
            simp [CoordsImpl.topsFrom] at ha
        | cons x2 xs'' =>
          cases ys' with
          | nil =>
            cases xs'' with
            | nil =>
              simp [CoordsImpl.topsFrom] at hb
            | cons x3 xs3 =>
              simp [CoordsImpl.topsFrom] at hb
          | cons y2 ys'' =>
            have e : CoordsImpl.topsFrom 0 1 t (x :: x2 :: xs'') (y :: y2 :: ys'') =
                t :: CoordsImpl.topsFrom 0 1 (t + x + 0 + 1 * y)
                  (x2 :: xs'') (y2 :: ys'') := rfl
            rw [e] at ha hb
            simp only [List.getElem?_cons_succ] at ha hb
            simp only [List.getElem?_cons_succ] at hh hss
            exact ih _ _ _ _ _ _ _ ha hb hh hss

/-- Consecutive layer tops differ by exactly the layer height plus the rank
step: `topsFrom` advances the cursor by `h + rankGap + slot * s`. The
`getElem?` form matches `topsFrom_disjoint` so both feed the same bounds. -/
private theorem partContent_tops_step {a b h s : Int} (hs ss : List Int) (t : Int)
    (r : Nat)
    (ha : (CoordsImpl.topsFrom 0 1 t hs ss)[r]? = some a)
    (hb : (CoordsImpl.topsFrom 0 1 t hs ss)[r + 1]? = some b)
    (hh : hs[r]? = some h) (hss : ss[r]? = some s) :
    b = a + h + s :=
  partContent_tops_step_aux hs ss t r a b h s ha hb hh hss

/-- The executed rank step at a covered rank is positive: the gap term is at
least the `rankGap` floor (both label-only branches clear `1` from
`1 ≤ rankGap`), and the slot term is nonneg. -/
private theorem partContent_steps_pos (p : Proper) (layers : List (List Nat))
    (slots : List Int) (rankGap slot : Int) (hg : 1 ≤ rankGap) (hs : 1 ≤ slot)
    (hnn : ∀ s ∈ slots, 0 ≤ s) {r : Nat} (hr : r < slots.length) :
    1 ≤ (CoordsImpl.rankSteps rankGap slot p layers slots).getD r 0 := by
  rw [CoordsImpl.rankSteps_getD _ _ _ _ _ _ hr]
  have hnnr : 0 ≤ slots.getD r 0 := by
    have e : slots.getD r 0 = slots[r]'hr := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
        Option.getD_some]
    rw [e]
    exact hnn _ (List.getElem_mem hr)
  have hgap : 1 ≤ CoordsImpl.rankGapAt rankGap p layers r := by
    unfold CoordsImpl.rankGapAt
    split
    · rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
      omega
    · omega
  have hmul : 0 ≤ slot * slots.getD r 0 :=
    Int.mul_nonneg (by omega) hnnr
  omega

/-- Ranks strictly increase along a semantic chain: every proper edge steps
its head exactly one rank above its tail (`layersOk`), so induction on the
chain position accumulates the offset. -/
private theorem partContent_chain_rk {p : Proper} {chain : List Nat}
    (hsegments : ∀ (j : Nat) (hj : j < chain.length) (hj1 : j + 1 < chain.length),
      ∃ pe ∈ p.edges, pe.tail = chain[j]'hj ∧ pe.head = chain[j + 1]'hj1)
    (hlok : ∀ (k : Nat) (_hk : k < p.edges.length),
      (RouteImpl.edgeAt p k).tail < p.nodes.length ∧
      (RouteImpl.edgeAt p k).head < p.nodes.length ∧
      rk p.rank (RouteImpl.edgeAt p k).head =
        rk p.rank (RouteImpl.edgeAt p k).tail + 1)
    {j : Nat} (hj : j < chain.length) :
    rk p.rank (chain[j]'hj) = rk p.rank (chain.getD 0 0) + (j : Int) := by
  have h0 : 0 < chain.length := by omega
  suffices h : ∀ (j : Nat) (hj : j < chain.length) (h0 : 0 < chain.length),
      rk p.rank (chain[j]'hj) = rk p.rank (chain.getD 0 0) + (j : Int) from
    h j hj h0
  intro j
  induction j with
  | zero =>
    intro hj h0
    have hgg : chain.getD 0 0 = chain[0]'hj := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        Option.getD_some]
    rw [hgg]
    simp
  | succ n ih =>
    intro hj h0
    have hn : n < chain.length := by omega
    obtain ⟨pe, hmem, ht, hh⟩ := hsegments n hn hj
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hmem
    have hkb : k < p.edges.length := (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨_, _, hrk⟩ := hlok k hkb
    have hat : RouteImpl.edgeAt p k = pe := by
      simp only [RouteImpl.edgeAt, List.getD_eq_getElem?_getD, hk,
        Option.getD_some]
    rw [hat] at hrk
    rw [← hh, hrk, ht, ih hn h0]
    push_cast
    omega
/-- Width from a plain candidate node: the port floor survives sizing, title
reservation, border insertion, and display materialization, and the shifted
frame rect keeps the width. -/
private theorem partContent_width_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run}
    {loops : List (Nat × LoopPlacement)} {area : Int}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    (heq : part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area })
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph part.1 index).nodes[v]? = some node)
    (hb : node.border = 0) :
    ∃ r : Rect, r ∈ part.2.rects ∧ 0 < r.w := by
  have hpg : 0 < execution.params.portGap := portGap_pos execution.checked
  obtain ⟨out, hout, _, hfloor⟩ := runProperFloor hrun hpg hnode hb
  have hlen : v < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hnode).1
  have hget := placeComponent_rects_get_copy execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops hlen
  have hr : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured
      loops).rects := by rw [heq]
  have hfr : frameRect execution.params
      (componentCandidate execution.graph part.1 index) run v =
      nodeRect (componentCandidate execution.graph part.1 index) run v := by
    apply frameRect_of_border_zero
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
    exact hb
  have hw : 0 < (nodeRect (componentCandidate execution.graph part.1 index) run v).w := by
    unfold nodeRect
    dsimp only
    have e : (run.proper.nodes.getD v default).node.w = out.node.w := by
      rw [List.getD_eq_getElem?_getD, hout, Option.getD_some]
    omega
  have hmem : shiftRect (0 - (placeBounds execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (0 - (placeBounds execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run v) ∈
      part.2.rects := by
    rw [hr]
    exact List.mem_of_getElem? hget
  have hwpos : 0 < (shiftRect (0 - (placeBounds execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (0 - (placeBounds execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
      (componentCandidate execution.graph part.1 index) run v)).w := by
    rw [hfr]
    exact hw
  exact ⟨_, hmem, hwpos⟩

/-- Strict vertical separation across a rank gap: the tail node's bottom edge
sits strictly below the head node's top edge. Band containment bounds both by
their layer bands; the consecutive top step clears at least one (the rank
step is positive), and disjointness carries the lead across further ranks. -/
private theorem partContent_band_strict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    {tV hV : Nat}
    (htB : tV < run.proper.nodes.length) (hhB : hV < run.proper.nodes.length)
    {k : Int} (hk : 1 ≤ k)
    (hrk : rk run.proper.rank hV = rk run.proper.rank tV + k) :
    run.ys.getD tV 0 + RouteImpl.nodeH run.proper tV < run.ys.getD hV 0 := by
  obtain ⟨rT, lT, hLT, hmemT, hbT1, hbT2⟩ := partContent_ys_band hrun htB
  obtain ⟨rH, lH, hLH, hmemH, hbH1, hbH2⟩ := partContent_ys_band hrun hhB
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteWith, hrouteEq, hry, _, _⟩ :=
    componentRun_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hrouteWith).1
  obtain ⟨_, _, hlay, _, _⟩ := RouteImpl.layersOk_spec hok
  have hrkT : rk run.proper.rank tV = (rT : Int) := (hlay rT lT hLT tV hmemT).2
  have hrkH : rk run.proper.rank hV = (rH : Int) := (hlay rH lH hLH hV hmemH).2
  obtain ⟨hgap1, hslot1, hlenS, hnn, _, htop, _⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hrTlen : rT < run.layers.length := (List.getElem?_eq_some_iff.mp hLT).1
  have hrHlen : rH < run.layers.length := (List.getElem?_eq_some_iff.mp hLH).1
  have hrT : rT < rH := by omega
  have htopEq : run.top = CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))) := htop
  have htopLen : run.top.length = run.layers.length := by
    have hcond : (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))).length + 1 =
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)).length := by
      have e1 : (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
          run.coordinateProper run.layers
          (run.routing.gaps.map (·.slots))).length =
          (run.routing.gaps.map (·.slots)).length :=
        CoordsImpl.rankSteps_length _ _ _ _ _
      have e2 : (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)).length =
          run.layers.length := by simp
      omega
    rw [htopEq, CoordsImpl.topsFrom_length _ _ _ _ _ hcond, List.length_map]
  have hrTtop : rT < run.top.length := by rw [htopLen]; exact hrTlen
  have hrHtop : rH < run.top.length := by rw [htopLen]; exact hrHlen
  have hrT1top : rT + 1 < run.top.length := by omega
  have hstepsLen : (CoordsImpl.rankSteps execution.params.rankGap
      execution.params.slot run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots))).length =
      (run.routing.gaps.map (·.slots)).length :=
    CoordsImpl.rankSteps_length _ _ _ _ _
  have hgapsLen : run.routing.gaps.length = run.layers.length - 1 := by
    have hg := (RouteImpl.routeWithLanes_geometry hrouteWith).2.2.2.2.1
    have heq : run.routing = run.lanes.routing := hrouteEq.symm
    rw [← heq] at hg
    exact hg
  have hrSlots : rT < (run.routing.gaps.map (·.slots)).length := by
    have e : (run.routing.gaps.map (·.slots)).length = run.routing.gaps.length := by
      simp
    omega
  have hstep := partContent_steps_pos run.coordinateProper run.layers
    (run.routing.gaps.map (·.slots)) execution.params.rankGap execution.params.slot
    hgap1 hslot1 hnn hrSlots
  have hrSteps : rT < (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots))).length := by
    rw [hstepsLen]; exact hrSlots
  have hssT : (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)))[rT]? =
      some ((CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)))[rT]'hrSteps) :=
    List.getElem?_eq_getElem hrSteps
  have esT : (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots))).getD rT 0 =
      ((CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)))[rT]'hrSteps) := by
    rw [List.getD_eq_getElem?_getD, hssT, Option.getD_some]
  have hsT : 1 ≤ ((CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
      run.coordinateProper run.layers
      (run.routing.gaps.map (·.slots)))[rT]'hrSteps) := by
    rw [← esT]; exact hstep
  have hhsT0 : (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))[rT]? =
      some (CoordsImpl.layerHeight run.coordinateProper lT) := by
    rw [List.getElem?_map, hLT, Option.map_some]
  have hrT1len : rT + 1 < run.layers.length := by omega
  have hlayT1 : run.layers[rT + 1]? =
      some (run.layers[rT + 1]'(by omega : rT + 1 < run.layers.length)) :=
    List.getElem?_eq_getElem (by omega : rT + 1 < run.layers.length)
  have hhsT1 : (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))[rT + 1]? =
      some (CoordsImpl.layerHeight run.coordinateProper
        (run.layers[rT + 1]'(by omega : rT + 1 < run.layers.length))) := by
    rw [List.getElem?_map, hlayT1, Option.map_some]
  have hTlen : (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)))).length = run.layers.length := by
    rw [← htopEq]; exact htopLen
  have hrTtops : rT < (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)))).length := by
    rw [hTlen]; exact hrTlen
  have hrT1tops : rT + 1 < (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)))).length := by
    rw [hTlen]; omega
  have hrHtops : rH < (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots)))).length := by
    rw [hTlen]; exact hrHlen
  have haT : (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))))[rT]? =
      some (run.top.getD rT 0) := by
    have g : run.top[rT]? = some (run.top[rT]'hrTtop) :=
      List.getElem?_eq_getElem hrTtop
    have e : run.top.getD rT 0 = run.top[rT]'hrTtop := by
      rw [List.getD_eq_getElem?_getD, g, Option.getD_some]
    rw [e, ← htopEq]; exact g
  have hbT1 : (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))))[rT + 1]? =
      some (run.top.getD (rT + 1) 0) := by
    have g : run.top[rT + 1]? = some (run.top[rT + 1]'hrT1top) :=
      List.getElem?_eq_getElem hrT1top
    have e : run.top.getD (rT + 1) 0 = run.top[rT + 1]'hrT1top := by
      rw [List.getD_eq_getElem?_getD, g, Option.getD_some]
    rw [e, ← htopEq]; exact g
  have hbH : (CoordsImpl.topsFrom 0 1 0
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))))[rH]? =
      some (run.top.getD rH 0) := by
    have g : run.top[rH]? = some (run.top[rH]'hrHtop) :=
      List.getElem?_eq_getElem hrHtop
    have e : run.top.getD rH 0 = run.top[rH]'hrHtop := by
      rw [List.getD_eq_getElem?_getD, g, Option.getD_some]
    rw [e, ← htopEq]; exact g
  have hstepEq := partContent_tops_step _ _ _ rT haT hbT1 hhsT0 hssT
  have ebH : run.top.getD rH 0 =
      ((CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
        (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
          run.coordinateProper run.layers
          (run.routing.gaps.map (·.slots))))[rH]'hrHtops) := by
    rw [List.getD_eq_getElem?_getD]
    have g : run.top[rH]? =
        some ((CoordsImpl.topsFrom 0 1 0
          (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
          (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
            run.coordinateProper run.layers
            (run.routing.gaps.map (·.slots))))[rH]'hrHtops) := by
      rw [htopEq]; exact List.getElem?_eq_getElem hrHtops
    rw [g, Option.getD_some]
  have hnnT1 : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
      (run.layers[rT + 1]'(by omega : rT + 1 < run.layers.length)) :=
    CoordsImpl.layerHeight_nonneg _ _
  have ebT1 : run.top.getD (rT + 1) 0 =
      ((CoordsImpl.topsFrom 0 1 0
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
        (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
          run.coordinateProper run.layers
            (run.routing.gaps.map (·.slots))))[rT + 1]'hrT1tops) := by
    rw [List.getD_eq_getElem?_getD]
    have g : run.top[rT + 1]? =
        some ((CoordsImpl.topsFrom 0 1 0
          (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
          (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
            run.coordinateProper run.layers
            (run.routing.gaps.map (·.slots))))[rT + 1]'hrT1tops) := by
      rw [htopEq]; exact List.getElem?_eq_getElem hrT1tops
    rw [g, Option.getD_some]
  by_cases heq : rT + 1 = rH
  · subst heq
    omega
  · have hlt : rT + 1 < rH := by omega
    have hh : ∀ h ∈ (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)),
        0 ≤ h := by
      intro h hm
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hm
      exact CoordsImpl.layerHeight_nonneg _ _
    have hss0 : ∀ s ∈ (CoordsImpl.rankSteps execution.params.rankGap
        execution.params.slot run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))), 0 ≤ s :=
      CoordsImpl.rankSteps_nonneg (by omega) (by omega) _ _ _ hnn
    have hlen : (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers
        (run.routing.gaps.map (·.slots))).length + 1 =
        (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)).length := by
      have e1 := hstepsLen
      have e2 : (run.layers.map (CoordsImpl.layerHeight run.coordinateProper)).length =
          run.layers.length := by
        simp
      omega
    have hdis := CoordsImpl.topsFrom_disjoint 0 1 (by omega) (by omega)
      (run.layers.map (CoordsImpl.layerHeight run.coordinateProper))
      (CoordsImpl.rankSteps execution.params.rankGap execution.params.slot
        run.coordinateProper run.layers (run.routing.gaps.map (·.slots))) 0
      hh hss0 hlen (rT + 1) rH _ _ _ hlt hbT1 hbH hhsT1
    omega

/-- Every candidate node is border-0 once no border `-2` node exists: the
marker trichotomy leaves `0`, and bottom markers rejoin a top. -/
private theorem partContent_all_zero {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat}
    (hcomp : part.1 ∈ components execution.graph)
    (hno2 : ∀ (v : Nat) (node : Node),
      (componentCandidate execution.graph part.1 index).nodes[v]? = some node →
      node.border ≠ -2)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph part.1 index).nodes[v]? = some node) :
    node.border = 0 := by
  have htri := componentCandidate_marker_shape execution.graph_eq hnode
  rcases htri.1 with h0 | h2m | h2p
  · exact h0
  · exact absurd h2m (hno2 v node hnode)
  · exact absurd h2p (partContent_no_bottom execution hcomp hno2 hnode)

/-- Candidate construction preserves the graph slot: every branch is an
edge-only update. -/
private theorem partContent_candidate_slot (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).slot = g.slot := by
  unfold componentCandidate componentGraph cycleGraph Compound.protect
    breakCyclesGreedy ProtectedCycles.breakWithHierarchy breakCycles
  dsimp only
  split
  · split <;> rfl

  · split <;> rfl
/-- An ordinary (non-self-loop) candidate edge lands on the shifted native
route points: loop placements only shadow self-loop declarations. -/
private theorem partContent_ordinary_placed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured = .ok loops)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph part.1 index).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ rt : EdgeRoute, run.routes[i]? = some rt ∧ rt.original = i ∧
      (placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops).routes[i]? =
        some (edge.decl, rt.points.map
          (shiftPoint (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph part.1 index) run execution.measured loops).minY))) := by
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hnd := componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq part.1 index
  have hloop0 := componentLoops_excludes_ordinary_decl hloops hnd hedge hne
  have hloop : ∀ l ∈ loops, l.1 ≠ (componentCandidate execution.graph part.1 index).edges[i].decl := by
    simpa only [he] using hloop0
  obtain ⟨rt, hget, horig, _⟩ := componentRun_route_of_index hrun hi
  have hplaced := placeComponent_route_entry_of_producer hrun 0 loops i hi hloop
  have h2 : ∀ (h : i < run.routes.length), run.routes[i]'h = rt := fun h =>
    Option.some.inj ((List.getElem?_eq_getElem h).symm.trans hget)
  rw [h2 _] at hplaced
  rw [he] at hplaced
  exact ⟨rt, hget, horig, hplaced⟩

/-- Ranks strictly separate along a non-self-loop candidate edge: the semantic
chain steps `+1` per proper edge, so the head sits at least one above the tail. -/
private theorem partContent_rk_step {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph part.1 index).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ k : Int, 1 ≤ k ∧
      rk run.proper.rank edge.head = rk run.proper.rank edge.tail + k := by
  obtain ⟨chain, hchain, hlen, hhead, hlast, hsegments⟩ :=
    componentRun_semantic_node_chain hrun hedge hne
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteWith, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hok := (RouteImpl.routeWithLanes_geometry hrouteWith).1
  obtain ⟨_, _, _, _, hedge_step⟩ := RouteImpl.layersOk_spec hok
  have hseg : ∀ (j : Nat) (hj : j < chain.length) (hj1 : j + 1 < chain.length),
      ∃ pe ∈ run.proper.edges,
        pe.tail = chain[j]'hj ∧ pe.head = chain[j + 1]'hj1 := by
    intro j hj hj1
    obtain ⟨pe, hmem, _, _, ht, hh⟩ := hsegments j hj hj1
    exact ⟨pe, hmem, ht, hh⟩
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hhead
  have hj : (edge.tail :: rest).length - 1 < (edge.tail :: rest).length := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hj] at hlast
  have hlastEq := Option.some.inj hlast
  have hrk := partContent_chain_rk (p := run.proper) (chain := edge.tail :: rest)
    hseg hedge_step hj
  rw [hlastEq] at hrk
  have hgetD : (edge.tail :: rest).getD 0 0 = edge.tail := rfl
  rw [hgetD] at hrk
  exact ⟨((edge.tail :: rest).length - 1 : Nat), by omega, hrk⟩

/-- The forward route start sits at or below the tail band top: either the
tail row itself or the tail row plus the (nonnegative) node height. -/
private theorem partContent_pieceStart_le {run : Run} {first : Nat} {edge : Edge}
    (htail : (RouteImpl.edgeAt run.proper first).tail = edge.tail)
    (hnodeH : 0 ≤ RouteImpl.nodeH run.proper edge.tail) :
    (RouteImpl.pieceStart run.proper run.ys run.lanes.routing first).y ≤
      run.ys.getD edge.tail 0 + RouteImpl.nodeH run.proper edge.tail := by
  have hps : (RouteImpl.pieceStart run.proper run.ys run.lanes.routing first).y =
      (if RouteImpl.frameKind run.proper (RouteImpl.edgeAt run.proper first).tail = -2
       then RouteImpl.yAt run.ys (RouteImpl.edgeAt run.proper first).tail
       else RouteImpl.yAt run.ys (RouteImpl.edgeAt run.proper first).tail +
         RouteImpl.nodeH run.proper (RouteImpl.edgeAt run.proper first).tail) := rfl
  rw [hps, htail]
  have hy : RouteImpl.yAt run.ys edge.tail = run.ys.getD edge.tail 0 := rfl
  rw [hy]
  by_cases hfk : RouteImpl.frameKind run.proper edge.tail = -2
  · rw [ite_eq_left hfk]
    omega
  · rw [ite_eq_right hfk]
    exact Int.le_refl _

/-- Native route points span two y-values across a rank gap: the lane
endpoints sit at the tail/head node rows, strictly ordered by the band gap. -/
private theorem partContent_rt_points_span {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    {i : Nat} {edge : Edge} {rt : EdgeRoute} {first last : Nat}
    (hrt : run.routes[i]? = some rt) (horig : rt.original = i)
    (hfirst : (RouteImpl.edgesOf run.proper i).head? = some first)
    (hlast : (RouteImpl.edgesOf run.proper i).getLast? = some last)
    (htail : (RouteImpl.edgeAt run.proper first).tail = edge.tail)
    (hhead : (RouteImpl.edgeAt run.proper last).head = edge.head)
    (htB : edge.tail < run.proper.nodes.length) (hhB : edge.head < run.proper.nodes.length)
    {k : Int} (hk : 1 ≤ k)
    (hrk : rk run.proper.rank edge.head = rk run.proper.rank edge.tail + k) :
    ∃ p₁ p₂ : Point, p₁ ∈ rt.points ∧ p₂ ∈ rt.points ∧ p₁.y ≠ p₂.y := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hr, _, _, _, hroutes⟩ :=
    componentRun_spec hrun
  have hmem : rt ∈ run.routes := List.mem_of_getElem? hrt
  rw [← horig] at hfirst hlast
  have hends := RouteImpl.laneSemantic_endpoints hr hroutes rt hmem first last hfirst hlast
  have hband := partContent_band_strict execution hrun htB hhB hk hrk
  have htn : run.proper.nodes[edge.tail]? = some (run.proper.nodes[edge.tail]'htB) :=
    List.getElem?_eq_getElem htB
  have hnn := (componentRun_dims_nonneg hrun _ _ htn).2
  have hnodeH : 0 ≤ RouteImpl.nodeH run.proper edge.tail := by
    unfold RouteImpl.nodeH
    rw [htn]
    exact hnn
  have hyAt : ∀ (y : List Int) (v : Nat), RouteImpl.yAt y v = y.getD v 0 := fun y v => rfl
  by_cases hrev : ((componentCandidate execution.graph part.1 index).edges.map
      (·.reversed)).getD rt.original false = true
  · rw [ite_eq_left hrev] at hends
    obtain ⟨hheadPt, hlastPt⟩ := hends
    rw [hhead, hyAt] at hheadPt
    rw [htail, hyAt] at hlastPt
    have yH : ∀ (p : Point), rt.points.head? = some p →
        p.y = run.ys.getD edge.head 0 := by
      intro p hp
      rw [hheadPt] at hp
      replace hp := Option.some.inj hp
      rw [← hp]
    have yL : ∀ (p : Point), rt.points.getLast? = some p →
        p.y = run.ys.getD edge.tail 0 + RouteImpl.nodeH run.proper edge.tail := by
      intro p hp
      rw [hlastPt] at hp
      replace hp := Option.some.inj hp
      rw [← hp]
    exact ⟨_, _, List.mem_of_getLast? hlastPt, List.mem_of_head? hheadPt,
      by rw [yL _ hlastPt, yH _ hheadPt]; omega⟩
  · rw [ite_eq_right hrev] at hends
    obtain ⟨hheadPt, hlastPt⟩ := hends
    have hsY := partContent_pieceStart_le htail hnodeH
    have hpe : (RouteImpl.pieceEnd run.proper run.ys run.lanes.routing last).y =
        RouteImpl.yAt run.ys (RouteImpl.edgeAt run.proper last).head := rfl
    have heY : (RouteImpl.pieceEnd run.proper run.ys run.lanes.routing last).y =
        run.ys.getD edge.head 0 := by
      rw [hpe, hhead, hyAt]
    have yH : ∀ (p : Point), rt.points.head? = some p →
        p.y ≤ run.ys.getD edge.tail 0 + RouteImpl.nodeH run.proper edge.tail := by
      intro p hp
      rw [hheadPt] at hp
      replace hp := Option.some.inj hp
      rw [← hp]
      exact hsY
    have yL : ∀ (p : Point), rt.points.getLast? = some p →
        p.y = run.ys.getD edge.head 0 := by
      intro p hp
      rw [hlastPt] at hp
      replace hp := Option.some.inj hp
      rw [← hp]
      exact heY
    exact ⟨_, _, List.mem_of_head? hheadPt, List.mem_of_getLast? hlastPt,
      by have g1 := yH _ hheadPt; have g2 := yL _ hlastPt; omega⟩

/-- A part whose content is a non-self-loop route has a positive vertical
span: the placed route inherits the native y-distinctness through the shift. -/
private theorem partContent_route_yspan {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    {area : Int}
    (hcomp : part.1 ∈ components execution.graph)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured = .ok loops)
    (heq : part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area })
    (hzero : ∀ (v : Nat) (node : Node),
      (componentCandidate execution.graph part.1 index).nodes[v]? = some node →
      node.border = 0)
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph part.1 index).edges[i]? = some edge)
    (hne : edge.tail ≠ edge.head) :
    ∃ pts : List Point, ∃ p₁ p₂ : Point,
      (∃ decl : Nat, (decl, pts) ∈ part.2.routes) ∧
      p₁ ∈ pts ∧ p₂ ∈ pts ∧ p₁.y ≠ p₂.y := by
  have hP := checkedParams_valid execution.checked
  have hnd := componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq part.1 index
  have hshape := componentCandidate_shape (components_nodup _ _ hcomp)
    (measuredGraph_shape execution.graph_eq) index
  obtain ⟨rt, hget, horig, hplaced⟩ :=
    partContent_ordinary_placed execution hrun hloops hedge hne
  obtain ⟨first, last, hfirst, hlast, htail, hhead⟩ :=
    componentRun_chain_endpoints hP hnd hshape hrun hedge hne
  obtain ⟨k, hk, hrk⟩ := partContent_rk_step execution hrun hedge hne
  have hbmem := List.mem_of_getElem? hedge
  have htb : edge.tail < (componentCandidate execution.graph part.1 index).nodes.length :=
    (partContent_edge_bounded execution hcomp hbmem).1
  have hhb : edge.head < (componentCandidate execution.graph part.1 index).nodes.length :=
    (partContent_edge_bounded execution hcomp hbmem).2
  have htn := List.getElem?_eq_getElem htb
  have hhn := List.getElem?_eq_getElem hhb
  obtain ⟨_, houtt, _, _⟩ :=
    runProperFloor hrun (portGap_pos execution.checked) htn (hzero _ _ htn)
  obtain ⟨_, houth, _, _⟩ :=
    runProperFloor hrun (portGap_pos execution.checked) hhn (hzero _ _ hhn)
  have htB : edge.tail < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp houtt).1
  have hhB : edge.head < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp houth).1
  obtain ⟨a, b, ha, hb, hne2⟩ := partContent_rt_points_span execution hrun hget horig
    hfirst hlast htail hhead htB hhB hk hrk
  have hroutesEq : part.2.routes = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops).routes := by
    rw [heq]
  rw [← hroutesEq] at hplaced
  have hdec : ∃ decl : Nat,
      (decl, rt.points.map (shiftPoint (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (0 - (placeBounds execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minY))) ∈
      part.2.routes :=
    ⟨edge.decl, List.mem_of_getElem? hplaced⟩
  obtain ⟨hsa1, hsa2, hsne⟩ := partContent_shift_yspan ha hb hne2
  exact ⟨_, _, _, ⟨hdec, hsa1, hsa2, hsne⟩⟩

/-- A part whose edges are all self-loops inherits y-span from its loop
placement: the emitted loop route is the shifted `centre ± slot` placement. -/
private theorem partContent_selfLoop_yspan {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} {index : Nat} {run : Run} {loops : List (Nat × LoopPlacement)}
    {area : Int}
    (hcomp : part.1 ∈ components execution.graph)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph part.1 index) execution.measured
      (candidateOrder index) = .ok run)
    (hloops : componentLoops execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured = .ok loops)
    (heq : part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area })
    {i : Nat} {edge : Edge}
    (hedge : (componentCandidate execution.graph part.1 index).edges[i]? = some edge)
    (hself : edge.tail = edge.head) :
    ∃ pts : List Point, ∃ p₁ p₂ : Point,
      (∃ decl : Nat, (decl, pts) ∈ part.2.routes) ∧
      p₁ ∈ pts ∧ p₂ ∈ pts ∧ p₁.y ≠ p₂.y := by
  have hv : edge.tail < (componentCandidate execution.graph part.1 index).nodes.length :=
    (partContent_edge_bounded execution hcomp (List.mem_of_getElem? hedge)).1
  obtain ⟨q, hqmem, _, _, hplaced⟩ :=
    componentLoops_emitted_self_edge hloops hedge hv hself 0
  obtain ⟨v, _, placements, hplacements, loop, hzip, _, _, _⟩ :=
    componentLoops_entry_origin hloops hqmem
  have hex := componentRun_exact_nil hrun
  have hcon : run.exact.contains v = false := by simp [hex]
  simp only [hcon] at hplacements
  have hmap := partContent_loops_ok_map hplacements
  have hmem2 : q.2 ∈ placements := (List.of_mem_zip hzip).2
  rw [hmap] at hmem2
  obtain ⟨qq, _, hqqeq⟩ := List.mem_map.mp hmem2
  obtain ⟨a, b, ha, hb, hys⟩ := partContent_placement_yspan _ _ _ _ qq.2 qq.1
  rw [hqqeq] at ha hb
  have hgs : execution.graph.slot = execution.params.slot := by
    obtain ⟨metric, labels, raw, _, _, _, hslot, hprep, _⟩ :=
      measuredGraph_loop_reservation_before_prepare execution.graph_eq
    rw [hprep]
    exact hslot
  have hslot : 1 ≤ (componentCandidate execution.graph part.1 index).slot := by
    rw [partContent_candidate_slot, hgs]
    exact (checkedParams_valid execution.checked).2.2.1
  have hne : a.y ≠ b.y := by omega
  have hroutesEq : part.2.routes = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops).routes := by
    rw [heq]
  rw [← hroutesEq] at hplaced
  have hdec : ∃ decl : Nat, (decl, q.2.points.map (shiftPoint
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY))) ∈
      part.2.routes :=
    ⟨edge.decl, List.mem_of_getElem? hplaced⟩
  obtain ⟨hsa1, hsa2, hsne⟩ := partContent_shift_yspan ha hb hne
  exact ⟨_, _, _, ⟨hdec, hsa1, hsa2, hsne⟩⟩

/-- Every placed part with a route has a positive-width rect and either a
positive-height rect or a route y-span: a group-top part goes through the
frame-positive route; otherwise all candidate nodes are border-0, width comes
from the port floor, and the height-or-span disjunct is discharged by the
non-loop route branch or the self-loop placement branch. -/
theorem partPositiveContent_holds {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true) :
    PartPositiveContent inp o res := by
  intro execution part hpart hroutes
  obtain ⟨index, run, loops, area, hcomp, hrun, hloops, heq⟩ :=
    partContent_run_loops execution hpart
  by_cases hlive : ∃ (v : Nat) (node : Node),
      (componentCandidate execution.graph part.1 index).nodes[v]? = some node ∧
      node.border = -2
  · obtain ⟨v, node, hnode, hb⟩ := hlive
    obtain ⟨hposW, hposH⟩ := top_frame_pos execution hcomp hrun hnode hb
    have hrectsEq : part.2.rects = (placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops).rects := by rw [heq]
    exact partPositiveContent_of_node execution hrectsEq hnode ⟨hposW, hposH⟩
  · have hno2 : ∀ (v : Nat) (node : Node),
        (componentCandidate execution.graph part.1 index).nodes[v]? = some node →
        node.border ≠ -2 := fun v node h hcon => hlive ⟨v, node, h, hcon⟩
    have hzero : ∀ (v : Nat) (node : Node),
        (componentCandidate execution.graph part.1 index).nodes[v]? = some node →
        node.border = 0 :=
      fun v node hnode => partContent_all_zero execution hcomp hno2 hnode
    have hroutesEq : part.2.routes = (placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops).routes := by rw [heq]
    have hlen := placeComponent_routes_length execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
    rw [← hroutesEq] at hlen
    have hpos : 0 < part.2.routes.length := by
      cases h : part.2.routes with
      | nil => exact absurd h hroutes
      | cons _ _ => exact Nat.zero_lt_succ _
    have helen : 0 < (componentCandidate execution.graph part.1 index).edges.length := by
      omega
    by_cases hns : ∃ (e : Edge), e ∈ (componentCandidate execution.graph part.1 index).edges ∧
        e.tail ≠ e.head
    · obtain ⟨e, hmem, hne⟩ := hns
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      have htb := (partContent_edge_bounded execution hcomp hmem).1
      have htn := List.getElem?_eq_getElem htb
      obtain ⟨wrect, hwmem, hwpos⟩ :=
        partContent_width_pos execution hrun heq htn (hzero _ _ htn)
      have hspan :=
        partContent_route_yspan execution hcomp hrun hloops heq hzero hi hne
      exact ⟨⟨wrect, hwmem, hwpos⟩, Or.inr hspan⟩
    · obtain ⟨e, hedge⟩ : ∃ e : Edge,
          (componentCandidate execution.graph part.1 index).edges[0]? = some e :=
        ⟨_, List.getElem?_eq_getElem helen⟩
      have hmem := List.mem_of_getElem? hedge
      have hself : e.tail = e.head := Classical.byContradiction (fun hcon => hns ⟨e, hmem, hcon⟩)
      have htb := (partContent_edge_bounded execution hcomp hmem).1
      have htn := List.getElem?_eq_getElem htb
      obtain ⟨wrect, hwmem, hwpos⟩ :=
        partContent_width_pos execution hrun heq htn (hzero _ _ htn)
      have hspan :=
        partContent_selfLoop_yspan execution hcomp hrun hloops heq hedge hself
      exact ⟨⟨wrect, hwmem, hwpos⟩, Or.inr hspan⟩

/-- Shelf positivity from positive content: the exact bridge the old
witness's downstream consumer needs. -/
theorem routePartShelfPositive_holds {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    RoutePartShelfPositive inp o res :=
  routePartShelfPositive_of_content (partPositiveContent_holds hwf hfp)
end PipelineImpl
end Layered
end Elegant
