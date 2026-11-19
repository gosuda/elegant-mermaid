import Elegant.Layered.Pipeline
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.PipelineFacts
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CgShape
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.SizingCoverageBridge
import Elegant.Layered.Labels
import Elegant.Layered.Coords
import Elegant.Layered.Compound
import Elegant.Layered.Order
import Elegant.Layered.ExecutedBorderOrderFacts
import ElegantGeometry.Validator
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl
theorem not_meetsInterior_shiftRect {a b : Rect} {dx dy : Int}
    (h : ¬ a.meetsInterior b) :
    ¬ (shiftRect dx dy a).meetsInterior (shiftRect dx dy b) := by
  intro h'
  apply h
  simp only [Rect.meetsInterior, shiftRect] at h' ⊢
  omega

theorem not_meetsInterior_orientRect {a b : Rect} {d : Direction} {h : Int}
    (hd : ¬ a.meetsInterior b) :
    ¬ (orientRect d h a).meetsInterior (orientRect d h b) := by
  intro h'
  apply hd
  cases d <;> simp only [Rect.meetsInterior, orientRect] at h' ⊢ <;> omega

theorem not_meetsInterior_of_contained {a b x y : Rect}
    (hab : ¬ a.meetsInterior b) (hx : a.Contained x) (hy : b.Contained y) :
    ¬ x.meetsInterior y := by
  intro h'
  apply hab
  simp only [Rect.meetsInterior, Rect.Contained] at h' hx hy ⊢
  omega
/-! ### Run-level disjointness of two plain positioned nodes -/

/-- Two distinct plain (border-0) nodes of one executed component run have disjoint
frame rectangles: same-layer nodes are separated horizontally by the cross-coordinate
pass, different-layer nodes occupy disjoint rank bands. -/
theorem componentRun_positions_disjoint
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {index : Nat} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp index) labels orderOptions = .ok run)
    {u v : Nat} {nodeU nodeV : Node}
    (hnodeU : (componentCandidate graph comp index).nodes[u]? = some nodeU)
    (hnodeV : (componentCandidate graph comp index).nodes[v]? = some nodeV)
    (hbU : nodeU.border = 0) (hbV : nodeV.border = 0) (hne : u ≠ v) :
    Disjoint (frameRect P (componentCandidate graph comp index) run u)
      (frameRect P (componentCandidate graph comp index) run v) := by
  let cg := componentCandidate graph comp index
  have hu' : u < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeU).1
  have hv' : v < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnodeV).1
  have hcovered := componentRun_original_nodes_covered hrun
  have huP : u < run.proper.nodes.length := hcovered u hu'
  have hvP : v < run.proper.nodes.length := hcovered v hv'
  obtain ⟨actualU, hcoordU, hpropU, -, hbU0, -, -, -, -⟩ :=
    componentRun_original_plain_record hrun hnodeU hbU
  obtain ⟨actualV, hcoordV, hpropV, -, hbV0, -, -, -, -⟩ :=
    componentRun_original_plain_record hrun hnodeV hbV
  -- frameRect reduces to nodeRect since the local border is 0
  have hgetU : cg.nodes.getD u default = nodeU := by
    rw [List.getD_eq_getElem?_getD, hnodeU]
    rfl
  have hgetV : cg.nodes.getD v default = nodeV := by
    rw [List.getD_eq_getElem?_getD, hnodeV]
    rfl
  have hframeU : frameRect P cg run u = nodeRect cg run u := by
    unfold frameRect
    simp only []
    rw [hgetU, hbU]
    rfl
  have hframeV : frameRect P cg run v = nodeRect cg run v := by
    unfold frameRect
    simp only []
    rw [hgetV, hbV]
    rfl
  rw [hframeU, hframeV]
  -- nodeRect in explicit actual-node coordinates
  have hrectU : nodeRect cg run u =
      ⟨run.xs.getD u 0 - Int.fdiv actualU.node.w 2, run.ys.getD u 0,
        actualU.node.w, actualU.node.h⟩ := by
    simp [nodeRect, hpropU]
  have hrectV : nodeRect cg run v =
      ⟨run.xs.getD v 0 - Int.fdiv actualV.node.w 2, run.ys.getD v 0,
        actualV.node.w, actualV.node.h⟩ := by
    simp [nodeRect, hpropV]
  -- run-level facts
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoord, hord, hcross, hproxy, hdrop, hroute,
    hlanes, hry, hys, hroutes⟩ := componentRun_spec hrun
  obtain ⟨ord, hordOk, hordLayers⟩ := hord
  have hlayersOk : RouteImpl.layersOk run.proper run.layers = true :=
    (RouteImpl.routeWithLanes_geometry hroute).1
  obtain ⟨_, hrank, hqlen, _, hrec1, hrec2⟩ := proxyWidths_rel hproxy
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hnodesLen : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [hnodes, hqlen]
  have huC : u < run.coordinateProper.nodes.length := by omega
  have hvC : v < run.coordinateProper.nodes.length := by omega
  have hranks : run.proper.rank = run.coordinateProper.rank := by
    rw [← hdrop]; exact hrank
  -- coordinateYs length and getElem access
  obtain ⟨hrg, hslot, hslotslen, hslotsnn, hsizes, htop, hy⟩ :=
    CoordsImpl.rankCoordsWith_spec hry
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    rw [hy]; simp
  -- run.ys equals coordinateYs at plain nodes via proxyYs
  have huCy : u < run.coordinateYs.length := by omega
  have hvCy : v < run.coordinateYs.length := by omega
  have hysEqU : run.ys.getD u 0 = run.coordinateYs.getD u 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordU huCy, hbU0]
    rfl
  have hysEqV : run.ys.getD v 0 = run.coordinateYs.getD v 0 := by
    rw [← hys, proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV hvCy, hbV0]
    rfl
  -- layer coverage
  have hcov := (RouteImpl.layersOk_spec hlayersOk).2.2.2.1
  obtain ⟨lU, hlyU, huIn, hrkU⟩ := hcov u huP
  obtain ⟨lV, hlyV, hvIn, hrkV⟩ := hcov v hvP
  let rU : Nat := (rk run.proper.rank u).toNat
  let rV : Nat := (rk run.proper.rank v).toNat
  have hrUdef : rU = (rk run.proper.rank u).toNat := rfl
  have hrVdef : rV = (rk run.proper.rank v).toNat := rfl
  have hrkU' : rk run.proper.rank u = (rU : Int) := by
    have h := Int.toNat_of_nonneg hrkU
    exact h.symm
  have hrkV' : rk run.proper.rank v = (rV : Int) := by
    have h := Int.toNat_of_nonneg hrkV
    exact h.symm
  have hrkCoordU : rk run.coordinateProper.rank u = (rU : Int) := by
    rw [← hranks]; exact hrkU'
  have hrkCoordV : rk run.coordinateProper.rank v = (rV : Int) := by
    rw [← hranks]; exact hrkV'
  have hlyU' : run.layers[rU]? = some lU := hlyU
  have hlyV' : run.layers[rV]? = some lV := hlyV
  rcases Nat.lt_trichotomy rU rV with hlt | heq | hgt
  · -- u in a strictly lower rank band than v: y-intervals disjoint
    have hbandU := rankAxis_node_in_band hry hlyU' huIn huC hrkCoordU
    have hbandV := rankAxis_node_in_band hry hlyV' hvIn hvC hrkCoordV
    have hbands := rankAxis_bands_disjoint hry rU rV lU lV hlt hlyU' hlyV'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega
  · -- same rank: horizontal separation
    rw [heq] at hlyU'
    obtain hlVeq : lV = lU := Option.some.inj (hlyV'.symm.trans hlyU')
    rw [hlVeq] at hvIn
    obtain ⟨pu, hpu⟩ := List.mem_iff_getElem?.mp huIn
    obtain ⟨pv, hpv⟩ := List.mem_iff_getElem?.mp hvIn
    have hnePV : pu ≠ pv := by
      intro heq'
      subst heq'
      exact hne (Option.some.inj (hpu.symm.trans hpv))
    have hlayerMem : lU ∈ run.layers := by
      obtain ⟨hmemLT, hmemEq⟩ := List.getElem?_eq_some_iff.mp hlyU'
      rw [← hmemEq]
      exact List.getElem_mem hmemLT
    rcases Nat.lt_or_gt_of_ne hnePV with hplt | hpgt
    · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        (layer := lU) hlayerMem
        hplt hpu hpv hcoordU hcoordV
        (by simp [hbU0]) (by simp [hbV0])
      -- hsep : leftOf u + nodeW u ≤ leftOf v
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
    · have hsep := componentRun_nonproxy_ordered_intervals hgraph hcomp hrun
        (layer := lU) hlayerMem
        hpgt hpv hpu hcoordV hcoordU
        (by simp [hbV0]) (by simp [hbU0])
      have hnodeWU : RouteImpl.nodeW run.proper u = actualU.node.w := by
        simp [RouteImpl.nodeW, hpropU]
      have hnodeWV : RouteImpl.nodeW run.proper v = actualV.node.w := by
        simp [RouteImpl.nodeW, hpropV]
      simp only [RouteImpl.leftOf, RouteImpl.xAt, hnodeWU, hnodeWV] at hsep
      rw [hrectU, hrectV]
      unfold Disjoint Rect.meetsInterior
      dsimp only
      omega
  · -- v in a strictly lower rank band than u
    have hbandU := rankAxis_node_in_band hry hlyU' huIn huC hrkCoordU
    have hbandV := rankAxis_node_in_band hry hlyV' hvIn hvC hrkCoordV
    have hbands := rankAxis_bands_disjoint hry rV rU lV lU hgt hlyV' hlyU'
    have hnodeHU : CoordsImpl.nodeH run.coordinateProper u = actualU.node.h := by
      simp [CoordsImpl.nodeH, hcoordU]
    have hnodeHV : CoordsImpl.nodeH run.coordinateProper v = actualV.node.h := by
      simp [CoordsImpl.nodeH, hcoordV]
    rw [hnodeHU] at hbandU
    rw [hnodeHV] at hbandV
    rw [hrectU, hrectV]
    unfold Disjoint Rect.meetsInterior
    dsimp only
    omega

/-! ### Disjointness and containment transport through the scene projection -/

theorem meetsInterior_of_shiftRect {a b : Rect} {dx dy : Int}
    (h : (shiftRect dx dy a).meetsInterior (shiftRect dx dy b)) : a.meetsInterior b := by
  simp only [Rect.meetsInterior, shiftRect] at h ⊢
  refine ⟨?_, ?_⟩ <;> omega

theorem meetsInterior_of_orientRect {a b : Rect} {d : Direction} {h : Int}
    (h : (orientRect d h a).meetsInterior (orientRect d h b)) : a.meetsInterior b := by
  cases d <;> simp only [Rect.meetsInterior, orientRect] at h ⊢ <;>
    refine ⟨?_, ?_⟩ <;> omega

/-- The interiors of two rects that meet force the interiors of any enclosing pair to
meet: containment only grows the closed extents. -/
theorem meetsInterior_contained_mono {a b x y : Rect} (h : x.meetsInterior y)
    (hx : a.Contained x) (hy : b.Contained y) : a.meetsInterior b := by
  unfold Rect.meetsInterior at h ⊢
  simp only [Rect.Contained] at hx hy
  refine ⟨?_, ?_⟩ <;> omega

theorem contained_shiftRect_imp {a x : Rect} {dx dy : Int} (hc : a.Contained x) :
    (shiftRect dx dy a).Contained (shiftRect dx dy x) := by
  simp only [Rect.Contained, shiftRect] at hc ⊢
  omega

private theorem pairwise_getElem_of_lt {α : Type} {R : α → α → Prop} {l : List α}
    (hp : l.Pairwise R) {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    R l[i] l[j] :=
  List.Pairwise.rel_getElem_of_lt hi hj hp hij

theorem contained_orientRect {a x : Rect} {d : Direction} {h : Int} (hc : a.Contained x) :
    (orientRect d h a).Contained (orientRect d h x) := by
  cases d <;> simp only [orientRect, Rect.Contained] at hc ⊢ <;> omega

/-! ### Well-formed exclusive boxes are plain nodes -/

theorem wellFormed_exclusive_not_group {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) {box : ModelBox} (hbox : box ∈ inp.boxes)
    (hex : box.exclusive = true) : box.role ≠ .group := by
  have hw : modelWellFormed (inputModel inp o) = true := hwf
  unfold modelWellFormed at hw
  simp only [Bool.and_eq_true] at hw
  have hb0 := List.all_eq_true.mp hw.2 box hbox
  simp only [hex, Bool.not_true] at hb0
  intro hgroup
  rw [hgroup] at hb0
  simp at hb0

/-- A non-group source box of the measured graph gives a border-0 node, whether or not
its size is fixed (fixed boxes are role-overridden before marking). -/
theorem measuredGraph_exclusive_node_border_zero
    {P : Params} {inp : Input} {o : Options} {lines : List (List Measure.Line)} {g : Graph}
    (_hp : checkedParams o.profile inp.kind = .ok P)
    (hg : measuredGraph P inp o lines = .ok g)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    (hng : box.role ≠ .group) :
    ∃ node, g.nodes[i]? = some node ∧ node.border = 0 := by
  have hrole : box.role = .node := by
    cases h : box.role with
    | node => rfl
    | group => exact absurd h hng
  cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
  | none =>
    obtain ⟨node, hnode, -, hborder⟩ :=
      measuredGraph_node_border_zero _hp hg hline hbox hrole
        (List.any_eq_false.mpr (List.find?_eq_none.mp hf))
    exact ⟨node, hnode, hborder⟩
  | some entry =>
    obtain ⟨-, -, node, -, -, hnode, hborder, -⟩ :=
      measuredGraph_fixed_loop_reservation hg
        (List.getElem?_eq_some_iff.mp hline).1 hbox hf
    exact ⟨node, hnode, hborder⟩

/-! ### Scene box source and part run lookup -/

/-- A scene box at index `bi` is the oriented, margin-shifted packed rect of the source
model box, carrying its id, parent, and exclusivity. -/
theorem sceneBox_source_rect {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {bi : Nat} {b : Box} (hb : res.scene.boxes[bi]? = some b) :
    ∃ source : ModelBox, inp.boxes[bi]? = some source ∧
      b.id = source.id ∧ b.parent = source.parent ∧ b.exclusive = source.exclusive ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)) := by
  have hbiLT : bi < inp.boxes.length := by
    have h := (List.getElem?_eq_some_iff.mp hb).1
    rw [execution.boxes_eq_map] at h
    simpa only [List.length_map, List.length_zipIdx] using h
  have hbox : res.scene.boxes[bi]? = some
      (Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD bi default)))
        inp.boxes[bi].parent inp.boxes[bi].exclusive) := by
    rw [execution.boxes_eq_map]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hbiLT,
      Option.map_some, Nat.zero_add]
  have hbeq : b = Box.mk inp.boxes[bi].id inp.boxes[bi].role.id
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD bi default)))
      inp.boxes[bi].parent inp.boxes[bi].exclusive :=
    Option.some.inj (hb.symm.trans hbox)
  refine ⟨inp.boxes[bi], List.getElem?_eq_getElem hbiLT, ?_, ?_, ?_, ?_⟩ <;>
    rw [hbeq]

/-- A packed box of one part contains every member frame rect of the part placed at
the pack origin. -/
private theorem packed_box_contains_frame {bounds : Bounds} {frame : Rect} {x y w h : Int}
    (hc : bounds.minX ≤ frame.x ∧ frame.x + frame.w ≤ bounds.right ∧
      bounds.minY ≤ frame.y ∧ frame.y + frame.h ≤ bounds.bottom)
    (hw : w = bounds.right - bounds.minX) (hh : h = bounds.bottom - bounds.minY) :
    (⟨x, y, w, h⟩ : Rect).Contained
      (shiftRect x y (shiftRect (0 - bounds.minX) (0 - bounds.minY) frame)) := by
  simp only [shiftRect, Rect.Contained]
  omega

private theorem placeComponent_rects_get {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponent P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBounds P cg run labels loops).minX)
        (0 - (placeBounds P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponent placeBounds
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- For the packed selection at part index `k`, the part's component run is fixed, and
every model box key of the component's node list gets its final packed rect from that
run's frame rectangle, shifted by the packed box origin. -/
theorem part_frame_lookup
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (packed : Pack.State)
    (hpacked : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    {k : Nat} {entry : List Nat × Part} {box : Rect}
    (hentry : execution.componentsAcc.parts[k]? = some entry)
    (hbox : packed.boxes[k]? = some box) :
    ∃ candidate run loops area,
      componentRun execution.params
        (componentCandidate execution.graph entry.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph entry.1 candidate) run execution.measured = .ok loops ∧
      entry.2 = { placeComponent execution.params
        (componentCandidate execution.graph entry.1 candidate) run 0 execution.measured loops
        with area := area } ∧
      ∀ (i key : Nat), entry.1[i]? = some key → key < inp.boxes.length →
        execution.packedAcc.rects.getD key default =
          shiftRect box.x box.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph entry.1 candidate) run execution.measured loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph entry.1 candidate) run execution.measured loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph entry.1 candidate) run i)) := by
  have hmem : entry ∈ execution.componentsAcc.parts := List.mem_of_getElem? hentry
  obtain ⟨candidate, -, run, loops, area, -, -, -, hrun, hloops, hpartdef⟩ :=
    (actual_components_parts_geometry (by rfl) execution.components_eq).2 entry hmem
  have hrectlen : entry.2.rects.length = entry.1.length := by
    rw [hpartdef]
    have h : { placeComponent execution.params
        (componentCandidate execution.graph entry.1 candidate) run 0
        execution.measured loops with area := area }.rects.length = entry.1.length := by
      have hl : (placeComponent execution.params
          (componentCandidate execution.graph entry.1 candidate) run 0
          execution.measured loops).rects.length = entry.1.length := by
        unfold placeComponent
        simp only [List.length_map, List.length_range]
        rw [componentCandidate_nodes]
        simp [componentGraph]
      simpa using hl
    exact h
  refine ⟨candidate, run, loops, area, hrun, hloops, hpartdef, ?_⟩
  intro i key hkey hkeyBound
  have hi : i < entry.1.length := (List.getElem?_eq_some_iff.mp hkey).1
  have hilen : i < entry.2.rects.length := by omega
  have hsize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_size]
    exact hkeyBound
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? =
      some ((entry, box) : (List Nat × Part) × Rect) :=
    List.getElem?_zip_eq_some.mpr ⟨hentry, hbox⟩
  obtain ⟨candidate', run', loops', area', hrun', hloops', hpartdef', hrect⟩ :=
    actual_components_packed_frame_source (by rfl) execution.components_eq execution.packed_eq
      packed hpacked hselected hkey hsize default
  have hiCG' : i < (componentCandidate execution.graph entry.1 candidate').nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using hi
  have hiCG : i < (componentCandidate execution.graph entry.1 candidate).nodes.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
    simpa using hi
  have hB : entry.2.rects[i]? = some
      (shiftRect (0 - (placeBounds execution.params
          (componentCandidate execution.graph entry.1 candidate') run' execution.measured loops').minX)
        (0 - (placeBounds execution.params
          (componentCandidate execution.graph entry.1 candidate') run' execution.measured loops').minY)
        (frameRect execution.params
          (componentCandidate execution.graph entry.1 candidate') run' i)) := by
    rw [hpartdef']
    exact placeComponent_rects_get hiCG'
  rw [hrect, Option.some.inj (hB.symm.trans (by
    rw [hpartdef]
    exact placeComponent_rects_get hiCG))]

end Elegant.Layered.PipelineImpl
