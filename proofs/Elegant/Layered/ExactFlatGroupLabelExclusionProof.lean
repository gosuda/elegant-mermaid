import Elegant.Layered.ExecutedExactParentFrameFitProof
import Elegant.Layered.ExactGroupLoopFixedLeafGapProof
import Elegant.Layered.ExactForwardScopeFreeProof
import Elegant.Layered.ExactBorderChainBProof
import Elegant.Layered.ExactCaptionCapBandProof
import Elegant.Layered.ExactCaptionSelfNarrowProof
import Elegant.Layered.ExactCaptionSelfBottomProof
import Elegant.Layered.ExactPlainNodePathProof
import Elegant.Layered.ExactForeignNonGroupSpansProof
import Elegant.Layered.ExactSideMarkerFactsProof
import Elegant.Layered.PlainNodeSizingFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem localStrictInside (direction : Direction) {frame label : Rect}
    {height margin : Int}
    (h : (shiftRect margin margin (orientRect direction height frame)).StrictInside
      (shiftRect margin margin (orientRect direction height label))) : frame.StrictInside label := by
  cases direction <;> simp only [Rect.StrictInside, shiftRect, orientRect] at h ⊢ <;> omega

private theorem strictInsideUnshift {frame label : Rect} {dx dy : Int}
    (h : (shiftRect dx dy frame).StrictInside (shiftRect dx dy label)) :
    frame.StrictInside label := by
  simp only [Rect.StrictInside, shiftRect] at h ⊢
  omega

private theorem withinSeparated {a b frame label : Rect} (h : RectAxisSeparated a b)
    (ha : a.Contained frame) (hb : b.Contained label) : RectAxisSeparated frame label := by
  simp only [RectAxisSeparated, Rect.Contained] at *
  omega

private theorem separatedNotInside {frame label : Rect} (h : RectAxisSeparated frame label)
    (hw : 0 ≤ label.w) (hh : 0 ≤ label.h) : ¬ frame.StrictInside label := by
  intro hi
  simp only [RectAxisSeparated, Rect.StrictInside] at h hi
  omega

private theorem separatedShift {a b : Rect} {x y : Int} (h : RectAxisSeparated a b) :
    RectAxisSeparated (shiftRect x y a) (shiftRect x y b) := by
  simp only [RectAxisSeparated, shiftRect] at h ⊢
  omega

private theorem separatedOrient (direction : Direction) {a b : Rect} {height : Int}
    (h : RectAxisSeparated a b) : RectAxisSeparated (orientRect direction height a)
      (orientRect direction height b) := by
  cases direction <;> simp only [RectAxisSeparated, orientRect] at h ⊢ <;> omega

private theorem overlapOfInside {frame owner label : Rect}
    (hfit : owner.Contained label) (hw : 0 < owner.w) (hh : 0 < owner.h)
    (hlw : 0 ≤ label.w) (hlh : 0 ≤ label.h) (hi : frame.StrictInside label) :
    owner.meetsInterior frame := by
  simp only [Rect.Contained, Rect.StrictInside, Rect.meetsInterior] at *
  constructor <;> omega

private theorem linesLength {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have h := execution.lines_eq
  unfold boxLines at h
  simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ h).1

private theorem packedRectsSize {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have size (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
      (pairs.foldl packStep start).rects.size = start.rects.size := by
    induction pairs generalizing start with
    | nil => rfl
    | cons pair rest ih => rw [List.foldl_cons, ih, (packStep_sizes start pair).1]
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  rw [← Except.ok.inj h]
  let start : Acc :=
    { execution.componentsAcc with canvasW := packed.width, canvasH := packed.height, titles := [] }
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep start).rects.size =
    inp.boxes.length
  rw [size]
  exact execution.components_rects_size

private theorem plainSource {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    (hplain : source.role = .node ∨ inp.fixedSizes.any (fun row => row.1 == source.id) = true) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.decl = key ∧ node.border = 0 := by
  have hi : key < execution.lines.length := by
    rw [linesLength execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  have hline := List.getElem?_eq_getElem hi
  have hraw : ∃ node, execution.graph0.nodes[key]? = some node ∧ node.decl = key ∧
      node.border = 0 := by
    cases hf : inp.fixedSizes.find? (fun row => row.1 == source.id) with
    | some entry =>
      obtain ⟨node, hn, hd, hb, _, _⟩ :=
        measuredGraph_fixed_node_dims execution.graph0_eq hline hsource hf
      exact ⟨node, hn, hd, hb⟩
    | none =>
      have hany : inp.fixedSizes.any (fun row => row.1 == source.id) = false :=
        List.any_eq_false.mpr (List.find?_eq_none.mp hf)
      have hr : source.role = .node := hplain.resolve_right (by simp [hany])
      exact measuredGraph_node_border_zero execution.checked execution.graph0_eq hline hsource hr hany
  obtain ⟨node, hnode, hdecl, hborder⟩ := hraw
  obtain ⟨sized, hsized, hborderEq, _, hdeclEq⟩ := exactGraph_node_key execution.graph_eq hnode
  exact ⟨sized, hsized, hdeclEq.trans hdecl, hborderEq.trans hborder⟩

private theorem fixedEntryPresent {inp : Input} {id : String} {entry : String × Size}
    (h : inp.fixedSizes.find? (fun row => row.1 == id) = some entry) :
    inp.fixedSizes.any (fun row => row.1 == id) = true :=
  List.any_eq_true.mpr ⟨entry, List.mem_of_find?_eq_some h,
    List.find?_some (p := fun row : String × Size => row.1 == id) h⟩

private theorem exactPartFrame {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {position : Nat} (hpos : position < cg.nodes.length) :
    (placeComponentExact P cg run 0 labels loops).rects[position]? =
      some (shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY) (frameRect P cg run position)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hpos, Option.map_some]

private theorem candidateLength (graph : Graph) (comp : List Nat) (candidate : Nat) :
    (componentCandidate graph comp candidate).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

private theorem candidateSlotPositive {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (comp : List Nat) (candidate : Nat) :
    0 < (componentCandidate execution.graph comp candidate).slot := by
  have hc : (componentCandidate execution.graph comp candidate).slot = execution.graph.slot := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hg := execution.graph_eq
  unfold exactGraph at hg
  obtain ⟨_, _, hg⟩ := bind_ok hg
  have hs : execution.graph.slot = execution.graph0.slot := by rw [← Except.ok.inj hg]
  obtain ⟨_, _, _, _, _, _, hslot, hprep, _⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph0_eq
  have hslot0 : execution.graph0.slot = execution.params.slot := by rw [hprep]; exact hslot
  have hvalid := (checkedParams_valid execution.checked).2.2.1
  rw [hc, hs, hslot0]
  omega

private theorem loopStackFit {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {index : Nat} {edge : Edge} {env label : Rect}
    (hslot : 0 < cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hedge : cg.edges[index]? = some edge) (hloop : edge.tail = edge.head)
    (henv : labelEnvelope P cg run labels index edge = some env)
    (hstack : label ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels edge.decl).map fun l => (l.width, l.height))) :
    let foot := loopFootprintExt cg run labels edge.tail
    0 < foot.w ∧ 0 < foot.h ∧ 0 ≤ label.w ∧ 0 ≤ label.h ∧ foot.Contained label := by
  let sizes := loopSizes cg.edges labels edge.tail cg.slot
  have he : edge ∈ loopEdges cg.edges edge.tail :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hedge, by simp [hloop]⟩
  have hsized : stackSize cg.slot (routeLabels labels edge.decl) ∈ sizes :=
    List.mem_map.mpr ⟨edge, he, rfl⟩
  have hcount : 0 < sizes.length := List.length_pos_iff.mpr (by
    intro he
    rw [he] at hsized
    simp at hsized)
  have hwidths : ∀ s ∈ sizes, 0 ≤ s.width := by
    intro s hs
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hs
    rw [stackSize_width_eq]
    exact Labels.stackWidth_nonneg _
  have hband : 2 * cg.slot ≤ Loops.band cg.slot sizes := foldl_max_height_ge _ _
  have hprod : 0 < (sizes.length : Int) * Loops.band cg.slot sizes :=
    Int.mul_pos (by omega) (by omega)
  have hh : 0 < (loopFootprintExt cg run labels edge.tail).h := by
    change 0 < max _ ((sizes.length : Int) * Loops.band cg.slot sizes)
    have hmax := Int.le_max_right (frameRect default cg run edge.tail).h
      ((sizes.length : Int) * Loops.band cg.slot sizes)
    omega
  have hs := Int.le_of_lt hslot
  have hbool : (edge.tail == edge.head) = true := by simp [hloop]
  have hsource := henv
  unfold labelEnvelope at hsource
  obtain ⟨_, _, hplacement⟩ := Option.bind_eq_some_iff.mp hsource
  have henvFit : (loopFootprintExt cg run labels edge.tail).Contained env := by
    cases hx : run.exact.contains edge.tail with
    | false =>
      simp only [hbool, hx] at hplacement
      exact X_loopEnvelope_containedExt hs hlab hx hedge hloop (Option.some.inj hplacement).symm
    | true =>
      simp only [hbool, hx] at hplacement
      exact X_loopExactEnvelope_containedExt hs hlab hedge hloop
        (Option.some.inj hplacement).symm hx
  have hw : 0 < (loopFootprintExt cg run labels edge.tail).w := by
    change 0 < (if run.exact.contains edge.tail then Loops.exactExtent else Loops.extent) cg.slot sizes
    cases hx : run.exact.contains edge.tail with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hle := extent_ge_lane_width hs hwidths hsized (by omega)
      have hbase := Int.mul_pos hslot (show 0 < (sizes.length : Int) + 1 by omega)
      have hws := hwidths _ hsized
      omega
    | true =>
      simp only [↓reduceIte]
      have nonneg (xs : List LoopLabel) (init : Int) (hinit : 0 ≤ init) :
          0 ≤ xs.foldl (fun w l => max w l.width) init := by
        induction xs generalizing init with
        | nil => exact hinit
        | cons x rest ih => exact ih _ (Int.le_trans hinit (Int.le_max_left _ _))
      have hbase := Int.mul_pos hslot (show 0 < 2 * (sizes.length : Int) + 1 by omega)
      have hmax := nonneg sizes 0 (Int.le_refl 0)
      have hne : sizes.isEmpty = false := by
        cases hsizes : sizes with
        | nil => simp [hsizes] at hcount
        | cons _ _ => rfl
      unfold Loops.exactExtent
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      omega
  have hdims : ∀ s ∈ (routeLabels labels edge.decl).map (fun l => (l.width, l.height)),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hmem
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hmem
    have hd := hlab l (List.mem_filter.mp hl).1
    exact ⟨hd.1, hd.2.1⟩
  obtain ⟨hew, heh⟩ := labelEnvelope_loop_size hloop henv
  obtain ⟨hlw, hlh, hfit⟩ := Labels.stackRects_contained env cg.slot hs hdims
    (by rw [hew, stackSize_width_eq] <;> exact Int.le_refl _)
    (by rw [heh, stackSize_height_eq] <;> exact Int.le_refl _) label hstack
  exact ⟨hw, hh, hlw, hlh, henvFit.trans hfit⟩

set_option maxHeartbeats 800000 in
private theorem routeStackNotInside {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {pos : Nat} {target : Node}
    (htarget : (componentCandidate execution.graph comp candidate).nodes[pos]? = some target)
    (hzero : target.border = 0) {index : Nat} {edge : Edge} {env label : Rect}
    (hedge : (componentCandidate execution.graph comp candidate).edges[index]? = some edge)
    (henv : labelEnvelope execution.params (componentCandidate execution.graph comp candidate)
      run execution.measured index edge = some env)
    (hstack : label ∈ Labels.stackRects env.x env.y
      (componentCandidate execution.graph comp candidate).slot
      ((routeLabels execution.measured edge.decl).map fun l => (l.width, l.height))) :
    ¬ (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      label := by
  let cg := componentCandidate execution.graph comp candidate
  let frame := frameRect execution.params cg run pos
  change ¬ frame.StrictInside label
  intro hi
  have hslot := candidateSlotPositive execution comp candidate
  by_cases hloop : edge.tail = edge.head
  · let foot := loopFootprintExt cg run execution.measured edge.tail
    obtain ⟨hw, hh, hlw, hlh, hfit⟩ :=
      loopStackFit hslot execution.measured_nonneg hedge hloop henv hstack
    have hmeet : foot.meetsInterior frame := overlapOfInside hfit hw hh hlw hlh hi
    have ht := (candidate_edge_endpoints_bounded_general execution.graph comp candidate hcomp
      (sceneExecutionX_edges_bounded execution) (List.mem_of_getElem? hedge)).1
    obtain ⟨owner, howner⟩ : ∃ owner, cg.nodes[edge.tail]? = some owner :=
      ⟨_, List.getElem?_eq_getElem ht⟩
    rcases (X_componentCandidate_marker_shape execution.graph0_eq execution.graph_eq howner).1 with
      hplain | hgroup | hbottom
    · exact componentRunX_plainLoop_footprint_misses_plain_frame execution hcomp hrun hedge
        hloop howner hplain htarget hzero hmeet
    · have hgap := componentRunX_groupLoop_footprint_horizontal_gap execution hwf hfp
        hcomp hrun hedge hloop howner hgroup htarget hzero hmeet.2
      have hx := hmeet.1
      change foot.x + foot.w ≤ frame.x ∨ frame.x + frame.w ≤ foot.x at hgap
      omega
    · exact exactBottomNoLoopX execution comp candidate run (candidateOrder candidate)
        hcomp cg rfl hrun edge.tail owner howner hbottom
        ⟨edge, List.mem_of_getElem? hedge, rfl, hloop.symm⟩
  · have hv := componentRunX_original_nodes_covered hrun pos (List.getElem?_eq_some_iff.mp htarget).1
    have hplain : (cg.nodes.getD pos default).border ≠ -2 := by
      simp [cg, List.getD_eq_getElem?_getD, htarget, hzero]
    have hframe := plain_frame_eq_boxRect execution.params cg run pos hv hplain
    obtain ⟨hlx, size, hsize, hwidth, hheight⟩ := stackRects_entry hstack
    obtain ⟨item, hitem, rfl⟩ := List.mem_map.mp hsize
    have hdims := execution.measured_nonneg item (List.mem_filter.mp hitem).1
    cases hrev : edge.reversed with
    | false =>
      have hsep := XFR_ForwardScopeFreeX_holds exactIds execution hcomp hrun
        index edge env pos label hedge hloop hrev henv hv
        (X_componentRun_source_isReal hrun htarget) hstack
      change (frameRect execution.params cg run pos).StrictInside label at hi
      rw [hframe] at hi
      simp only [RectAxisSeparated, Rect.StrictInside] at hsep hi
      omega
    | true =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
      obtain ⟨_, lane, _, hlane, henvEq⟩ := reversed_envelope_eq hloop hrev henv
      have hmem : lane ∈ run.lanes.runs := List.mem_of_find?_eq_some hlane
      obtain ⟨_, _, hparamSlot, hlist⟩ := RouteImpl.routeWithLanes_spec hlanes
      rw [hlist] at hmem
      have hright := RouteImpl.plannedLane_right_strict (by omega : 0 ≤ execution.params.slot) hmem
      have hbound := RouteImpl.laneRight_bound run.proper run.xs hv
      have henvX : env.x = lane.lane + cg.slot := by rw [henvEq] <;> rfl
      have hlw : 0 ≤ label.w := by rw [hwidth]; exact hdims.1
      change 0 < cg.slot at hslot
      change (frameRect execution.params cg run pos).StrictInside label at hi
      rw [hframe] at hi
      simp only [Rect.StrictInside, boxRect_left, boxRect_w, fdiv2_ediv] at hi
      rw [hlx, henvX] at hi
      rw [fdiv2_ediv] at hbound
      have hreserve : 0 ≤ ((run.proper.nodes.getD pos default).node.loopExtent : Int) := by omega
      omega

private theorem leafNotInPath {inp : Input} {key : Nat} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source) (hleaf : ExactFixedLeaf inp source.id)
    (fuel : Nat) (box : ModelBox) (hbox : box ∈ inp.boxes) :
    key ∉ Compound.ancestors inp.boxes fuel box.parent := by
  induction fuel generalizing box with
  | zero => simp [Compound.ancestors]
  | succ fuel ih =>
    by_cases he : box.parent = ""
    · simp [Compound.ancestors, he]
    cases hfind : inp.boxes.findIdx? (fun b => b.id == box.parent) with
    | none => simp [Compound.ancestors, hfind]
    | some k =>
      obtain ⟨hk, hid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
      have hkb : inp.boxes[k]? = some inp.boxes[k] := List.getElem?_eq_getElem hk
      have hne : key ≠ k := by
        intro heq
        subst k
        have hb := Option.some.inj (hkb.symm.trans hsource)
        exact hleaf box hbox he ((beq_iff_eq.mp hid).symm.trans (congrArg ModelBox.id hb))
      simp [Compound.ancestors, hfind, hkb, hne, ih inp.boxes[k] (List.mem_of_getElem? hkb)]

private theorem groupDecl {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} {candidate pos : Nat} {group : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[pos]? = some group)
    (hborder : group.border = -2) :
    execution.graph.nodes[group.decl]? = some group := by
  obtain ⟨key, _, hg⟩ := componentCandidate_nonplain_source hnode (by omega)
  have hlen := exactGraph_length execution.graph_eq
  have hk : key < execution.graph0.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hg).1
    omega
  have hbase : execution.graph0.nodes[key]? = some execution.graph0.nodes[key] :=
    List.getElem?_eq_getElem hk
  obtain ⟨mapped, hm, hb, _, hd⟩ := exactGraph_node_key execution.graph_eq hbase
  have heq := Option.some.inj (hm.symm.trans hg)
  subst mapped
  have hdecl := (measuredGraph_group_origin execution.graph0_eq hbase (hb.symm.trans hborder)).1
  rw [hd, hdecl]
  exact hg

private theorem exactCoordinateRank {P : Params} {selected : List Nat} {cg : Graph}
    {rr : RankImpl.RankResult} {p : Proper}
    (hrr : rankWithBudget (Compound.rankingGraph cg) = .ok rr)
    (hranks : ∀ (i : Nat) (r : Int), rr.ranks[i]? = some r → p.rank[i]? = some r)
    {i : Nat} (hi : i < cg.nodes.length) :
    rk (coordinateGraphX P selected p).rank i = rk rr.ranks i := by
  obtain ⟨_, _, hinv, _⟩ := RankImpl.rank_spec (g := Compound.rankingGraph cg)
    (r := rr.ranks) (by simp only [RankImpl.rank, hrr])
  have hlen : rr.ranks.length = cg.nodes.length := hinv.1
  have hir : i < rr.ranks.length := hlen.symm ▸ hi
  have hraw : rr.ranks[i]? = some rr.ranks[i] := List.getElem?_eq_getElem hir
  have hp := hranks i _ hraw
  obtain ⟨borderRanks, hborder⟩ := addClusterBorders_rank_prefix
    (titleReservations (sizeProperPortsX P selected p)) P.clusterBorderW
  obtain ⟨titleRanks, htitle⟩ :
      ∃ tail, (titleReservations (sizeProperPortsX P selected p)).rank = p.rank ++ tail := by
    unfold titleReservations sizeProperPortsX
    exact ⟨_, rfl⟩
  have hcoord : (coordinateGraphX P selected p).rank[i]? = some rr.ranks[i] := by
    change (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P selected p)) P.clusterBorderW).rank[i]? = _
    rw [hborder, htitle, List.append_assoc, List.getElem?_append_left
      (List.getElem?_eq_some_iff.mp hp).1]
    exact hp
  simp only [rk, List.getD_eq_getElem?_getD, hcoord, hraw, Option.getD_some]

set_option maxHeartbeats 800000 in
private theorem titleNotInside {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {comp : List Nat} {candidate : Nat} {run : Run}
    (hcomp : comp ∈ components execution.graph)
    (hrun : componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    {key pos : Nat} {target : Node} {source : ModelBox}
    (hsource : inp.boxes[key]? = some source) (hleaf : ExactFixedLeaf inp source.id)
    (hglobal : execution.graph.nodes[key]? = some target) (hdecl : target.decl = key)
    (htarget : (componentCandidate execution.graph comp candidate).nodes[pos]? = some target)
    (hzero : target.border = 0) {i : Nat} {raw : Rect}
    (hraw : (i, raw) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hw : 0 ≤ (transportCaption execution.params o execution.lines comp i raw).w)
    (hh : 0 ≤ (transportCaption execution.params o execution.lines comp i raw).h) :
    ¬ (frameRect execution.params (componentCandidate execution.graph comp candidate) run pos).StrictInside
      (transportCaption execution.params o execution.lines comp i raw) := by
  obtain ⟨⟨group, j⟩, hj, hgroup, hij, _, _⟩ := componentTitles_dimension_source _ _ _ hraw
  change i = j at hij
  subst j
  have hnode := List.mem_zipIdx_iff_getElem?.mp hj
  change group.border = -2 at hgroup
  intro hi
  cases hpath : target.clusterPath.contains group.decl with
  | false =>
    have hne : group.decl ≠ target.decl := by
      intro he
      have hgrp := groupDecl execution hnode hgroup
      rw [he, hdecl] at hgrp
      have hb : group.border = target.border :=
        congrArg Node.border (Option.some.inj (hgrp.symm.trans hglobal))
      rw [hgroup, hzero] at hb
      exact (by decide : (-2 : Int) ≠ 0) hb
    obtain ⟨owner, howner, hownerPath⟩ :=
      X_cg_group_box execution.graph0_eq execution.graph_eq hnode hgroup
    have hreverse : group.clusterPath.contains target.decl = false := by
      apply Bool.eq_false_iff.mpr
      intro hp
      rw [List.contains_iff_mem, hownerPath, hdecl] at hp
      rcases List.mem_append.mp hp with ha | he
      · exact leafNotInPath hsource hleaf inp.boxes.length owner (List.mem_of_getElem? howner) ha
      · exact hne ((List.mem_singleton.mp he).symm.trans hdecl.symm)
    have hchain : X_ForeignBorderChainXAligned exactIds :=
      X_foreignBorderChainXAligned_framed exactIds
    have hdisj := XN_foreignNonGroupSpansClear_holds exactIds
      (XN_bracketMarkersAtRank_holds exactIds)
      (XN_plainClearOfSideMarker_of_path exactIds (XN_plainNodePathResidual_holds exactIds))
      (XN_sideMarkerSpanAligned_of_chain exactIds hchain)
      execution.graph0_eq execution.graph_eq (linesLength execution) hwf hfp hcomp hrun
      hnode htarget hgroup (by omega) hne hpath hreverse
    obtain ⟨hleft, hright⟩ := XC_selfSidesX_closed exactIds execution hcomp hrun i raw group
      hraw hnode hgroup
    have htop := XC_selfTopX_holds exactIds execution hcomp hrun i raw group hraw hnode hgroup
    have hbottom := XC_selfBottomX_closed exactIds execution hcomp hrun i raw group hraw hnode hgroup
    have hfit : (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run i).Contained (transportCaption execution.params o execution.lines comp i raw) := by
      exact ⟨by omega, by omega, by omega, by omega⟩
    obtain ⟨hgw, hgh⟩ := componentRunX_group_frame_dims_pos execution hcomp hrun hnode hgroup
    exact hdisj (overlapOfInside hfit hgw hgh hw hh hi)
  | true =>
    obtain ⟨rr, _, hrr, hcoord, _, _, _, hranks, _⟩ :=
      X_cg_run_bundle execution.graph0_eq execution.graph_eq hcomp hrun
    obtain ⟨bottom, hbottom⟩ :=
      X_componentRun_cg_bottom_find execution.graph0_eq execution.graph_eq (linesLength execution)
        hcomp hnode hgroup
    have hbetween := ranked_compound_member_interval hrr
      (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hgroup hbottom
      (List.mk_mem_zipIdx_iff_getElem?.mpr htarget) hzero hpath
    have hit := (List.getElem?_eq_some_iff.mp hnode).1
    have hpt := (List.getElem?_eq_some_iff.mp htarget).1
    have hri := exactCoordinateRank (P := execution.params) (selected := exactDecls exactIds inp)
      hrr hranks hit
    have hrp := exactCoordinateRank (P := execution.params) (selected := exactDecls exactIds inp)
      hrr hranks hpt
    rw [hcoord] at hri hrp
    have hv := componentRunX_original_nodes_covered hrun pos hpt
    obtain ⟨layer, hl, _, hlo, _⟩ := componentRunX_node_rank_band hrun hv
    obtain ⟨top, htop, _, _, _⟩ := componentRunX_node_rank_band hrun
      (componentRunX_original_nodes_covered hrun i hit)
    rw [X_proper_rank_eq_local hrun pos] at hl hlo
    rw [X_proper_rank_eq_local hrun i] at htop
    have hlt : (rk run.coordinateProper.rank i).toNat <
        (rk run.coordinateProper.rank pos).toNat := by
      have hstrict : rk rr.ranks i < rk rr.ranks pos :=
        Int.lt_iff_add_one_le.mpr hbetween.1
      rw [hri, hrp]
      exact (Int.toNat_lt_toNat
        (Int.lt_of_le_of_lt (rankWithBudget_rk_nonneg hrr i) hstrict)).2 hstrict
    have hgap := (X_ReserveBands_holds exactIds hrun).2 _ _ _ _ hlt htop hl
    have hcap := XC_capBandX_holds exactIds execution hcomp hrun i raw group hraw hnode hgroup
    have htopLayer : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = top := by
      simp only [List.getD_eq_getElem?_getD, htop, Option.getD_some]
    rw [htopLayer] at hcap
    have hcapBelow := Int.le_trans hcap (Int.le_trans hgap hlo)
    have hplain : ((componentCandidate execution.graph comp candidate).nodes.getD pos default).border
        ≠ -2 := by simp [List.getD_eq_getElem?_getD, htarget, hzero]
    rw [plain_frame_eq_boxRect _ _ _ _ hv hplain] at hi
    have ht : run.ys.getD pos 0 < (transportCaption execution.params o execution.lines comp i raw).y :=
      hi.2.2.1
    exact Int.not_lt_of_ge (Int.le_trans (Int.le_add_of_nonneg_right hh) hcapBelow) ht

private theorem plainCoordinateRecord {P : Params} {selected : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P selected cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node) (hb : node.border = 0) :
    ∃ actual : ProperNode, run.coordinateProper.nodes[i]? = some actual ∧
      actual.node.border = 0 := by
  obtain ⟨_, _, _, _, hnorm, hlabels, hcoord, _, _, _, _, _, _, _⟩ := componentRunX_spec hrun
  obtain ⟨actual, ha, _, hborder, _, _⟩ := coordinateGraphX_plain_anchor_dims P
    (addLabelNodes_untouched_node hlabels (normalize_node_record hnorm hn) rfl) hb
  rw [hcoord] at ha
  exact ⟨actual, ha, hborder⟩

set_option maxHeartbeats 600000 in
private theorem plainFramesSeparated {exactIds : List String} {inp : Input} {P : Params}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunX P (exactDecls exactIds inp) cg labels orderOptions = .ok run)
    {i j : Nat} {a b : Node} (ha : cg.nodes[i]? = some a) (hb : cg.nodes[j]? = some b)
    (ha0 : a.border = 0) (hb0 : b.border = 0) (hne : i ≠ j) :
    RectAxisSeparated (frameRect P cg run i) (frameRect P cg run j) := by
  have hi := componentRunX_original_nodes_covered hrun i (List.getElem?_eq_some_iff.mp ha).1
  have hj := componentRunX_original_nodes_covered hrun j (List.getElem?_eq_some_iff.mp hb).1
  have hai : (cg.nodes.getD i default).border ≠ -2 := by
    simp [List.getD_eq_getElem?_getD, ha, ha0]
  have hbj : (cg.nodes.getD j default).border ≠ -2 := by
    simp [List.getD_eq_getElem?_getD, hb, hb0]
  rw [plain_frame_eq_boxRect _ _ _ _ hi hai, plain_frame_eq_boxRect _ _ _ _ hj hbj]
  let ri := (rk run.proper.rank i).toNat
  let rj := (rk run.proper.rank j).toNat
  obtain ⟨li, hli, _, hloi, hhii⟩ := componentRunX_node_rank_band hrun hi
  obtain ⟨lj, hlj, _, hloj, hhij⟩ := componentRunX_node_rank_band hrun hj
  have atRank := (X_ReserveBands_holds exactIds hrun).2
  rcases Nat.lt_trichotomy ri rj with hlt | heq | hgt
  · have hgap := atRank ri rj li lj hlt hli hlj
    exact Or.inr (Or.inr (Or.inl (by
      change run.ys.getD i 0 + RouteImpl.nodeH run.proper i ≤ run.ys.getD j 0
      exact Int.le_trans hhii (Int.le_trans hgap hloj))))
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, _, _⟩ := componentRunX_spec hrun
    have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hlanes).1).2.2.2.1
    obtain ⟨la, hla, hma, _⟩ := hcov i hi
    obtain ⟨lb, hlb, hmb, _⟩ := hcov j hj
    change run.layers[ri]? = some la at hla
    change run.layers[rj]? = some lb at hlb
    rw [← heq, hla] at hlb
    have hab : la = lb := Option.some.inj hlb
    subst lb
    obtain ⟨x, hx⟩ := List.mem_iff_getElem?.mp hma
    obtain ⟨y, hy⟩ := List.mem_iff_getElem?.mp hmb
    obtain ⟨aa, haa, haa0⟩ := plainCoordinateRecord hrun ha ha0
    obtain ⟨bb, hbb, hbb0⟩ := plainCoordinateRecord hrun hb hb0
    rcases Nat.lt_trichotomy x y with hxy | hxy | hyx
    · exact Or.inl (XLrr_fixedSep0_holds exactIds P inp cg run labels orderOptions hrun
        la x y i j aa bb (List.mem_of_getElem? hla) hxy hx hy haa hbb haa0 hbb0)
    · subst y
      exact False.elim (hne (Option.some.inj (hx.symm.trans hy)))
    · exact Or.inr (Or.inl (XLrr_fixedSep0_holds exactIds P inp cg run labels orderOptions hrun
        la y x j i bb aa (List.mem_of_getElem? hla) hyx hy hx hbb haa hbb0 haa0))
  · have hgap := atRank rj ri lj li hgt hlj hli
    exact Or.inr (Or.inr (Or.inr (by
      change run.ys.getD j 0 + RouteImpl.nodeH run.proper j ≤ run.ys.getD i 0
      exact Int.le_trans hhij (Int.le_trans hgap hloi))))

private theorem captionSizeNonneg (P : Params) (o : Options) (lines : List Measure.Line)
    (hline : 0 ≤ P.lineH) :
    0 ≤ (titleCaptionSize P o lines).w ∧ 0 ≤ (titleCaptionSize P o lines).h := by
  have widthNonneg (rows : List Measure.Line) (initial : Int) (hi : 0 ≤ initial) :
      0 ≤ rows.foldl (fun width line => max width line.width) initial := by
    induction rows generalizing initial with
    | nil => exact hi
    | cons line rest ih => exact ih _ (Int.le_trans hi (Int.le_max_left _ _))
  have hw := widthNonneg lines 0 (Int.le_refl 0)
  have hh : 0 ≤ (max 1 lines.length : Int) * P.lineH := Int.mul_nonneg (by omega) hline
  cases hd : o.direction <;> simp only [titleCaptionSize, hd] <;>
    first | exact ⟨hw, hh⟩ | exact ⟨hh, hw⟩

set_option maxHeartbeats 1600000 in
private theorem foreignLabelNotInside {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} {id : String} {entry : String × Size} {frame : Box} {label : SceneLabel}
    (hrun : layoutX exactIds inp o = .ok res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hfit : InputFixedFit inp o)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == id) = some entry)
    (hleaf : ExactFixedLeaf inp id)
    (hlookup : res.scene.boxes.find? (fun box => box.id == id) = some frame)
    (hrole : frame.role = "group") (hlabel : label ∈ res.scene.labels)
    (hforeign : label.owner ≠ id) : ¬ frame.rect.StrictInside label.rect := by
  obtain ⟨execution⟩ := layoutX_sceneExecution hrun
  obtain ⟨key, hframe⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hlookup)
  obtain ⟨source, hsource, hframeId, _, _, hframeRect⟩ := sceneBox_source_rectX execution hframe
  have hfind := List.find?_some (p := fun box : Box => box.id == id) hlookup
  have hid : source.id = id := hframeId.symm.trans (beq_iff_eq.mp hfind)
  have hleafSource : ExactFixedLeaf inp source.id := by rwa [hid]
  have hfixedSource : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry := by
    rwa [hid]
  have hgroup : source.role.id = "group" := by
    have h := hframe
    rw [execution.boxes_eq_mapX] at h
    simp only [List.getElem?_map, List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add] at h
    exact (congrArg Box.role (Option.some.inj h)).trans hrole
  have hplain : source.role = .node ∨ inp.fixedSizes.any (fun e => e.1 == source.id) = true := by
    cases hs : source.role with
    | node => simp [hs, BoxRole.id] at hgroup
    | group => exact Or.inr (fixedEntryPresent hfixedSource)
  obtain ⟨target, htarget, hdecl, hzero⟩ := plainSource execution hsource hplain
  obtain ⟨packed, hpack, hrects, hlabels, htitles, hnonneg⟩ :=
    X_packedPartTransportBounded_closed exactIds execution
  have hkey : key < execution.packedAcc.rects.size := by
    rw [packedRectsSize execution]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨pk, part, pos, fr, shelf, hpart, hpos, hfr, hshelf, hpackedFr, hcontainFr⟩ :=
    hrects key hkey _ rfl
  have across {p : Nat} {shelf' r : Rect} (hne : pk ≠ p)
      (hsh : packed.boxes[p]? = some shelf') (hsub : shelf'.Contained r) :
      RectAxisSeparated (execution.packedAcc.rects.getD key default) r :=
    withinSeparated (pack_shelves_axisSeparatedX hpack hne hshelf hsh) hcontainFr hsub
  let margin := execution.params.canvasMargin
  let canvasH := execution.packedAcc.canvasH
  let P := execution.params
  have hline := checkedParams_lineH_nonneg execution.checked
  have hacc := execution.packedAcc_bounded (exactPartsBounded' execution)
  rw [execution.scene_eq] at hlabel
  have hlabBridge := (sceneOf_straightenAcc execution.params inp o execution.lines
    execution.packedAcc execution.straightAcc execution.measured execution.straight_eq).2.2
  rw [hlabBridge] at hlabel
  obtain ⟨⟨original, index⟩, hzip, hemitted⟩ := List.mem_filterMap.mp hlabel
  cases hex : inp.boxes.any (fun box => box.id == original.owner && box.exclusive) with
  | true => simp only [hex, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hex, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == index) with
    | some measured =>
      simp only [hm] at hemitted
      have hrect := congrArg (fun sl : SceneLabel => sl.rect) (Option.some.inj hemitted)
      let r := execution.packedAcc.labels.getD measured.index default
      change shiftRect margin margin (orientRect o.direction canvasH r) = label.rect at hrect
      rw [← hrect, hframeRect]
      intro hi
      have hinside := localStrictInside o.direction hi
      rcases hlabels measured.index r rfl with
        ⟨p, other, rr, sh, hother, hrr, hsh, hr, hsub⟩ | hdefault
      · by_cases hsame : pk = p
        · subst p
          have heq : other = part := Option.some.inj (hother.symm.trans hpart)
          have hshEq : sh = shelf := Option.some.inj (hsh.symm.trans hshelf)
          subst other
          subst sh
          obtain ⟨candidate, run, loops, _, hcomp, hrun, hplaced⟩ :=
            X_execution_part_run execution (List.mem_of_getElem? hpart)
          let cg := componentCandidate execution.graph part.1 candidate
          let bd := placeBoundsX P cg run execution.measured loops
          have hp : pos < cg.nodes.length := by
            rw [candidateLength]
            exact (List.getElem?_eq_some_iff.mp hpos).1
          have hf : fr = shiftRect (0 - bd.minX) (-bd.minY) (frameRect P cg run pos) := by
            rw [hplaced] at hfr
            exact Option.some.inj (hfr.symm.trans (exactPartFrame hp))
          have hl : part.2.labels = (placedLabels P cg run execution.measured).map
              (fun q => (q.1, shiftRect (0 - bd.minX) (-bd.minY) q.2)) := by
            rw [hplaced] <;> exact X_placeComponentExact_labels_eq
          rw [hl] at hrr
          obtain ⟨⟨k, routeRect⟩, hlocal, hshift⟩ := List.mem_map.mp hrr
          obtain ⟨_, _, edge, env, _, _, _, _, hedge, henv, hstack, hlocalRect⟩ :=
            placedLabels_pair_inv (measureLabels_index_nodup execution.measured_eq) hlocal
          have hclear := routeStackNotInside execution hwf hfp hcomp hrun
            (component_node_lookupX hpos htarget) hzero hedge henv
            (List.of_mem_zip (List.mem_of_find?_eq_some hstack)).2
          have hshiftRect : shiftRect (0 - bd.minX) (-bd.minY) routeRect = rr :=
            congrArg Prod.snd hshift
          rw [hpackedFr, hr, hf, ← hshiftRect, hlocalRect] at hinside
          exact hclear (strictInsideUnshift (strictInsideUnshift hinside))
        · have hs := across hsame hsh hsub
          have hd : 0 ≤ r.w ∧ 0 ≤ r.h := by
            rw [hr]
            have hdim := (exactPartsBounded' execution other (List.mem_of_getElem? hother)).2.2.2.2.2
              (measured.index, rr) hrr
            exact hdim.2.2.2.2
          exact separatedNotInside hs hd.1 hd.2 hinside
      · have hx := hnonneg key _ rfl
        rw [hdefault] at hinside
        change (execution.packedAcc.rects.getD key default).StrictInside ⟨0, 0, 0, 0⟩ at hinside
        exact Int.not_lt_of_ge hx hinside.1
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box => box.id == original.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerKey =>
        simp only [ho] at hemitted
        have hlabelEq := Option.some.inj hemitted
        have hrect := congrArg (fun sl : SceneLabel => sl.rect) hlabelEq
        change sceneCaptionRect P inp o execution.lines execution.packedAcc ownerKey original.owner =
          label.rect at hrect
        unfold sceneCaptionRect at hrect
        cases ht : (sceneTitlesExpr P inp o execution.lines execution.packedAcc).find?
            (fun title => title.1 == original.owner) with
        | some title =>
          simp only [ht, Option.map_some, Option.getD_some] at hrect
          obtain ⟨⟨titleKey, stored⟩, hstored, hemit⟩ :=
            List.mem_filterMap.mp (List.mem_of_find?_eq_some ht)
          obtain ⟨_, _, htitle⟩ := Option.bind_eq_some_iff.mp hemit
          let size := titleCaptionSize P o (execution.lines.getD titleKey [])
          let caption : Rect := { stored with w := size.w, h := size.h }
          have htitleRect : shiftRect margin margin (orientRect o.direction canvasH caption) =
              title.2 := congrArg Prod.snd (Option.some.inj htitle)
          rw [← hrect, ← htitleRect, hframeRect]
          intro hi
          have hinside := localStrictInside o.direction hi
          have hd := captionSizeNonneg P o (execution.lines.getD titleKey []) hline
          obtain ⟨p, other, i, rr, sh, hother, hiKey, hrr, hsh, hr, hsub⟩ :=
            htitles titleKey stored hstored
          have hcaption : caption = shiftRect sh.x sh.y { rr with w := size.w, h := size.h } := by
            dsimp only [caption]
            rw [hr] <;> rfl
          by_cases hsame : pk = p
          · subst p
            have heq : other = part := Option.some.inj (hother.symm.trans hpart)
            have hshEq : sh = shelf := Option.some.inj (hsh.symm.trans hshelf)
            subst other
            subst sh
            obtain ⟨candidate, run, loops, _, hcomp, hrun, hplaced⟩ :=
              X_execution_part_run execution (List.mem_of_getElem? hpart)
            let cg := componentCandidate execution.graph part.1 candidate
            let bd := placeBoundsX P cg run execution.measured loops
            have hp : pos < cg.nodes.length := by
              rw [candidateLength]
              exact (List.getElem?_eq_some_iff.mp hpos).1
            have hf : fr = shiftRect (0 - bd.minX) (-bd.minY) (frameRect P cg run pos) := by
              rw [hplaced] at hfr
              exact Option.some.inj (hfr.symm.trans (exactPartFrame hp))
            have hT : part.2.titles = (componentTitles P cg run).map
                (fun q => (q.1, shiftRect (0 - bd.minX) (-bd.minY) q.2)) := by
              rw [hplaced] <;> rfl
            rw [hT] at hrr
            obtain ⟨⟨j, raw⟩, hraw, hshift⟩ := List.mem_map.mp hrr
            have hj : j = i := congrArg Prod.fst hshift
            subst j
            have hrrShift : shiftRect (0 - bd.minX) (-bd.minY) raw = rr :=
              congrArg Prod.snd hshift
            have hlocal : transportCaption P o execution.lines part.1 i raw =
                { raw with w := size.w, h := size.h } := by
              simp [transportCaption, transportCapSize, List.getD_eq_getElem?_getD, hiKey, size]
            have hclear := titleNotInside execution hwf hfp hcomp hrun hsource hleafSource
              htarget hdecl (component_node_lookupX hpos htarget) hzero hraw
              (by rw [hlocal]; exact hd.1) (by rw [hlocal]; exact hd.2)
            rw [hlocal] at hclear
            rw [hpackedFr, hf, hcaption, ← hrrShift] at hinside
            change (shiftRect shelf.x shelf.y
                (shiftRect (0 - bd.minX) (-bd.minY) (frameRect P cg run pos))).StrictInside
              (shiftRect shelf.x shelf.y
                (shiftRect (0 - bd.minX) (-bd.minY) { raw with w := size.w, h := size.h }))
              at hinside
            exact hclear (strictInsideUnshift (strictInsideUnshift hinside))
          · rw [← hcaption] at hsub
            exact separatedNotInside (across hsame hsh hsub) hd.1 hd.2 hinside
        | none =>
          obtain ⟨hb, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
          let ownerSource := inp.boxes[ownerKey]'hb
          have hownerSource : inp.boxes[ownerKey]? = some ownerSource := List.getElem?_eq_getElem hb
          have hownerId : ownerSource.id = original.owner := hp.1
          have hownerEq : original.owner = label.owner :=
            congrArg (fun sl : SceneLabel => sl.owner) hlabelEq
          have hne : key ≠ ownerKey := by
            intro he
            rw [he] at hsource
            have heq := congrArg ModelBox.id (Option.some.inj (hownerSource.symm.trans hsource))
            exact hforeign (hownerEq.symm.trans (hownerId.symm.trans (heq.trans hid)))
          have hnone : (sceneTitlesExpr P inp o execution.lines execution.packedAcc).find?
              (fun title => title.1 == ownerSource.id) = none := by rwa [hownerId]
          have hcases : X_FallbackOwnerCasesX exactIds :=
            X_FallbackOwnerCasesX_holds exactIds (X_NonfixedGroupTitleX_holds exactIds)
          obtain ⟨ownerNode, hownerNode, _, hownerPlain⟩ :=
            plainSource execution hownerSource (hcases execution hwf hownerSource hnone)
          have hown : ∃ l ∈ inp.labels, l.owner = ownerSource.id :=
            ⟨original, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hzip), hownerId.symm⟩
          have hOwnerFit := xctb_ownerCaptionContainFallbackFitW_of_cases exactIds hcases
            inp o res execution hwf hfit ownerKey ownerSource hownerSource hnone hp.2 hown
          have hOwnerPos : ownerKey < (sceneBoxesExpr P inp o execution.packedAcc).length := by
            simpa only [sceneBoxesExpr, List.length_map, List.length_zipIdx] using hb
          let owner := (sceneBoxesExpr P inp o execution.packedAcc)[ownerKey]'hOwnerPos
          have hownerMap : (sceneBoxesExpr P inp o execution.packedAcc)[ownerKey]? = some owner :=
            List.getElem?_eq_getElem hOwnerPos
          have hget : (sceneBoxesExpr P inp o execution.packedAcc).getD ownerKey
              ⟨"", "", default, "", false⟩ = owner := by
            simp only [List.getD_eq_getElem?_getD, hownerMap, Option.getD_some]
          dsimp only at hOwnerFit
          rw [hget] at hOwnerFit
          simp only [ht, Option.map_none, Option.getD_none, hget] at hrect
          rw [← hrect]
          have hOwnerScene : res.scene.boxes[ownerKey]? = some owner := by
            rw [execution.boxes_eq_mapX]
            exact hownerMap
          obtain ⟨_, _, _, _, _, hOwnerRect⟩ := sceneBox_source_rectX execution hOwnerScene
          have hOwnerBound : ownerKey < execution.packedAcc.rects.size := by
            rw [packedRectsSize execution]
            simpa only [sceneBoxesExpr, List.length_map, List.length_zipIdx] using hOwnerPos
          obtain ⟨p, other, i, rr, sh, hother, hiKey, hrr, hsh, hr, hsub⟩ :=
            hrects ownerKey hOwnerBound _ rfl
          have hsep : RectAxisSeparated frame.rect owner.rect := by
            rw [hframeRect, hOwnerRect]
            apply separatedShift
            apply separatedOrient
            by_cases hsame : pk = p
            · subst p
              have heq : other = part := Option.some.inj (hother.symm.trans hpart)
              have hshEq : sh = shelf := Option.some.inj (hsh.symm.trans hshelf)
              subst other
              subst sh
              obtain ⟨candidate, run, loops, _, _, hrun, hplaced⟩ :=
                X_execution_part_run execution (List.mem_of_getElem? hpart)
              let cg := componentCandidate execution.graph part.1 candidate
              let bd := placeBoundsX P cg run execution.measured loops
              have hlocal (p : Nat) (r : Rect) (hl : part.2.rects[p]? = some r)
                  (hp : p < part.1.length) :
                  r = shiftRect (0 - bd.minX) (-bd.minY) (frameRect P cg run p) := by
                have hsize : p < cg.nodes.length := by rwa [candidateLength]
                rw [hplaced] at hl
                exact Option.some.inj (hl.symm.trans (exactPartFrame hsize))
              rw [hpackedFr, hr, hlocal pos fr hfr (List.getElem?_eq_some_iff.mp hpos).1,
                hlocal i rr hrr (List.getElem?_eq_some_iff.mp hiKey).1]
              apply separatedShift
              apply separatedShift
              have hdiff : pos ≠ i := by
                intro he
                rw [he] at hpos
                exact hne (Option.some.inj (hpos.symm.trans hiKey))
              exact plainFramesSeparated (exactIds := exactIds) (inp := inp) hrun
                (component_node_lookupX hpos htarget) (component_node_lookupX hiKey hownerNode)
                hzero hownerPlain hdiff
            · exact across hsame hsh hsub
          have hOwnerWidth : 0 ≤ owner.rect.w := by
            have hmargin : 0 ≤ P.canvasMargin := by
              change 0 ≤ execution.params.canvasMargin
              exact Int.le_trans (by decide : (0 : Int) ≤ 1)
                (checkedParams_canvasMargin_ge_one execution.checked)
            have hb := sceneOf_boxes_bounded P inp o execution.lines execution.packedAcc
              execution.measured hacc hmargin
            have hs : (sceneOf P inp o execution.lines execution.packedAcc
                execution.measured).boxes[ownerKey]? = some owner := hownerMap
            have hbound := hb (owner, ownerKey) (List.mem_zipIdx_iff_getElem?.mpr hs)
            simp only [Size.containsCellRect, decide_eq_true_iff] at hbound
            exact hbound.2.2.1
          have hcaptionDim :
              0 ≤ (ownedTextRect P owner (execution.lines.getD ownerKey [])).w ∧
              0 ≤ (ownedTextRect P owner (execution.lines.getD ownerKey [])).h := by
            unfold ownedTextRect
            split
            · unfold titleRect
              exact ⟨Int.le_max_left _ _, Int.mul_nonneg (by omega) hline⟩
            · exact ⟨hOwnerWidth, Int.mul_nonneg (Int.natCast_nonneg _) hline⟩
          exact separatedNotInside
            (withinSeparated hsep (Rect.Contained.refl frame.rect) hOwnerFit)
            hcaptionDim.1 hcaptionDim.2

/-- The actual flat exact run cannot put a foreign scene label strictly inside a fixed group leaf,
    even if a frame, shelf or emitted rectangle has a zero dimension. -/
theorem exactFlatFixedLeafLabelExclusion_holds (exactIds : List String) :
    ExactFlatFixedLeafLabelExclusion exactIds := by
  intro obstruction
  cases obstruction with
  | @found _ _ _ _ _ _ _ hrun hwf hfp hfit hfixed hleaf hlookup hrole hlabel hforeign hinside =>
    exact foreignLabelNotInside hrun hwf hfp hfit hfixed hleaf hlookup hrole hlabel hforeign hinside

end Elegant.Layered.PipelineImpl
