import Elegant.Layered.ExactParentAttachedClosedProof
import Elegant.Layered.ExactLoopRectFactsProof
import Elegant.Layered.ExactStepLeafFactsProof
import Elegant.Layered.LaneValidity
import Elegant.Layered.PolylineBoxMiss

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A collapsed frame has no children left in the current input. The empty parent
    sentinel is not a parent pointer, even if a box has the empty ID. -/
def ExactFixedLeaf (inp : Input) (id : String) : Prop :=
  ∀ box ∈ inp.boxes, box.parent ≠ "" → box.parent ≠ id

/-- The remaining base case concerns a fixed leaf of a successful flat exact
    layout, including nonexclusive group frames. -/
def ExactFlatFixedLeafMiss (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult} {fixed : ModelBox}
    {entry : String × Size},
    layoutX exactIds inp o = .ok res → WellFormed (inputModel inp o) →
    framedParents inp = true →
    inp.fixedSizes.find? (fun row => row.1 == fixed.id) = some entry →
    ExactFixedLeaf inp fixed.id → ExpandChildParentRouteFrameClear fixed res

private theorem exactFixedLeaf_select {inp : Input} {id : String}
    (h : ExactFixedLeaf inp id) (keep : ModelBox → Bool) (root : String) :
    ExactFixedLeaf (selectInput inp keep root) id := by
  intro box hbox hne
  obtain ⟨source, hsource, _, _, hparent⟩ := selectInput_box_spec inp keep root hbox
  split at hparent
  · exact False.elim (hne hparent)
  · rw [hparent] at hne ⊢
    exact h source hsource hne

private theorem exactFixedLeaf_parent {inp : Input} {group : ModelBox}
    {P : Params} {titleLines : List Measure.Line} {child : FamilyResult}
    (hnodup : (inp.boxes.map (·.id)).Nodup) (hgroup : group ∈ inp.boxes) :
    ExactFixedLeaf (parentSubInput inp group P titleLines child) group.id := by
  intro box hbox hne hpar
  change box ∈ (selectInput inp (fun b => !Compound.inside inp.boxes group.id b.id) "").boxes
    at hbox
  obtain ⟨source, hsource, hkeep, _, hparent⟩ := selectInput_box_spec inp
    (fun b => !Compound.inside inp.boxes group.id b.id) "" hbox
  split at hparent
  · exact hne hparent
  · rw [hparent] at hne hpar
    have hin := inside_of_parent hnodup hgroup hsource hpar.symm hne
    simp [hin] at hkeep

private theorem exactSelectedGroup_notFixed {inp : Input} {group : ModelBox}
    (hgroup : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun row => row.1 == box.id)) = some group) :
    inp.fixedSizes.find? (fun row => row.1 == group.id) = none := by
  have hpred := List.find?_some hgroup
  simp only [Bool.and_eq_true] at hpred
  have hany : inp.fixedSizes.any (fun row => row.1 == group.id) = false := by
    simpa using hpred.2
  exact List.find?_eq_none.mpr (List.any_eq_false.mp hany)

private theorem exactFixedEntry_parent {inp : Input} {group : ModelBox}
    {P : Params} {titleLines : List Measure.Line} {child : FamilyResult}
    (hgroup : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun row => row.1 == box.id)) = some group) :
    ∃ entry, (parentSubInput inp group P titleLines child).fixedSizes.find?
      (fun row => row.1 == group.id) = some entry := by
  let entry : String × Size :=
    (group.id, childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0)
      ((max 1 titleLines.length : Int) * P.lineH)
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩)
  refine ⟨entry, ?_⟩
  change (inp.fixedSizes ++ [entry]).find? (fun row => row.1 == group.id) = some entry
  rw [List.find?_append, exactSelectedGroup_notFixed hgroup]
  simp [entry]

/-- The selected exact run exposes the lane-router execution needed for obstacle
    clearance. Its coordinate premise is on the final reserved ranks, not on
    the ordinary layout or on the unreserved coordinates. -/
theorem componentRunX_route_avoids_real_of_coordFacts
    {P : Params} {exact : List Nat} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions} {rankGap : Nat → Int}
    (hrun : componentRunX P exact cg labels orderOptions = .ok run)
    (hcoords : RouteImpl.CoordFacts run.proper run.layers run.xs run.ys run.top
      run.routing P.nodeGap rankGap P.slot)
    {rt : EdgeRoute} (hrt : rt ∈ run.routes) {start finish v : Nat}
    (hstart : (RouteImpl.edgesOf run.proper rt.original).head? = some start)
    (hfinish : (RouteImpl.edgesOf run.proper rt.original).getLast? = some finish)
    (hv : v < run.proper.nodes.length) (hreal : RouteImpl.IsReal run.proper v)
    (hfrom : v ≠ (RouteImpl.edgeAt run.proper start).tail)
    (hto : v ≠ (RouteImpl.edgeAt run.proper finish).head) :
    ¬ Polyline.hitsRect rt.points (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlanes, hrouting, hpoints⟩ :=
    componentRunX_spec hrun
  rw [← hrouting] at hcoords
  exact route_avoids_nodes (componentRunX_properShape hrun) hlanes hpoints hcoords
    rt hrt start finish hstart hfinish v hv hreal hfrom hto

/-- At the actual offsets of an exact expansion, a child route confined by its
    reservation misses every rectangle disjoint from the parent group frame. -/
theorem exact_childRoute_misses_disjoint_parentFrame
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleLines titles : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {frame : Box} {other : Rect} {dx dy : Int}
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hframed : framedParents inp = true)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hwrap : ExpandChildTitleWrapped P inp o group titles)
    (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
      (titles.foldl (fun width line => max width line.width) 0) titleHeight).x - P.canvasMargin)
    (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
      (titles.foldl (fun width line => max width line.width) 0) titleHeight).y - P.canvasMargin)
    (hdisj : Disjoint frame.rect other) {route : Route} (hroute : route ∈ child.scene.routes) :
    ¬ Polyline.hitsRect (route.points.map (shiftPoint dx dy)) other := by
  have hexpand := hctx.2.2.2.2.2
  have hpos := XG_frame_posB exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams frame hframe
  have hfit := XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams frame titles dx dy hframe hdx hdy hwrap
  have hinset := XG_child_routes_insetB exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctx hparams route hroute
  refine polyline_in_box_misses_disjoint hpos.1 hpos.2 ?_ hdisj
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hstrict := hfit ⟨q.x, q.y, 0, 0⟩ (pointIn_contained.mp (hinset q hq))
  apply pointIn_contained.mpr
  change frame.rect.Contained (shiftRect dx dy ⟨q.x, q.y, 0, 0⟩)
  simp only [Rect.StrictInside, Rect.Contained] at hstrict ⊢
  omega

private theorem exact_fixed_graph_node {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {source : ModelBox} {entry : String × Size}
    (hsource : inp.boxes[key]? = some source)
    (hfixed : inp.fixedSizes.find? (fun row => row.1 == source.id) = some entry) :
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0 := by
  have hlinesEq := execution.lines_eq
  unfold boxLines at hlinesEq
  have hlines : execution.lines.length = inp.boxes.length := by
    simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ hlinesEq).1
  have hkey : key < execution.lines.length := by
    rw [hlines]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨_, _, _, _, _, hnode, hzero, _⟩ :=
    measuredGraph_fixed_loop_reservation execution.graph0_eq hkey hsource hfixed
  obtain ⟨node, hlookup, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode
  exact ⟨node, hlookup, hborder.trans hzero⟩

private theorem exact_packedFrame_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0 (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun q => ⟨q.2.width, q.2.height, q.2.area⟩) =
        .ok packed)
    {k : Nat} {part : List Nat × Part} {shelf : Rect}
    (hpart : execution.componentsAcc.parts[k]? = some part)
    (hshelf : packed.boxes[k]? = some shelf) :
    ∃ candidate run loops,
      componentRunX execution.params (exactDecls exactIds inp)
        (componentCandidate execution.graph part.1 candidate) execution.measured
        (candidateOrder candidate) = .ok run ∧
      ∀ (pos key : Nat), part.1[pos]? = some key → key < inp.boxes.length →
        let cg := componentCandidate execution.graph part.1 candidate
        let bounds := placeBoundsX execution.params cg run execution.measured loops
        let localRect := shiftRect (0 - bounds.minX) (-bounds.minY)
          (frameRect execution.params cg run pos)
        execution.packedAcc.rects.getD key default = shiftRect shelf.x shelf.y localRect ∧
          shelf.Contained (shiftRect shelf.x shelf.y localRect) := by
  obtain ⟨candidate, run, loops, _, hrun, _, hplaced, hrect⟩ :=
    part_frame_lookupX execution packed hpack hpart hshelf
  have hdim := congrArg (fun dims : List (Int × Int) => dims[k]?) (Pack.pack_dimensions hpack)
  simp only [Pack.dimensions, List.getElem?_map, hshelf, hpart, Option.map_some,
    Option.some.injEq, Prod.mk.injEq] at hdim
  refine ⟨candidate, run, loops, hrun, ?_⟩
  intro pos key hpos hkey
  dsimp only
  refine ⟨hrect pos key hpos hkey, ?_⟩
  let cg := componentCandidate execution.graph part.1 candidate
  let bounds := placeBoundsX execution.params cg run execution.measured loops
  let localRect := shiftRect (0 - bounds.minX) (-bounds.minY)
    (frameRect execution.params cg run pos)
  have hposLen : pos < cg.nodes.length := by
    change pos < (componentCandidate execution.graph part.1 candidate).nodes.length
    rw [componentCandidate_nodes]
    simpa only [componentGraph, List.length_map] using (List.getElem?_eq_some_iff.mp hpos).1
  have hmember : localRect ∈ part.2.rects := by
    rw [hplaced]
    refine List.mem_iff_getElem?.mpr ⟨pos, ?_⟩
    change (((List.range cg.nodes.length).map (frameRect execution.params cg run)).map
      (shiftRect (0 - bounds.minX) (-bounds.minY)))[pos]? = some localRect
    have hrange : (List.range cg.nodes.length)[pos]? = some pos :=
      List.getElem?_range hposLen
    rw [List.getElem?_map, List.getElem?_map, hrange]
    simp only [Option.map_some, localRect]
  obtain ⟨_, _, hrectBounds, _, _, _⟩ :=
    exactPartsBounded' execution part (List.mem_of_getElem? hpart)
  have hbounds := hrectBounds localRect hmember
  change shelf.Contained (shiftRect shelf.x shelf.y localRect)
  simp only [Rect.Contained, shiftRect, hdim.1, hdim.2]
  omega

/-- Two distinct fixed entries are disjoint in a successful flat exact run,
    independently of the emitted boxes' exclusive flags. -/
theorem layoutX_fixedFrames_disjoint {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult} (h : layoutX exactIds inp o = .ok res)
    {a b : String} (hne : a ≠ b) {aEntry bEntry : String × Size}
    (hfixA : inp.fixedSizes.find? (fun row => row.1 == a) = some aEntry)
    (hfixB : inp.fixedSizes.find? (fun row => row.1 == b) = some bEntry)
    {fa fb : Box}
    (hfa : res.scene.boxes.find? (fun box => box.id == a) = some fa)
    (hfb : res.scene.boxes.find? (fun box => box.id == b) = some fb) :
    Disjoint fa.rect fb.rect := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hpackEq := execution.packed_eq
  unfold packAcc at hpackEq
  obtain ⟨packed, hpack, _⟩ := bind_ok hpackEq
  obtain ⟨ka, hka⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hfa)
  obtain ⟨kb, hkb⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hfb)
  obtain ⟨sa, hsa, hida, _, _, hra⟩ := sceneBox_source_rectX execution hka
  obtain ⟨sb, hsb, hidb, _, _, hrb⟩ := sceneBox_source_rectX execution hkb
  have ha : sa.id = a := hida.symm.trans (by simpa using List.find?_some hfa)
  have hb : sb.id = b := hidb.symm.trans (by simpa using List.find?_some hfb)
  have hkeyNe : ka ≠ kb := by
    intro eq
    subst kb
    have hs : sa = sb := Option.some.inj (hsa.symm.trans hsb)
    exact hne (ha.symm.trans ((congrArg ModelBox.id hs).trans hb))
  have hlenA := (List.getElem?_eq_some_iff.mp hsa).1
  have hlenB := (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨pa, posA, ca, _, hpa, hposA⟩ := key_part_positionX execution hlenA
  obtain ⟨pb, posB, cb, _, hpb, hposB⟩ := key_part_positionX execution hlenB
  have hca := part_packed_box_lenX execution packed hpack hpa
  have hcb := part_packed_box_lenX execution packed hpack hpb
  have hshA : packed.boxes[ca]? = some packed.boxes[ca] := List.getElem?_eq_getElem hca
  obtain ⟨candidate, run, _, hrun, hgeo⟩ :=
    exact_packedFrame_source execution packed hpack hpa hshA
  obtain ⟨hrectA, hcontainA⟩ := hgeo posA ka hposA hlenA
  by_cases hpart : ca = cb
  · subst cb
    have hp : pb = pa := Option.some.inj (hpb.symm.trans hpa)
    subst pb
    have hpos : posA ≠ posB := by
      intro eq
      subst posB
      exact hkeyNe (Option.some.inj (hposA.symm.trans hposB))
    obtain ⟨na, hna, hzA⟩ :=
      exact_fixed_graph_node execution hsa (entry := aEntry) (by simpa only [ha] using hfixA)
    obtain ⟨nb, hnb, hzB⟩ :=
      exact_fixed_graph_node execution hsb (entry := bEntry) (by simpa only [hb] using hfixB)
    have hrunDisj := XL_fixedDisjoint_closed exactIds execution.params inp
      (componentCandidate execution.graph pa.1 candidate) run execution.measured
      (candidateOrder candidate) hrun (component_node_lookupX hposA hna)
      (component_node_lookupX hposB hnb) hzA hzB hpos
    rw [hra, hrb, hrectA, (hgeo posB kb hposB hlenB).1]
    exact orient_transport_disjoint (shift_preserves_disjoint _ _
      (shift_preserves_disjoint _ _ hrunDisj))
  · have hshB : packed.boxes[cb]? = some packed.boxes[cb] := List.getElem?_eq_getElem hcb
    obtain ⟨_, _, _, _, hgeoB⟩ := exact_packedFrame_source execution packed hpack hpb hshB
    obtain ⟨hrectB, hcontainB⟩ := hgeoB posB kb hposB hlenB
    rw [hra, hrb, hrectA, hrectB]
    exact orient_transport_disjoint (disjoint_contained_right
      (disjoint_contained_left hcontainA (Pack.pack_boxes_disjoint hpack ca cb hca hcb hpart))
      hcontainB)

private theorem exact_merged_frame_sources {inp : Input} {group : ModelBox}
    {parent child res : FamilyResult} {dx dy : Int}
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++ parent.scene.boxes).find?
        (fun box => box.id == model.id)))
    {key : String} {frame : Box}
    (hframe : res.scene.boxes.find? (fun box => box.id == key) = some frame) :
    (∃ native, child.scene.boxes.find? (fun box => box.id == key) = some native ∧
      frame = embedBox group.id dx dy native) ∨
        parent.scene.boxes.find? (fun box => box.id == key) = some frame := by
  have hid : frame.id = key := by simpa using List.find?_some hframe
  have hmem := List.mem_of_find?_eq_some hframe
  rw [hboxes] at hmem
  obtain ⟨model, _, hlookup⟩ := List.mem_filterMap.mp hmem
  have hmodel : frame.id = model.id := by simpa using List.find?_some hlookup
  rw [hmodel.symm.trans hid, List.find?_append, List.find?_map] at hlookup
  change ((child.scene.boxes.find? (fun box => box.id == key)).map
    (embedBox group.id dx dy)).or
      (parent.scene.boxes.find? (fun box => box.id == key)) = some frame at hlookup
  cases hc : child.scene.boxes.find? (fun box => box.id == key) with
  | none =>
    exact Or.inr (by simpa only [hc, Option.map_none, Option.none_or] using hlookup)
  | some native =>
    refine Or.inl ⟨native, rfl, ?_⟩
    apply Option.some.inj
    symm
    simpa only [hc, Option.map_some, Option.some_or] using hlookup

set_option maxHeartbeats 800000 in
/-- Exact recursion preserves fixed-frame disjointness. At a split, replace
    the child box by the fresh parent-side reservation before applying the
    smaller-fuel disjointness result. -/
theorem layoutRecursiveX_fixedFrames_disjoint (exactIds : List String) :
    ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult},
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveX exactIds fuel inp o = .ok res →
      ∀ {a b : String}, a ≠ b → ∀ {aEntry bEntry : String × Size},
      inp.fixedSizes.find? (fun row => row.1 == a) = some aEntry →
      inp.fixedSizes.find? (fun row => row.1 == b) = some bEntry →
      ∀ {fa fb : Box},
      res.scene.boxes.find? (fun box => box.id == a) = some fa →
      res.scene.boxes.find? (fun box => box.id == b) = some fb →
      Disjoint fa.rect fb.rect := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _ _ h a b hne aEntry bEntry hfixA hfixB fa fb hfa hfb
    exact layoutX_fixedFrames_disjoint h hne hfixA hfixB hfa hfb
  | succ fuel ih =>
    intro inp o res hwf hframed h a b hne aEntry bEntry hfixA hfixB fa fb hfa hfb
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hl⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hx⟩
    · exact layoutX_fixedFrames_disjoint hl hne hfixA hfixB hfa hfb
    let height := (max 1 titleLines.length : Int) * P.lineH
    let parentInput := parentSubInput inp group P titleLines child
    have hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
        titleLines height parent child res := ⟨hwf, hg, rfl, hc, hp, hx⟩
    have hparams : ExpandChildCallParams P inp o group titleLines height :=
      ⟨hP, rfl, ⟨metric, hm, ht⟩⟩
    obtain ⟨hwc, hfc, hwp, hfp⟩ := subInputWellFormedB_layoutX exactIds fuel inp o group
      P metric titleLines child parent hwf hframed hP hm ht hc hp
    have hpc : layoutRecursiveX exactIds fuel parentInput o = .ok parent := hp
    have hcc : layoutRecursiveX exactIds fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child := hc
    have hpreserve {id : String} {entry : String × Size}
        (hfixed : inp.fixedSizes.find? (fun row => row.1 == id) = some entry) :
        parentInput.fixedSizes.find? (fun row => row.1 == id) = some entry := by
      change (inp.fixedSizes ++ _).find? (fun row => row.1 == id) = some entry
      rw [List.find?_append, hfixed, Option.some_or]
    have hforeign {id : String} {entry : String × Size}
        (hfixed : inp.fixedSizes.find? (fun row => row.1 == id) = some entry) :
        group.id ≠ id := by
      intro eq
      have hnone := exactSelectedGroup_notFixed hg
      rw [eq, hfixed] at hnone
      cases hnone
    obtain ⟨_, hfresh⟩ := exactFixedEntry_parent (P := P) (titleLines := titleLines) (child := child) hg
    obtain ⟨frame, metric', titles, _, dx, dy, hframe, hm', ht', _, hdx, hdy, _, hboxes⟩ :=
      expandChild_sources hx
    have hwrap : ExpandChildTitleWrapped P inp o group titles := ⟨metric', hm', ht'⟩
    have hcontained {id : String} {native : Box}
        (hf : child.scene.boxes.find? (fun box => box.id == id) = some native) :
        frame.rect.Contained (embedBox group.id dx dy native).rect := by
      have hinset := XG_child_boxes_insetB exactIds fuel P inp o group titleLines height
        parent child res hx hframed hctx hparams native (List.mem_of_find?_eq_some hf)
      have hstrict := XG_content_fit_strict exactIds fuel P inp o group titleLines height
        parent child res hx hframed hctx hparams frame titles dx dy hframe hdx hdy hwrap
        native.rect hinset
      change frame.rect.Contained (shiftRect dx dy native.rect)
      simp only [Rect.StrictInside, Rect.Contained] at hstrict ⊢
      omega
    rcases exact_merged_frame_sources (group := group) hboxes hfa with ⟨na, hna, rfl⟩ | ha
    · rcases exact_merged_frame_sources (group := group) hboxes hfb with ⟨nb, hnb, rfl⟩ | hb
      · exact shift_preserves_disjoint dx dy (ih hwc hfc hcc hne hfixA hfixB hna hnb)
      · exact disjoint_contained_left (hcontained hna)
          (ih hwp hfp hpc (hforeign hfixB) hfresh (hpreserve hfixB) hframe hb)
    · rcases exact_merged_frame_sources (group := group) hboxes hfb with ⟨nb, hnb, rfl⟩ | hb
      · exact disjoint_contained_right
          (ih hwp hfp hpc (Ne.symm (hforeign hfixA)) (hpreserve hfixA) hfresh ha hframe)
          (hcontained hnb)
      · exact ih hwp hfp hpc hne (hpreserve hfixA) (hpreserve hfixB) ha hb

set_option maxHeartbeats 800000 in
/-- The only route geometry needed across the exact recursion is the flat
    fixed-leaf miss. At a child/parent split, apply fixed-frame separation or
    use the freshly fixed group in the smaller-fuel parent call. -/
theorem layoutRecursiveX_fixedLeaf_frameClear (exactIds : List String)
    (hflat : ExactFlatFixedLeafMiss exactIds) :
    ∀ (fuel : Nat) {inp : Input} {o : Options} {res : FamilyResult}
      {fixed : ModelBox} {entry : String × Size},
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursiveX exactIds fuel inp o = .ok res →
      inp.fixedSizes.find? (fun row => row.1 == fixed.id) = some entry →
      ExactFixedLeaf inp fixed.id → ExpandChildParentRouteFrameClear fixed res := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res fixed entry hwf hframed h hfixed hleaf
    exact hflat h hwf hframed hfixed hleaf
  | succ fuel ih =>
    intro inp o res fixed entry hwf hframed h hfixed hleaf
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hl⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hx⟩
    · exact hflat hl hwf hframed hfixed hleaf
    let titleHeight := (max 1 titleLines.length : Int) * P.lineH
    let parentInput := parentSubInput inp group P titleLines child
    have hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
        titleLines titleHeight parent child res := ⟨hwf, hg, rfl, hc, hp, hx⟩
    have hparams : ExpandChildCallParams P inp o group titleLines titleHeight :=
      ⟨hP, rfl, ⟨metric, hm, ht⟩⟩
    obtain ⟨hwc, hfc, hwp, hfp⟩ := subInputWellFormedB_layoutX exactIds fuel inp o group
      P metric titleLines child parent hwf hframed hP hm ht hc hp
    have hpc : layoutRecursiveX exactIds fuel parentInput o = .ok parent := hp
    have hcc : layoutRecursiveX exactIds fuel (childSubInput inp group)
        (childSubOptions o group) = .ok child := hc
    have hchildClear : ExpandChildParentRouteFrameClear fixed child :=
      ih hwc hfc hcc hfixed (exactFixedLeaf_select hleaf _ _)
    have hpfixed : parentInput.fixedSizes.find? (fun row => row.1 == fixed.id) = some entry := by
      change (inp.fixedSizes ++ _).find? (fun row => row.1 == fixed.id) = some entry
      rw [List.find?_append, hfixed, Option.some_or]
    have hparentClear : ExpandChildParentRouteFrameClear fixed parent :=
      ih hwp hfp hpc hpfixed (by
        intro box hbox hparent
        let keep := fun b : ModelBox => !Compound.inside inp.boxes group.id b.id
        change box ∈ (selectInput inp keep "").boxes at hbox
        exact exactFixedLeaf_select hleaf keep "" box hbox hparent)
    obtain ⟨_, hfreshEntry⟩ := exactFixedEntry_parent (P := P)
      (titleLines := titleLines) (child := child) hg
    have hfresh : ExpandChildParentRouteFrameClear group parent :=
      ih hwp hfp hpc hfreshEntry (exactFixedLeaf_parent (Model.boxIds_nodup hwf)
        (List.mem_of_find?_eq_some hg))
    obtain ⟨groupFrame, measuredMetric, titles, _, dx, dy, hgroupFrame, hmetric,
      htitles, _, hdx, hdy, _, hboxes⟩ := expandChild_sources hx
    have hwrap : ExpandChildTitleWrapped P inp o group titles :=
      ⟨measuredMetric, hmetric, htitles⟩
    have hroutes := expandChild_routes_eq hx groupFrame measuredMetric titles dx dy
      hgroupFrame hmetric htitles hdx hdy
    intro frame hframe route hroute hfrom hto
    have hrouteSide : (∃ native ∈ child.scene.routes,
        { native with points := native.points.map (shiftPoint dx dy) } = route) ∨
        route ∈ parent.scene.routes := by
      rw [hroutes] at hroute
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hroute
      rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchild | hparent
      · exact Or.inl (List.mem_map.mp hchild)
      · exact Or.inr hparent
    rcases exact_merged_frame_sources (group := group) hboxes hframe with
      ⟨nativeFrame, hchildFrame, rfl⟩ | hparentFrame
    · change ¬ Polyline.hitsRect route.points (shiftRect dx dy nativeFrame.rect)
      rcases hrouteSide with ⟨native, hnative, rfl⟩ | hparentRoute
      · exact not_hitsRect_shift dx dy native.points nativeFrame.rect
          (hchildClear nativeFrame hchildFrame native hnative hfrom hto)
      · have hinset := XG_child_boxes_insetB exactIds fuel P inp o group titleLines titleHeight
          parent child res hx hframed hctx hparams nativeFrame (List.mem_of_find?_eq_some hchildFrame)
        have hstrict := XG_content_fit_strict exactIds fuel P inp o group titleLines titleHeight
          parent child res hx hframed hctx hparams groupFrame titles dx dy hgroupFrame
          hdx hdy hwrap nativeFrame.rect hinset
        by_cases hfromGroup : route.fromId = group.id
        · exact parentRouteAttachedClear_layoutX hctx groupFrame hgroupFrame route hparentRoute
            (Or.inl hfromGroup) _ hstrict
        by_cases htoGroup : route.toId = group.id
        · exact parentRouteAttachedClear_layoutX hctx groupFrame hgroupFrame route hparentRoute
            (Or.inr htoGroup) _ hstrict
        exact fun hit => hfresh groupFrame hgroupFrame route hparentRoute hfromGroup htoGroup
          (hitsRect_of_strictInside hstrict hit)
    · rcases hrouteSide with ⟨native, hnative, rfl⟩ | hparentRoute
      · have hne : group.id ≠ fixed.id := by
          intro eq
          have hnone := exactSelectedGroup_notFixed hg
          rw [eq, hfixed] at hnone
          cases hnone
        have hdisj := layoutRecursiveX_fixedFrames_disjoint exactIds fuel hwp hfp hpc
          hne hfreshEntry hpfixed hgroupFrame hparentFrame
        exact exact_childRoute_misses_disjoint_parentFrame hctx hframed hparams hgroupFrame
          hwrap hdx hdy hdisj hnative
      · exact hparentClear frame hparentFrame route hparentRoute hfrom hto

/-- Specialize the fixed-leaf induction to the fresh entry in the executed
    parent call. -/
theorem parentRouteFrameClear_layoutX_of_flat
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hflat : ExactFlatFixedLeafMiss exactIds)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res) : ExpandChildParentRouteFrameClear group parent := by
  obtain ⟨hwf, hg, _, _, hparent, _⟩ := hctx
  let parentInput := parentSubInput inp group P titleLines child
  have hwp : WellFormed (inputModel parentInput o) :=
    (subInputWellFormedC2 inp o group hwf).2
      parentInput.fixedSizes parentInput.fixedChildren parentInput.fixedAreas
  have hfp : framedParents parentInput = true :=
    (framedParentsSub inp o group hwf hframed).2
      (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩)
      child.scene child.itemArea
  obtain ⟨_, hfixed⟩ := exactFixedEntry_parent (P := P) (titleLines := titleLines) (child := child) hg
  have hleaf : ExactFixedLeaf parentInput group.id :=
    exactFixedLeaf_parent (Model.boxIds_nodup hwf) (List.mem_of_find?_eq_some hg)
  exact layoutRecursiveX_fixedLeaf_frameClear exactIds hflat fuel hwp hfp hparent hfixed hleaf

/-- The flat fixed-leaf miss gives the whole step miss when combined with the
    closed exact attached theorem. -/
theorem stepC6Miss_layoutX_of_flat
    {exactIds : List String} {fuel : Nat} {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hflat : ExactFlatFixedLeafMiss exactIds)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
    ∀ frame : Box, parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
      ∀ route ∈ parent.scene.routes, ∀ rect : Rect, frame.rect.StrictInside rect →
        ¬ Polyline.hitsRect route.points rect := by
  have hforeign := parentRouteFrameClear_layoutX_of_flat hflat hframed hctx
  have hattached := parentRouteAttachedClear_layoutX hctx
  exact XSGL_stepC6Miss_of_routeClear exactIds fuel P inp o group titleLines titleHeight
    parent child res hctx.2.2.2.2.2 hframed hctx hparams
    (fun frame hframe => ⟨hforeign frame hframe, hattached frame hframe⟩)

end Elegant.Layered.PipelineImpl
