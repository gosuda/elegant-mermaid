import Elegant.Kinds.UsecaseValidExact
import Elegant.Layered.RegionCrossCoordsMetadata
import Elegant.Layered.RegionSubInputStepC2
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.RegionFlatInset
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RegionRunSpec

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem graphEdgesFrom_routesCovered (inp : Input) (routes : List ModelRoute)
    (offset : Nat) {edges : List Edge} (h : graphEdgesFrom inp offset routes = .ok edges) :
    ∀ route ∈ routes,
      (∃ box ∈ inp.boxes, box.id = route.fromId) ∧ (∃ box ∈ inp.boxes, box.id = route.toId) := by
  induction routes generalizing offset edges with
  | nil => simp
  | cons first rest ih =>
    simp only [graphEdgesFrom] at h
    obtain ⟨edge, hedge, h⟩ := bind_ok' h
    obtain ⟨_, hrest, _⟩ := bind_ok' h
    intro route hroute
    rcases List.mem_cons.mp hroute with rfl | hmem
    · obtain ⟨_, _, source, target, hsource, hfrom, htarget, hto⟩ :=
        edgeOf_semantic_endpoints hedge
      exact ⟨⟨source, List.mem_of_getElem? hsource, hfrom⟩,
        ⟨target, List.mem_of_getElem? htarget, hto⟩⟩
    · exact ih (offset + 1) hrest route hmem

/-- The base graph checks route endpoints. Id uniqueness, label owners, and framed
parents are checked at the family entry, not by this graph-construction guard. -/
theorem layoutRIds_routesCovered {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) : RoutesCovered inp := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hgraph := execution.graph0_eq
  unfold measuredGraph at hgraph
  obtain ⟨_, _, hgraph⟩ := bind_ok' hgraph
  obtain ⟨_, hedges, _⟩ := bind_ok' hgraph
  exact graphEdgesFrom_routesCovered inp inp.routes 0 hedges

private theorem sceneBoxExists {scene : Scene} {id : String}
    (h : id ∈ scene.boxes.map (·.id)) : ∃ box, scene.layoutDump.box? id = some box := by
  obtain ⟨source, hsource, hid⟩ := List.mem_map.mp h
  have hfind : (scene.boxes.find? (fun box => box.id == id)).isSome = true :=
    List.find?_isSome.mpr ⟨source, hsource, beq_iff_eq.mpr hid⟩
  change ∃ box, scene.boxes.find? (fun box => box.id == id) = some box
  cases heq : scene.boxes.find? (fun box => box.id == id) with
  | none => simp [heq] at hfind
  | some box => exact ⟨box, rfl⟩

/-- Both route ids resolve in the actual dump. The route points' boundary locations
are a separate geometric obligation. -/
theorem layoutRIds_routeBoxLookups {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ route ∈ res.scene.layoutDump.routes, ∃ fromBox toBox : Box,
      res.scene.layoutDump.box? route.fromId = some fromBox ∧
      res.scene.layoutDump.box? route.toId = some toBox := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hids := (RB_layout_ids h).1
  have hcovered := layoutRIds_routesCovered h
  intro route hroute
  have hr : route ∈ res.scene.routes := hroute
  obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hr
  have hlen : index < inp.routes.length := by
    have hl := (List.getElem?_eq_some_iff.mp hindex).1
    rw [execution.scene_eq, sceneOf_routes_length] at hl
    exact hl
  have hsource := sceneOf_routes_getElem? execution.params inp o execution.lines
    execution.packedAcc execution.measured index hlen
  rw [← execution.scene_eq, hindex] at hsource
  have hfrom := congrArg Route.fromId (Option.some.inj hsource)
  have hto := congrArg Route.toId (Option.some.inj hsource)
  obtain ⟨⟨source, hsourceMem, hsourceId⟩, ⟨target, htargetMem, htargetId⟩⟩ :=
    hcovered inp.routes[index] (List.getElem_mem hlen)
  have hfromMem : route.fromId ∈ res.scene.boxes.map (·.id) := by
    rw [hids]
    exact List.mem_map.mpr ⟨source, hsourceMem, hsourceId.trans hfrom.symm⟩
  have htoMem : route.toId ∈ res.scene.boxes.map (·.id) := by
    rw [hids]
    exact List.mem_map.mpr ⟨target, htargetMem, htargetId.trans hto.symm⟩
  obtain ⟨fromBox, hf⟩ := sceneBoxExists hfromMem
  obtain ⟨toBox, ht⟩ := sceneBoxExists htoMem
  exact ⟨fromBox, toBox, hf, ht⟩

private theorem sceneBoxSource {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) {box : Box}
    (hbox : box ∈ res.scene.boxes) :
    ∃ source ∈ inp.boxes, box.id = source.id ∧ box.parent = source.parent ∧
      box.role = source.role.id := by
  rw [execution.boxes_eq_mapR] at hbox
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hbox
  have hsource : q.1 ∈ inp.boxes.zipIdx.map Prod.fst := List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [List.zipIdx_map_fst] at hsource
  exact ⟨q.1, hsource, rfl, rfl, rfl⟩

/-- The admitted input parent survives as a group box of the dump. C3 still needs
containment of the child rectangle in this group's rectangle. -/
theorem layoutRIds_parentBoxLookup {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ box ∈ res.scene.layoutDump.boxes, box.parent ≠ "" →
      ∃ parent : Box, res.scene.layoutDump.box? box.parent = some parent ∧ parent.role = "group" := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  intro box hbox hnonroot
  obtain ⟨source, hsource, _, hparent, _⟩ := sceneBoxSource execution hbox
  obtain ⟨modelParent, hmodelParent, hmodelId, hmodelRole, _⟩ :=
    framedParents_parent hframed hsource (by simpa only [← hparent] using hnonroot)
  have hmem : box.parent ∈ res.scene.boxes.map (·.id) := by
    rw [(RB_layout_ids h).1]
    exact List.mem_map.mpr ⟨modelParent, hmodelParent, hmodelId.trans hparent.symm⟩
  obtain ⟨parent, hlookup⟩ := sceneBoxExists hmem
  have hfind : res.scene.boxes.find? (fun b => b.id == box.parent) = some parent := hlookup
  have hpid : parent.id = box.parent := beq_iff_eq.mp
    (List.find?_some (p := fun b : Box => b.id == box.parent) hfind)
  obtain ⟨actual, hactual, hactualId, _, hactualRole⟩ :=
    sceneBoxSource execution (List.mem_of_find?_eq_some hfind)
  have heq : actual = modelParent := eq_of_mem_id (Model.boxIds_nodup hwf)
    hactual hmodelParent (hactualId.symm.trans (hpid.trans (hparent.trans hmodelId.symm)))
  rw [heq, hmodelRole] at hactualRole
  exact ⟨parent, hlookup, hactualRole⟩

private theorem partRectsWithin {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (part : List Nat × Part)
    (hpart : part ∈ execution.componentsAcc.parts) (rect : Rect) (hrect : rect ∈ part.2.rects) :
    0 ≤ rect.x ∧ rect.x + rect.w ≤ part.2.width ∧
      0 ≤ rect.y ∧ rect.y + rect.h ≤ part.2.height := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometryR (by rfl) execution.components_eq
  obtain ⟨_, _, cg, run, loops, _, _, _, _, _, _, _, _, heq⟩ := hall part hpart
  rw [heq] at hrect ⊢
  exact placeComponentExact_rects_bounds_zero execution.params cg run execution.measured loops
    rect hrect

private theorem packedRectsWithin {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) (index : Nat)
    (hi : index < inp.boxes.length) :
    (⟨0, 0, execution.packedAcc.canvasW, execution.packedAcc.canvasH⟩ : Rect).Contained
      (execution.packedAcc.rects.getD index default) := by
  obtain ⟨part, hpart, ⟨key, rect⟩, hentry, hkey⟩ := sceneExecutionR_parts_entryR execution hi
  change key = index at hkey
  subst key
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpart
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hentry
  have hp := execution.packed_eq
  unfold packAcc at hp
  obtain ⟨packed, hpack, hout⟩ := bind_ok' hp
  rw [inlineFold_eq_packStep] at hout
  have hcanvas : packed.width = execution.packedAcc.canvasW ∧
      packed.height = execution.packedAcc.canvasH := by
    rw [← Except.ok.inj hout]
    have hfold := foldl_packStep_canvas (execution.componentsAcc.parts.zip packed.boxes)
      ({ execution.componentsAcc with
        canvasW := packed.width
        canvasH := packed.height
        titles := [] } : Acc)
    rw [hfold.1, hfold.2]
    exact ⟨rfl, rfl⟩
  have hkLen : k < packed.boxes.length := by
    rw [Pack.pack_count hpack, List.length_map]
    exact (List.getElem?_eq_some_iff.mp hk).1
  let shelf := packed.boxes[k]
  have hshelf : packed.boxes[k]? = some shelf := List.getElem?_eq_getElem hkLen
  have hselected : (execution.componentsAcc.parts.zip packed.boxes)[k]? = some (part, shelf) :=
    List.getElem?_zip_eq_some.mpr ⟨hk, hshelf⟩
  have hsize : index < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_sizeR]
    exact hi
  have hrect := actual_components_packed_rect_valueR (by rfl) execution.components_eq
    execution.packed_eq packed hpack hselected hj hsize default
  have hpartBounds := partRectsWithin execution part hpart rect (List.of_mem_zip hentry).2
  have hshelfBounds := (Pack.pack_bounds hpack).2 shelf (List.mem_of_getElem? hshelf)
  have hdim := Pack.pack_dimensions hpack
  simp only [Pack.dimensions, List.map_map, Function.comp_def] at hdim
  have hsizeEq := congrArg (fun sizes : List (Int × Int) => sizes[k]?) hdim
  rw [List.getElem?_map, hshelf, List.getElem?_map, hk] at hsizeEq
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsizeEq
  rw [hrect, ← hcanvas.1, ← hcanvas.2]
  simp only [Rect.Contained, shiftRect]
  omega

/-- C1 needs only the box rectangles' hull, independent of label envelope fit. -/
theorem layoutRIds_inset_executed {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∃ P : Params, checkedParams o.profile inp.kind = .ok P ∧
      0 ≤ P.canvasMargin ∧ InsetC1 res.scene P.canvasMargin := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hm := checkedParams_canvasMargin_ge_one execution.checked
  refine ⟨execution.params, execution.checked, by omega, ?_⟩
  intro box hbox
  rw [execution.boxes_eq_mapR] at hbox
  obtain ⟨⟨source, index⟩, hsource, rfl⟩ := List.mem_map.mp hbox
  have hlookup := List.mem_zipIdx_iff_getElem?.mp hsource
  have hi := (List.getElem?_eq_some_iff.mp hlookup).1
  have hrect := packedRectsWithin execution index hi
  have hcanvas := congrArg Scene.canvas execution.scene_eq
  rw [hcanvas]
  change (insetRect (orientCanvas o.direction
      (execution.packedAcc.canvasW + 2 * execution.params.canvasMargin)
      (execution.packedAcc.canvasH + 2 * execution.params.canvasMargin))
    execution.params.canvasMargin).Contained
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD index default)))
  revert hrect
  cases o.direction <;> simp only [orientRect, orientCanvas, insetRect, shiftRect, Rect.Contained]
  all_goals omega

theorem layoutRIds_c1 {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) : Validator.C1 res.scene.layoutDump := by
  obtain ⟨_, _, hmargin, hinset⟩ := layoutRIds_inset_executed h
  intro box hbox
  exact (insetRect_subset_canvas hmargin).trans (hinset box hbox)

theorem layoutRIds_c4 {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutRIds exactIds idSets inp o = .ok res) : Validator.C4 res.scene.layoutDump := by
  intro route hroute _
  exact flatC4B_layoutRIds_closed exactIds idSets inp o res h route hroute

/-- The region selection used by a portfolio trial is stable when its candidate
rewrites the component's edges. A chosen `some` spec does not take the
region-free placement branch. -/
theorem componentTrialR_selected_regions {P : Params} {spec : Option RegionSpec}
    {inp : Input} {g : Graph} {comp : List Nat} (index : Nat)
    {regions : Option ComponentRegions}
    (h : newComponentRegions spec P inp (componentGraph g comp) = .ok regions) :
    let selected := if regions.isSome then spec else none
    newComponentRegions selected P inp (componentCandidateR selected g comp index) =
      .ok regions := by
  cases regions with
  | none => rfl
  | some regions =>
    change newComponentRegions spec P inp (componentCandidateR spec g comp index) =
      .ok (some regions)
    have heq : newComponentRegions spec P inp (componentCandidateR spec g comp index) =
        newComponentRegions spec P inp (componentGraph g comp) := by
      cases spec <;> rfl
    exact heq.trans h

private theorem coordinateGraphR_nodes_length_le (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) (p : Proper) :
    p.nodes.length ≤ (coordinateGraphR P exact spec p).nodes.length := by
  cases spec with
  | none =>
    obtain ⟨extra, hp⟩ := (coordinateGraphX_anchor_prefix P exact p).1
    have hlen := congrArg List.length hp
    simp only [List.length_append, List.length_map] at hlen
    change p.nodes.length ≤ (coordinateGraphX P exact p).nodes.length
    omega
  | some spec =>
    let titled := titleReservationsR spec.titles P.clusterPad (sizeProperPortsX P exact p)
    obtain ⟨_, hb, _⟩ := addClusterBorders_extra titled P.clusterBorderW
    change p.nodes.length ≤ (materializeDummyPaths
      (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW))).nodes.length
    unfold materializeDummyPaths clearProxyExtents
    simp only [List.length_map, List.length_zipIdx]
    rw [hb]
    dsimp only [titled, titleReservationsR]
    simp only [List.length_append, List.length_map, sizeProperPortsX_length]
    omega

/-- Coverage half of `R_PartSizingRResidual`, from the executed normalization,
label sizing, coordinate placement, and proxy materialization. -/
theorem componentRunR_original_nodes_covered {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∀ i, i < cg'.nodes.length → i < run.proper.nodes.length := by
  obtain ⟨_, _, _, p0, labeled, pCoord, _, _, _, _, placedProper, q0, _, _, stages⟩ :=
    componentRunR_stages h
  have hn := normalize_nodes_length_le stages.hNorm
  have hl := congrArg List.length (addLabelNodes_anchor_keys stages.hLabels).2
  simp only [List.length_map] at hl
  have hc : labeled.nodes.length ≤ pCoord.nodes.length := by
    rw [← stages.hCoord]
    exact coordinateGraphR_nodes_length_le P exact spec labeled
  have hp : pCoord.nodes.length ≤ placedProper.nodes.length := by
    rcases stages.hPlaced with ⟨_, _, _, _, heq⟩ | ⟨_, _, _, _, hplace⟩
    · simpa only [heq] using (Nat.le_refl pCoord.nodes.length)
    · apply Nat.le_of_not_gt
      intro hi
      have hmeta : Metadata.NodeMetadata pCoord placedProper :=
        rfc4CrossCoordsR_metadata_holds hplace
      obtain ⟨_, hnode, _⟩ := hmeta placedProper.nodes.length
        pCoord.nodes[placedProper.nodes.length] (List.getElem?_eq_getElem hi)
      exact (Nat.lt_irrefl _) (List.getElem?_eq_some_iff.mp hnode).1
  have hproxy := (proxyWidths_rel stages.hProxy).2.2.1
  intro i hi
  rw [← stages.hDrop, OrderImpl.dropSynthetic_nodes]
  omega

/-- Loop and reversed-lane envelopes reserve the measured stack directly.
Only the forward non-loop branch needs a transported label anchor. -/
theorem SceneExecutionR.nonForwardEnvelopeFits {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    {comp : List Nat} {candidate : Nat} {spec : Option RegionSpec}
    {cg : Graph} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRunR execution.params (exactDecls exactIds inp) spec inp
      (componentCandidateR spec execution.graph comp candidate) execution.measured
      orderOptions = .ok (cg, run))
    {k : Nat} {edge : Edge} {env : Rect} (hk : cg.edges[k]? = some edge)
    (henv : labelEnvelope execution.params cg run execution.measured k edge = some env)
    (hkind : edge.tail = edge.head ∨ edge.reversed = true) :
    0 ≤ env.w ∧ 0 ≤ env.h ∧
      ∃ entry, entry ∈ labelBounds execution.params cg run execution.measured ∧
        entry.x ≤ env.x ∧ entry.y ≤ env.y ∧
        env.x + Labels.stackWidth
          ((routeLabels execution.measured edge.decl).map fun l => (l.width, l.height)) ≤
          entry.x + entry.w ∧
        env.y + Labels.stackHeight cg.slot
          ((routeLabels execution.measured edge.decl).map fun l => (l.width, l.height)) ≤
          entry.y + entry.h := by
  have hslot := (R_partSizingR_chosenFacts execution hrun).2.2
  have hlab := execution.measured_nonnegR
  by_cases hloop : edge.tail = edge.head
  · exact labelEnvelope_loop_fits hk hloop henv hslot hlab
  have hrev := hkind.resolve_left hloop
  obtain ⟨hw, hh⟩ := labelEnvelope_reversed_size hloop hrev henv
  rw [stackSize_width_eq] at hw
  rw [stackSize_height_eq] at hh
  exact labelEnvelope_nonloop_fits hk hloop henv hlab hslot
    (by omega) (by omega)

/-- Without region sets the successful base execution is the exact pipeline.
The fixed-size and structural premises are the ordinary flat exact admission
conditions, not assumptions about the result. -/
theorem layoutRIds_nil_valid {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) (hfit : InputFixedFit inp o)
    (hpos : FixedSizesPositive inp) (h : layoutRIds exactIds [] inp o = .ok res) :
    HardConstraints res.scene.layoutDump := by
  have hx : layoutX exactIds inp o = .ok res := (layoutRIds_nil exactIds inp o).symm.trans h
  have seams := Elegant.Kinds.Usecase.exactBaseSeams exactIds
  have hc5 : Validator.C5 res.scene.layoutDump := by
    intro route hroute
    obtain ⟨_, _, _, _, _, _, hports⟩ := (seams.flatC5 hwf hframed hx).2.2 route hroute
    exact hports
  exact ⟨layoutRIds_c1 h,
    seams.flatC2 inp o res hwf hx,
    seams.flatC3 inp o res hwf hframed hx,
    layoutRIds_c4 h,
    hc5,
    seams.flatC6 inp o res hwf hframed hpos (seams.frameClear inp o res hwf hframed) hx,
    seams.flatC7 inp o res hwf hframed hfit (seams.partsSep inp o res)
      (seams.labelRuns inp o res hwf hframed) (seams.captions inp o res hwf hframed hfit) hx,
    seams.flatC8a inp o res hwf hframed hx,
    seams.flatC8b inp o res hwf hframed hfit hx⟩

end Elegant.Layered.PipelineImpl
