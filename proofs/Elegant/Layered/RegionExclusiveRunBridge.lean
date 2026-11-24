import Elegant.Layered.RegionExclusivePath
import Elegant.Layered.RegionRunNodeIdentity
import Elegant.Layered.RegionGroupEndpointProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

def R7_ExclusiveBoxInLabelRun (exactIds : List String)
    (idSets : List (String × List String)) (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecutionR exactIds idSets inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : MeasuredLabel)
    (comp : List Nat) (candidate : Nat) (run : Run)
    (orderOptions : OrderOptions) (cg cg' : Graph) (edge decl : Nat) (e : Edge)
    (packed : Pack.State) (c : Nat) (labelPart : List Nat × Part)
    (shelfc : Rect) (loops : List (Nat × LoopPlacement)) (area : Int) (rl : Nat × Rect),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    comp ∈ components execution.graph →
    ∀ (rs : Option ComponentRegions),
    newComponentRegions (r7Spec idSets o execution.params execution.lines)
      execution.params inp (componentGraph execution.graph comp) = .ok rs →
    cg = componentCandidateR (r7Eff idSets o execution.params execution.lines rs)
      execution.graph comp candidate →
    componentRunR execution.params (exactDecls exactIds inp)
      (r7Eff idSets o execution.params execution.lines rs)
      inp cg execution.measured orderOptions = .ok (cg', run) →
    cg'.edges[edge]? = some e →
    (cg'.edges[edge]?).map (·.decl) = some decl →
    measured ∈ routeLabels execution.measured decl →
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) →
    labelPart.1 = comp →
    labelPart.2 = { placeComponentExact execution.params cg' run 0
      execution.measured loops with area := area } →
    rl ∈ labelPart.2.labels →
    l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect shelfc.x shelfc.y rl.2)) →
    ∀ (b : Box),
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ v : Nat,
      v < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      (∃ node : Node, cg'.nodes[v]? = some node ∧ node.border = 0) ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg'.nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((cg'.nodes[e.head]?).map (·.clusterPath)).getD [] ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect
            (shelfc.x + (0 - (placeBoundsX execution.params cg' run
              execution.measured loops).minX))
            (shelfc.y + (-(placeBoundsX execution.params cg' run
              execution.measured loops).minY))
            (RouteImpl.boxRect run.proper run.xs run.ys v)))) ∨
    (∃ (packed' : Pack.State) (c d : Nat)
      (labelPart' boxPart : List Nat × Part)
      (shelfc' shelfd : Rect) (rl' : Nat × Rect) (r : Rect),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed' ∧
      execution.componentsAcc.parts[c]? = some labelPart' ∧
      packed'.boxes[c]? = some shelfc' ∧
      execution.componentsAcc.parts[d]? = some boxPart ∧
      packed'.boxes[d]? = some shelfd ∧
      c ≠ d ∧
      rl' ∈ labelPart'.2.labels ∧
      r ∈ boxPart.2.rects ∧
      l.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfc'.x shelfc'.y rl'.2)) ∧
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect shelfd.x shelfd.y r)))

theorem r7_exclusiveBoxInLabelRun {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) : R7_ExclusiveBoxInLabelRun exactIds idSets inp o res := by
  intro execution l index source measured comp candidate run orderOptions cg cg' edge decl e
    packed c labelPart shelfc loops area rl
    _hlmem _hin _hid _hmeasured hcomp rs hnew hcg hrun _he _hdeclmap _hmlabel
    hpacked hselected hpart1 hpartdef hrlmem hlrect b hdump hex _hscope
  have hbox : b ∈ res.scene.boxes := hdump
  rw [execution.boxes_eq_mapR] at hbox
  obtain ⟨⟨boxSource, key⟩, hsourceMem, rfl⟩ := List.mem_map.mp hbox
  have hsource : inp.boxes[key]? = some boxSource := List.mem_zipIdx_iff_getElem?.mp hsourceMem
  have hkey : key < inp.boxes.length := (List.getElem?_eq_some_iff.mp hsource).1
  have hkeysize : key < execution.componentsAcc.rects.size := by
    rw [execution.components_rects_sizeR]
    exact hkey
  by_cases hmem : key ∈ labelPart.1
  · obtain ⟨v, hv⟩ := List.mem_iff_getElem?.mp hmem
    have hcompv : comp[v]? = some key := by
      rw [← hpart1]
      exact hv
    have hexcl : boxSource.exclusive = true := hex
    have hrole : boxSource.role ≠ .group :=
      wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsource) hexcl
    have hlines : execution.lines.length = inp.boxes.length := by
      have h := execution.lines_eq
      unfold boxLines at h
      simpa only [List.length_zipIdx] using (mapM_getElem? _ _ _ h).1
    have hlineKey : key < execution.lines.length := by
      rw [hlines]
      exact hkey
    obtain ⟨node0, hnode0, hborder0⟩ := measuredGraph_exclusive_node_border_zero
      execution.checked execution.graph0_eq (List.getElem?_eq_getElem hlineKey) hsource hrole
    obtain ⟨node, hnode, hborder, _, _⟩ := exactGraph_node_key execution.graph_eq hnode0
    have hcand : cg.nodes[v]? = some node := by
      rw [hcg]
      exact component_node_lookupR hcompv hnode
    have hnodes : cg'.nodes = cg.nodes := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, stages⟩ := componentRunR_stages hrun
      rcases stages.hRank with ⟨_, _, _, _, heq, _⟩ | ⟨_, _, hrank⟩
      · rw [heq]
      · exact rankEquivalentR_nodes_eq hrank
    have hranked : cg'.nodes[v]? = some node := by
      rw [hnodes]
      exact hcand
    obtain ⟨_, hproperNode, _⟩ := regionRun_keepsCandidateDecl hrun hcand
    have hproper : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hproperNode).1
    have hreal := rgeIsRealR hrun hcand
    have hdecl := r7_exclusiveRunNodeDecl_holds exactIds idSets inp o res execution
      comp candidate run orderOptions cg cg' hcomp rs hnew hcg hrun v key boxSource hcompv hsource
    have hcandidateNodes (spec : Option RegionSpec) :
        (componentCandidateR spec execution.graph comp candidate).nodes =
          (componentGraph execution.graph comp).nodes := by
      cases spec with
      | none => exact componentCandidate_nodes execution.graph comp candidate
      | some _ => rfl
    have houtside (u : Nat) : RouteImpl.nodeDecl run.proper v ∉
        ((cg'.nodes[u]?).map (·.clusterPath)).getD [] := by
      rw [hdecl]
      cases hu : cg'.nodes[u]? with
      | none => simp
      | some nd =>
        have hs : (componentCandidateR (r7Spec idSets o execution.params execution.lines)
            execution.graph comp candidate).nodes[u]? = some nd := by
          simpa only [hnodes, hcg, hcandidateNodes] using hu
        simp only [Option.map_some, Option.getD_some]
        exact r7_exclusiveKeyOutsideCgPaths_holds exactIds idSets inp o res hwf hfp
          comp candidate v key boxSource execution hcomp hcompv hsource hexcl u nd hs
    have hzero : node.border = 0 := hborder.trans hborder0
    have hplain : (cg'.nodes.getD v default).border ≠ -2 := by
      rw [List.getD_eq_getElem?_getD, hranked, Option.getD_some, hzero]
      decide
    have hframe := plain_frame_eq_boxRect execution.params cg' run v hproper hplain
    have hrect : labelPart.2.rects[v]? =
        some (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured loops).minX)
          (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
          (frameRect execution.params cg' run v)) := by
      rw [hpartdef]
      have hvlen : v < cg'.nodes.length := (List.getElem?_eq_some_iff.mp hranked).1
      unfold placeComponentExact placeBoundsX
      simp only [List.getElem?_map, List.getElem?_range hvlen, Option.map_some]
    have hval := actual_components_packed_rect_valueR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected
      (List.getElem?_zip_eq_some.mpr ⟨hv, hrect⟩) hkeysize default
    refine Or.inl ⟨v, hproper, hreal, ⟨node, hranked, hzero⟩, houtside e.tail, houtside e.head, ?_⟩
    change shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD key default)) = _
    rw [hval, hframe]
    change shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect shelfc.x shelfc.y
          (shiftRect (0 - (placeBoundsX execution.params cg' run execution.measured loops).minX)
            (-(placeBoundsX execution.params cg' run execution.measured loops).minY)
            (RouteImpl.boxRect run.proper run.xs run.ys v)))) = _
    rw [shiftRect_shiftRect]
  · obtain ⟨boxPart, hboxPart, ⟨entryKey, rect⟩, hentryMem, hentryKey⟩ :=
      sceneExecutionR_parts_entryR execution hkey
    change entryKey = key at hentryKey
    subst entryKey
    obtain ⟨d, hboxIndex⟩ := List.mem_iff_getElem?.mp hboxPart
    have hpackedCount : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpacked, List.length_map]
    have hd : d < packed.boxes.length := by
      rw [hpackedCount]
      exact (List.getElem?_eq_some_iff.mp hboxIndex).1
    have hshelf : packed.boxes[d]? = some (packed.boxes[d]'hd) :=
      List.getElem?_eq_getElem hd
    have hboxSelected : (execution.componentsAcc.parts.zip packed.boxes)[d]? =
        some (boxPart, packed.boxes[d]'hd) :=
      List.getElem?_zip_eq_some.mpr ⟨hboxIndex, hshelf⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hentryMem
    have hval := actual_components_packed_rect_valueR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hboxSelected hi hkeysize default
    obtain ⟨hlabelIndex, hlabelShelf⟩ := List.getElem?_zip_eq_some.mp hselected
    obtain ⟨hboxKeyMem, hrectMem⟩ := List.of_mem_zip hentryMem
    have hcd : c ≠ d := by
      intro heq
      rw [heq] at hlabelIndex
      have hs : labelPart = boxPart := Option.some.inj (hlabelIndex.symm.trans hboxIndex)
      exact hmem (by simpa only [hs] using hboxKeyMem)
    refine Or.inr ⟨packed, c, d, labelPart, boxPart, shelfc, packed.boxes[d]'hd, rl, rect,
      hpacked, hlabelIndex, hlabelShelf, hboxIndex, hshelf, hcd, hrlmem, hrectMem, hlrect, ?_⟩
    change shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (execution.packedAcc.rects.getD key default)) = _
    rw [hval]

end Elegant.Layered.PipelineImpl
