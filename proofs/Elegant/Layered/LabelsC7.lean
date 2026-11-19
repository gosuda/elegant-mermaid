import Elegant.Layered.SceneBounds
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.LabelsClearance
import Elegant.Layered.RouteScopeClearance
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered

/-! Flat-layered clause 7: every scene label of a successful flat
`PipelineImpl.layout` keeps clear of every exclusive box outside its owner
scope.  `PipelineImpl.label_source_split` splits the emitted labels into
measured route labels and owner captions, so the clause is proved from two
seams of the executed pipeline:

* `LabelRunsClearExclusiveBoxes` — the route-label seam, stated per
  component run like `FrameClearRuns` (FlatC6.lean): the placed rect of a
  measured label on an edge misses the `RouteImpl.boxRect` of every real
  node outside the edge's run scope, and the dump-level bridges carry the
  executed transport of both rectangles.  The bridge is a disjunction: for
  boxes of the label's own component run it returns the run witness; for
  boxes of another executed part it returns the distinct-part evidence
  (both rects transported from distinct packed shelf rectangles), which
  the packing separation premise `PartsSeparated` settles.  To be discharged at the family
  seam from `RouteScopeClearance.componentRun_exclusive_clear` (route-point
  avoidance under `PipelineImpl.FrameClearance`) and the envelope placement
  (`PipelineImpl.labelEnvelope`, `Labels.stackRects_contained`);
* `SceneCaptionBoxContainment` — the caption seam: a caption label (the
  unmeasured branch of `label_source_split`) does not meet an exclusive
  dump box outside its owner scope.  To be discharged from
  `SceneExecution.scene_caption_box_containment` (installed titles),
  `ownedTextRect_containsCellRect` (fallbacks) and the component packing
  disjointness (`Pack.pack_components_disjoint`). -/

/-- The rect `PipelineImpl.placedLabels` pairs with `l.index` for the edge
of declaration `decl` in the executed run; `0` fallback for an unplaced
label (which a successful run never emits). -/
def routeLabelRect (P : PipelineImpl.Params) (cg : Graph) (run : PipelineImpl.Run)
    (measured : List PipelineImpl.MeasuredLabel)
    (l : PipelineImpl.MeasuredLabel) : Rect :=
  ((PipelineImpl.placedLabels P cg run measured).filter (fun q => q.1 == l.index)).headD
    (l.index, ⟨0, 0, 0, 0⟩) |>.2

/-- Route-label seam, run-local half (the `FrameClearRuns` shape): for every
executed component run, the placed rect of a measured label on an edge
misses the frame rect of every real node outside that edge's run scope. -/
def RunLocalLabelClearance (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res)
    (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
    (orderOptions : OrderOptions) (cg : Graph) (edge decl v i₀ i₁ : Nat)
    (l : PipelineImpl.MeasuredLabel),
    comp ∈ PipelineImpl.components execution.graph →
    cg = PipelineImpl.componentCandidate execution.graph comp candidate →
    PipelineImpl.componentRun execution.params cg execution.measured orderOptions = .ok run →
    (cg.edges[edge]?).map (·.decl) = some decl →
    l ∈ PipelineImpl.routeLabels execution.measured decl →
    v < run.proper.nodes.length →
    RouteImpl.IsReal run.proper v →
    v ≠ (RouteImpl.edgeAt run.proper i₀).tail →
    v ≠ (RouteImpl.edgeAt run.proper i₁).head →
    RouteImpl.nodeDecl run.proper v ∉
      ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
        (·.node.clusterPath)).getD [] →
    RouteImpl.nodeDecl run.proper v ∉
      ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
        (·.node.clusterPath)).getD [] →
    ¬ (routeLabelRect execution.params cg run execution.measured l).meetsInterior
        (RouteImpl.boxRect run.proper run.xs run.ys v)

/-- Separation of the packed component parts: for the executed packing, every
transported label rect and frame rect of a selected part stays inside that
part's transported shelf rectangle.  The route-label bridge's other-part
case consumes this premise; it is discharged per part from the executed
`placeComponent`/`packAcc` bounds (the `PipelineImpl.PartSeparated`
program). -/
def PartsSeparated (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (packed : Pack.State)
    (c : Nat) (part : List Nat × PipelineImpl.Part) (shelf : Rect),
    Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
    execution.componentsAcc.parts[c]? = some part →
    packed.boxes[c]? = some shelf →
    (∀ l ∈ part.2.labels,
        Rect.Contained
          (PipelineImpl.shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
              (PipelineImpl.shiftRect shelf.x shelf.y ⟨0, 0, shelf.w, shelf.h⟩)))
          (PipelineImpl.shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
              (PipelineImpl.shiftRect shelf.x shelf.y l.2)))) ∧
    (∀ r ∈ part.2.rects,
        Rect.Contained
          (PipelineImpl.shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
              (PipelineImpl.shiftRect shelf.x shelf.y ⟨0, 0, shelf.w, shelf.h⟩)))
          (PipelineImpl.shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
              (PipelineImpl.shiftRect shelf.x shelf.y r))))

/-- Route-label seam, bridge half: a measured scene label and an exclusive
dump box outside its owner scope are either the executed transports (pack
shift, orientation, canvas margin) of the placed label rect and the
`boxRect` of a real node of the SAME component run satisfying the run-local
scope conditions, or — when the box belongs to another executed part — the
transports of contents of two distinct packed shelf rectangles, which the
packing separation (`PartsSeparated`) keeps apart. -/
def RouteLabelDumpBridges (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : PipelineImpl.MeasuredLabel) (b : Box),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
    (∃ (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
      (orderOptions : OrderOptions) (cg : Graph) (edge decl v i₀ i₁ : Nat)
      (px py m h : Int) (d : Direction),
      comp ∈ PipelineImpl.components execution.graph ∧
      cg = PipelineImpl.componentCandidate execution.graph comp candidate ∧
      PipelineImpl.componentRun execution.params cg execution.measured orderOptions = .ok run ∧
      (cg.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ PipelineImpl.routeLabels execution.measured decl ∧
      v < run.proper.nodes.length ∧
      RouteImpl.IsReal run.proper v ∧
      v ≠ (RouteImpl.edgeAt run.proper i₀).tail ∧
      v ≠ (RouteImpl.edgeAt run.proper i₁).head ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₀).tail]?).map
          (·.node.clusterPath)).getD [] ∧
      RouteImpl.nodeDecl run.proper v ∉
        ((run.proper.nodes[(RouteImpl.edgeAt run.proper i₁).head]?).map
          (·.node.clusterPath)).getD [] ∧
      l.rect = PipelineImpl.shiftRect m m
        (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
          (routeLabelRect execution.params cg run execution.measured measured))) ∧
      b.rect = PipelineImpl.shiftRect m m
        (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
          (RouteImpl.boxRect run.proper run.xs run.ys v)))) ∨
    (∃ (packed : Pack.State) (c d : Nat)
      (labelPart boxPart : List Nat × PipelineImpl.Part)
      (shelfc shelfd : Rect) (rl : Nat × Rect) (r : Rect),
      Pack.pack (if o.profile == .cell then o.maxWidth else 0)
        execution.params.nodeGap 0
        (LayoutConst.component_aspect_num.get o.profile)
        (LayoutConst.component_aspect_den.get o.profile)
        (execution.componentsAcc.parts.map fun part =>
          ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
      execution.componentsAcc.parts[c]? = some labelPart ∧
      packed.boxes[c]? = some shelfc ∧
      execution.componentsAcc.parts[d]? = some boxPart ∧
      packed.boxes[d]? = some shelfd ∧
      c ≠ d ∧
      rl ∈ labelPart.2.labels ∧
      r ∈ boxPart.2.rects ∧
      l.rect = PipelineImpl.shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
          (PipelineImpl.shiftRect shelfc.x shelfc.y rl.2)) ∧
      b.rect = PipelineImpl.shiftRect execution.params.canvasMargin
        execution.params.canvasMargin
        (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
          (PipelineImpl.shiftRect shelfd.x shelfd.y r)))

/-- Seam 1: the route-label family of clause 7, per executed component run. -/
abbrev LabelRunsClearExclusiveBoxes (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  RunLocalLabelClearance inp o res ∧ RouteLabelDumpBridges inp o res

/-- Seam 2: the caption family of clause 7 — an owner caption (the
unmeasured branch of `PipelineImpl.label_source_split`) does not meet an
exclusive dump box outside its owner scope. -/
abbrev SceneCaptionBoxContainment (inp : Input) (o : Options)
    (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = none →
    (∃ ownerIndex : Nat, inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex) →
    ∀ b : Box, b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
      ¬ l.rect.meetsInterior b.rect

/-- Clause 7 for a successful flat `PipelineImpl.layout`: a label does not
overlap an exclusive box outside its owner scope.  The proof classifies the
label through `PipelineImpl.label_source_split` and applies the matching
seam; the bridge's same-run branch goes through the run-local clearance and
the rect transport, and the other-part branch from the packing separation
`hsep` plus the disjoint transported shelf rectangles. -/
theorem layout_c7 {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (hsep : PartsSeparated inp o res)
    (hseam1 : LabelRunsClearExclusiveBoxes inp o res)
    (hseam2 : SceneCaptionBoxContainment inp o res)
    (h : PipelineImpl.layout inp o = .ok res) :
    Validator.C7 res.scene.layoutDump := by
  obtain ⟨execution⟩ := PipelineImpl.layout_sceneExecution h
  intro l hl b hb hex hscope
  rw [Scene.layoutDump] at hl
  obtain ⟨sl, hsl, hleq⟩ := List.mem_map.mp hl
  subst hleq
  obtain ⟨source, index, hsource, _, hid, _, hbranch⟩ :=
    PipelineImpl.label_source_split execution hsl
  cases hbranch with
  | inl hmeas =>
    obtain ⟨measured, hmeasured⟩ := hmeas
    obtain ⟨comp, candidate, run, orderOptions, cg, edge, decl, v, i₀, i₁,
        px, py, m, hgt, hdir, hcomp, hcg, hrun, hedge, hmlabel, hv, hreal, hv0, hv1,
        hs0, hs1, hlreq, hbreq⟩ |
      ⟨packed, c, d, labelPart, boxPart, shelfc, shelfd, rl, r, hpacked,
        hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem, hrmem, hlrect, hbrect⟩ :=
      hseam1.2 execution sl index source measured b hsl hsource hid hmeasured
        hb hex hscope
    · have hclr := hseam1.1 execution comp candidate run orderOptions cg edge decl v
        i₀ i₁ measured hcomp hcg hrun hedge hmlabel hv hreal hv0 hv1 hs0 hs1
      have hrect : sl.toLabel.rect = sl.rect := rfl
      rw [hrect, hlreq, hbreq]
      exact PipelineImpl.not_meetsInterior_transport hclr
    · obtain ⟨hlwithin, _⟩ := hsep execution packed c labelPart shelfc hpacked
        hcpart hcshelf
      obtain ⟨_, hrwithin⟩ := hsep execution packed d boxPart shelfd hpacked
        hdpart hdshelf
      have hlw := hlwithin rl hrlmem
      have hrw := hrwithin r hrmem
      rw [← hlrect] at hlw
      rw [← hbrect] at hrw
      obtain ⟨hc1, hsc⟩ := List.getElem?_eq_some_iff.mp hcshelf
      obtain ⟨hd1, hsd⟩ := List.getElem?_eq_some_iff.mp hdshelf
      have hboxes := Pack.pack_boxes_disjoint hpacked c d hc1 hd1 hcd
      rw [hsc, hsd] at hboxes
      have hT : ¬ (PipelineImpl.shiftRect execution.params.canvasMargin
          execution.params.canvasMargin
          (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH shelfc)).meetsInterior
          (PipelineImpl.shiftRect execution.params.canvasMargin
            execution.params.canvasMargin
            (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH shelfd)) :=
        PipelineImpl.not_meetsInterior_shiftRect
          (PipelineImpl.not_meetsInterior_orientRect hboxes)
      have hso : PipelineImpl.shiftRect shelfc.x shelfc.y
          (Rect.mk 0 0 shelfc.w shelfc.h) = shelfc := by
        cases shelfc; simp [PipelineImpl.shiftRect]
      have hsdo : PipelineImpl.shiftRect shelfd.x shelfd.y
          (Rect.mk 0 0 shelfd.w shelfd.h) = shelfd := by
        cases shelfd; simp [PipelineImpl.shiftRect]
      rw [hso] at hlw
      rw [hsdo] at hrw
      have hrect : sl.toLabel.rect = sl.rect := rfl
      rw [hrect]
      exact PipelineImpl.not_meetsInterior_of_contained hT hlw hrw
  | inr hcap =>
    obtain ⟨hnone, howner⟩ := hcap
    obtain ⟨ownerIndex, hownerIdx⟩ := howner
    exact hseam2 execution sl index source hsl hsource hid hnone
      ⟨ownerIndex, hownerIdx⟩ b hb hex hscope

end Elegant.Layered
