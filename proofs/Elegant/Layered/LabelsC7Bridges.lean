import Elegant.Layered.LabelsC7

set_option autoImplicit false

namespace Elegant.Layered

/-! Bridge half of the flat route-label seam (`RouteLabelDumpBridges`,
defined in `Elegant.Layered.LabelsC7`).  The bridge decomposes into two
strictly weaker executed facts, each stated as a named `def` so that they can
be discharged independently from the executed pipeline:

* `LabelBelongsToRun` — a measured scene label is the common transport
  (`shiftRect` margin, `orientRect`, component pack shift) of the placed rect
  `routeLabelRect` of its own edge in some executed component run;
* `ExclusiveBoxInLabelRun` — anchored to any witness `LabelBelongsToRun` may
  return, and conditional on the same-run case: an exclusive dump box outside
  the label's owner scope either is the transport of the `boxRect` of a real
  node of that run whose declaration lies in neither endpoint cluster path
  of the label's own component-graph edge (endpoints included), or belongs
  to another executed part: the label and the box are the transported
  contents of two distinct packed shelf rectangles, which the packing
  separation (`LabelsC7.PartsSeparated`) keeps apart.  The scope is stated
  through the label's own edge (`edge`/`decl`/`e`), never through free
  proper-edge indices: the free-index form excluded exactly the endpoint
  boxes the validator requires the label to miss (see
  `proofs/wip/Layered/ExclusiveBoxInLabelRunRefuted.lean`).

`routeLabelDumpBridges` is their combination: the box branch is attached to
the label witness, giving the disjunction the seam needs. -/

 /-- Executed label half: the scene rect of a measured label is the common
 transport of the placed rect of its edge in some executed component run.
 Strictly weaker than `RouteLabelDumpBridges`: it fixes a witness for the
 label only and asserts nothing about exclusive dump boxes.
 The transport is pinned to the executed one: `m` is the canvas margin, `h`
 the packed canvas height, `d` the output direction, and `(px, py)` the
 shelf-plus-placement shift of the label's own executed part (whose packing
 witnesses `packed`, `c`, `shelfc` and whose placement witnesses `loops`,
 `area` are provided, together with the placed pair `rl` they transport).
 Labels with no placed rect do not occur in successful runs
 (`labelEnvelope_some_of_routeLabels` in `LabelRunBridgeFacts` makes the
 no-carry branch of `labelBelongsToRun` vacuous), so no default disjunct is
 needed. -/
 def LabelBelongsToRun (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
   ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
     (source : ModelLabel) (measured : PipelineImpl.MeasuredLabel),
     l ∈ res.scene.labels →
     inp.labels[index]? = some source →
     l.id = source.id →
     execution.measured.find? (fun label => label.index == index) = some measured →
     ∃ (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
       (orderOptions : OrderOptions) (cg : Graph) (edge decl : Nat)
       (px py m h : Int) (d : Direction)
       (packed : Pack.State) (c : Nat) (labelPart : List Nat × PipelineImpl.Part)
       (shelfc : Rect) (loops : List (Nat × LoopPlacement)) (area : Int)
       (rl : Nat × Rect),
       comp ∈ PipelineImpl.components execution.graph ∧
       cg = PipelineImpl.componentCandidate execution.graph comp candidate ∧
       PipelineImpl.componentRun execution.params cg execution.measured orderOptions = .ok run ∧
       orderOptions = candidateOrder candidate ∧
       (cg.edges[edge]?).map (·.decl) = some decl ∧
       measured ∈ PipelineImpl.routeLabels execution.measured decl ∧
       l.rect = PipelineImpl.shiftRect m m
         (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
           (routeLabelRect execution.params cg run execution.measured measured))) ∧
       m = execution.params.canvasMargin ∧
       h = execution.packedAcc.canvasH ∧
       d = o.direction ∧
       Pack.pack (if o.profile == .cell then o.maxWidth else 0)
         execution.params.nodeGap 0
         (LayoutConst.component_aspect_num.get o.profile)
         (LayoutConst.component_aspect_den.get o.profile)
         (execution.componentsAcc.parts.map fun part =>
           ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed ∧
       (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) ∧
       labelPart.1 = comp ∧
       labelPart.2 = { PipelineImpl.placeComponent execution.params cg run 0
         execution.measured loops with area := area } ∧
       px = shelfc.x + (0 - (PipelineImpl.placeBounds execution.params cg run
         execution.measured loops).minX) ∧
       py = shelfc.y + (0 - (PipelineImpl.placeBounds execution.params cg run
         execution.measured loops).minY) ∧
       rl ∈ labelPart.2.labels ∧
       l.rect = PipelineImpl.shiftRect execution.params.canvasMargin
         execution.params.canvasMargin
         (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
           (PipelineImpl.shiftRect shelfc.x shelfc.y rl.2))

 /-- Executed box half, anchored to the pinned label witness: for the executed
 transport of the label's placed rect (margin, direction, canvas height, and
 the label part's shelf-plus-placement shift, all fixed by the witness), an
 exclusive dump box outside the label's owner scope either is the same
 transport of the `boxRect` of a real node of that run whose declaration lies
 in neither endpoint cluster path of the label's own component-graph edge
 (endpoints included), or lies in another executed part: the label and the
 box are the transported contents of two distinct packed shelf rectangles,
 which the packing separation (`LabelsC7.PartsSeparated`) keeps apart.
 There are no free transports: the shift is written out from the part shelf
 and placement bounds.  The owner-scope hypothesis is subsumed by the
 id-level residuals (an exclusive box is never a group, and cluster paths
 list only groups), which the proof takes as hypotheses. -/
 def ExclusiveBoxInLabelRun (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
   ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
     (source : ModelLabel) (measured : PipelineImpl.MeasuredLabel)
     (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
     (cg : Graph) (edge decl : Nat)
     (e : Edge)
     (packed : Pack.State) (c : Nat) (labelPart : List Nat × PipelineImpl.Part)
     (shelfc : Rect) (loops : List (Nat × LoopPlacement)) (area : Int)
     (rl : Nat × Rect),
     l ∈ res.scene.labels →
     inp.labels[index]? = some source →
     l.id = source.id →
     execution.measured.find? (fun label => label.index == index) = some measured →
     comp ∈ PipelineImpl.components execution.graph →
     cg = PipelineImpl.componentCandidate execution.graph comp candidate →
     PipelineImpl.componentRun execution.params cg execution.measured
       (candidateOrder candidate) = .ok run →
     (cg.edges[edge]?) = some e →
     (cg.edges[edge]?).map (·.decl) = some decl →
     measured ∈ PipelineImpl.routeLabels execution.measured decl →
     Pack.pack (if o.profile == .cell then o.maxWidth else 0)
       execution.params.nodeGap 0
       (LayoutConst.component_aspect_num.get o.profile)
       (LayoutConst.component_aspect_den.get o.profile)
       (execution.componentsAcc.parts.map fun part =>
         ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed →
     (execution.componentsAcc.parts.zip packed.boxes)[c]? = some (labelPart, shelfc) →
     labelPart.1 = comp →
     labelPart.2 = { PipelineImpl.placeComponent execution.params cg run 0
       execution.measured loops with area := area } →
     rl ∈ labelPart.2.labels →
     l.rect = PipelineImpl.shiftRect execution.params.canvasMargin
       execution.params.canvasMargin
       (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
         (PipelineImpl.shiftRect shelfc.x shelfc.y rl.2)) →
     ∀ (b : Box),
     b ∈ res.scene.layoutDump.boxes →
     b.exclusive = true →
     b.id ∉ res.scene.layoutDump.labelOwnerAnc l.toLabel →
     (∃ v : Nat,
       v < run.proper.nodes.length ∧
       RouteImpl.IsReal run.proper v ∧
       RouteImpl.nodeDecl run.proper v ∉
         ((cg.nodes[e.tail]?).map (·.clusterPath)).getD [] ∧
       RouteImpl.nodeDecl run.proper v ∉
         ((cg.nodes[e.head]?).map (·.clusterPath)).getD [] ∧
       b.rect = PipelineImpl.shiftRect execution.params.canvasMargin
         execution.params.canvasMargin
         (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
           (PipelineImpl.shiftRect
             (shelfc.x + (0 - (PipelineImpl.placeBounds execution.params cg run
               execution.measured loops).minX))
             (shelfc.y + (0 - (PipelineImpl.placeBounds execution.params cg run
               execution.measured loops).minY))
             (RouteImpl.boxRect run.proper run.xs run.ys v)))) ∨
     (∃ (packed : Pack.State) (c d' : Nat)
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
       execution.componentsAcc.parts[d']? = some boxPart ∧
       packed.boxes[d']? = some shelfd ∧
       c ≠ d' ∧
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
/-- The bridge seam of `LabelsC7.RouteLabelDumpBridges`: attach the box
branch of `ExclusiveBoxInLabelRun` to the label witness of
`LabelBelongsToRun`. -/
theorem routeLabelDumpBridges {inp : Input} {o : Options} {res : FamilyResult}
    (_hwf : WellFormed (inputModel inp o))
    (hlabel : LabelBelongsToRun inp o res)
    (hbox : ExclusiveBoxInLabelRun inp o res) :
    RouteLabelDumpBridges inp o res := by
   intro execution l index source measured b hlmem hin hleq hmeasured hdump hex hscope
   obtain ⟨comp, candidate, run, orderOptions, cg, edge, decl, px, py, m, hgt, dir,
     packed, c, labelPart, shelfc, loops, area, rl,
     hcomp, hcg, hrun, hord, hedge, hmlabel, hrect,
     hm, hh, hd, hpacked, hselected, hpart1, hpartdef, hpx, hpy, hrlmem, hlrect⟩ :=
     hlabel execution l index source measured hlmem hin hleq hmeasured
   obtain ⟨e, he⟩ : ∃ e, (cg.edges[edge]?) = some e := by
     cases h : cg.edges[edge]? with
     | none => simp [h] at hedge
     | some e => exact ⟨e, rfl⟩
   have hrun' : PipelineImpl.componentRun execution.params cg execution.measured
       (candidateOrder candidate) = .ok run := by
     rw [← hord]; exact hrun
   have hrect' : l.rect = PipelineImpl.shiftRect execution.params.canvasMargin
       execution.params.canvasMargin
       (PipelineImpl.orientRect o.direction execution.packedAcc.canvasH
         (PipelineImpl.shiftRect
           (shelfc.x + (0 - (PipelineImpl.placeBounds execution.params cg run
             execution.measured loops).minX))
           (shelfc.y + (0 - (PipelineImpl.placeBounds execution.params cg run
             execution.measured loops).minY))
           (routeLabelRect execution.params cg run execution.measured measured))) := by
     rw [hrect, hm, hh, hd, hpx, hpy]
   obtain ⟨v, hv, hreal, hs0, hs1, hbrect⟩ |
     ⟨packed', c', d', labelPart', boxPart, shelfc', shelfd, rl', r, hpacked', hcpart,
       hcshelf, hdpart, hdshelf, hcd, hrlmem', hrmem, hlrect', hbrect'⟩ :=
     hbox execution l index source measured comp candidate run cg edge decl e
       packed c labelPart shelfc loops area rl
       hlmem hin hleq hmeasured hcomp hcg hrun' he hedge hmlabel hpacked hselected
       hpart1 hpartdef hrlmem hlrect b hdump hex hscope
   · have hbrectFree : b.rect = PipelineImpl.shiftRect m m
       (PipelineImpl.orientRect dir hgt (PipelineImpl.shiftRect px py
         (RouteImpl.boxRect run.proper run.xs run.ys v))) := by
       rw [hm, hh, hd, hpx, hpy]; exact hbrect
     exact Or.inl ⟨comp, candidate, run, orderOptions, cg, edge, decl, v, e, px, py,
       m, hgt, dir, hcomp, hcg, hrun, he, hedge, hmlabel, hv, hreal, hs0, hs1,
       hrect, hbrectFree⟩
   · exact Or.inr ⟨packed', c', d', labelPart', boxPart, shelfc', shelfd, rl', r, hpacked',
       hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem', hrmem, hlrect', hbrect'⟩

end Elegant.Layered
