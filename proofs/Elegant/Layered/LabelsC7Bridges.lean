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
label only and asserts nothing about exclusive dump boxes. -/
def LabelBelongsToRun (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : PipelineImpl.MeasuredLabel),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    ∃ (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
      (orderOptions : OrderOptions) (cg : Graph) (edge decl _i₀ _i₁ : Nat)
      (px py m h : Int) (d : Direction),
      comp ∈ PipelineImpl.components execution.graph ∧
      cg = PipelineImpl.componentCandidate execution.graph comp candidate ∧
      PipelineImpl.componentRun execution.params cg execution.measured orderOptions = .ok run ∧
      (cg.edges[edge]?).map (·.decl) = some decl ∧
      measured ∈ PipelineImpl.routeLabels execution.measured decl ∧
      l.rect = PipelineImpl.shiftRect m m
        (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
          (routeLabelRect execution.params cg run execution.measured measured)))

/-- Executed box half, anchored to any label witness: for every witness that
`LabelBelongsToRun` may return, an exclusive dump box outside the label's
owner scope either is the transport of the `boxRect` of a real node of that
run whose declaration lies in neither endpoint cluster path of the label's
own component-graph edge (endpoints included), or lies in another executed
part: the label and the box are the transported contents of two distinct
packed shelf rectangles, which the packing separation
(`LabelsC7.PartsSeparated`) keeps apart. -/
def ExclusiveBoxInLabelRun (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : PipelineImpl.SceneExecution inp o res) (l : SceneLabel) (index : Nat)
    (source : ModelLabel) (measured : PipelineImpl.MeasuredLabel)
    (comp : List Nat) (candidate : Nat) (run : PipelineImpl.Run)
    (orderOptions : OrderOptions) (cg : Graph) (edge decl : Nat)
    (e : Edge) (px py m h : Int) (d : Direction),
    l ∈ res.scene.labels →
    inp.labels[index]? = some source →
    l.id = source.id →
    execution.measured.find? (fun label => label.index == index) = some measured →
    comp ∈ PipelineImpl.components execution.graph →
    cg = PipelineImpl.componentCandidate execution.graph comp candidate →
    PipelineImpl.componentRun execution.params cg execution.measured orderOptions = .ok run →
    (cg.edges[edge]?) = some e →
    (cg.edges[edge]?).map (·.decl) = some decl →
    measured ∈ PipelineImpl.routeLabels execution.measured decl →
    l.rect = PipelineImpl.shiftRect m m
      (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
        (routeLabelRect execution.params cg run execution.measured measured))) →
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
      b.rect = PipelineImpl.shiftRect m m
        (PipelineImpl.orientRect d h (PipelineImpl.shiftRect px py
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
  obtain ⟨comp, candidate, run, orderOptions, cg, edge, decl, _i₀, _i₁, px, py, m, hgt, dir,
    hcomp, hcg, hrun, hedge, hmlabel, hrect⟩ :=
    hlabel execution l index source measured hlmem hin hleq hmeasured
  obtain ⟨e, he⟩ : ∃ e, (cg.edges[edge]?) = some e := by
    cases h : cg.edges[edge]? with
    | none => simp [h] at hedge
    | some e => exact ⟨e, rfl⟩
  obtain ⟨v, hv, hreal, hs0, hs1, hbrect⟩ |
    ⟨packed, c, d', labelPart, boxPart, shelfc, shelfd, rl, r, hpacked, hcpart,
      hcshelf, hdpart, hdshelf, hcd, hrlmem, hrmem, hlrect, hbrect⟩ :=
    hbox execution l index source measured comp candidate run orderOptions cg edge decl e
      px py m hgt dir hlmem hin hleq hmeasured hcomp hcg hrun he hedge hmlabel hrect
      b hdump hex hscope
  · exact Or.inl ⟨comp, candidate, run, orderOptions, cg, edge, decl, v, e, px, py,
      m, hgt, dir, hcomp, hcg, hrun, he, hedge, hmlabel, hv, hreal, hs0, hs1,
      hrect, hbrect⟩
  · exact Or.inr ⟨packed, c, d', labelPart, boxPart, shelfc, shelfd, rl, r, hpacked,
      hcpart, hcshelf, hdpart, hdshelf, hcd, hrlmem, hrmem, hlrect, hbrect⟩

end Elegant.Layered
