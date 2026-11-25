import Elegant.Layered.ExactStepLeafFactsProof
import Elegant.Layered.ExpandChildParentRouteAttachedCtxProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Validator

/-! # Exact step recursion premises: parent-scene validity bundle.

Proved here:

* `XSRP_ParentSceneValid`: the validated-parent-scene bundle the recursion
  supplies — `HardConstraints parent.scene.layoutDump`, i.e. clauses
  C1 through C8 of the parent scene, from the fuel induction hypothesis
  applied to the parent sub-input recursive result.
* `XSRP_stepC6Disj_from_valid`: the `stepC6Disj` leaf from the bundle's C8a
  (via `XSGL_stepC6Disj_of_c8a`; ancestor isolation is the closed
  `stepC8aAncestry_layoutX`, the frame role the closed `xsgl` mirror).
* `XSRP_stepC8bParentFrame_from_valid`: the `stepC8bParentFrame` leaf from the
  bundle's C8a/C8b plus the two call-local strictness facts
  (`ExpandChildParentFrameStrict`, `ExpandChildParentStrictStep`).
* `XSRP_stepC7Parent_from_valid`: the `stepC7Parent` leaf from the bundle
  plus the same strictness facts. The box half reuses the C6Disj theorem;
  the label half projects out of the ParentFrame theorem at the call's own
  title lines, so no private frame-role copy is needed. `hstepStrict`
  travels through that bridge and is stronger than the minimum this leaf
  needs on its own.
* Thin conditionals `XSRP_stepC6Miss_from_routeClear`,
  `XSRP_stepC7Child_from_inset`, `XSRP_stepC7Caption_from_owners`: the
  remaining step leaves from their existing named call-local premises
  (`ExpandChildParentRouteClear`, the child-label inset,
  `ExpandChildLabelOwners`).

Open (not closed here): `ExpandChildParentRouteClear` (router-level port and
middle-segment avoidance at the frame), `ExpandChildParentFrameStrict` and
`ExpandChildParentStrictStep` (positive sizing gaps the flat layout
reserves; parent C3 gives only non-strict containment), the child-label
inset (needs the `InputFixedFit` induction), and `ExpandChildLabelOwners`
(label pipeline invariant, cf. `ExpandChildLabelFactsProof`). The recursion
must supply `hvalid` from its fuel induction hypothesis on the parent
sub-input result; the call bundle (`hexpand`, `hframed`, `hctxB`,
`hparams`) is local to the executed call.

Probe evidence: `XSRPT_run ["g"]` below replicates one B-base `expandChild`
call per input (same tracer shape as `XSGLT_run`, plus the attached-route
input `XSRPT_attached` carrying an `a -> g` route). All seven calls below
evaluate to every flag `true`:

| input | c8 | c6 | c5 | disj | plabel | fstrict | attF | attI | outS | anc | pfS | pfF |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nested g(a,b) | true | true | true | true | true | true | true | true | true | true | true | true |
| self-loop a->a,a->b | true | true | true | true | true | true | true | true | true | true | true | true |
| caption owned by g | true | true | true | true | true | true | true | true | true | true | true | true |
| empty group | true | true | true | true | true | true | true | true | true | true | true | true |
| zero-size fixed child | true | true | true | true | true | true | true | true | true | true | true | true |
| duplicate box id | true | true | true | true | true | true | true | true | true | true | true | true |
| attached a->g, long title | true | true | true | true | true | true | true | true | true | true | true | true |

No FALSE witness was found; in particular the attached `a -> g` route misses
the frame rectangle and its shrink-by-1/3 interiors, and the parent dumps
satisfy C8/C6/C5 on every input including the degenerate ones.
-/

/-- The validated-parent-scene bundle the recursion supplies for one
`expandChild` step: the full hard-constraint conjunction of the parent
scene dump. `FamilyAssembly` discharges this from its fuel induction
hypothesis on the parent sub-input recursive result. -/
def XSRP_ParentSceneValid (_group : ModelBox) (parent : FamilyResult) : Prop :=
  HardConstraints parent.scene.layoutDump

/-- The `stepC6Disj` leaf from the validated parent scene: the bundle's C8a
feeds `XSGL_stepC6Disj_of_c8a`; ancestor isolation and the frame role are
the closed `stepC8aAncestry_layoutX` and role mirror inside it. -/
theorem XSRP_stepC6Disj_from_valid (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hvalid : XSRP_ParentSceneValid group parent) :
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
      Disjoint frame.rect pb.rect := by
  have hC8a : Validator.C8a parent.scene.layoutDump :=
    hvalid.2.2.2.2.2.2.2.1
  exact XSGL_stepC6Disj_of_c8a exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams hC8a

/-- The `stepC8bParentFrame` leaf from the validated parent scene: the
bundle's C8a/C8b feed `XSGL_stepC8bParentFrame_of` together with the two
call-local strictness facts. -/
theorem XSRP_stepC8bParentFrame_from_valid (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hvalid : XSRP_ParentSceneValid group parent)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent) :
    ExpandChildParentFrame P inp o group titleHeight parent child := by
  have hC8a : Validator.C8a parent.scene.layoutDump :=
    hvalid.2.2.2.2.2.2.2.1
  have hC8b : Validator.C8b parent.scene.layoutDump :=
    hvalid.2.2.2.2.2.2.2.2
  exact XSGL_stepC8bParentFrame_of exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams hC8a hC8b
    hframeStrict hstepStrict

/-- The `stepC7Parent` leaf from the validated parent scene. The box half is
the C6Disj theorem above; the label half projects out of the ParentFrame
theorem at the call's own title lines (its statement is offset-free), which
is why `hstepStrict` appears here through that bridge. -/
theorem XSRP_stepC7Parent_from_valid (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hvalid : XSRP_ParentSceneValid group parent)
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hstepStrict : ExpandChildParentStrictStep parent) :
    ExpandChildC7ParentClear P inp o group titleHeight parent := by
  have hwrap : ExpandChildTitleWrapped P inp o group titleLines :=
    hparams.2.2
  have hPF : ExpandChildParentFrame P inp o group titleHeight parent child :=
    XSRP_stepC8bParentFrame_from_valid exactIds fuel P inp o group titleLines
      titleHeight parent child res hexpand hframed hctxB hparams hvalid
      hframeStrict hstepStrict
  have hbox := XSRP_stepC6Disj_from_valid exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams hvalid
  intro frame _tl _dx _dy hframe _hdx _hdy _hwrap'
  exact ⟨hbox frame hframe, (hPF frame titleLines _ _ hframe rfl rfl hwrap).2.1⟩

/-- The `stepC6Miss` leaf from its call-local premise: the out-of-scope
case goes through the public `parentRoute_outside_inner` monotonicity, the
attached case is the premise itself. -/
theorem XSRP_stepC6Miss_from_routeClear (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hroute : ExpandChildParentRouteClear group parent) :
    ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pr ∈ parent.scene.routes, ∀ (r : Rect), frame.rect.StrictInside r →
      ¬ Polyline.hitsRect pr.points r :=
  XSGL_stepC6Miss_of_routeClear exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams hroute

/-- The `stepC7Child` leaf from its call-local premise: the child-label
inset plus the exact content fit. -/
theorem XSRP_stepC7Child_from_inset (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hlabels : ∀ cl ∈ child.scene.labels,
      (insetRect child.scene.canvas P.canvasMargin).Contained cl.rect) :
    ExpandChildC7ChildInside P inp o group titleHeight parent child :=
  XSGL_stepC7Child_of_labels exactIds fuel P inp o group titleLines titleHeight
    parent child res hexpand hframed hctxB hparams hlabels

/-- The `stepC7Caption` leaf from its call-local premise: the label-owner
invariant plus the exact title band. -/
theorem XSRP_stepC7Caption_from_owners (exactIds : List String)
    (fuel : Nat) (P : Params) (inp : Input) (o : Options)
    (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
    (parent child res : FamilyResult)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctxB : ExpandChildCallContextB (layoutX exactIds) fuel P inp o group
      titleLines titleHeight parent child res)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (howners : ExpandChildLabelOwners inp parent child) :
    ExpandChildC7CaptionFit P inp o group titleHeight parent child res :=
  XSGL_stepC7Caption_of_owners exactIds fuel P inp o group titleLines
    titleHeight parent child res hexpand hframed hctxB hparams howners

/-! ## Probe: executed `expandChild` calls at the exact base -/

/-- Nested group with two children. -/
def XSRPT_nested : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "a", role := .node, parent := "g" },
      { id := "b", role := .node, parent := "g" }]
    routes := []
    texts := ["G", "A", "B"]
    edges := [] }

/-- Group with a self-loop on member `a` plus `a -> b`. -/
def XSRPT_selfloop : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "a", role := .node, parent := "g" },
      { id := "b", role := .node, parent := "g" }]
    routes := [{ id := "e1", fromId := "a", toId := "a" },
      { id := "e2", fromId := "a", toId := "b" }]
    texts := ["G", "A", "B"]
    edges := [] }

/-- Group with a caption label owned by the group. -/
def XSRPT_caption : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "a", role := .node, parent := "g" }]
    routes := []
    texts := ["G", "A"]
    edges := []
    labels := [{ id := "cap", owner := "g", text := "Caption" }] }

/-- Degenerate empty group. -/
def XSRPT_empty : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" }]
    routes := []
    texts := ["G"]
    edges := [] }

/-- Child `a` pinned to a zero-size fixed box. -/
def XSRPT_zerosize : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "a", role := .node, parent := "g" },
      { id := "b", role := .node, parent := "g" }]
    routes := []
    texts := ["G", "A", "B"]
    edges := []
    fixedSizes := [("a", { w := 0, h := 0 })] }

/-- Ill-formed input: duplicate box id `a`. -/
def XSRPT_dup : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "a", role := .node, parent := "g" },
      { id := "a", role := .node, parent := "g" }]
    routes := []
    texts := ["G", "A", "B"]
    edges := [] }

/-- Titled group with an attached `a -> g` route (exercises the attached
route premise alongside the out-of-scope one). -/
def XSRPT_attached : Input :=
  { kind := "flowchart"
    boxes := [{ id := "g", role := .group, direction := "TB" },
      { id := "x", role := .node, parent := "g" },
      { id := "y", role := .node, parent := "g" },
      { id := "a", role := .node }]
    routes := [{ id := "e1", fromId := "x", toId := "y" },
      { id := "e2", fromId := "a", toId := "g" }]
    texts := ["GGGGGGGGGGGGGGGGGGGG", "x", "y", "a"]
    edges := [.plain, .plain] }

def XSRPT_opts : Options := {}

/-- `xsrpt_` copies of the `XSGLT_` boolean geometry helpers
(`ExactStepGeometryLeavesTProbe.lean`), for the probe below. -/
private def xsrpt_contained (outer inner : Rect) : Bool :=
  decide (outer.x ≤ inner.x) && decide (inner.x + inner.w ≤ outer.x + outer.w) &&
  decide (outer.y ≤ inner.y) && decide (inner.y + inner.h ≤ outer.y + outer.h)

private def xsrpt_strictInside (outer inner : Rect) : Bool :=
  decide (outer.x < inner.x) && decide (inner.x + inner.w < outer.x + outer.w) &&
  decide (outer.y < inner.y) && decide (inner.y + inner.h < outer.y + outer.h)

private def xsrpt_meets (a b : Rect) : Bool :=
  decide (max a.x b.x < min (a.x + a.w) (b.x + b.w)) &&
  decide (max a.y b.y < min (a.y + a.h) (b.y + b.h))

private def xsrpt_disjoint (a b : Rect) : Bool := !xsrpt_meets a b

/-- Replicate one B-base `expandChild` call and report the bundle clauses
plus each theorem premise/conclusion in this file as `Bool`s. -/
def XSRPT_run (exactIds : List String) (inp : Input) (o : Options) : String :=
  let fuel := inp.boxes.length + 1
  match inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
      !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) with
  | none => "no-group"
  | some group =>
    match checkedParams o.profile inp.kind with
    | .error _ => "params"
    | .ok P =>
    match metricOf o.profile with
    | .error _ => "metric"
    | .ok metric =>
      let childInput := selectInput inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      match layoutRecursiveB (layoutX exactIds) fuel childInput
          { o with direction := directionOf group.direction } with
      | .error _ => "child"
      | .ok child =>
      let index := inp.boxes.findIdx? (fun box => box.id == group.id)
      let title := inp.texts.getD (index.getD 0) group.id
      match StyledMeasure.wrap metric
          (Measure.wrapTarget metric.profile P.wrapWidth
            (if o.profile == .cell then o.maxWidth else 0)) title.toList with
      | .error _ => "wrap"
      | .ok titleLines =>
        let titleWidth :=
          titleLines.foldl (fun width line => max width line.width) 0
        let titleHeight := (max 1 titleLines.length : Int) * P.lineH
        let size := childFrameSize group.direction P.clusterPad titleWidth titleHeight
          ⟨child.scene.canvas.w - 2 * P.canvasMargin,
            child.scene.canvas.h - 2 * P.canvasMargin⟩
        let parentInput := selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id)
        let parentInput := { parentInput with
          fixedSizes := parentInput.fixedSizes ++ [(group.id, size)]
          fixedChildren := parentInput.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := parentInput.fixedAreas ++ [(group.id, child.itemArea)] }
        match layoutRecursiveB (layoutX exactIds) fuel parentInput o with
        | .error _ => "parent"
        | .ok parent =>
        match expandChild P inp o group titleHeight parent child with
        | .error _ => "expand"
        | .ok res =>
        match parent.scene.boxes.find? (fun box => box.id == group.id) with
        | none => "no-frame"
        | some frame =>
          let scope := group.id :: parent.scene.layoutDump.ancestors group.id
          let parentC8 := Validator.c8 parent.scene.layoutDump
          let parentC6 := Validator.c6 parent.scene.layoutDump
          let parentC5 := Validator.c5 parent.scene.layoutDump
          let disjB := parent.scene.boxes.all (fun pb =>
            !pb.exclusive || scope.contains pb.id ||
            xsrpt_disjoint frame.rect pb.rect)
          let plabelB := parent.scene.labels.all (fun pl =>
            pl.owner == group.id || xsrpt_disjoint frame.rect pl.rect)
          let fstrictB := parent.scene.labels.all (fun pl =>
            pl.owner == group.id || !xsrpt_strictInside frame.rect pl.rect)
          let attF := parent.scene.routes.all (fun pr =>
            !(pr.fromId == group.id || pr.toId == group.id) ||
            !_root_.Polyline.hitsRectB pr.points frame.rect)
          let sh1 : Rect := ⟨frame.rect.x + 1, frame.rect.y + 1,
            frame.rect.w - 2, frame.rect.h - 2⟩
          let sh3 : Rect := ⟨frame.rect.x + 3, frame.rect.y + 3,
            frame.rect.w - 6, frame.rect.h - 6⟩
          let attI := parent.scene.routes.all (fun pr =>
            !(pr.fromId == group.id || pr.toId == group.id) ||
            (!xsrpt_strictInside frame.rect sh1 ||
              !_root_.Polyline.hitsRectB pr.points sh1) &&
            (!xsrpt_strictInside frame.rect sh3 ||
              !_root_.Polyline.hitsRectB pr.points sh3))
          let outS := parent.scene.routes.all (fun pr =>
            (pr.fromId == group.id || pr.toId == group.id) ||
            !_root_.Polyline.hitsRectB pr.points frame.rect)
          let ancB := parent.scene.boxes.all (fun pb =>
            pb.id == group.id ||
            !((parent.scene.layoutDump.ancestors pb.id).contains group.id))
          let pfS := parent.scene.boxes.all (fun g =>
            !(g.role == "group") ||
            !((parent.scene.layoutDump.ancestors group.id).contains g.id) ||
            xsrpt_strictInside g.rect frame.rect)
          let pfF := parent.scene.boxes.all (fun g =>
            !(g.role == "group") || g.id == group.id ||
            ((parent.scene.layoutDump.ancestors group.id).contains g.id) ||
            !((parent.scene.layoutDump.ancestors g.id).contains group.id) ||
            xsrpt_disjoint g.rect frame.rect)
          let nres := res.scene.layoutDump.labels.length
          s!"c8={parentC8} c6={parentC6} c5={parentC5} disj={disjB} " ++
          s!"plabel={plabelB} fstrict={fstrictB} attF={attF} attI={attI} " ++
          s!"outS={outS} anc={ancB} pfS={pfS} pfF={pfF} nres={nres}"

#eval XSRPT_run ["g"] XSRPT_nested XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_selfloop XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_caption XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_empty XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_zerosize XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_dup XSRPT_opts
#eval XSRPT_run ["g"] XSRPT_attached XSRPT_opts
