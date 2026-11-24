import Elegant.Layered.Assembly
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.ExpandChildStructureFacts
import Elegant.Layered.FramedParentsSub
import Elegant.Layered.InsetFit
import Elegant.Layered.InputFixedFit
import Elegant.Layered.LabelsC8b
import Elegant.Layered.OutputParentContained
import Elegant.Layered.PipelineFacts
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.RecursiveC78
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveFit
import Elegant.Layered.SelectFacts
import Elegant.Layered.SubInputWellFormedFacts
import ElegantGeometry.Basic
import Elegant.Layered.RecursiveCallParams
import ElegantGeometry.Route
import ElegantGeometry.Validator

set_option autoImplicit false

open Elegant.Layered.Compound

namespace Elegant.Layered.PipelineImpl

/-! # The group frame inside the parent scene

Anchor: Tony Hoare, Edsger W. Dijkstra.

For one executed `expandChild` call of `layoutRecursive` (the three call
premises `hexpand`, `hframed`, `hctx` below), the parent scene holds the
split group as a fixed-size box.  This module proves, about the parent
scene alone with the frame bound by
`parent.scene.boxes.find? (fun box => box.id == group.id) = some frame`:

* (boxes) the frame is disjoint from out-of-scope exclusive parent boxes;
* (unrelated) the frame is disjoint from unrelated group frames;
* (labels) the frame is disjoint from parent labels it does not own;
* (ancestor) ancestor group frames strictly contain the frame;
* (routes) parent routes miss every rectangle strictly inside the frame.

The caption conjunct of the C8 consumer
(`pl.owner = group.id → pl.rect = groupTitleRectC8 …`) is FALSE as stated:
on the executed nested-group input `nestLab` the parent label `lG` sits at
the fallback title rect `⟨2048, 10240, 8720, 1280⟩` while the caption is the
centered `⟨6072, 10240, 672, 1280⟩` (and an `LR` variant disagrees in `y`
as well, so no containment holds either way).  The parent layout places a
group-owned label by the `sceneOf` title/measured/fallback branches, never
uniformly at the installed caption, so no uniform parent-alone equation is
stated here.

Exclusive-flag finding (decides the clause routes): the fixed-size group
box is NON-exclusive in the parent scene.  `sceneOf`/`componentScene` copy
`exclusive` from the input model box, `selectInput` keeps it, and
`WellFormed` forbids exclusive groups (`wellFormed_iff`), so the frame has
`exclusive = false` (`#eval` on ten executed calls: every frame shows
`exclusive=false`, `role=group`).  Hence parent C2/C6/C7 (which need
exclusive boxes) do not apply to the frame: boxes go through parent C8a,
labels through parent C8b plus strictness exclusion, routes through a
router residual plus transport.

Seam plumbing: the per-call lifts take their flat/step premises directly
instead of through `LayeredSeams`, because `FamilyAssembly` currently has
eight application mismatches (the `ExpandChildCallParams` step assembly
versus the parameter-free seam fields) and does not compile.  The granular
hypotheses below are exactly the seam's fields (`FlatC8a`, `FlatC8b`, the
`∀`-quantified geometry/ancestry/owner remainders), so rebundling them
into `S` once the assembly compiles is mechanical.
-/

/-! ## Residuals: one parent-scene fact each -/

/-- Residual for labels: the group frame does not strictly contain a parent
label owned elsewhere. True for executed calls: parent labels are
measured run rects or title-band rects sized to their own text, while the
frame reserves the whole child canvas plus pads and the title band; the two
interactions the statement singles out — a label owned by a route ending
at the group and the title label of an ancestor group — sit at the frame
or overlap it at most on the boundary on every probed executed call, but
no proved sizing bound rules out strict containment in general. -/
def ExpandChildParentFrameStrict (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
      ¬ frame.rect.StrictInside pl.rect

/-- Residual for (ancestor): one strict step.  Every group parent strictly
contains its child box in the parent scene.  True on every probed executed
call (including an `LR`-direction ancestor); the mechanism is the
`clusterPad`/title reservation the flat layout wraps members in.  If a
layout ever packed a group flush against a member (zero gap on one side),
this would fail; nothing proved here establishes the positive gap. -/
def ExpandChildParentStrictStep (parent : FamilyResult) : Prop :=
  ∀ (b : Box), b ∈ parent.scene.boxes → b.parent ≠ "" →
    ∀ (p : Box), parent.scene.layoutDump.box? b.parent = some p →
      p.role = "group" → p.rect.StrictInside b.rect

/-- The parent sub-input is well-formed and framed: `inputModel` ignores the
fixed side tables, so `selectInput` preservation suffices; no wrap equation
is needed. -/
private theorem parentInput_wellFormed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) := by
  exact inputModel_wellFormed_fixed_congr _ _ _
    (selectInput_wellFormed inp o
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hctx.1
      (fun c hc hkept => keepOutside_close (group := group.id)
        (inputFacts_of_wellFormed hctx.1) hc hkept) o)

private theorem parentInput_framed
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    framedParents (parentSubInput inp group P titleLines child) = true := by
  exact framedParents_selectInput_outside_append inp o group hctx.1 hframed
    _ child.scene child.itemArea
/-- Residual for (routes): parent routes avoid the frame interior.  The
out-of-scope conjunct is at the frame rectangle; the attached conjunct
covers routes with an endpoint at the group for every rectangle strictly
inside the frame.  True on every probed executed call: out-of-scope routes
(including an `L → R` route spanning the frame) and attached routes
(`a → G`, orthogonal, ending on the frame boundary) miss the frame
rectangle and its shrink-by-1/3 interiors.  The mechanism is router
design — channels run around the reserved fixed-size frame and port stubs
face outward — which no proved clause establishes (the frame is
non-exclusive, so parent C6 does not apply; C5 plus orthogonality pins the
boundary endpoint but not the stub exterior or the middle segments). -/
def ExpandChildParentRouteClear (group : ModelBox) (parent : FamilyResult) : Prop :=
  ∀ (frame : Box),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    (∀ pr ∈ parent.scene.routes, pr.fromId ≠ group.id → pr.toId ≠ group.id →
        ¬ Polyline.hitsRect pr.points frame.rect) ∧
    (∀ pr ∈ parent.scene.routes, (pr.fromId = group.id ∨ pr.toId = group.id) →
        ∀ (r : Rect), frame.rect.StrictInside r →
          ¬ Polyline.hitsRect pr.points r)


/-! ## Shared builders -/

/-- The located frame carries the group id. -/
private theorem frame_id_eq {group : ModelBox} {parent : FamilyResult}
    {frame : Box}
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame) :
    frame.id = group.id := by
  simpa using List.find?_some hframe

/-- The frame has group role and the group's ancestor chain is isolated
from the other parent boxes: the structural remainder of the C8a step at
the caller's own frame and offsets. -/
private theorem parentFrame_role_isolation
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines titleLines' : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult} {frame : Box} {dx dy : Int}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hancAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aAncestry group parent child res)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin)
    (hwrap : ExpandChildTitleWrapped P inp o group titleLines') :
    frame.role = "group" ∧
      (∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
        group.id ∉ parent.scene.layoutDump.ancestors pb.id) := by
  obtain ⟨_, _, _, _, hrole, _, _, hiso⟩ :=
    expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx
      (hancAll fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx)
      frame titleLines' dx dy hframe hdx hdy hwrap
  exact ⟨hrole, hiso⟩

/-- The parent scene satisfies C8a: the flat clause plus the per-expansion
step assembled from the geometry remainder and the ancestry remainder,
lifted through the recursion at the parent sub-input. -/
private theorem parentScene_c8a
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hflat8a : FlatC8a)
    (hgeoAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res)
    (hancAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aAncestry group parent child res)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    Validator.C8a parent.scene.layoutDump := by
  have hstep : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8aStep P inp o group titleHeight parent child res := by
    intro fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams
    have _hp := hparams
    intro frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ :=
      expandChild_c8a_structure fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx
        (hancAll fuel P inp o group titleLines titleHeight parent child res
          hexpand hframed hctx)
        frame tl dx dy hframe hdx hdy hwrap
    have hg := hgeoAll fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx frame tl dx dy hframe hdx hdy hwrap
    exact ⟨s1, s2, s3, s4, s5, s6, hg, s7, s8⟩
  have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent := hctx.2.2.2.2.1
  exact layoutRecursive_c8a_of_flat hflat8a subInputsWellFormed hstep fuel
    (parentSubInput inp group P titleLines child) o parent
    (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hparent

/-- The parent scene satisfies C8b. -/
private theorem parentScene_c8b
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hflat8b : FlatC8b)
    (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o)
    (hgeoAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res)
    (hownersAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildLabelOwners inp parent child)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    Validator.C8b parent.scene.layoutDump := by
  have hstep : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC8bStep P inp o group titleHeight parent child res := by
    intro fuel P inp o group titleLines titleHeight parent child res
      hexpand hframed hctx hparams
    have _hp := hparams
    intro frame tl dx dy hframe hdx hdy hwrap
    have hc := expandChild_c8b_structure fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx
      (hownersAll fuel P inp o group titleLines titleHeight parent child res
        hexpand hframed hctx)
      frame tl dx dy hframe hdx hdy hwrap
    obtain ⟨g1, g2, g3, g4⟩ := hgeoAll fuel P inp o group titleLines titleHeight
      parent child res hexpand hframed hctx frame tl dx dy hframe hdx hdy hwrap
    exact ⟨hc, g1, g2, g3, g4⟩
  have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent := hctx.2.2.2.2.1
  exact layoutRecursive_c8b_of_flat hflat8b subInputsWellFormed hstep fuel
    (parentSubInput inp group P titleLines child) o parent
    (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hfit hparent

/-- The parent scene satisfies C3: the flat clause needs no seam, so the
inset lift applies directly. -/
private theorem parentScene_c3
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    Validator.C3 parent.scene.layoutDump := by
  have hflat3 : FlatC3' := fun inp o res hwf hframed h => layout_c3 h hwf hframed
  have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent := hctx.2.2.2.2.1
  exact (layoutRecursive_c1_c3_of_inset subInputWellFormedC2 framedParentsSub hflat3
    fuel (parentSubInput inp group P titleLines child) o parent
    (parentInput_wellFormed hctx) (parentInput_framed hframed hctx) hparent).2

/-! ## Ancestor-walk toolkit -/

/-- Scene box ids of the parent stay nodup along `layoutRecursive`. -/
private theorem parentScene_box_ids_nodup
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    (parent.scene.boxes.map (·.id)).Nodup := by
  have hwf : WellFormed (inputModel inp o) := hctx.1
  have hparent : layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent := hctx.2.2.2.2.1
  have hcov : RoutesCovered (parentSubInput inp group P titleLines child) :=
    selectInput_routesCovered inp
      (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hids := layoutRecursive_ids (fun _ _ _ hl => layout_ids hl) fuel
    (parentSubInput inp group P titleLines child) o parent hcov hparent
  rw [hids.1]
  show ((selectInput inp
    (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
    (·.id)).Nodup
  rw [selectInput_box_ids]
  exact (Model.boxIds_nodup hwf).sublist
    (List.Sublist.map (fun b : ModelBox => b.id) List.filter_sublist)

/-- One unfolded step of the ancestor walk. -/
private theorem go_succ {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. -/
private theorem go_none {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. -/
private theorem go_root {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- Strict containment is transitive through a non-strict containment. -/
private theorem strictInside_of_strictInside_contained {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.Contained c) : a.StrictInside c := by
  simp only [Rect.StrictInside, Rect.Contained] at hab hbc ⊢
  omega

/-! ## `hitsRect` monotonicity through strict containment -/

/-- A corner-minimum bound: the `minCorner` of a rectangle lies below the
corner product at any point of its closed extent. -/
private theorem minCorner_le_dot {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    Polyline.minCorner nx ny outer ≤ nx * x + ny * y := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega

private theorem dot_le_maxCorner {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    nx * x + ny * y ≤ Polyline.maxCorner nx ny outer := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : nx * (outer.x + outer.w) + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : nx * (outer.x + outer.w) + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : nx * outer.x + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : nx * outer.x + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega

/-- A segment that misses an outer rectangle misses every strictly
inner one: axis separations transport by the gap, diagonal separations by
the corner bounds. -/
private theorem segMisses_of_strictInside {outer inner : Rect} {p q : Point}
    (hSI : outer.StrictInside inner)
    (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (hm : Polyline.segMisses p q outer) : Polyline.segMisses p q inner := by
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  unfold Polyline.segMisses at hm ⊢
  rcases hm with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · obtain ⟨hne, hle | hge⟩ := h
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl ?_⟩)))
      have c1 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * inner.y :=
        minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c2 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y :=
        minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c3 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) :=
        minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have c4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) :=
        minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          Polyline.minCorner (p.y - q.y) (q.x - p.x) inner := by
        simp only [Polyline.minCorner, Polyline.dot] at c1 c2 c3 c4 ⊢
        omega
      exact Int.le_trans hle h4
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr ?_⟩)))
      have g1 : (p.y - q.y) * inner.x + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g2 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g3 : (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have g4 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.maxCorner (p.y - q.y) (q.x - p.x) inner ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer := by
        simp only [Polyline.maxCorner, Polyline.dot] at g1 g2 g3 g4 ⊢
        omega
      exact Int.le_trans h4 hge

/-- A polyline that misses an outer rectangle misses every strictly
inner one. -/
private theorem allSegsMiss_of_strictInside {outer inner : Rect}
    (hSI : outer.StrictInside inner) (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (pts : List Point) :
    Polyline.allSegsMiss pts outer → Polyline.allSegsMiss pts inner := by
  induction pts
  case nil => intro h; trivial
  case cons head tail ih =>
    intro h
    cases tail with
    | nil => trivial
    | cons q rest' =>
        obtain ⟨hseg, htail⟩ := h
        exact ⟨segMisses_of_strictInside hSI hw hh hseg, ih htail⟩
/-- Hitting a strictly inner rectangle implies hitting the outer one. -/
private theorem hitsRect_of_strictInside {outer inner : Rect} {pts : List Point}
    (hSI : outer.StrictInside inner) (h : Polyline.hitsRect pts inner) :
    Polyline.hitsRect pts outer := by
  obtain ⟨hwI, hhI, hmissI⟩ := h
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  refine ⟨by omega, by omega, ?_⟩
  intro hmissO
  exact hmissI (allSegsMiss_of_strictInside ⟨hox, how, hoy, hoh⟩
    (Int.le_of_lt hwI) (Int.le_of_lt hhI) _ hmissO)

/-! ## Ancestor strictness by parent-chain induction -/

/-- Every ancestor group strictly contains the descendant box: one C3
containment per parent link, strictness from the one-step residual at the
link into the ancestor. -/
private theorem ancestor_strict_aux
    (d : LayoutDump)
    (hC3 : Validator.C3 d)
    (hstep : ∀ (b : Box), b ∈ d.boxes → b.parent ≠ "" →
      ∀ (p : Box), d.box? b.parent = some p → p.role = "group" →
        p.rect.StrictInside b.rect)
    (g : Box) (hgRole : g.role = "group")
    (hfindg : d.box? g.id = some g) :
    ∀ (n : Nat) (s : String) (b : Box),
      d.box? s = some b → g.id ∈ LayoutDump.ancestors.go d n s →
      g.rect.StrictInside b.rect := by
  intro n
  induction n with
  | zero =>
      intro s b hb hm
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hm
      cases hm
  | succ n ih =>
      intro s b hb hm
      have hbmem : b ∈ d.boxes := List.mem_of_find?_eq_some hb
      by_cases hpar : b.parent = ""
      · rw [go_root hb hpar] at hm
        cases hm
      · rw [go_succ hb hpar] at hm
        rcases List.mem_cons.mp hm with heq | hmem
        · have hlook : d.box? b.parent = some g := heq ▸ hfindg
          exact hstep b hbmem hpar g hlook hgRole
        · cases hq : d.box? b.parent with
          | none =>
              cases hn : n with
              | zero =>
                  have e : LayoutDump.ancestors.go d 0 b.parent = [] := rfl
                  rw [hn] at hmem
                  rw [e] at hmem
                  cases hmem
              | succ m =>
                  rw [hn, go_none hq] at hmem
                  cases hmem
          | some q1 =>
              have hIH := ih b.parent q1 hq hmem
              have hcont := hC3 b hbmem hpar q1 hq
              exact strictInside_of_strictInside_contained hIH hcont

/-! ## The five parent-scene facts -/

/-- (boxes) The frame is disjoint from out-of-scope exclusive parent boxes.
The frame is non-exclusive, so parent C2 does not apply; parent C8a does,
with the group's ancestor-chain isolation from the C8a structural
remainder. -/
theorem expandChild_parentFrame_boxes
    (hflat8a : FlatC8a)
    (hgeoAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res)
    (hancAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aAncestry group parent child res)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
      pb.id ∉ group.id :: parent.scene.layoutDump.ancestors group.id →
      Disjoint frame.rect pb.rect := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap pb hpbMem hex hforeign
  have hfid := frame_id_eq hframe
  have hC8a := parentScene_c8a hflat8a hgeoAll hancAll hexpand hframed hctx
  obtain ⟨hrole, hiso⟩ := parentFrame_role_isolation hexpand hframed hctx
    hancAll hframe hdx hdy hwrap
  have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hframe
  have hpbMemD : pb ∈ parent.scene.layoutDump.boxes := hpbMem
  have hne' : pb.id ≠ group.id := by
    intro h
    apply hforeign
    rw [h]
    exact List.mem_cons.mpr (Or.inl rfl)
  have hne : pb.id ≠ frame.id := by
    rw [hfid]
    exact hne'
  have h1 : frame.id ∉ parent.scene.layoutDump.ancestors pb.id := by
    rw [hfid]
    exact hiso pb hpbMem hne'
  have h2 : pb.id ∉ parent.scene.layoutDump.ancestors frame.id := by
    rw [hfid]
    exact fun hm => hforeign (List.mem_cons.mpr (Or.inr hm))
  exact hC8a frame hframeMem hrole pb hpbMemD hne h1 h2

/-- (unrelated) The frame is disjoint from unrelated group frames:
parent C8a at the group, where both non-ancestry directions are
hypotheses. -/
theorem expandChild_parentFrame_unrelated
    (hflat8a : FlatC8a)
    (hgeoAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aGeometry P inp o group titleHeight parent child res)
    (hancAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aAncestry group parent child res)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ g ∈ parent.scene.boxes, g.role = "group" → g.id ≠ group.id →
      g.id ∉ parent.scene.layoutDump.ancestors group.id →
      group.id ∉ parent.scene.layoutDump.ancestors g.id →
      Disjoint g.rect frame.rect := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap g hg hgRole hgNe hgNotAnc1 hgNotAnc2
  have _hdx := hdx
  have _hdy := hdy
  have _hwrap := hwrap
  have _hdxv : dx = dx := rfl
  have _hdyv : dy = dy := rfl
  have _htlv : titleLines' = titleLines' := rfl
  have hfid := frame_id_eq hframe
  have hC8a := parentScene_c8a hflat8a hgeoAll hancAll hexpand hframed hctx
  have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hframe
  have hgMemD : g ∈ parent.scene.layoutDump.boxes := hg
  have hne : frame.id ≠ g.id := by
    rw [hfid]
    exact fun h => hgNe h.symm
  have h1 : g.id ∉ parent.scene.layoutDump.ancestors frame.id := by
    rw [hfid]
    exact hgNotAnc1
  have h2 : frame.id ∉ parent.scene.layoutDump.ancestors g.id := by
    rw [hfid]
    exact hgNotAnc2
  exact hC8a g hgMemD hgRole frame hframeMem hne h1 h2

/-- (labels) The frame is disjoint from parent labels it does not own.
The frame is non-exclusive, so parent C7 does not apply; parent C8b gives
disjointness or strict containment, and the residual excludes the strict
case for labels owned elsewhere. -/
theorem expandChild_parentFrame_labels
    (hflat8b : FlatC8b)
    (hgeoAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8bGeometry P inp o group titleHeight parent child res)
    (hownersAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildLabelOwners inp parent child)
    (hancAll : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options)
      (group : ModelBox) (titleLines : List Measure.Line) (titleHeight : Int)
      (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight
        parent child res →
      ExpandChildC8aAncestry group parent child res)
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hframeStrict : ExpandChildParentFrameStrict group parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res)
    (hfit : InputFixedFit (parentSubInput inp group P titleLines child) o) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ pl ∈ parent.scene.labels, pl.owner ≠ group.id →
      Disjoint frame.rect pl.rect := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap pl hplMem hown
  have hC8b := parentScene_c8b hflat8b hfit hgeoAll hownersAll hexpand hframed hctx
  obtain ⟨hrole, _⟩ := parentFrame_role_isolation hexpand hframed hctx
    hancAll hframe hdx hdy hwrap
  have hframeMem : frame ∈ parent.scene.layoutDump.boxes :=
    List.mem_of_find?_eq_some hframe
  have hplD : pl.toLabel ∈ parent.scene.layoutDump.labels :=
    List.mem_map.mpr ⟨pl, hplMem, rfl⟩
  rcases hC8b frame hframeMem hrole pl.toLabel hplD with hdisj | hstrict
  · exact hdisj
  · have hstrict' : frame.rect.StrictInside pl.rect := hstrict
    exact absurd hstrict' (hframeStrict frame hframe pl hplMem hown)

/-- (ancestor) Ancestor group frames strictly contain the frame: C3
containment along the ancestor walk by parent-chain induction, strictness
from the one-step residual at the link into the ancestor. -/
theorem expandChild_parentFrame_ancestor
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hstepStrict : ExpandChildParentStrictStep parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ g ∈ parent.scene.boxes, g.role = "group" →
      g.id ∈ parent.scene.layoutDump.ancestors group.id →
      g.rect.StrictInside frame.rect := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap g hg hgRole hgAnc
  have _hex := hexpand
  have _hfr := hframed
  have _hdx := hdx
  have _hdy := hdy
  have _hwrap := hwrap
  have hC3 := parentScene_c3 hframed hctx
  have hnodup := parentScene_box_ids_nodup hctx
  have hfindg : parent.scene.layoutDump.box? g.id = some g :=
    Assembly.keyed_lookup_eq (fun b : Box => b.id) parent.scene.boxes hnodup g hg
  have hbox : parent.scene.layoutDump.box? group.id = some frame := hframe
  have hmem : g.id ∈ LayoutDump.ancestors.go parent.scene.layoutDump
      parent.scene.layoutDump.boxes.length group.id := hgAnc
  exact ancestor_strict_aux parent.scene.layoutDump hC3 hstepStrict g hgRole hfindg
    _ group.id frame hbox hmem

/-- (routes) Parent routes miss every rectangle strictly inside the frame.
The frame is non-exclusive, so parent C6 does not apply; the residual
supplies the frame-level miss for out-of-scope routes (transported inward
by `hitsRect` monotonicity) and the inner miss for attached ones. -/
theorem expandChild_parentFrame_routes
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child res : FamilyResult}
    (hroute : ExpandChildParentRouteClear group parent)
    (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
      parent child res) :
    ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    ExpandChildTitleWrapped P inp o group titleLines' →
    ∀ pr ∈ parent.scene.routes, ∀ (r : Rect),
      frame.rect.StrictInside r → ¬ Polyline.hitsRect pr.points r := by
  intro frame titleLines' dx dy hframe hdx hdy hwrap pr hpr r hSI
  have _hex := hexpand
  have _hfr := hframed
  have _hctx := hctx
  have _hdx := hdx
  have _hdy := hdy
  have _hwrap := hwrap
  have _hdxv : dx = dx := rfl
  have _hdyv : dy = dy := rfl
  have _htlv : titleLines' = titleLines' := rfl
  obtain ⟨hOut, hAtt⟩ := hroute frame hframe
  by_cases hfrom : pr.fromId = group.id
  · exact hAtt pr hpr (Or.inl hfrom) r hSI
  · by_cases hto : pr.toId = group.id
    · exact hAtt pr hpr (Or.inr hto) r hSI
    · exact fun hr => hOut pr hpr hfrom hto (hitsRect_of_strictInside hSI hr)
