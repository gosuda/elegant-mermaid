import Elegant.Layered.RecursiveFit
import Elegant.Layered.RouteTransport
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import ElegantGeometry.Validator

set_option autoImplicit false

/-!
# C6 through `layoutRecursive`: routes miss exclusive boxes outside their scope

`layoutRecursive_c6_of_flat` lifts clause 6 of the layout validator (a route
does not meet the interior of an exclusive box outside its route scope)
through the recursive group expansion, assuming the flat clause for leaf
layouts.  The per-expansion facts are packaged in `ExpandChildC6Step`.

The geometric core is unit U7 (`FrameRouteClearance`), stated as
`expandChild_childRoutes_inFrame`: the routes an expanded child group
contributes to the merged scene stay inside that child's frame — every
point of an embedded child route lies in the frame rectangle, because the
shifted child canvas is contained in the frame (the fit fact of
`ExpandChildFits` / `ExpandChildFitAt`) and every child-route point lies in
the child canvas.  A route confined to its own frame therefore misses every
exclusive box of a foreign frame, which is exactly the `hforeign`
component of `ExpandChildC6Step`.
-/

namespace Elegant.Layered.PipelineImpl

open Validator

/-- A point lies inside the closed rectangle `r`. -/
def pointWithin (p : Point) (r : Rect) : Prop :=
  r.x ≤ p.x ∧ p.x ≤ r.x + r.w ∧ r.y ≤ p.y ∧ p.y ≤ r.y + r.h

/-- Frame-clearance seam of the flat clause: every component run that the
successful flat layout executes keeps its frame clearance.  This is the
same per-component premise `FrameClearRuns` (in `FlatC6.lean`) states; it
is restated locally so this module does not depend on the flat clause
module. -/
abbrev FrameClearanceSeam (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat)
    (run : Run) (orderOptions : OrderOptions),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run →
    FrameClearance run.proper run.layers run.xs

/-- The flat clause of the brief: a single non-recursive layout keeps every
route clear of exclusive boxes outside the route's scope.  Assumed here,
discharged at the family seam; the well-formedness, framed-parent, and
frame-clearance premises are the ones the flat clause proof consumes. -/
abbrev FlatC6 : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    FrameClearanceSeam inp o res →
    layout inp o = .ok res → Validator.C6 res.scene.layoutDump


/-- Per-expansion seam about the recursion: whenever the input that
`layoutRecursive` splits at `group` is well-formed and has framed parents,
both sub-inputs the recursion builds are well-formed and have framed
parents as well.  The parent sub-input is stated at the values
`layoutRecursive` actually constructs, so the family seam discharges this
from `selectInput` preservation alone. -/
def SubInputWellFormed : Prop :=
  ∀ (fuel : Nat) (inp : Input) (o : Options) (group : ModelBox)
    (P : Params) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (child parent : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    checkedParams o.profile inp.kind = .ok P →
    metricOf o.profile o.fontFamily = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines →
    layoutRecursive fuel (childSubInput inp group) (childSubOptions o group) = .ok child →
    layoutRecursive fuel (parentSubInput inp group P titleLines child) o = .ok parent →
    WellFormed (inputModel (childSubInput inp group) (childSubOptions o group)) ∧
    framedParents (childSubInput inp group) = true ∧
    WellFormed (inputModel (parentSubInput inp group P titleLines child) o) ∧
    framedParents (parentSubInput inp group P titleLines child) = true

/-- Unit U7 (`FrameRouteClearance`): a route of an expanded child group
stays inside that child's frame.  Every child-scene route, once shifted by
the expansion offsets, has all its points in the frame rectangle: the
shifted child canvas lies inside the frame and the child-route points lie
in the child canvas. -/
theorem expandChild_childRoutes_inFrame
    {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    {frame : Box} {dx dy : Int}
    (_h : expandChild P inp o group titleHeight parent child = .ok result)
    (hfit : frame.rect.Contained
      (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)))
    (hbnd : ∀ rt ∈ child.scene.routes, ∀ p ∈ rt.points,
      pointWithin p (Validator.canvasRect child.scene.layoutDump)) :
    ∀ r ∈ result.scene.routes, (∃ cr ∈ child.scene.routes,
        r.points = cr.points.map (shiftPoint dx dy)) →
      ∀ p ∈ r.points, pointWithin p frame.rect := by
  intro r _ ⟨cr, hcr, hrP⟩ p hp
  rw [hrP] at hp
  obtain ⟨q, hq, hpq⟩ := List.mem_map.mp hp
  subst hpq
  have hc := hbnd cr hcr q hq
  simp only [pointWithin, shiftPoint, shiftRect, Validator.canvasRect,
    Rect.Contained] at hfit hc ⊢
  omega

/-- The route list of a successful `expandChild`: one merged route per
input route model, child routes shifted by the expansion offsets, resolved
in favour of the child scene on id collisions. -/
theorem expandChild_routes_eq {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int} {parent child res : FamilyResult}
    (h : expandChild P inp o group titleHeight parent child = .ok res)
    (frame : Box) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (dx dy : Int)
    (hframe : parent.scene.boxes.find? (fun box : Box => box.id == group.id) = some frame)
    (hmetric : metricOf o.profile o.fontFamily = .ok metric)
    (htitle : StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines)
    (hdx : dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
        P.canvasMargin)
    (hdy : dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
        P.canvasMargin) :
    res.scene.routes = inp.routes.filterMap (fun model =>
      ((child.scene.routes.map (fun route : Route =>
            { route with points := route.points.map (shiftPoint dx dy) })) ++
        parent.scene.routes).find? (fun route => route.id == model.id)) := by
  unfold expandChild at h
  simp only [hframe] at h
  obtain ⟨_, hframeOk, h⟩ := bind_ok' h
  have hfr : frame = _ := Except.ok.inj hframeOk
  subst hfr
  obtain ⟨metric0, hmetric0, h⟩ := bind_ok' h
  have hm : metric0 = metric := Except.ok.inj (hmetric0.symm.trans hmetric)
  subst hm
  obtain ⟨titleLines0, htitle0, h⟩ := bind_ok' h
  have htl : titleLines0 = titleLines := Except.ok.inj (htitle0.symm.trans htitle)
  subst htl
  obtain ⟨_, _, h⟩ := bind_ok' h
  obtain ⟨_, _, h⟩ := bind_ok' h
  have he := Except.ok.inj h
  subst he
  rw [hdx, hdy]

/-- Route scope is monotone under ancestor inclusion: with equal endpoints
and, for each endpoint, an inclusion between the two ancestor lists, every
scoped id of the source dump is scoped in the target dump. -/
theorem routeScope_subset {dD fD : LayoutDump} {rF rR : Route}
    (hF : rF.fromId = rR.fromId) (hT : rF.toId = rR.toId)
    (hA : ∀ x, x ∈ dD.ancestors rF.fromId → x ∈ fD.ancestors rR.fromId)
    (hB : ∀ x, x ∈ dD.ancestors rF.toId → x ∈ fD.ancestors rR.toId) :
    ∀ x, x ∈ dD.routeScope rF → x ∈ fD.routeScope rR := by
  intro x hx
  unfold LayoutDump.routeScope at hx ⊢
  rw [hF, hT] at hx
  rcases List.mem_append.mp hx with hfront | hrest
  · rcases List.mem_append.mp hfront with hhead | hAanc
    · rcases List.mem_cons.mp hhead with rfl | hfront2
      · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
      · rcases List.mem_cons.mp hfront2 with hlast | hnil
        · exact List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inr
            (List.mem_cons.mpr (Or.inl hlast)))))
        · exact absurd hnil (by simp)
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (hA _ (by rw [hF]; exact hAanc)))))
  · exact List.mem_append.mpr (Or.inr (hB _ (by rw [hT]; exact hrest)))

/-- The id of a located dump box is the lookup key. -/
theorem boxLookupId {d : LayoutDump} {y : String} {yb : Box}
    (hyb : d.box? y = some yb) : yb.id = y :=
  beq_iff_eq.mp (List.find?_some (p := fun (b : Box) => b.id == y) hyb)

/-- Ancestor walks are monotone under a lookup transport: if every box of
the source dump resolves in the target dump to an image that keeps the
parent pointer whenever it is nonempty, then every id on a source ancestor
chain also lies on the corresponding target ancestor chain (the target has
at least as much fuel).  Rewriting an empty parent to a fresh group root
only appends ids, never removes them. -/
theorem ancestors_mono (childD finD : LayoutDump) (E : Box → Box)
    (hres : ∀ (y : String) (yb : Box), childD.box? y = some yb →
      finD.box? y = some (E yb))
    (hpar : ∀ (yb : Box), yb.parent ≠ "" → (E yb).parent = yb.parent)
    (hlen : childD.boxes.length ≤ finD.boxes.length) :
    ∀ (x : String), childD.ancestors x ⊆ finD.ancestors x := by
  have key : ∀ (n m : Nat) (x : String), n ≤ m →
      List.Subset (LayoutDump.ancestors.go childD n x)
        (LayoutDump.ancestors.go finD m x) := by
    intro n
    induction n with
    | zero =>
        intro m _ x y hy
        simp only [LayoutDump.ancestors.go] at hy
        exact absurd hy (by simp)
    | succ n ih =>
        intro m x hnm y hy
        cases hm : m with
        | zero => exact absurd hnm (by omega)
        | succ m' =>
          cases hpx : childD.box? x with
          | none =>
              simp only [LayoutDump.ancestors.go, hpx] at hy
              exact absurd hy (by simp)
          | some yb =>
            by_cases hpb : yb.parent = ""
            · simp only [LayoutDump.ancestors.go, hpx, ite_eq_left hpb] at hy
              exact absurd hy (by simp)
            · have hEp : (E yb).parent = yb.parent := hpar yb hpb
              simp only [LayoutDump.ancestors.go, hpx, ite_eq_right hpb] at hy
              simp only [LayoutDump.ancestors.go, hres x yb hpx, hEp,
                ite_eq_right hpb]
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact List.Mem.head _
              · exact List.Mem.tail _ (ih m' yb.parent (by omega) hy')
  intro x
  exact key childD.boxes.length finD.boxes.length x hlen

/-- The per-expansion facts the C6 merge needs: box lookup transport for
both merged scenes, scene sizes, the two cross-scene clearance facts
(foreign-frame clearance for child routes, frame clearance for parent
routes), and the scope anchors `{group.id} ++ ancestors group.id` of the
expanded group inside the merged dump. -/
def ExpandChildC6Step (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (lines : List (List Measure.Line)) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    metricOf o.profile o.fontFamily = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines →
    boxLines metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      inp = .ok lines →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    (∀ b : Box, child.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some (embedBox group.id dx dy b)) ∧
    (∀ b : Box, parent.scene.layoutDump.box? b.id = some b →
        result.scene.layoutDump.box? b.id = some b) ∧
    child.scene.boxes.length ≤ result.scene.boxes.length ∧
    parent.scene.boxes.length ≤ result.scene.boxes.length ∧
    (∀ cr ∈ child.scene.routes, ∀ pb ∈ parent.scene.boxes, pb.exclusive = true →
        pb.id ∉ (group.id :: parent.scene.layoutDump.ancestors group.id) →
        ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) pb.rect) ∧
    (∀ pr ∈ parent.scene.routes, ∀ cb ∈ child.scene.boxes, cb.exclusive = true →
        ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect)) ∧
    (∀ rt ∈ child.scene.routes,
        ∀ x ∈ (group.id :: parent.scene.layoutDump.ancestors group.id),
          x ∈ result.scene.layoutDump.ancestors rt.fromId ∨
            x ∈ result.scene.layoutDump.ancestors rt.toId)

/-- `expandChild` preserves C6.  A merged route is either an embedded child
route (shifted points, same endpoints) or a parent-scene route verbatim,
and a merged box is either an embedded child box or a parent-scene box:

* child route vs child box: the child clause transports through the common
  shift, because the child route scope is included in the merged scope
  (`ancestors_mono` via the child lookup transport);
* child route vs parent box: the group and its ancestors are scope anchors
  of every embedded route, so a box outside them lies in a foreign frame
  and is missed by `hforeign`;
* parent route vs parent box: the parent clause transports, because parent
  ancestor chains resolve unchanged in the merged dump;
* parent route vs child box: every child box is missed by `hmissChild`,
  which is stronger than the scope exclusion C6 asks for (child ids never
  occur on a parent-scene ancestor chain). -/
theorem expandChild_c6 {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleHeight : Int} {parent child result : FamilyResult}
    (hchildC6 : Validator.C6 child.scene.layoutDump)
    (hparentC6 : Validator.C6 parent.scene.layoutDump)
    (hstep : ExpandChildC6Step P inp o group titleHeight parent child result)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C6 result.scene.layoutDump := by
  obtain ⟨frame, metric, titleLines, lines, dx, dy, hframe, hmetric, htitle,
    hlines, hdx, hdy, _hcanvas, hboxes⟩ := expandChild_sources h
  obtain ⟨hchildLk, hparentLk, hlenC, hlenP, hforeign, hmissChild, hanchor⟩ :=
    hstep frame metric titleLines lines dx dy hframe hmetric htitle hlines hdx hdy
  have hroutes := expandChild_routes_eq h frame metric titleLines dx dy hframe
    hmetric htitle hdx hdy
  have hchildMono := ancestors_mono (child.scene.layoutDump) (result.scene.layoutDump)
    (embedBox group.id dx dy)
    (fun y yb hyb => by
      have key := hchildLk yb (by rw [boxLookupId hyb]; exact hyb)
      rw [boxLookupId hyb] at key
      exact key)
    (fun yb hne => by
      have hfalse : (yb.parent == "") = false := by
        cases h : (yb.parent == "") with
        | true => exact absurd (beq_iff_eq.mp h) hne
        | false => rfl
      simp [embedBox, hfalse])
    hlenC
  have hparentMono := ancestors_mono (parent.scene.layoutDump) (result.scene.layoutDump)
    (fun b => b)
    (fun y yb hyb => by
      have key := hparentLk yb (by rw [boxLookupId hyb]; exact hyb)
      rw [boxLookupId hyb] at key
      exact key)
    (fun _ _ => rfl) hlenP
  intro r hr b hb hex hscope
  simp only [Scene.layoutDump] at hr hb
  change r ∈ result.scene.routes at hr
  change b ∈ result.scene.boxes at hb
  rw [hroutes] at hr
  obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hr
  have hrItems : r ∈ (child.scene.routes.map (fun route =>
        { route with points := route.points.map (shiftPoint dx dy) })) ++
      parent.scene.routes := List.mem_of_find?_eq_some hfind
  rw [hboxes] at hb
  obtain ⟨_, -, hfindB⟩ := List.mem_filterMap.mp hb
  have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes := List.mem_of_find?_eq_some hfindB
  rcases List.mem_append.mp hrItems with hrc | hrp
  · -- r is an embedded child route
    obtain ⟨cr, hcr, hcrEq⟩ := List.mem_map.mp hrc
    have hrP : r.points = cr.points.map (shiftPoint dx dy) := by
      rw [← hcrEq]
    have hrF : r.fromId = cr.fromId := by
      rw [← hcrEq]
    have hrT : r.toId = cr.toId := by
      rw [← hcrEq]
    rcases List.mem_append.mp hbItems with hbc | hbp
    · -- exclusive box is an embedded child box: the child clause transports
      obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hbex' : cb.exclusive = true := by
        rw [← hbEq] at hex
        simpa [embedBox] using hex
      have hbid : b.id = cb.id := by
        rw [← hbEq]; rfl
      have hcbScope : cb.id ∉ child.scene.layoutDump.routeScope cr := by
        intro hmem
        refine absurd ?_ hscope
        rw [hbid]
        exact routeScope_subset hrF.symm hrT.symm
          (fun x hx => hchildMono r.fromId (by rw [hrF]; exact hx))
          (fun x hx => hchildMono r.toId (by rw [hrT]; exact hx)) cb.id hmem
      have hmiss := hchildC6 cr (by simp only [Scene.layoutDump]; exact hcr)
        cb (by simp only [Scene.layoutDump]; exact hcb) hbex' hcbScope
      rw [hrP, ← hbEq]
      exact not_hitsRect_shift dx dy cr.points cb.rect hmiss
    · -- exclusive box is a parent-scene box: foreign-frame clearance
      by_cases hin : b.id ∈ (group.id :: parent.scene.layoutDump.ancestors group.id)
      · rcases hanchor cr hcr b.id hin with h1 | h1
        · refine absurd ?_ hscope
          simp only [LayoutDump.routeScope, hrF, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr h1)
        · refine absurd ?_ hscope
          simp only [LayoutDump.routeScope, hrT, List.mem_append, List.mem_cons]
          exact Or.inr h1
      · rw [hrP]
        exact hforeign cr hcr b hbp hex hin
  · -- r is a parent-scene route
    rcases List.mem_append.mp hbItems with hbc | hbp
    · -- child box: parent routes miss child exclusive boxes
      obtain ⟨cb, hcb, hbEq⟩ := List.mem_map.mp hbc
      have hbex' : cb.exclusive = true := by
        rw [← hbEq] at hex
        simpa [embedBox] using hex
      have hbrect : b.rect = shiftRect dx dy cb.rect := by
        rw [← hbEq]; rfl
      rw [hbrect]
      exact hmissChild r hrp cb hcb hbex'
    · -- parent box: the parent clause transports
      have hparScope : b.id ∉ parent.scene.layoutDump.routeScope r := by
        intro hmem
        exact absurd (routeScope_subset rfl rfl
          (fun x hx => hparentMono r.fromId hx)
          (fun x hx => hparentMono r.toId hx) b.id hmem) hscope
      exact hparentC6 r hrp b hbp hex hparScope

/-- Route endpoints name boxes of the model: the `RoutesCovered` fact for
a well-formed layered input (restated here; the ExecutedPortsFacts version
is private). -/
theorem inputRoutesCovered {inp : Input} {o : Options}
    (hwf : WellFormed (inputModel inp o)) : RoutesCovered inp := by
  unfold WellFormed modelWellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hroutes⟩, _⟩, _⟩ := hwf
  intro route hroute
  have h := List.all_eq_true.mp hroutes route hroute
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.mem_map] at h
  exact h

/-- `layoutRecursive` preserves C6 given the flat clause for leaf layouts,
the global frame-clearance seam, the sub-input well-formedness seam, and,
for every expansion the recursion performs, the per-expansion facts of
`ExpandChildC6Step`.  Well-formedness and framed parents are carried
through the recursion by `SubInputWellFormed`, so the flat clause applies
at every `layout` leaf the recursion performs. -/
theorem layoutRecursive_c6_of_flat (hflat : FlatC6)
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hsub : SubInputWellFormed)
    (hgeo : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
      (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
      expandChild P inp o group titleHeight parent child = .ok res →
      framedParents inp = true →
      ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
      ExpandChildCallParams P inp o group titleLines titleHeight →
      ExpandChildC6Step P inp o group titleHeight parent child res) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      layoutRecursive fuel inp o = .ok res → Validator.C6 res.scene.layoutDump := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hwf hframed h
      exact hflat inp o res hwf hframed (hclear inp o res hwf hframed) h
  | succ fuel ih =>
      intro inp o res hwf hframed h
      have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      have hcovered : RoutesCovered inp := inputRoutesCovered hwf
      rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
        ⟨group, _P0, _metric0, _child0, _titleLines0, _parent0, hg, _, _, _, _, _, _⟩
      · exact hflat inp o res hwf hframed (hclear inp o res hwf hframed) hlayout
      · obtain ⟨P, metric, child, titleLines, parent, _frame, _lines, _dx, _dy,
          hP, hm, hchild, hwrap, hparentAt, hexpandAt, _, _, _, _, _, _, _, _⟩ :=
          layoutRecursive_embedding_assembly_sources hboxIds hcovered hg h
        obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
          hsub fuel inp o group P metric titleLines child parent hwf hframed hP hm hwrap
            hchild hparentAt
        have hchildC6 := ih _ _ _ hwfChild hframedChild hchild
        have hparentC6 := ih _ _ _ hwfParent hframedParent hparentAt
        have hstep := hgeo fuel P inp o group titleLines _ parent child res hexpandAt hframed
          ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩ ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
        exact expandChild_c6 hchildC6 hparentC6 hstep hexpandAt

end Elegant.Layered.PipelineImpl
