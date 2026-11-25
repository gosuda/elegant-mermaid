import Elegant.Layered.ExpandChildParentRouteClearProof
import Elegant.Layered.RecursiveC6
import Elegant.Layered.ExpandChildStepsFacts
import Elegant.Layered.MergedRouteIdsProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Lifting fixed-group frame clearance through `layoutRecursive`

Target theorems proved here:

* `layoutRecursive_frame_clear`: for every fuel, every input with
  `WellFormed (inputModel inp o)` and `framedParents inp = true` in which box
  `g` is a fixed-size leaf
  (`∃ entry, inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry`,
  the shape `parentInput_group_fixedEntry` delivers), and every
  `layoutRecursive fuel inp o = .ok res`: every route of `res` out of scope of
  `g` misses the frame rect of `g` in `res`. Proof by induction on fuel,
  mirroring `layoutRecursive_c6_of_flat`:
  - zero case and no-group case: `frame_clear_of_flat` (from `flat_frame_clear`
    via `layout_sceneExecution` and `frameRunBridge`).
  - successor case: the merge residual `ExpandChildFrameStep` applied to the
    child and parent induction hypotheses. The step itself is proved by cases
    in `expandChild_frame_step` (same-side pairs from the induction hypotheses;
    cross-side pairs remain as the two step residuals below).
* `expandChild_frame_step`: the one-expansion merge, proved by splitting the
  merged route (`expandChild_routes_eq`) and locating the merged frame by the
  box equation of `expandChild`. Same-side cases are proved (child route with
  child frame via child IH + shift transport + scope transport; parent route
  with parent frame via parent IH + scope transport). Cross-side cases stay as
  `ExpandChildChildRouteParentFrame` and `ExpandChildParentRouteChildFrame`.
* `expandChild_frame_scope_outside`: `ExpandChildFrameScopeOutside` from route
  endpoint coverage (`expandChild_parent_route_endpoints`) plus the one-scene
  residual `ExpandChildParentIsolated` (dump ancestors avoid the group).
* `expandChild_parentRouteFrameClear`: `ExpandChildParentRouteFrameClear` for
  an executed call, from the lift (applied to the parent scene) and the scope
  fact, via `expandChild_parentRouteFrame_of_recursion`.

Residuals (`ExpandChildChildRouteParentFrame`,
`ExpandChildParentRouteChildFrame`, `ExpandChildParentIsolated`): each about
ONE executed expansion or scene, each strictly simpler than the lifted goal,
each used below, each exercised on the probe copy
`proofs/wip/Probe/ParentFrameRouteLiftProbe.lean` (the original
`ParentFrameRouteProbe.lean` is untouched).
-/

/-! ## Flat case helper (zero case and no-group case) -/

/-- Flat case of the lift: a successful flat `layout` keeps every out-of-scope
route clear of a fixed group frame. From `flat_frame_clear` via the executed
`SceneExecution` and the bridge built from the fixed-size entry. -/
theorem frame_clear_of_flat
    (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      FrameClearanceSeam inp o res)
    (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ExclusiveRunNodeDecl inp o res)
    (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RunRouteEndpointIdsScoped inp o res)
    (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      WellFormed (inputModel inp o) → framedParents inp = true →
      RoutePartShelfPositive inp o res)
    (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
      comp ∈ components execution.graph →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopReservation (componentCandidate execution.graph comp candidate) run
        execution.measured v)
    (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
      (execution : SceneExecution inp o res),
      WellFormed (inputModel inp o) → framedParents inp = true →
      ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
      comp ∈ components execution.graph →
      ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
      componentRun execution.params
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok run →
      LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
        execution.measured v b)
    {inp : Input} {o : Options} {g : ModelBox} {res : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hfixed : ∃ entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry)
    (hlay : layout inp o = .ok res)
    {frame : Box}
    (hfind : res.scene.boxes.find? (fun box => box.id == g.id) = some frame)
    {r : Route} (hr : r ∈ res.scene.routes)
    (hfrom : r.fromId ≠ g.id) (hto : r.toId ≠ g.id)
    (hscope : g.id ∉ LayoutDump.routeScope res.scene.layoutDump r) :
    ¬ Polyline.hitsRect r.points frame.rect := by
  have _hfrom := hfrom
  have _hto := hto
  obtain ⟨entry, hentry⟩ := hfixed
  obtain ⟨execution⟩ := layout_sceneExecution hlay
  have hbridge : FrameRunBridge inp o res g :=
    frameRunBridge (fun _hb hbid => ⟨entry, by rw [hbid]; exact hentry⟩)
  have hb : frame ∈ res.scene.boxes := List.mem_of_find?_eq_some hfind
  have hframe : frame.id = g.id := by simpa using List.find?_some hfind
  exact flat_frame_clear execution (hclear inp o res hwf hframed) hbridge
    (hnodeDecl inp o res hwf hframed) (hscoped inp o res hwf hframed)
    (fun comp candidate run v hcomp hrun =>
      hloopRes inp o res execution hwf hframed comp candidate run v hcomp hrun)
    (fun comp candidate run v b hcomp hb0 hrun =>
      hloopSep inp o res execution hwf hframed comp candidate run v b hcomp hb0 hrun)
    (hpos inp o res hwf hframed) hr hb hframe hscope

/-! ## Successor merge residual (one expansion) -/

/-- One-expansion frame merge: the frame-clear conclusion for the merged scene
of a single `expandChild` call, from the same conclusions for the child and
parent scenes. Strictly simpler than the lifted goal (one merge, no fuel).
Proved by cases in `expandChild_frame_step`; the two cross-side cases stay as
the named residuals below. -/
def ExpandChildFrameStep (inp : Input) (parent child result : FamilyResult) : Prop :=
  ∀ (g : ModelBox),
    (∃ entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
    ∀ (gFrame : Box),
    result.scene.boxes.find? (fun box => box.id == g.id) = some gFrame →
    (∀ (cFrame : Box),
      child.scene.boxes.find? (fun box => box.id == g.id) = some cFrame →
      ∀ r ∈ child.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id →
        g.id ∉ LayoutDump.routeScope child.scene.layoutDump r →
        ¬ Polyline.hitsRect r.points cFrame.rect) →
    (∀ (pFrame : Box),
      parent.scene.boxes.find? (fun box => box.id == g.id) = some pFrame →
      ∀ r ∈ parent.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id →
        g.id ∉ LayoutDump.routeScope parent.scene.layoutDump r →
        ¬ Polyline.hitsRect r.points pFrame.rect) →
    ∀ r ∈ result.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id →
      g.id ∉ LayoutDump.routeScope result.scene.layoutDump r →
      ¬ Polyline.hitsRect r.points gFrame.rect

/-! ## Successor merge, proved by cases -/

/-- Cross-side residual (child route vs parent frame): a shifted child route
out of scope of the fixed group in the merged dump misses a parent-side
located frame of that group. One expansion step, tied to the executed call
through the call premises; strictly simpler than the merge (one route
origin, one frame side). Intended discharge: the shifted child route lies
inside the expanded group's content rect (the fit facts used by
`expandChild_c6`), while a parent-side leaf frame is disjoint from that
rect (or is the group itself, excluded by scope). Probed by the `RES-VIOL`
checks (child-origin merged routes) and the `FRAME-VIOL` checks (parent
scenes) of the probe copy. -/
def ExpandChildChildRouteParentFrame (fuel : Nat) (P : Params) (inp : Input)
    (o : Options) (group : ModelBox) (titleLines : List Measure.Line)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  expandChild P inp o group titleHeight parent child = .ok result →
  framedParents inp = true →
  ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child result →
  ExpandChildCallParams P inp o group titleLines titleHeight →
  ∀ (g : ModelBox),
    (∃ entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
    ∀ (gFrame : Box),
      parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame →
      ∀ (frame : Box) (metric : Measure.Metric) (titleLines₀ : List Measure.Line)
        (dx dy : Int),
        parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
        metricOf o.profile = .ok metric →
        StyledMeasure.wrap metric
          (Measure.wrapTarget metric.profile P.wrapWidth
            (if o.profile == .cell then o.maxWidth else 0))
          (inp.texts.getD
            ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
            .ok titleLines₀ →
        dx = frame.rect.x + (childInset group.direction P.clusterPad
            (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).x -
          P.canvasMargin →
        dy = frame.rect.y + (childInset group.direction P.clusterPad
            (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).y -
          P.canvasMargin →
        ExpandChildTitleWrapped P inp o group titleLines₀ →
        ∀ (cr : Route), cr ∈ child.scene.routes →
          cr.fromId ≠ g.id → cr.toId ≠ g.id →
          g.id ∉ LayoutDump.routeScope result.scene.layoutDump cr →
          ¬ Polyline.hitsRect (cr.points.map (shiftPoint dx dy)) gFrame.rect

/-- Cross-side residual (parent route vs child frame): a verbatim parent route
out of scope of the fixed group in the merged dump misses a child-side
located frame of that group, transported to the merged scene. One expansion
step, tied to the executed call through the call premises; strictly simpler
than the merge (one route origin, one frame side). Intended discharge: the
parent route out of scope of the expanded group misses its whole frame (the
lift applied to the expanded group itself, which is fixed in the parent
input), hence any frame it contains. Probed by the `FRAME-VIOL` checks and
the `SCOPE-ANC-VIOL` checks of the probe copy. -/
def ExpandChildParentRouteChildFrame (fuel : Nat) (P : Params) (inp : Input)
    (o : Options) (group : ModelBox) (titleLines : List Measure.Line)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  expandChild P inp o group titleHeight parent child = .ok result →
  framedParents inp = true →
  ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child result →
  ExpandChildCallParams P inp o group titleLines titleHeight →
  ∀ (g : ModelBox),
    (∃ entry : String × Size,
      inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
    ∀ (gFrame : Box),
      result.scene.boxes.find? (fun box => box.id == g.id) = some gFrame →
      ∀ (cb : Box),
        child.scene.boxes.find? (fun box => box.id == g.id) = some cb →
        ∀ (frame : Box) (metric : Measure.Metric) (titleLines₀ : List Measure.Line)
          (dx dy : Int),
          parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
          metricOf o.profile = .ok metric →
          StyledMeasure.wrap metric
            (Measure.wrapTarget metric.profile P.wrapWidth
              (if o.profile == .cell then o.maxWidth else 0))
            (inp.texts.getD
              ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
              .ok titleLines₀ →
          dx = frame.rect.x + (childInset group.direction P.clusterPad
              (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).x -
            P.canvasMargin →
          dy = frame.rect.y + (childInset group.direction P.clusterPad
              (titleLines₀.foldl (fun width line => max width line.width) 0) titleHeight).y -
            P.canvasMargin →
          ExpandChildTitleWrapped P inp o group titleLines₀ →
          gFrame = embedBox group.id dx dy cb →
          ∀ (pr : Route), pr ∈ parent.scene.routes →
            pr.fromId ≠ g.id → pr.toId ≠ g.id →
            g.id ∉ LayoutDump.routeScope result.scene.layoutDump pr →
            ¬ Polyline.hitsRect pr.points (shiftRect dx dy cb.rect)

/-- One-expansion frame merge, proved by cases. For an executed `expandChild`
call, every merged route out of scope of the fixed group misses its frame.
The merged route is split by `expandChild_routes_eq` (shifted child route or
verbatim parent route) and the merged frame is located by the box equation of
`expandChild` (embedded child box or verbatim parent box):
* child route with child frame: the child induction hypothesis, transported
  through the common shift (`not_hitsRect_shift`) with scope carried by
  `routeScope_subset` and `ancestors_mono` over the child lookup transport;
* parent route with parent frame: the parent induction hypothesis directly,
  with scope carried the same way over the parent lookup transport;
* child route with parent frame: `ExpandChildChildRouteParentFrame`;
* parent route with child frame: `ExpandChildParentRouteChildFrame`.
Lookup transports come from `expandChild_boxLookup_transport` (their offsets
only ever touch ids and parents, never geometry, so no pinning against the
route/box equations is needed); sizes from `expandChild_merge_bounds`. -/
theorem expandChild_frame_step
    {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
    {titleLines : List Measure.Line} {titleHeight : Int}
    {parent child result : FamilyResult}
    (hexpand : expandChild P inp o group titleHeight parent child = .ok result)
    (hframed : framedParents inp = true)
    (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child result)
    (hparams : ExpandChildCallParams P inp o group titleLines titleHeight)
    (hchildCross : ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight parent child result)
    (hparentCross : ExpandChildParentRouteChildFrame fuel P inp o group titleLines titleHeight parent child result) :
    ExpandChildFrameStep inp parent child result := by
  have hctx' : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child result := hctx
  have hparams' : ExpandChildCallParams P inp o group titleLines titleHeight := hparams
  obtain ⟨hwfC, hgC, _hpboxesC, hchildC, hparentC, hexpandC⟩ := hctx
  have _hexpandC := hexpandC
  obtain ⟨frame₀, metric₀, tl₀, _lines₀, dx₀, dy₀, hframe₀, hmetric₀, htitle₀, _hlines₀,
      hdx₀, hdy₀, _hcanvas, hboxes₀⟩ := expandChild_sources hexpand
  have hroutes₀ := expandChild_routes_eq hexpand frame₀ metric₀ tl₀ dx₀ dy₀
    hframe₀ hmetric₀ htitle₀ hdx₀ hdy₀
  have hwrap₀ : ExpandChildTitleWrapped P inp o group tl₀ := ⟨metric₀, hmetric₀, htitle₀⟩
  obtain ⟨hlenC, hlenP, _⟩ := expandChild_merge_bounds hwfC hgC hchildC hparentC hexpand
  obtain ⟨hcid, _hpid, hnC, _hnP, _hdisj⟩ := expandChild_selected_ids hwfC hchildC hparentC
  obtain ⟨_frame₁, _tl₁, dx₁, dy₁, _hframe₁, _hdx₁, _hdy₁, hchildLk, hparentLk⟩ :=
    expandChild_boxLookup_transport hwfC hchildC hparentC hexpand
  have hchildMono := ancestors_mono (child.scene.layoutDump) (result.scene.layoutDump)
    (embedBox group.id dx₁ dy₁)
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
  have hchildNodup : (child.scene.boxes.map (·.id)).Nodup := by
    rw [hcid]; exact hnC
  intro g hgEx gFrame hfindG hChildIH hParentIH r hr hfrom hto hscope
  have hgId : gFrame.id = g.id := by simpa using List.find?_some hfindG
  have hgmem : gFrame ∈ result.scene.boxes := List.mem_of_find?_eq_some hfindG
  rw [hboxes₀] at hgmem
  obtain ⟨model, hmodel, hfindM⟩ := List.mem_filterMap.mp hgmem
  have hfgId : gFrame.id = model.id := by simpa using List.find?_some hfindM
  have hmodelId : model.id = g.id := hfgId.symm.trans hgId
  have hframeSide : (∃ native : Box, native ∈ child.scene.boxes ∧ native.id = g.id ∧
      gFrame = embedBox group.id dx₀ dy₀ native ∧
      child.scene.boxes.find? (fun box => box.id == g.id) = some native) ∨
      (parent.scene.boxes.find? (fun box => box.id == g.id) = some gFrame) := by
    rw [List.find?_append] at hfindM
    cases hleft : (child.scene.boxes.map (embedBox group.id dx₀ dy₀)).find?
        (fun box => box.id == model.id) with
    | some x =>
      rw [hleft] at hfindM
      have hgX : gFrame = x := (Option.some.inj hfindM).symm
      have hxmem : x ∈ (child.scene.boxes.map (embedBox group.id dx₀ dy₀)) :=
        List.mem_of_find?_eq_some hleft
      obtain ⟨native, hnatmem, hnatEq⟩ := List.mem_map.mp hxmem
      have hxId : x.id = model.id := by simpa using List.find?_some hleft
      have hnatId : native.id = model.id := by
        rw [← hnatEq] at hxId
        exact hxId
      have hnatG : native.id = g.id := hnatId.trans hmodelId
      have hkeyNative : child.scene.boxes.find? (fun box => box.id == g.id) = some native := by
        have hkey := Assembly.keyed_lookup_eq (·.id) child.scene.boxes hchildNodup native hnatmem
        rw [hnatG] at hkey
        exact hkey
      have hgEmb : gFrame = embedBox group.id dx₀ dy₀ native := by
        rw [hgX]; exact hnatEq.symm
      exact Or.inl ⟨native, hnatmem, hnatG, hgEmb, hkeyNative⟩
    | none =>
      rw [hleft] at hfindM
      have hfindP : parent.scene.boxes.find? (fun box => box.id == model.id) = some gFrame :=
        hfindM
      rw [hmodelId] at hfindP
      exact Or.inr hfindP
  have _hmodel := hmodel
  rw [hroutes₀] at hr
  obtain ⟨modelR, _hmodelR, hfindR⟩ := List.mem_filterMap.mp hr
  have hrItems : r ∈ ((child.scene.routes.map fun (route : Route) =>
      { route with points := route.points.map (shiftPoint dx₀ dy₀) }) ++
      parent.scene.routes) := List.mem_of_find?_eq_some hfindR
  rcases List.mem_append.mp hrItems with hrc | hrp
  · obtain ⟨cr, hcr, hcrEq⟩ := List.mem_map.mp hrc
    have hrP : r.points = cr.points.map (shiftPoint dx₀ dy₀) := by rw [← hcrEq]
    have hrF : r.fromId = cr.fromId := by rw [← hcrEq]
    have hrT : r.toId = cr.toId := by rw [← hcrEq]
    have hcrFrom : cr.fromId ≠ g.id := by rw [← hrF]; exact hfrom
    have hcrTo : cr.toId ≠ g.id := by rw [← hrT]; exact hto
    rcases hframeSide with ⟨native, hnatmem, hnatG, hgEmb, hkeyNative⟩ | hfindP
    · have _hnatmem := hnatmem
      have _hnatG := hnatG
      have hscopeC : g.id ∉ LayoutDump.routeScope child.scene.layoutDump cr := by
        intro hmem
        exact hscope (routeScope_subset hrF.symm hrT.symm
          (fun x hx => hchildMono r.fromId (by rw [hrF]; exact hx))
          (fun x hx => hchildMono r.toId (by rw [hrT]; exact hx)) g.id hmem)
      have hmiss := hChildIH native hkeyNative cr hcr hcrFrom hcrTo hscopeC
      rw [hrP, hgEmb]
      exact not_hitsRect_shift dx₀ dy₀ cr.points native.rect hmiss
    · have hscopeS : g.id ∉ LayoutDump.routeScope result.scene.layoutDump cr := by
        have h := hscope
        unfold LayoutDump.routeScope at h ⊢
        rwa [hrF, hrT] at h
      rw [hrP]
      exact hchildCross hexpand hframed hctx' hparams' g hgEx gFrame hfindP
        frame₀ metric₀ tl₀ dx₀ dy₀ hframe₀ hmetric₀ htitle₀ hdx₀ hdy₀ hwrap₀
        cr hcr hcrFrom hcrTo hscopeS
  · rcases hframeSide with ⟨native, hnatmem, hnatG, hgEmb, hkeyNative⟩ | hfindP
    · have _hnatmem := hnatmem
      have _hnatG := hnatG
      rw [hgEmb]
      exact hparentCross hexpand hframed hctx' hparams' g hgEx gFrame hfindG
        native hkeyNative frame₀ metric₀ tl₀ dx₀ dy₀
        hframe₀ hmetric₀ htitle₀ hdx₀ hdy₀ hwrap₀ hgEmb
        r hrp hfrom hto hscope
    · have hparScope : g.id ∉ parent.scene.layoutDump.routeScope r := by
        intro hmem
        exact hscope (routeScope_subset rfl rfl
          (fun x hx => hparentMono r.fromId hx)
          (fun x hx => hparentMono r.toId hx) g.id hmem)
      exact hParentIH gFrame hfindP r hrp hfrom hto hparScope

 /-! ## The lift -/

 /-- Frame clearance for a fixed group through `layoutRecursive`: every route of
 the recursive result that is out of scope of the fixed group misses its frame.
 By induction on fuel, mirroring `layoutRecursive_c6_of_flat`. The fixed entry
 propagates to both sub-inputs (`selectInput` keeps the fixed tables; the parent
 input only appends the expanded group's entry); sub-input well-formedness comes
 from `SubInputWellFormed`; each successor merge is closed by
 `expandChild_frame_step` from the two cross-side residuals. -/
 theorem layoutRecursive_frame_clear
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
       comp ∈ components execution.graph →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopReservation (componentCandidate execution.graph comp candidate) run
         execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
       comp ∈ components execution.graph →
       ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
         execution.measured v b)
     (hsub : SubInputWellFormed)
     (hchildCross : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
       (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight parent child res)
     (hparentCross : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
       (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentRouteChildFrame fuel P inp o group titleLines titleHeight parent child res) :
     ∀ (fuel : Nat) (inp : Input) (o : Options) (g : ModelBox) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       (∃ entry : String × Size,
         inp.fixedSizes.find? (fun fixed => fixed.1 == g.id) = some entry) →
       layoutRecursive fuel inp o = .ok res →
       ∀ (frame : Box),
       res.scene.boxes.find? (fun box => box.id == g.id) = some frame →
       ∀ r ∈ res.scene.routes, r.fromId ≠ g.id → r.toId ≠ g.id →
         g.id ∉ LayoutDump.routeScope res.scene.layoutDump r →
         ¬ Polyline.hitsRect r.points frame.rect := by
   intro fuel
   induction fuel with
   | zero =>
       intro inp o g res hwf hframed hfixed h frame hfind r hr hfrom hto hscope
       exact frame_clear_of_flat hclear hnodeDecl hscoped hpos hloopRes hloopSep
         hwf hframed hfixed h hfind hr hfrom hto hscope
   | succ fuel ih =>
       intro inp o g res hwf hframed hfixed h
       rcases layoutRecursive_succ_sources h with ⟨_, hlayout⟩ |
         ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hchild, hwrap,
           hparentAt, hexpandAt⟩
       · intro frame hfind r hr hfrom hto hscope
         exact frame_clear_of_flat hclear hnodeDecl hscoped hpos hloopRes hloopSep
           hwf hframed hfixed hlayout hfind hr hfrom hto hscope
       · obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
           hsub fuel inp o group P metric titleLines child parent
             hwf hframed hP hm hwrap hchild hparentAt
         have hctx : ExpandChildCallContext fuel P inp o group titleLines _
             parent child res :=
           ⟨hwf, hg, rfl, hchild, hparentAt, hexpandAt⟩
         have hparams : ExpandChildCallParams P inp o group titleLines _ :=
           ⟨hP, rfl, ⟨metric, hm, hwrap⟩⟩
         obtain ⟨entry, hentry⟩ := hfixed
         have hfixedChild : ∃ entry : String × Size,
             (childSubInput inp group).fixedSizes.find?
               (fun fixed => fixed.1 == g.id) = some entry :=
           ⟨entry, hentry⟩
         have hfixedParent : ∃ entry : String × Size,
             (parentSubInput inp group P titleLines child).fixedSizes.find?
               (fun fixed => fixed.1 == g.id) = some entry := by
           refine ⟨entry, ?_⟩
           have hfix : (parentSubInput inp group P titleLines child).fixedSizes =
               inp.fixedSizes ++
                 [(group.id, childFrameSize group.direction P.clusterPad
                   (titleLines.foldl (fun width line => max width line.width) 0)
                   ((max 1 titleLines.length : Int) * P.lineH)
                   ⟨child.scene.canvas.w - 2 * P.canvasMargin,
                     child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
           rw [hfix, List.find?_append, hentry]
           rfl
         have hChildIH := ih (childSubInput inp group)
           (childSubOptions o group) g child
           hwfChild hframedChild hfixedChild hchild
         have hParentIH := ih (parentSubInput inp group P titleLines child) o g parent
           hwfParent hframedParent hfixedParent hparentAt
         have hstep : ExpandChildFrameStep inp parent child res :=
           expandChild_frame_step hexpandAt hframed hctx hparams
             (hchildCross fuel P inp o group titleLines _ parent child res
               hexpandAt hframed hctx hparams)
             (hparentCross fuel P inp o group titleLines _ parent child res
               hexpandAt hframed hctx hparams)
         intro frame hfind r hr hfrom hto hscope
         exact hstep g ⟨entry, hentry⟩
           frame hfind hChildIH hParentIH r hr hfrom hto hscope

 /-! ## Scope from endpoints (one parent scene) -/

 /-- One-scene scope residual for the executed parent call: no other parent box
 carries the group among its dump ancestors. Strictly simpler than
 `ExpandChildFrameScopeOutside` (no routes, no scope). -/
 def ExpandChildParentIsolated (group : ModelBox) (parent : FamilyResult) : Prop :=
   ∀ pb ∈ parent.scene.boxes, pb.id ≠ group.id →
     group.id ∉ parent.scene.layoutDump.ancestors pb.id

 /-- Scope from endpoints for the executed parent call: a parent route whose
 endpoints differ from the group id has the group id outside its dump route
 scope. Route-endpoint coverage comes from `expandChild_parent_route_endpoints`
 (proved by induction on fuel in `MergedRouteIdsProof`); ancestor isolation is
 the remaining residual. The rest is list reasoning on `routeScope`. -/
 theorem expandChild_frame_scope_outside
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hiso : ExpandChildParentIsolated group parent)
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ExpandChildFrameScopeOutside fuel P inp o group titleLines titleHeight
       parent child res := by
   have hcov := expandChild_parent_route_endpoints hexpand hframed hctx hparams
   intro _frame _hfind pr hpr hfrom hto
   obtain ⟨hcovFrom, hcovTo⟩ := hcov pr hpr
   obtain ⟨pbFrom, hpbFrom, hpidFrom⟩ := List.mem_map.mp hcovFrom
   obtain ⟨pbTo, hpbTo, hpidTo⟩ := List.mem_map.mp hcovTo
   have hneFrom : pbFrom.id ≠ group.id := by rw [hpidFrom]; exact hfrom
   have hneTo : pbTo.id ≠ group.id := by rw [hpidTo]; exact hto
   have hancFrom : group.id ∉ parent.scene.layoutDump.ancestors pr.fromId := by
     rw [← hpidFrom]
     exact hiso pbFrom hpbFrom hneFrom
   have hancTo : group.id ∉ parent.scene.layoutDump.ancestors pr.toId := by
     rw [← hpidTo]
     exact hiso pbTo hpbTo hneTo
   intro hmem
   unfold LayoutDump.routeScope at hmem
   rcases List.mem_append.mp hmem with hfront | hrest
   · rcases List.mem_append.mp hfront with hhead | hAanc
     · obtain hEq | hRest := List.mem_cons.mp hhead
       · exact hfrom hEq.symm
       · obtain hEq₂ | hNil := List.mem_cons.mp hRest
         · exact hto hEq₂.symm
         · exact absurd hNil (by simp)
     · exact hancFrom hAanc
   · exact hancTo hrest

 /-! ## The wanted fact for an executed call -/

 /-- Parent route frame clearance for an executed `expandChild` call: every
 parent route out of scope of the group misses the group frame. From the lift
 (applied to the parent scene, whose fixed entry is `parentInput_group_fixedEntry`)
 and the scope fact, via `expandChild_parentRouteFrame_of_recursion`. -/
 theorem expandChild_parentRouteFrameClear
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hclear : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       FrameClearanceSeam inp o res)
     (hnodeDecl : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ExclusiveRunNodeDecl inp o res)
     (hscoped : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RunRouteEndpointIdsScoped inp o res)
     (hpos : ∀ (inp : Input) (o : Options) (res : FamilyResult),
       WellFormed (inputModel inp o) → framedParents inp = true →
       RoutePartShelfPositive inp o res)
     (hloopRes : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v : Nat),
       comp ∈ components execution.graph →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopReservation (componentCandidate execution.graph comp candidate) run
         execution.measured v)
     (hloopSep : ∀ (inp : Input) (o : Options) (res : FamilyResult)
       (execution : SceneExecution inp o res),
       WellFormed (inputModel inp o) → framedParents inp = true →
       ∀ (comp : List Nat) (candidate : Nat) (run : Run) (v b : Nat),
       comp ∈ components execution.graph →
       ((componentCandidate execution.graph comp candidate).nodes.getD b default).border = 0 →
       componentRun execution.params
         (componentCandidate execution.graph comp candidate) execution.measured
         (candidateOrder candidate) = .ok run →
       LoopFootprintSeparation (componentCandidate execution.graph comp candidate) run
         execution.measured v b)
     (hsub : SubInputWellFormed)
     (hchildCross : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
       (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildChildRouteParentFrame fuel P inp o group titleLines titleHeight parent child res)
     (hparentCross : ∀ (fuel : Nat) (P : Params) (inp : Input) (o : Options) (group : ModelBox)
       (titleLines : List Measure.Line) (titleHeight : Int) (parent child res : FamilyResult),
       expandChild P inp o group titleHeight parent child = .ok res →
       framedParents inp = true →
       ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res →
       ExpandChildCallParams P inp o group titleLines titleHeight →
       ExpandChildParentRouteChildFrame fuel P inp o group titleLines titleHeight parent child res)
     (hiso : ExpandChildParentIsolated group parent)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res)
     (hparams : ExpandChildCallParams P inp o group titleLines titleHeight) :
     ExpandChildParentRouteFrameClear group parent := by
   have hctx' : ExpandChildCallContext fuel P inp o group titleLines titleHeight parent child res := hctx
   have hparams' : ExpandChildCallParams P inp o group titleLines titleHeight := hparams
   obtain ⟨hwfC, hgC, _hpboxesC, hchildC, hparentC, hexpandC⟩ := hctx
   have hrec : ExpandChildFrameRecursion fuel P inp o group titleLines titleHeight
       parent child res := by
     intro frame hfind pr hpr hfrom hto hscopeP
     obtain ⟨hP, hheight, hwrap⟩ := hparams
     have _hheight := hheight
     obtain ⟨metric, hm, hwrapEq⟩ := hwrap
     obtain ⟨_, _, hwfParent, hframedParent⟩ :=
       hsub fuel inp o group P metric titleLines child parent
         hwfC hframed hP hm hwrapEq hchildC hparentC
     have hfixedParent : ∃ entry : String × Size,
         (parentSubInput inp group P titleLines child).fixedSizes.find?
           (fun fixed => fixed.1 == group.id) = some entry := by
       have hpred := List.find?_some hgC
       simp only [Bool.and_eq_true] at hpred
       obtain ⟨_, hnotfixed⟩ := hpred
       have hany : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
         simpa using hnotfixed
       have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
         List.find?_eq_none.mpr (List.any_eq_false.mp hany)
       have hfix : (parentSubInput inp group P titleLines child).fixedSizes =
           inp.fixedSizes ++
             [(group.id, childFrameSize group.direction P.clusterPad
               (titleLines.foldl (fun width line => max width line.width) 0)
               ((max 1 titleLines.length : Int) * P.lineH)
               ⟨child.scene.canvas.w - 2 * P.canvasMargin,
                 child.scene.canvas.h - 2 * P.canvasMargin⟩)] := rfl
       refine ⟨(group.id, childFrameSize group.direction P.clusterPad
         (titleLines.foldl (fun width line => max width line.width) 0)
         ((max 1 titleLines.length : Int) * P.lineH)
         ⟨child.scene.canvas.w - 2 * P.canvasMargin,
           child.scene.canvas.h - 2 * P.canvasMargin⟩), ?_⟩
       rw [hfix, List.find?_append, hnone]
       simp
     have hstep : ExpandChildFrameStep inp parent child res :=
       expandChild_frame_step hexpandC hframed hctx' hparams'
         (hchildCross fuel P inp o group titleLines _ parent child res
           hexpandC hframed hctx' hparams')
         (hparentCross fuel P inp o group titleLines _ parent child res
           hexpandC hframed hctx' hparams')
     exact layoutRecursive_frame_clear hclear hnodeDecl hscoped hpos hloopRes hloopSep
       hsub hchildCross hparentCross fuel (parentSubInput inp group P titleLines child) o group parent
       hwfParent hframedParent hfixedParent hparentC frame hfind pr hpr hfrom hto hscopeP
   have hscope : ExpandChildFrameScopeOutside fuel P inp o group titleLines titleHeight
       parent child res :=
     expandChild_frame_scope_outside hiso hexpandC hframed hctx' hparams'
   exact expandChild_parentRouteFrame_of_recursion hrec hscope

 end Elegant.Layered.PipelineImpl
