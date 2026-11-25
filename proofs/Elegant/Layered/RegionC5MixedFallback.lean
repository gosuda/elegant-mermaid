import Elegant.Layered.RegionC5NativeEndpoints
import Elegant.Layered.RegionFlatC8a

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

elab "mixedC5AliasTerminal%" : term =>
  pure (Lean.mkConst (Lean.mkPrivateNameCore `Elegant.Layered.RegionC5NativeEndpoints
    `Elegant.Layered.PipelineImpl.aliasTerminal))

/-- A successful region fold supplies the selected exact run when the owning
component's region probe returned `none`. Packing is that of the original scene. -/
theorem regionC5FallbackBoundaryForOrdinaryOwnedRoute
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {key : Nat} {part : List Nat × Part} {out : Route}
    (hout : res.scene.routes[key]? = some out) (hmem : part ∈ e.componentsAcc.parts)
    (howned : key ∈ (componentGraph e.graph part.1).edges.map (·.decl))
    (hfallback : newComponentRegions (selectedC5TerminalSpec idSets e.params o e.lines)
      e.params inp (componentGraph e.graph part.1) = .ok none)
    (hne : out.fromId ≠ out.toId) : EmittedC5Boundary res.scene out := by
  obtain ⟨hparts, hall⟩ := actual_components_parts_geometryR (by rfl) e.components_eq
  have hc : part.1 ∈ components e.graph := by
    rw [← hparts]
    exact List.mem_map_of_mem hmem
  have hgeom : ActualPartGeometryR e.params exactIds
      (selectedC5TerminalSpec idSets e.params o e.lines) inp o e.graph e.measured part :=
    hall part hmem
  obtain ⟨index, _, actual, run, loops, area, used, _, _, _, ⟨regions, hregions, hused⟩,
    hrunR, hloops, hpart⟩ := hgeom
  have hnone : regions = none := Except.ok.inj (hregions.symm.trans hfallback)
  subst regions
  change used = none at hused
  subst used
  obtain ⟨hrun, hgraph⟩ := r8aC8a_runX_of_none hrunR
  subst actual
  let cg := componentCandidate e.graph part.1 index
  have howned' : key ∈ cg.edges.map Edge.decl := by
    change key ∈ (componentCandidate e.graph part.1 index).edges.map Edge.decl
    rwa [componentCandidate_decls]
  obtain ⟨edge, hedgeMem, hdecl⟩ := List.mem_map.mp howned'
  obtain ⟨i, hedge⟩ := List.mem_iff_getElem?.mp hedgeMem
  rw [← hdecl] at hout
  obtain ⟨native, raw, hnative, hraw, htail, hhead, htailBound, hheadBound⟩ :=
    c5NativeRouteOrigin e hc hrunR hedge
  obtain ⟨_, _, source, target, hsource, hsourceId, htarget, htargetId⟩ :=
    edgeOf_semantic_endpoints hraw
  have hscene := sceneOf_routes_getElem? e.params inp o e.lines e.packedAcc e.measured
    edge.decl (List.getElem?_eq_some_iff.mp hnative).1
  rw [← e.scene_eq] at hscene
  have hemit := Option.some.inj (hout.symm.trans hscene)
  have hfromId : source.id = out.fromId := by
    refine hsourceId.trans ?_
    rw [← (List.getElem?_eq_some_iff.mp hnative).2]
    exact (congrArg Route.fromId hemit).symm
  have htoId : target.id = out.toId := by
    refine htargetId.trans ?_
    rw [← (List.getElem?_eq_some_iff.mp hnative).2]
    exact (congrArg Route.toId hemit).symm
  have hneEdge : edge.tail ≠ edge.head := by
    intro heq
    have hsameLocal : edge.original.tail = edge.original.head := by
      cases hr : edge.reversed with
      | false => simpa only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] using heq
      | true => simpa only [Edge.original, hr, ↓reduceIte] using heq.symm
    have hsameAnchor : (aliasEdgeOf inp raw).tail = (aliasEdgeOf inp raw).head := by
      rw [hsameLocal] at htail
      exact Option.some.inj (htail.symm.trans hhead)
    let node := e.graph.nodes[(aliasEdgeOf inp raw).tail]'htailBound
    have hs := (List.getElem?_eq_getElem htailBound :
      e.graph.nodes[(aliasEdgeOf inp raw).tail]? = some node)
    have ht : e.graph.nodes[(aliasEdgeOf inp raw).head]? = some node := by
      rw [← hsameAnchor]
      exact hs
    have hsk := (c5NativeAliasTerminalNode e (front := true) (other := raw.head) hsource hs).1
    have htk := (c5NativeAliasTerminalNode e (front := false) (other := raw.tail) htarget ht).1
    have hs' := hsource
    rw [hsk.symm.trans htk] at hs'
    have hsameBox := Option.some.inj (hs'.symm.trans htarget)
    exact hne (hfromId.symm.trans ((congrArg ModelBox.id hsameBox).trans htoId))
  have hcgRun : componentRunX e.params (exactDecls exactIds inp) cg e.measured
      (candidateOrder index) = .ok run := hrun
  have hn : (cg.edges.map Edge.decl).Nodup :=
    componentCandidate_decls_nodup e.graph part.1 index
      (exactGraph_decls_nodup e.graph0_eq e.graph_eq)
  have hi := (List.getElem?_eq_some_iff.mp hedge).1
  have he := (List.getElem?_eq_some_iff.mp hedge).2
  have hloop : ∀ l ∈ loops, l.1 ≠ cg.edges[i].decl := by
    simpa only [he] using componentLoops_excludes_ordinary_decl hloops hn hedge hneEdge
  have hrev : (cg.edges.map (·.reversed)).getD i false = edge.reversed := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, hedge, Option.map_some, Option.getD_some]
  obtain ⟨first, last, hf, hl, ht, hh⟩ := X_componentRun_chain_endpoints hcgRun hedge hneEdge
  let bounds := placeBoundsX e.params cg run e.measured loops
  let move := shiftPoint (0 - bounds.minX) (-bounds.minY)
  obtain ⟨rt, start, finish, hrt, _, hplaced, hstart, hfinish, hgeometry⟩ :=
    x_runAttach_holds exactIds e.graph0_eq e.graph_eq (boxLines_length e.lines_eq) hwf hfp
      hc index hcgRun hi hf hl 0 loops hloop 0 .TB 0 bounds.minX bounds.minY
  rw [ht, hh, hrev] at hgeometry
  have untransport {p : Point} {r : Rect}
      (h : Validator.onBoundary
        (routePointTransport 0 .TB 0 bounds.minX bounds.minY bounds.minX bounds.minY p)
        (shiftRect 0 0 (orientRect .TB 0
          (shiftRect (bounds.minX - bounds.minX) (bounds.minY - bounds.minY) r)))) :
      Validator.onBoundary p r :=
    (onBoundary_shift _ _ _ _).mp ((onBoundary_shift_orient _ _ _ _ _ _).mp h)
  have hstartFrame : Validator.onBoundary start
      (if edge.reversed then frameRect e.params cg run edge.head
        else frameRect e.params cg run edge.tail) := untransport hgeometry.1
  have hfinishFrame : Validator.onBoundary finish
      (if edge.reversed then frameRect e.params cg run edge.tail
        else frameRect e.params cg run edge.head) := untransport hgeometry.2
  obtain ⟨packed, hpack, _⟩ := packAcc_components_disjoint e.packed_eq
  obtain ⟨c, hpartIndex⟩ := List.mem_iff_getElem?.mp hmem
  have hcount : packed.boxes.length = e.componentsAcc.parts.length := by
    simpa only [List.length_map] using Pack.pack_count hpack
  have hcPacked : c < packed.boxes.length := by
    rw [hcount]
    exact (List.getElem?_eq_some_iff.mp hpartIndex).1
  let q : (List Nat × Part) × Rect := (part, packed.boxes[c]'hcPacked)
  have hselected : (e.componentsAcc.parts.zip packed.boxes)[c]? = some q :=
    List.getElem?_zip_eq_some.mpr ⟨hpartIndex, List.getElem?_eq_getElem hcPacked⟩
  have hplace : q.1.2 = { placeComponentExact e.params cg run 0 e.measured loops with area := area } := hpart
  have hlocal : q.1.2.routes[i]? = some (edge.decl, rt.points.map move) := by
    rw [he] at hplaced
    rw [hplace]
    exact hplaced
  have emit {v j : Nat} {box : ModelBox} {front : Bool} {p : Point}
      (hindex : part.1[v]? = some j) (hbox : inp.boxes[j]? = some box)
      (hp : c5EndpointPoint front rt.points = some p)
      (hb : Validator.onBoundary p (frameRect e.params cg run v)) :
      ∃ p' b, c5EndpointPoint front out.points = some p' ∧
        res.scene.layoutDump.box? box.id = some b ∧ Validator.onBoundary p' b.rect := by
    have hv : v < cg.nodes.length := by
      change v < (componentCandidate e.graph part.1 index).nodes.length
      rw [componentCandidate_nodes]
      simpa only [componentGraph, List.length_map] using (List.getElem?_eq_some_iff.mp hindex).1
    exact c5TransportEndpoint e hwf hpack hselected hout hlocal
      (c5TransportPlacedFrameEntry hplace hv hindex) hbox
      (p := move p) (by rw [c5EndpointPoint_map, hp]; rfl)
      ((onBoundary_shift _ _ _ _).mpr hb)
  let AtPort (front : Bool) (v : Nat) : Prop :=
    ∃ px, c5EndpointPoint front rt.points = some ⟨px, run.ys.getD v 0⟩ ∧
      (RouteImpl.boxRect run.proper run.xs run.ys v).x ≤ px ∧
      px ≤ (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w
  have tailPort (hb : (cg.nodes.getD edge.tail default).border = 2) :
      AtPort (!edge.reversed) edge.tail := by
    obtain ⟨rt', px, hrt', hx₁, hx₂, hlast, hhead⟩ :=
      x_tailPort_holds exactIds (inp := inp) hcgRun hi hf (by rw [ht]; exact hb)
    have heq := Option.some.inj (hrt'.symm.trans hrt)
    subst rt'
    rw [ht] at hx₁ hx₂ hlast hhead
    rw [hrev] at hlast hhead
    refine ⟨px, ?_, hx₁, hx₂⟩
    cases hr : edge.reversed with
    | false => exact hhead hr
    | true => exact hlast hr
  have headPort : AtPort edge.reversed edge.head := by
    obtain ⟨px, hx₁, hx₂, hhead, hlast⟩ := X_flat_head_port_on_ys hcgRun hi hf hl hrt
    rw [hh] at hx₁ hx₂ hhead hlast
    rw [hrev] at hhead hlast
    refine ⟨px, ?_, hx₁, hx₂⟩
    cases hr : edge.reversed with
    | false => exact hlast hr
    | true => exact hhead hr
  have emitTerminal {v j : Nat} {box : ModelBox} {front : Bool} {p : Point}
      (hbox : inp.boxes[j]? = some box)
      (terminal : ((cg.nodes.getD v default).border = 0 ∧ part.1[v]? = some j) ∨
        ∃ top, SelectedC5SemanticGroupTerminal cg v top ∧ part.1[top]? = some j)
      (hp : c5EndpointPoint front rt.points = some p)
      (hb : Validator.onBoundary p (frameRect e.params cg run v))
      (bottomPort : (cg.nodes.getD v default).border = 2 → AtPort front v) :
      ∃ p' b, c5EndpointPoint front out.points = some p' ∧
        res.scene.layoutDump.box? box.id = some b ∧ Validator.onBoundary p' b.rect := by
    rcases terminal with ⟨_, hk⟩ | ⟨t, ⟨n, top, hv, htop, htag, hkind, hdecl⟩, hk⟩
    · exact emit hk hbox hp hb
    · rcases hkind with ⟨heq, _⟩ | hbottom
      · rw [← heq] at hk
        exact emit hk hbox hp hb
      · have hvb : (cg.nodes.getD v default).border = 2 := by
          simpa only [List.getD_eq_getElem?_getD, hv, Option.getD_some] using hbottom
        obtain ⟨px, hpoint, hlo, hhi⟩ := bottomPort hvb
        have htopBorder : (cg.nodes.getD t default).border = -2 := by
          simpa only [List.getD_eq_getElem?_getD, htop, Option.getD_some] using htag
        have hsameDecl : (cg.nodes.getD v default).decl = (cg.nodes.getD t default).decl := by
          simpa only [List.getD_eq_getElem?_getD, hv, htop, Option.getD_some] using hdecl
        have hframe := x_bottomBoundary_holds exactIds e.graph0_eq e.graph_eq
          (boxLines_length e.lines_eq) hwf hfp hc (candidate := index) hcgRun
          (v := v) (t := t) (px := px) hvb htopBorder hsameDecl ⟨hlo, hhi⟩
        exact emit hk hbox hpoint hframe
  have hs := mixedC5AliasTerminal% e hc hrunR (front := true) (other := raw.head)
    htail htailBound hsource
  have ht' := mixedC5AliasTerminal% e hc hrunR (front := false) (other := raw.tail)
    hhead hheadBound htarget
  cases hr : edge.reversed with
  | false =>
    simp only [Edge.original, hr, Bool.false_eq_true, ↓reduceIte] at hs ht'
    obtain ⟨start', fromBox, hstart', hfrom, hsb⟩ := emitTerminal (front := true)
      hsource hs hstart (by simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hstartFrame)
      (by simpa only [hr, Bool.not_false] using tailPort)
    obtain ⟨finish', toBox, hfinish', hto, htb⟩ := emitTerminal (front := false)
      htarget ht' hfinish (by simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hfinishFrame)
      (fun _ => by simpa only [hr] using headPort)
    exact ⟨start', finish', fromBox, toBox, hstart', hfinish', hfromId ▸ hfrom,
      htoId ▸ hto, hsb, htb⟩
  | true =>
    simp only [Edge.original, hr, ↓reduceIte] at hs ht'
    obtain ⟨start', fromBox, hstart', hfrom, hsb⟩ := emitTerminal (front := true)
      hsource hs hstart (by simpa only [hr, ↓reduceIte] using hstartFrame)
      (fun _ => by simpa only [hr] using headPort)
    obtain ⟨finish', toBox, hfinish', hto, htb⟩ := emitTerminal (front := false)
      htarget ht' hfinish (by simpa only [hr, ↓reduceIte] using hfinishFrame)
      (by simpa only [hr, Bool.not_true] using tailPort)
    exact ⟨start', finish', fromBox, toBox, hstart', hfinish', hfromId ▸ hfrom,
      htoId ▸ hto, hsb, htb⟩

/-- Ordinary C5 without distinguishing active and fallback owners. -/
theorem regionC5OrdinaryRouteBoundary
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (e : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    {out : Route} (hout : out ∈ res.scene.routes) (hne : out.fromId ≠ out.toId) :
    EmittedC5Boundary res.scene out := by
  rcases regionC5OrdinaryRouteBoundary_or_owningFallback e hwf hfp hout hne with
    hok | ⟨_, _, hroute, hmem, howned, hfallback⟩
  · exact hok
  · exact regionC5FallbackBoundaryForOrdinaryOwnedRoute e hwf hfp hroute hmem howned hfallback hne

end Elegant.Layered.PipelineImpl
