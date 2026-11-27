import Elegant.Kinds.SwimlaneEndsSplitCutover
import Elegant.Layered.LaneBandsCoverageProof
import Elegant.Layered.FamilyAssembly

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Elegant
namespace Kinds

open Layered Layered.LaneBands

namespace SwimlaneEndsExecuted

open PipelineImpl

private theorem first_le_last_of_pairwise {α : Type} (f : α → Nat) {xs : List α}
    {first last : α} (hpair : xs.Pairwise (fun a b => f a < f b))
    (hfirst : xs.head? = some first) (hlast : xs.getLast? = some last) :
    f first ≤ f last := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hfirst
  cases rest with
  | nil =>
    have heq : first = last := Option.some.inj hlast
    exact Nat.le_of_eq (congrArg f heq)
  | cons next rest =>
    rw [List.getLast?_cons_cons] at hlast
    exact Nat.le_of_lt ((List.pairwise_cons.mp hpair).1 last (List.mem_of_getLast? hlast))

private theorem endpoints_length {pts : List Point} {start finish : Point}
    (hs : pts.head? = some start) (hf : pts.getLast? = some finish)
    (hne : start.y ≠ finish.y) : 1 < pts.length := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp hs
  cases rest with
  | nil => exact (hne (congrArg Point.y (Option.some.inj hf))).elim
  | cons next rest => simp

private theorem rank_gap_positive {P : Params} (hP : P.Valid)
    (p : Proper) (layers : List (List Nat)) (k : Nat) :
    0 < CoordsImpl.rankGapAt P.rankGap p layers k := by
  have hpos := hP.2.1
  unfold CoordsImpl.rankGapAt
  split
  · rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
    omega
  · omega

private theorem separated_rank_bands {P : Params} (hP : P.Valid)
    {p : Proper} {layers : List (List Nat)} {x y top : List Int} {r : Routing}
    (hcoords : RouteImpl.CoordFacts p layers x y top r
      (min P.nodeGap P.clusterPad) (CoordsImpl.rankGapAt P.rankGap p layers) P.slot)
    (hslots : ∀ k, k + 1 < layers.length → 0 ≤ (r.gaps.getD k default).slots)
    {i j : Nat} {li lj : List Nat} (hi : layers[i]? = some li)
    (hj : layers[j]? = some lj) (hij : i < j) :
    top.getD i 0 + RouteImpl.layerHeight p li < top.getD j 0 := by
  have hjlt := (List.getElem?_eq_some_iff.mp hj).1
  have histep := hcoords.band_step i li hi (by omega)
  have hmul := Int.mul_nonneg (show 0 ≤ P.slot by have := hP.2.2.1; omega)
    (hslots i (by omega))
  have hstrict := rank_gap_positive hP p layers i
  by_cases heq : i + 1 = j
  · rw [← heq]
    omega
  · have htail := RouteImpl.top_mono hcoords.rank_gap_nonneg
      (show 0 ≤ P.slot by have := hP.2.2.1; omega) hslots hcoords.band_step
      (j - (i + 2)) (i + 1) (by omega)
    rw [show i + 1 + (j - (i + 2)) + 1 = j by omega] at htail
    have hnonneg : 0 ≤ (layers.map (RouteImpl.layerHeight p)).getD (i + 1) 0 := by
      have hik : i + 1 < layers.length := by omega
      rw [RouteImpl.heights_getD (List.getElem?_eq_getElem hik)]
      exact RouteImpl.layerHeight_nonneg _ _
    omega

private theorem empty_chain_route_points {slot : Int} {p : Proper} {layers : List (List Nat)}
    {x y top heights : List Int} {reversed : List Bool} {widths : List Int}
    {r : RouteImpl.LaneRouting} {i : Nat} {rt : EdgeRoute}
    (hr : RouteImpl.routeWithLanes slot p layers x reversed widths = .ok r)
    (he : RouteImpl.edgesOf p i = [])
    (hroute : RouteImpl.laneRouteOf slot p y top heights r i = .ok rt) :
    rt.points = [] := by
  obtain ⟨base, _, _, hlanes⟩ := RouteImpl.routeWithLanes_spec hr
  have hruns : r.runs = RouteImpl.plannedLanes slot p base x reversed widths :=
    congrArg RouteImpl.LaneRouting.runs hlanes
  have hfind : r.runs.find? (fun lane => lane.original == i) = none := by
    apply List.find?_eq_none.mpr
    intro lane hmem htest
    rw [hruns] at hmem
    obtain ⟨key, index, hentry, rfl⟩ := RouteImpl.plannedLanes_mem hmem
    have hki : key = i := beq_iff_eq.mp htest
    have hkey : key ∈ RouteImpl.laneOriginals p reversed := by
      rw [← List.zipIdx_map_fst 0 (RouteImpl.laneOriginals p reversed)]
      exact List.mem_map.mpr ⟨(key, index), hentry, rfl⟩
    subst key
    simp [RouteImpl.laneOriginals, he] at hkey
  rw [RouteImpl.laneRouteOf, hfind, RouteImpl.routeOf, he] at hroute
  have heq : (⟨i, []⟩ : EdgeRoute) = rt := Except.ok.inj hroute
  exact congrArg EdgeRoute.points heq.symm

set_option maxHeartbeats 1000000 in
private theorem routed_cardinality {P : Params} (hP : P.Valid)
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hd : (cg.edges.map (·.decl)).Nodup) (hshape : CgShape cg)
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hclear : FrameClearance run.proper run.layers run.xs)
    {i : Nat} (hi : i < cg.edges.length) (edge : Edge) :
    edgePoints run i edge = [] ∨ 1 < (edgePoints run i edge).length := by
  obtain ⟨route, hget, hkey, hroute⟩ := PipelineImpl.componentRun_route_of_index hrun hi
  have hpoints : edgePoints run i edge = route.points := by
    simp only [edgePoints, List.getD_eq_getElem?_getD, hget, Option.getD_some]
  rw [hpoints]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouting, hr, _, _, hrouteList⟩ :=
    componentRun_spec hrun
  by_cases he : RouteImpl.edgesOf run.proper i = []
  · exact Or.inl (empty_chain_route_points hrouting he hroute)
  · right
    have hlay := (RouteImpl.routeWithLanes_geometry hrouting).1
    obtain ⟨hchain, _, hcoordsOf⟩ := componentRun_facts hP hd hshape hrun
    have hcoords := hcoordsOf hclear
    obtain ⟨first, hfirst⟩ : ∃ first, (RouteImpl.edgesOf run.proper i).head? = some first :=
      ⟨_, List.head?_eq_some_head he⟩
    obtain ⟨last, hlast⟩ : ∃ last, (RouteImpl.edgesOf run.proper i).getLast? = some last :=
      ⟨_, List.getLast?_eq_some_getLast he⟩
    obtain ⟨_, hsizes, _, hcov, hedge⟩ := RouteImpl.layersOk_spec hlay
    have hfirstEdge := hedge first (RouteImpl.mem_edgesOf (RouteImpl.mem_of_head' hfirst))
    have hlastEdge := hedge last (RouteImpl.mem_edgesOf (List.mem_of_getLast? hlast))
    let tail := (RouteImpl.edgeAt run.proper first).tail
    let head := (RouteImpl.edgeAt run.proper last).head
    let low := (rk run.proper.rank tail).toNat
    let high := (rk run.proper.rank head).toNat
    obtain ⟨lowLayer, hlo, htail, hlow⟩ := hcov _ hfirstEdge.1
    obtain ⟨highLayer, hhi, hhead, hhigh⟩ := hcov _ hlastEdge.2.1
    have hgapLe := first_le_last_of_pairwise (RouteImpl.gapOf run.proper)
      (chain_pairwise (R := RouteImpl.ChainLink run.proper) _
        (fun _ _ h => chain_gap_lt hlay h) _ (hchain i)) hfirst hlast
    change low ≤ (rk run.proper.rank (RouteImpl.edgeAt run.proper last).tail).toNat at hgapLe
    have hlastRank := hlastEdge.2.2
    change rk run.proper.rank head = rk run.proper.rank (RouteImpl.edgeAt run.proper last).tail + 1 at hlastRank
    obtain ⟨_, _, _, hlastTail⟩ := hcov _ hlastEdge.1
    have hlt : low < high := by
      change low < (rk run.proper.rank head).toNat
      omega
    have hslots := RouteImpl.routeWithLanes_gap_nonneg hrouting
    rw [hr] at hslots
    have hband := separated_rank_bands hP hcoords hslots hlo hhi hlt
    have htailBand := hcoords.node_in_band low lowLayer tail hlo htail hfirstEdge.1
      (Int.toNat_of_nonneg hlow).symm
    have hheadBand := hcoords.node_in_band high highLayer head hhi hhead hlastEdge.2.1
      (Int.toNat_of_nonneg hhigh).symm
    have hsep : RouteImpl.yAt run.ys tail + RouteImpl.nodeH run.proper tail <
        RouteImpl.yAt run.ys head :=
      Int.lt_of_le_of_lt htailBand.2 (Int.lt_of_lt_of_le hband hheadBand.1)
    have htailNonneg : 0 ≤ RouteImpl.nodeH run.proper tail := (hsizes _ hfirstEdge.1).2
    have hportSep : RouteImpl.tailPortY run.proper run.ys tail < RouteImpl.yAt run.ys head :=
      Int.lt_of_le_of_lt (RouteImpl.tailPortY_le_bottom htailNonneg) hsep
    have hrouteMem := List.mem_of_getElem? hget
    have hends := RouteImpl.laneSemantic_endpoints hrouting hrouteList route hrouteMem first last
      (by simpa only [hkey] using hfirst) (by simpa only [hkey] using hlast)
    split at hends
    · exact endpoints_length hends.1 hends.2 (Int.ne_of_gt hportSep)
    · refine endpoints_length hends.1 hends.2 (Int.ne_of_lt ?_)
      change RouteImpl.tailPortY run.proper run.ys tail < RouteImpl.yAt run.ys head
      exact hportSep

private theorem loop_cardinality {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    (hloops : componentLoops P cg run labels = .ok loops) {loop : Nat × LoopPlacement}
    (hloop : loop ∈ loops) : 1 < loop.2.points.length := by
  unfold componentLoops at hloops
  obtain ⟨groups, hgroups, hrest⟩ := bind_ok hloops
  have hgEq : groups.flatten = loops := Except.ok.inj hrest
  subst loops
  obtain ⟨group, hgrp, hloop⟩ := List.mem_flatten.mp hloop
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hgrp
  have hjout := (List.getElem?_eq_some_iff.mp hj).1
  have hspec := mapM_except_spec _ _ _ hgroups
  have hjin : j < (List.range cg.nodes.length).length := by rw [← hspec.1]; exact hjout
  obtain ⟨v, group', _, hg', hrun⟩ := hspec.2 j hjin hjout
  have heq : group' = group := Option.some.inj (hg'.symm.trans hj)
  subst group'
  obtain ⟨out, hout, hdone⟩ := bind_ok hrun
  have hgroup : ((loopEdges cg.edges v).zip out).map (fun q => (q.1.decl, q.2)) = group :=
    Except.ok.inj hdone
  rw [← hgroup] at hloop
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hloop
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hentry
  have hm := List.mem_of_getElem? (List.getElem?_zip_eq_some.mp hk).2
  split at hout
  · unfold Loops.exactLoops at hout
    dsimp only at hout
    split at hout
    · contradiction
    · split at hout
      · contradiction
      · split at hout
        · contradiction
        · split at hout
          · have h := Except.ok.inj hout
            subst out
            obtain ⟨_, _, hp⟩ := List.mem_map.mp hm
            rw [← hp]
            simp [Loops.exactPlacement]
          · contradiction
  · unfold Loops.loops at hout
    dsimp only at hout
    split at hout
    · contradiction
    · split at hout
      · contradiction
      · split at hout
        · contradiction
        · split at hout
          · have h := Except.ok.inj hout
            subst out
            obtain ⟨_, _, hp⟩ := List.mem_map.mp hm
            rw [← hp]
            simp [Loops.placement]
          · contradiction

private theorem component_route_array_size {P : Params} {inp : Input} {o : Options}
    {g : Graph} {labels : List MeasuredLabel}
    (comps : List (List Nat)) {start out : Acc}
    (h : comps.foldlM (fun acc comp => layoutComponent P inp o g acc comp labels) start =
      .ok out) : out.routes.size = start.routes.size := by
  induction comps generalizing start with
  | nil =>
    have heq : start = out := Except.ok.inj h
    rw [heq]
  | cons comp rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨next, hnext, hrest⟩ := bind_ok h
    exact (ih hrest).trans (layoutComponent_sizes hnext).2.1.symm

private theorem scene_cardinality {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) {rt : Route} (hrt : rt ∈ res.scene.routes) :
    rt.points = [] ∨ 1 < rt.points.length := by
  obtain ⟨key, hindex⟩ := List.mem_iff_getElem?.mp hrt
  have hlength : res.scene.routes.length = inp.routes.length := by
    rw [execution.scene_eq]
    exact Elegant.Layered.sceneOf_routes_length _ _ _ _ _ _
  have hkey : key < inp.routes.length := by
    rw [← hlength]
    exact (List.getElem?_eq_some_iff.mp hindex).1
  obtain ⟨packed, c, q, candidate, run, loops, _, i, edge,
    hpacked, hselected, hrun, hloops, hpart, hedge, hdecl⟩ :=
    execution.route_component_source hkey
  let cg := componentCandidate execution.graph q.1.1 candidate
  have hcgpart : q.1.1 ∈ components execution.graph := by
    rw [← (actual_components_parts (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem (List.mem_of_getElem? (zip_getElem?_left hselected))
  have hnd : (cg.edges.map (·.decl)).Nodup :=
    componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq q.1.1 candidate
  have hP := checkedParams_valid execution.checked
  have hcshape : CgShape cg := componentCandidate_shape (components_nodup _ _ hcgpart)
    (measuredGraph_shape execution.graph_eq) candidate
  have hc : FrameClearance run.proper run.layers run.xs :=
    frameClearanceSeam_holds
      (bracketInsidePremises
        (fun exec => dummyInsideProxyRowClear_executed' exec hwf hframed)
        (fun exec => titleCopySpanClearStrict_executed hwf hframed exec))
      execution q.1.1 candidate run (candidateOrder candidate) hcgpart hrun
  let pts := ((loops.find? (fun l => l.1 == edge.decl)).map (fun l => l.2.points)).getD
    (edgePoints run i edge)
  let bounds := placeBounds execution.params cg run execution.measured loops
  have hentry : q.1.2.routes[i]? = some (edge.decl,
      pts.map (PipelineImpl.shiftPoint (0 - bounds.minX) (0 - bounds.minY))) := by
    rw [hpart]
    dsimp only [placeComponent, placeBounds, cg, pts, bounds]
    simp only [List.getElem?_map, zipIdx_getElem?, hedge, Option.map_some, Nat.zero_add]
  have hpartNodup : (q.1.2.routes.map (·.1)).Nodup := by
    rw [hpart]
    exact PipelineImpl.placeComponent_routes_decls_nodup _ cg run 0 execution.measured loops hnd
  have hsize : execution.componentsAcc.routes.size = inp.routes.length := by
    have h := component_route_array_size _ execution.components_eq
    simpa only [Array.size_replicate] using h
  have hrouteSize : edge.decl < execution.componentsAcc.routes.size := by rw [hsize, hdecl]; exact hkey
  have hpackedRoute := Elegant.Layered.actual_components_packAcc_routes_getD
    (by rfl) execution.components_eq (measuredGraph_decls_nodup execution.graph_eq)
    packed execution.packed_eq hpacked c q hselected i _ _ [] hentry hpartNodup hrouteSize
  have hscene := Elegant.Layered.sceneOf_route_points execution.params inp o execution.lines
    execution.straightAcc execution.measured key hkey
  rw [← execution.scene_eq, hindex, Option.map_some, ← hdecl] at hscene
  have hkey' : edge.decl < inp.routes.length := by
    rw [hdecl]
    exact hkey
  have hpsize : execution.packedAcc.routes.size = inp.routes.length := by
    rw [Elegant.Layered.packAcc_routes_size execution.packed_eq, hsize]
  have hsizeS : edge.decl < execution.straightAcc.routes.size := by
    have hpb := execution.packedAcc_bounded execution.components_parts_bounded
    obtain ⟨_, _, _, _, _, hsz, _⟩ :=
      Elegant.Layered.PipelineImpl.straightenAcc_bounded execution.straight_eq hpb.routes_bounded
    rw [hsz, hpsize]
    exact hkey'
  have hgetS : execution.straightAcc.routes[edge.decl]? =
      some (execution.straightAcc.routes.getD edge.decl []) := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsizeS,
      Option.getD_some]
  rcases execution.route_cases hgetS with hpackedPts | hinst
  · have hbridgeEq : execution.packedAcc.routes.getD edge.decl [] =
        execution.straightAcc.routes.getD edge.decl [] := by
      rw [Array.getD_eq_getD_getElem?, hpackedPts, Option.getD_some]
    rw [← hbridgeEq, hpackedRoute] at hscene
    have heq := Option.some.inj hscene
    have hcard : pts = [] ∨ 1 < pts.length := by
      unfold pts
      cases hfind : loops.find? (fun l => l.1 == edge.decl) with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        exact routed_cardinality hP hnd hcshape hrun hc (List.getElem?_eq_some_iff.mp hedge).1 edge
      | some loop =>
        simp only [Option.map_some, Option.getD_some]
        exact Or.inr (loop_cardinality hloops (List.mem_of_find?_eq_some hfind))
    rw [heq]
    simpa using hcard
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hptsEq, _, _, _, _, _, _⟩ :=
      execution.installed_endpoints hinst
    rw [hptsEq] at hscene
    have heq := Option.some.inj hscene
    refine Or.inr ?_
    rw [heq]
    simp

private theorem recursive_cardinality (fuel : Nat) {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true) (h : layoutRecursive fuel inp o = .ok res) :
    ∀ rt ∈ res.scene.routes, rt.points = [] ∨ 1 < rt.points.length := by
  induction fuel generalizing inp o res with
  | zero =>
    obtain ⟨execution⟩ := layout_sceneExecution h
    exact fun _ hr => scene_cardinality execution hwf hframed hr
  | succ fuel ih =>
    rcases layoutRecursive_succ_sources h with ⟨_, hbase⟩ |
      ⟨group, _, _, _, _, _, hg, _, _, _, _, _, _⟩
    · obtain ⟨execution⟩ := layout_sceneExecution hbase
      exact fun _ hr => scene_cardinality execution hwf hframed hr
    · obtain ⟨P, metric, child, titleLines, parent, _, _, _, _,
        hP, hm, hchild, hwrap, hparent, _, _, _, _, _, _, _, hmerged, _⟩ :=
        layoutRecursive_embedding_assembly_sources (Model.boxIds_nodup hwf)
          (inputRoutesCovered hwf) hg h
      obtain ⟨hwfChild, hframedChild, hwfParent, hframedParent⟩ :=
        subInputWellFormed fuel inp o group P metric titleLines child parent hwf hframed
          hP hm hwrap hchild hparent
      intro rt hrt
      rw [hmerged] at hrt
      obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hrt
      rcases List.mem_append.mp (List.mem_of_find?_eq_some hfind) with hchildRoute | hparentRoute
      · obtain ⟨original, hm, rfl⟩ := List.mem_map.mp hchildRoute
        simpa using ih (inp := childSubInput inp group) (o := childSubOptions o group)
          (res := child) hwfChild hframedChild hchild original hm
      · exact ih (inp := parentSubInput inp group P titleLines child)
          (o := o) (res := parent) hwfParent hframedParent hparent rt hparentRoute

private theorem covered_index {bands : List Band} {id : String}
    (hcover : ∃ band ∈ bands, band.id = id ∨ id ∈ band.members) :
    ∃ i, bands.findIdx? (fun band => band.id == id || band.members.contains id) = some i := by
  obtain ⟨band, hb, hc⟩ := hcover
  refine ⟨_, List.findIdx?_eq_some_of_exists ⟨band, hb, ?_⟩⟩
  apply Bool.or_eq_true_iff.mpr
  rcases hc with hid | hmem
  · exact Or.inl (beq_iff_eq.mpr hid)
  · exact Or.inr (List.contains_iff_mem.mpr hmem)

/-- The family router emits no singleton route. C5 rules out empty routes and
supplies both endpoint lookups; lane admission covers both endpoints. The first
covering indices then decide whether the pin reroutes or shifts rigidly. -/
theorem swimlane_endsPremise_of_admitted {m : Model}
    (hnested : NestedInLane m.boxes) (hadmitted : layeredAdmissibleB (Swimlane.input m) = true) :
    SwimlaneEndsPremise m := by
  intro base hfam sp hsp rt hrt
  obtain ⟨hwf, hrec⟩ := layoutFamily_success hfam
  obtain ⟨hids, hdisj, hfix, _⟩ := layeredAdmissibleB_spec hadmitted m.options
  have hbase := layoutFamily_valid_of_seams hids hfix hdisj hfam
  have hC5 : Validator.C5 base.scene.layoutDump := hbase.2.2.2.2.1
  obtain ⟨p, _, fromBox, toBox, hhead, _, hfrom, hto, _, _⟩ := hC5 rt hrt
  have hlength : 1 < rt.points.length := by
    rcases recursive_cardinality _ hwf (layoutFamily_framed_parents hfam) hrec rt hrt with hnil | hlen
    · simp [hnil] at hhead
    · exact hlen
  change base.scene.boxes.find? (fun b => b.id == rt.fromId) = some fromBox at hfrom
  change base.scene.boxes.find? (fun b => b.id == rt.toId) = some toBox at hto
  have hcover := swimlane_pinBoxCoverage hfam hsp hnested
  have hfromId := beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == rt.fromId) hfrom)
  have htoId := beq_iff_eq.mp (List.find?_some (p := fun b : Box => b.id == rt.toId) hto)
  have hcoverFrom := hcover fromBox (List.mem_of_find?_eq_some hfrom)
  have hcoverTo := hcover toBox (List.mem_of_find?_eq_some hto)
  rw [hfromId] at hcoverFrom
  rw [htoId] at hcoverTo
  obtain ⟨fi, hfi⟩ := covered_index hcoverFrom
  obtain ⟨ti, hti⟩ := covered_index hcoverTo
  by_cases heq : fi = ti
  · right
    subst ti
    simp only [bandShift, List.find?_eq_bind_findIdx?_getElem?, hfi, hti]
  · exact Or.inl ⟨fi, ti, hfi, hti, heq, hlength⟩

end SwimlaneEndsExecuted
end Kinds
end Elegant
