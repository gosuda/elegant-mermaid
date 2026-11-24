import Elegant.Layered.RegionFlatC7
import Elegant.Layered.RegionFlatC6
import Elegant.Layered.RunStagePathFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CgShape

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open RegionImpl

private theorem r7_setDecls (nodes : Array ProperNode) (i : Nat) (n : ProperNode)
    (hkey : n.node.decl = (nodes.getD i default).node.decl) :
    (nodes.set! i n).toList.map (fun p => p.node.decl) =
      nodes.toList.map (fun p => p.node.decl) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, List.getElem?_map, Array.getElem?_toList, Array.getElem?_toList]
  rw [Array.set!_eq_setIfInBounds]
  by_cases heq : i = j
  · subst j
    by_cases hi : i < nodes.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hi, Array.getElem?_eq_getElem hi]
      have hget : nodes.getD i default = nodes[i]'hi := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      rw [hget] at hkey
      exact congrArg Option.some hkey
    · have hn : nodes[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt hi)
      have hs : (nodes.setIfInBounds i n)[i]? = none := by
        rw [Array.getElem?_setIfInBounds_self]
        simp [hi]
      rw [hs, hn]
  · rw [Array.getElem?_setIfInBounds_ne heq]

private theorem r7_reservedDeclsFold (pl : RegionPlacement) (cg : Graph)
    (labels : List MeasuredLabel) (clusters : List (RegionCluster × Nat))
    {start finish : List Int × Array ProperNode}
    (h : clusters.foldlM (fun acc q => do
      let c := q.1
      let footprint := max c.titleH
        (Loops.requiredHeight cg.slot (loopSizes cg.edges labels c.node cg.slot))
      if c.titleW < 0 ∨ footprint < 0 then throw LayoutError.domain
      else
        let x ← clusterPortR pl q.2 c.top acc.1
        let x ← clusterPortR pl q.2 c.bottom x
        let top := acc.2.getD c.top default
        let nodes := acc.2.set! c.top
          { top with node := { top.node with h := max (RouteImpl.nodeH pl.p c.top) footprint } }
        pure (x, nodes)) start = .ok finish) :
    finish.2.toList.map (fun p => p.node.decl) =
      start.2.toList.map (fun p => p.node.decl) := by
  induction clusters generalizing start with
  | nil =>
    have he : start = finish := Except.ok.inj h
    rw [he]
  | cons q rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, hrest⟩ := bind_ok h
    dsimp only at hmid
    split at hmid
    · simp at hmid
    · obtain ⟨_, _, hmid⟩ := bind_ok hmid
      obtain ⟨_, _, hmid⟩ := bind_ok hmid
      rw [ih hrest]
      rw [← congrArg Prod.snd (Except.ok.inj hmid)]
      exact r7_setDecls _ _ _ rfl

private theorem r7_reservedDecls {pl : RegionPlacement} {cg : Graph}
    {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) :
    out.2.nodes.map (fun p => p.node.decl) = pl.p.nodes.map (fun p => p.node.decl) := by
  unfold reservedPortsR at h
  obtain ⟨finish, hfold, hret⟩ := bind_ok h
  have hout : (finish.1, { pl.p with nodes := finish.2.toList }) = out := Except.ok.inj hret
  rw [← hout]
  change finish.2.toList.map (fun p => p.node.decl) = pl.p.nodes.map (fun p => p.node.decl)
  rw [r7_reservedDeclsFold pl cg labels pl.rm.clusters.zipIdx hfold, List.toList_toArray]

private theorem r7_crossCoordsDecls {P : Params} {rm : ComponentRegions}
    {cg : Graph} {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    out.2.2.2.nodes.map (fun n => n.node.decl) = p.nodes.map (fun n => n.node.decl) := by
  unfold crossCoordsR at h
  obtain ⟨_, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    exact absurd h (by simp)
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, _, h⟩ := bind_ok h
    obtain ⟨⟨_, _⟩, hreserved, hret⟩ := bind_ok h
    rw [← Except.ok.inj hret]
    exact r7_reservedDecls hreserved

private theorem r7_sizedDecl {P : Params} {exact : List Nat} {p : Proper}
    {v : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) :
    ∃ out : ProperNode, (sizeProperPortsX P exact p).nodes[v]? = some out ∧
      out.node.decl = n.node.decl := by
  unfold sizeProperPortsX
  simp only [List.getElem?_map, List.getElem?_zipIdx, hn, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  split <;> rfl

private theorem r7_titleDecl {titles : List (Int × Int)} {pad : Int} {p : Proper}
    {v : Nat} {n : ProperNode} (hn : p.nodes[v]? = some n) :
    ∃ out : ProperNode, (titleReservationsR titles pad p).nodes[v]? = some out ∧
      out.node.decl = n.node.decl := by
  have hv := (List.getElem?_eq_some_iff.mp hn).1
  unfold titleReservationsR
  rw [List.getElem?_append_left (by rw [List.length_map]; exact hv)]
  simp only [List.getElem?_map, hn, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  split <;> rfl

private theorem r7_coordinateDecl {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {p : Proper} {v : Nat} {n : ProperNode}
    (hn : p.nodes[v]? = some n) :
    ∃ out : ProperNode, (coordinateGraphR P exact spec p).nodes[v]? = some out ∧
      out.node.decl = n.node.decl := by
  let sized := sizeProperPortsX P exact p
  let titled := match spec with
    | none => titleReservations sized
    | some s => titleReservationsR s.titles P.clusterPad sized
  have he : coordinateGraphR P exact spec p = materializeDummyPaths
      (clearProxyExtents (OrderImpl.addClusterBorders titled P.clusterBorderW)) := by
    cases spec <;> rfl
  obtain ⟨ns, hs, hds⟩ := r7_sizedDecl (P := P) (exact := exact) hn
  obtain ⟨nt, ht, hdt⟩ : ∃ nt : ProperNode, titled.nodes[v]? = some nt ∧
      nt.node.decl = ns.node.decl := by
    cases spec with
    | none =>
      obtain ⟨nt, ht, hdt, _, _, _⟩ := titleReservations_decl hs
      exact ⟨nt, ht, hdt⟩
    | some s => exact r7_titleDecl (titles := s.titles) (pad := P.clusterPad) hs
  obtain ⟨nb, hb, hdb, _, _, _⟩ := addClusterBorders_decl (w := P.clusterBorderW) ht
  obtain ⟨nc, hc, hdc, _, _, _⟩ := clearProxyExtents_decl hb
  obtain ⟨nm, hm, hdm, _, _⟩ := materialize_decl hc
  rw [he]
  exact ⟨nm, hm, hdm.trans (hdc.trans (hdb.trans (hdt.trans hds)))⟩

theorem regionRun_keepsCandidateDecl {P : Params} {exact : List Nat}
    {spec : Option RegionSpec} {inp : Input} {cg cg' : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run))
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node) :
    ∃ out : ProperNode, run.proper.nodes[v]? = some out ∧ out.node.decl = node.decl := by
  obtain ⟨_, _, _, p0, labeled, pCoord, _, _, _, _, placed, q0, _, _, hs⟩ :=
    componentRunR_stages hrun
  have hranked : cg'.nodes[v]? = some node := by
    rcases hs.hRank with ⟨_, _, _, _, he, _⟩ | ⟨_, _, hrank⟩
    · rw [he]
      exact hnode
    · rw [rankEquivalentR_nodes_eq hrank]
      exact hnode
  obtain ⟨n0, h0, hd0, _, _, _⟩ := normalize_decl_prefix hs.hNorm hranked
  obtain ⟨n1, h1, hd1, _, _, _⟩ := addLabelNodes_decl _ p0 labeled hs.hLabels h0
  obtain ⟨n2, h2, hd2⟩ := r7_coordinateDecl (P := P) (exact := exact) (spec := spec) h1
  rw [hs.hCoord] at h2
  obtain ⟨n3, h3, hd3⟩ : ∃ n3 : ProperNode, placed.nodes[v]? = some n3 ∧
      n3.node.decl = n2.node.decl := by
    rcases hs.hPlaced with ⟨_, _, _, _, he⟩ | ⟨_, _, _, _, hcross⟩
    · rw [he]
      exact ⟨n2, h2, rfl⟩
    · have hkeys : placed.nodes.map (fun p => p.node.decl) =
          pCoord.nodes.map (fun p => p.node.decl) := r7_crossCoordsDecls hcross
      have hk : (placed.nodes.map (fun p => p.node.decl))[v]? = some n2.node.decl := by
        rw [hkeys, List.getElem?_map, h2, Option.map_some]
      rw [List.getElem?_map] at hk
      cases hfound : placed.nodes[v]? with
      | none => simp [hfound] at hk
      | some found =>
        simp only [hfound, Option.map_some, Option.some.injEq] at hk
        exact ⟨found, rfl, hk⟩
  obtain ⟨n4, h4, hd4, _, _, _⟩ := proxyWidths_decl_path hs.hProxy h3
  rw [← hs.hDrop, OrderImpl.dropSynthetic_nodes]
  exact ⟨n4, h4, hd4.trans (hd3.trans (hd2.trans (hd1.trans hd0)))⟩

private theorem r7_sceneGraphDecl {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source) :
    ∃ node : Node, execution.graph.nodes[key]? = some node ∧ node.decl = key := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  have hlineCount : execution.lines.length = inp.boxes.length :=
    (mapM_getElem? _ _ _ hlines).1.trans List.length_zipIdx
  obtain ⟨nodes, _, titles, hprepared, hcount, hmetadata⟩ :=
    measuredGraph_prepared_source execution.graph0_eq
  have hkey : key < nodes.length := by
    rw [hcount, hlineCount]
    exact (List.getElem?_eq_some_iff.mp hsource).1
  let prepared := inp.boxes.map fun box =>
    if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then { box with role := .node } else box
  let node := nodes[key]'hkey
  let marked := markOne prepared execution.params.clusterPad titles (node, 0 + key)
  have hprefix : key < (nodes.zipIdx.map (markOne prepared execution.params.clusterPad titles)).length := by
    rw [List.length_map, List.length_zipIdx]
    exact hkey
  have hmarked : execution.graph0.nodes[key]? = some marked := by
    rw [hprepared]
    change (Compound.markNodes prepared execution.params.clusterPad titles nodes)[key]? = some marked
    rw [markNodes_eq, List.getElem?_append_left hprefix]
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hkey,
      Option.map_some, marked, node]
  have hkeep : marked.decl = node.decl := by
    dsimp only [marked]
    unfold markOne
    split
    · rfl
    · split <;> rfl
  have hdecl := (hmetadata key node (List.getElem?_eq_getElem hkey)).1
  obtain ⟨out, hout, _, _, hdout⟩ := exactGraph_node_key execution.graph_eq hmarked
  exact ⟨out, hout, hdout.trans (hkeep.trans hdecl)⟩

theorem r7_exclusiveRunNodeDecl_holds (exactIds : List String)
    (idSets : List (String × List String)) : R7_ExclusiveRunNodeDecl exactIds idSets := by
  intro inp o res execution comp candidate run orderOptions cg cg' _ rs _ hcg hrun
    v key source hcomp hsource
  obtain ⟨node, hnode, hdecl⟩ := r7_sceneGraphDecl execution hsource
  have hcandidate : cg.nodes[v]? = some node := by
    rw [hcg]
    exact component_node_lookupR hcomp hnode
  obtain ⟨out, hout, hdout⟩ := regionRun_keepsCandidateDecl hrun hcandidate
  rw [RouteImpl.nodeDecl, hout]
  exact hdout.trans hdecl

theorem r6_exclusiveRunNodeDecl_holds (exactIds : List String)
    (idSets : List (String × List String)) : R6_ExclusiveRunNodeDecl exactIds idSets := by
  intro inp o res execution comp candidate spec cg run _ hrun v key source hcomp hsource
  obtain ⟨node, hnode, hdecl⟩ := r7_sceneGraphDecl execution hsource
  have hcandidate : (componentCandidateR spec execution.graph comp candidate).nodes[v]? =
      some node := component_node_lookupR hcomp hnode
  obtain ⟨out, hout, hdout⟩ := regionRun_keepsCandidateDecl hrun hcandidate
  rw [RouteImpl.nodeDecl, hout]
  exact hdout.trans hdecl

end Elegant.Layered.PipelineImpl
