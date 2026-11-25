import Elegant.Layered.RegionActualParts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-!
# Region-run chain facts.

Replays of the exact-run chain facts over `componentRunR`:
* `componentRunR_proper_chains_lengthR` (twin of `componentRunX_proper_chains_length`),
* `componentRunR_edges_declsR` (declaration preservation of `rankEquivalentR`),
* `componentRunR_coordinate_chainsR` (coordinate/proper chain agreement).
-/
/-- A mapped zip-indexed list keeps every declaration when each mapped edge does. -/
private theorem rrc_map_decl_of_mem (l : List Edge) (n : Nat) (f : Edge × Nat → Edge)
    (hf : ∀ q ∈ l.zipIdx n, (f q).decl = q.1.decl) :
    (((l.zipIdx n).map f).map (·.decl) = l.map (·.decl)) := by
  induction l generalizing n with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have htail := ih (n + 1) (fun q hq => hf q (List.mem_cons_of_mem (e, n) hq))
    rw [htail]
    have hhead := hf (e, n) (by simp)
    simpa using congrArg (fun d => d :: rest.map (·.decl)) hhead

/-- Rank rewriting preserves edge declarations (only orientations change). -/
private theorem rrc_rankEquivalentR_decls {rm : ComponentRegions} {cg cg' : Graph}
    {ranks : List Int} {budget : Bool}
    (h : rankEquivalentR rm cg = .ok (ranks, cg', budget)) :
    cg'.edges.map (·.decl) = cg.edges.map (·.decl) := by
  unfold rankEquivalentR at h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨conds, _, h⟩ := bind_ok h
    obtain ⟨out1, _, h⟩ := bind_ok h
    obtain ⟨flagsAndOut, _, h⟩ := bind_ok h
    obtain ⟨ranked, _, h⟩ := bind_ok h
    have he := Except.ok.inj h
    have hmap := congrArg (fun q : List Int × Graph × Bool => q.2.1.edges.map (·.decl)) he
    dsimp only at hmap
    rw [← hmap]
    refine rrc_map_decl_of_mem cg.edges 0 _ ?_
    intro q _
    split
    · rfl
    · split
      · rfl
      · exact (Edge.reverse_identity q.1).1
/-- The region coordinate graph keeps the labeled chains in both modes. -/
private theorem rrc_coordinateGraphR_chains (P : Params) (exact : List Nat)
    (spec : Option RegionSpec) (p : Proper) :
    (coordinateGraphR P exact spec p).chains = p.chains := by
  cases spec with
  | none => exact coordinateGraphX_chains P exact p
  | some s =>
    unfold coordinateGraphR materializeDummyPaths clearProxyExtents
    exact (OrderImpl.addClusterBorders_metadata
      (titleReservationsR s.titles P.clusterPad (sizeProperPortsX P exact p))
      P.clusterBorderW).2.1
/-- `reservedPortsR` only rewrites nodes, so chains are unchanged. -/
private theorem rrc_reservedPortsR_chains {pl : RegionPlacement}
    {cg : Graph} {labels : List MeasuredLabel} {x : List Int} {out : List Int × Proper}
    (h : reservedPortsR pl cg labels x = .ok out) :
    out.2.chains = pl.p.chains := by
  unfold reservedPortsR at h
  obtain ⟨fo, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hc := congrArg (fun q : List Int × Proper => q.2.chains) he
  exact hc.symm
/-- `crossCoordsR` only rewrites coordinates, layers, and lanes: chains are unchanged. -/
private theorem rrc_crossCoordsR_chains {P : Params} {rm : ComponentRegions} {cg : Graph}
    {labels : List MeasuredLabel} {p : Proper} {minimum : RegionConstraints}
    {layers : List (List Nat)} {out : List Int × List (List Nat) × List (Option Int) × Proper}
    (h : crossCoordsR P rm cg labels p minimum layers = .ok out) :
    out.2.2.2.chains = p.chains := by
  unfold crossCoordsR at h
  obtain ⟨children, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · have hF : False := by
      simp only [bind, Except.bind] at h
      exact absurd h (by simp)
    exact hF.elim
  · obtain ⟨ngs, _, h⟩ := bind_ok h
    obtain ⟨x, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨⟨alloc, x2⟩, halloc, h⟩ := bind_ok h
    obtain ⟨⟨x3, p3⟩, hres, h⟩ := bind_ok h
    have he := Except.ok.inj h
    have hfin := (congrArg (fun q :
      List Int × List (List Nat) × List (Option Int) × Proper => q.2.2.2.chains) he).symm
    exact hfin.trans (rrc_reservedPortsR_chains hres)
/-- Bundle the peeled run equations into the chain spec. -/
private theorem rrc_pack_run_spec {exact : List Nat}
    {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {cg1 : Graph} {ranks : List Int} {p0 labeled : Proper}
    {ord : OrderResult} {rankBudget : Bool}
    {placed : List Int × List (List Nat) × List (Option Int) × Proper}
    {resv : List Int × List Int} {yt : List Int × List Int} {lanes : RouteImpl.LaneRouting}
    {routes : List EdgeRoute} {q0 : Proper} {xs' : List Int}
    (hp0 : normalize cg1 ranks = .ok p0)
    (hlab : Labels.addLabelNodes cg1 p0 (componentLabels cg1 labels) = .ok labeled)
    (hccArm : placed.2.snd.snd.chains = labeled.chains)
    (hrouted : proxyWidths placed.2.snd.snd placed.1 = .ok (q0, xs'))
    (HD : cg1.edges.map (·.decl) = cg.edges.map (·.decl))
    (he : (cg1, ⟨OrderImpl.dropSynthetic q0, placed.2.fst, xs', resv.1, resv.2,
      lanes.routing, routes, rankBudget || ord.budgetExhausted, lanes, placed.2.snd.snd,
      placed.1, yt.1,
      (cg1.nodes.zipIdx.filterMap fun q => if exact.contains q.1.decl then some q.2 else none)⟩) =
      (cg', run)) :
    ∃ (cgmid : Graph) (ranks : List Int) (p0 labeled : Proper) (coordXs : List Int)
      (q0 : Proper) (xs' : List Int),
      normalize cgmid ranks = .ok p0 ∧
      Labels.addLabelNodes cgmid p0 (componentLabels cgmid labels) = .ok labeled ∧
      run.coordinateProper.chains = labeled.chains ∧
      proxyWidths run.coordinateProper coordXs = .ok (q0, xs') ∧
      run.proper = OrderImpl.dropSynthetic q0 ∧
      cgmid.edges.map (·.decl) = cg.edges.map (·.decl) ∧
      cg'.edges.map (·.decl) = cg.edges.map (·.decl) := by
  have hC0 : run.coordinateProper = placed.2.snd.snd :=
    (congrArg (fun q : Graph × Run => q.2.coordinateProper) he).symm
  have hP : run.proper = OrderImpl.dropSynthetic q0 :=
    (congrArg (fun q : Graph × Run => q.2.proper) he).symm
  have hcc : run.coordinateProper.chains = labeled.chains := by
    rw [hC0]; exact hccArm
  have hprox : proxyWidths run.coordinateProper placed.1 = .ok (q0, xs') := by
    rw [hC0]; exact hrouted
  have hdecls : cg'.edges.map (·.decl) = cg.edges.map (·.decl) := by
    have hcg1 : cg' = cg1 := (congrArg (fun q : Graph × Run => q.1) he).symm
    rw [hcg1]; exact HD
  exact ⟨cg1, ranks, p0, labeled, placed.1, q0, xs', hp0, hlab, hcc, hprox, hP, HD, hdecls⟩
/-- The region run equations behind the chain facts (both ranking arms). -/
private theorem rrc_run_chain_spec {P : Params} {exact : List Nat} {spec : Option RegionSpec}
    {inp : Input} {cg cg' : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact spec inp cg labels orderOptions = .ok (cg', run)) :
    ∃ (cgmid : Graph) (ranks : List Int) (p0 labeled : Proper) (coordXs : List Int)
      (q0 : Proper) (xs' : List Int),
      normalize cgmid ranks = .ok p0 ∧
      Labels.addLabelNodes cgmid p0 (componentLabels cgmid labels) = .ok labeled ∧
      run.coordinateProper.chains = labeled.chains ∧
      proxyWidths run.coordinateProper coordXs = .ok (q0, xs') ∧
      run.proper = OrderImpl.dropSynthetic q0 ∧
      cgmid.edges.map (·.decl) = cg.edges.map (·.decl) ∧
      cg'.edges.map (·.decl) = cg.edges.map (·.decl) := by
  unfold componentRunR at h; obtain ⟨rs, _, h⟩ := bind_ok h; dsimp only at h
  split at h
  · obtain ⟨rr, _, h⟩ := bind_ok h
    obtain ⟨⟨ranks, cg1, rankBudget⟩, hranked, h⟩ := bind_ok h; dsimp only at h
    obtain ⟨p0, hp0, h⟩ := bind_ok h; obtain ⟨labeled, hlab, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨ord, _, h⟩ := bind_ok h
    obtain ⟨xs, _, h⟩ := bind_ok h; obtain ⟨placed, hplaced, h⟩ := bind_ok h
    obtain ⟨⟨q0, xs'⟩, hrouted, h⟩ := bind_ok h; dsimp only at h
    have h1 : cg = cg1 :=
      congrArg (fun q : List Int × Graph × Bool => q.2.1) (Except.ok.inj hranked)
    have hpl := Except.ok.inj hplaced
    have hccArm : placed.2.snd.snd.chains = labeled.chains := by
      rw [← hpl]; exact rrc_coordinateGraphR_chains P exact spec labeled
    have HD : cg1.edges.map (·.decl) = cg.edges.map (·.decl) := by rw [h1]
    split at h
    · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
      obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
      exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
    · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
      obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
      exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
  · obtain ⟨⟨ranks, cg1, rankBudget⟩, hranked, h⟩ := bind_ok h; dsimp only at h
    obtain ⟨p0, hp0, h⟩ := bind_ok h; obtain ⟨labeled, hlab, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h; obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨ord, _, h⟩ := bind_ok h; split at h
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨placed, hplaced, h⟩ := bind_ok h
      obtain ⟨⟨q0, xs'⟩, hrouted, h⟩ := bind_ok h; dsimp only at h
      have hccArm : placed.2.snd.snd.chains = labeled.chains :=
        (rrc_crossCoordsR_chains hplaced).trans (rrc_coordinateGraphR_chains P exact spec labeled)
      have HD : cg1.edges.map (·.decl) = cg.edges.map (·.decl) :=
        rrc_rankEquivalentR_decls hranked
      split at h
      · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
        obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
        exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
      · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
        obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
        exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
    · obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨placed, hplaced, h⟩ := bind_ok h
      obtain ⟨⟨q0, xs'⟩, hrouted, h⟩ := bind_ok h; dsimp only at h
      have hccArm : placed.2.snd.snd.chains = labeled.chains :=
        (rrc_crossCoordsR_chains hplaced).trans (rrc_coordinateGraphR_chains P exact spec labeled)
      have HD : cg1.edges.map (·.decl) = cg.edges.map (·.decl) :=
        rrc_rankEquivalentR_decls hranked
      split at h
      · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
        obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
        exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
      · obtain ⟨lanes, _, h⟩ := bind_ok h; obtain ⟨yt, _, h⟩ := bind_ok h
        obtain ⟨resv, _, h⟩ := bind_ok h; obtain ⟨routes, _, h⟩ := bind_ok h
        exact rrc_pack_run_spec hp0 hlab hccArm hrouted HD (Except.ok.inj h)
/-- Rank chains cover the rewritten edges (region replay of the exact fact). -/
theorem componentRunR_proper_chains_lengthR : componentRunR_proper_chains_length_factR := by
  unfold componentRunR_proper_chains_length_factR
  intro P exact spec inp cg cg' run labels orderOptions h
  obtain ⟨cgmid, _, p0, labeled, _, q0, _, hp0, hlab, hcc, hprox, hdrop, hdeclsMid, hdecls⟩ :=
    rrc_run_chain_spec h
  have hdropC : run.proper.chains = q0.chains := by
    rw [hdrop, OrderImpl.dropSynthetic_chains]
  have hproxC : q0.chains = run.coordinateProper.chains := proxyWidths_chains hprox
  have hlblC : labeled.chains = p0.chains := (Labels.addLabelNodes_metadata hlab).2.2.1
  have hnorm : p0.chains.length = cgmid.edges.length := normalize_chains_length hp0
  have hlen : cg'.edges.length = cgmid.edges.length := by
    have hll := congrArg List.length hdecls
    have hml := congrArg List.length hdeclsMid
    simp only [List.length_map] at hll hml
    rw [hll, ← hml]
  rw [hdropC, hproxC, hcc, hlblC, hnorm, hlen]
/-- Rank rewriting preserves edge declarations (region replay of the declaration fact). -/
theorem componentRunR_edges_declsR : componentRunR_edges_decls_factR := by
  unfold componentRunR_edges_decls_factR
  intro P exact spec inp cg cg' run labels orderOptions h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hdecls⟩ := rrc_run_chain_spec h
  exact hdecls
/-- Coordinate chains match the routed chains (region replay of the exact fact). -/
theorem componentRunR_coordinate_chainsR : componentRunR_coordinate_chains_factR := by
  unfold componentRunR_coordinate_chains_factR
  intro P exact spec inp cg cg' run labels orderOptions h
  obtain ⟨_, _, _, _, _, q0, _, _, _, _, hprox, hdrop, _, _⟩ := rrc_run_chain_spec h
  have hdropC : run.proper.chains = q0.chains := by rw [hdrop, OrderImpl.dropSynthetic_chains]
  have hproxC : q0.chains = run.coordinateProper.chains := proxyWidths_chains hprox
  rw [← hproxC, hdropC]
end PipelineImpl
end Layered
end Elegant
