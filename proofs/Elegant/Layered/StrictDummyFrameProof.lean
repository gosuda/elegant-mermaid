import Elegant.Layered.RouteRunClearCases
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.DummyChainRankProof
import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.BottomNestedRankProof
import Elegant.Layered.BottomSeamsRank
import Elegant.Layered.ExecutedFrameClearanceFacts
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ParentContainmentFacts
import Elegant.Layered.RouteProxyStart
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

 /-! # Strict dummy frame for executed runs

 The unlinked statement (formerly as stated in `RouteRunClearCases.lean`)
 quantified the dummy index `d` and the dummy node `nd` independently: for
 every group position and *every* `d : Nat` and *every* dummy `nd` whose path
 carries the declaration, the frame must lie strictly inside `rectAt d`. That
 statement is FALSE: the index and the node are not linked.

 Minimal witness (probe `proofs/wip/Probe/StrictDummyLiteralWitness.lean`,
 `insideGroup/vecTB`, group `G` at `gpos = 0`, linked label dummy `d = 4`):

 * `frameRect = { x := -256, y := 0, w := 5972, h := 22016 }`
 * at the unlinked index `d' = 0` (the group top marker, height zero),
   `rectAt 0 = { x := -256, y := 0, w := 5972, h := 0 }`
 * `StrictInside` needs `frame.x < rectAt.x`, i.e. `-256 < -256`: false.

 Every unlinked `d'` whose rect does not strictly contain the frame refutes the
 as-stated def; the probe finds one on every group input with a label dummy
 (`litWit` on `insideGroup`/`nestedGroups`, both profiles), while the linked
 form holds everywhere (`linkedBad = 0`).

 The weakest true replacement is `StrictDummyFrameLinked` (now defined in
 `RouteRunClearCases.lean`, consumed at the use site `case_group_inside` there):
 it links the index to the node, exactly as the probe's H1 check and the use
 site do (there `(nd, d)` comes from one `find?` hit, so
 `run.proper.nodes[d]? = some nd` holds). This file proves the executed form
 (`strictDummyFrame_of_run`) modulo the order-stage residual
 `DummyMarkerBracket` below. -/

/-- Order-stage residual: the dummy sits strictly between its group's side
markers in layer order at its own rank, and both markers have positive width.
Rank/layer positions and marker records only, no geometry: strictly narrower
than the target, one pipeline stage. Probe: `StrictDummyLiteralWitness.lean`
extended check `bracketOk/bracketBad` (positions) and marker widths. -/
def DummyMarkerBracket (cg : Graph) (run : Run) : Prop :=
  ∀ (gpos : Nat) (gn : Node), cg.nodes[gpos]? = some gn → gn.border = -2 →
    ∀ (d : Nat) (nd : ProperNode), run.proper.nodes[d]? = some nd →
      nd.dummy = true → gn.decl ∈ nd.node.clusterPath →
      ∃ (mL mR : Nat) (nL nR : ProperNode) (layer : List Nat),
        layer ∈ run.layers ∧
        run.coordinateProper.nodes[mL]? = some nL ∧
        run.coordinateProper.nodes[mR]? = some nR ∧
        nL.node.border = -1 ∧ nR.node.border = 1 ∧
        nL.node.clusterPath.getLast? = some gn.decl ∧
        nR.node.clusterPath.getLast? = some gn.decl ∧
        1 ≤ nL.node.w ∧ 1 ≤ nR.node.w ∧
        rk run.coordinateProper.rank mL = rk run.coordinateProper.rank d ∧
        rk run.coordinateProper.rank mR = rk run.coordinateProper.rank d ∧
        ∃ li mi ri : Nat,
          layer[li]? = some mL ∧ layer[mi]? = some d ∧
            layer[ri]? = some mR ∧ li < mi ∧ mi < ri

/-- Copied from `proper_rank_eq_local` (`DummyChainRankProof.lean`): executed
proper ranks agree with coordinate ranks index-wise. -/
private theorem proper_rank_eq_local_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (x : Nat) :
    rk run.proper.rank x = rk run.coordinateProper.rank x := by
  have h : run.proper.rank = run.coordinateProper.rank := by
    obtain ⟨_, _, _, q0, _, _, _, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
      componentRun_spec hrun
    obtain ⟨_, hrankEq, _, _, _, _⟩ := proxyWidths_rel hprox
    rw [← hdrop, OrderImpl.dropSynthetic_rank]
    exact hrankEq
  rw [h]

/-- Copied from `proper_to_coordinate_dummy` (`DummyChainRankProof.lean`): an
executed proper dummy has the same record in the coordinate graph. -/
private theorem proper_to_coordinate_dummy_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} {pn : ProperNode}
    (hp : run.proper.nodes[i]? = some pn) (hd : pn.dummy = true) :
    ∃ cn, run.coordinateProper.nodes[i]? = some cn ∧ cn.dummy = true ∧
      cn.node.border = pn.node.border ∧ cn.node.clusterPath = pn.node.clusterPath := by
  obtain ⟨_, _, labeled, q0, hn, hl, hc, _, _, hprox, hdrop, _, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hnodes : run.proper.nodes = q0.nodes := by rw [← hdrop]; rfl
  have hq0i : q0.nodes[i]? = some pn := by rw [← hnodes]; exact hp
  have hlen : q0.nodes.length = run.coordinateProper.nodes.length :=
    (proxyWidths_rel hprox).2.2.1
  have hiC : i < run.coordinateProper.nodes.length := by
    have hi0 : i < q0.nodes.length := (List.getElem?_eq_some_iff.mp hq0i).1
    omega
  obtain ⟨cn, hcn⟩ : ∃ cn, run.coordinateProper.nodes[i]? = some cn :=
    ⟨_, List.getElem?_eq_getElem hiC⟩
  obtain ⟨nd', hnd', hddum, _, _⟩ :=
    (proxyWidths_rel hprox).2.2.2.2.1 i cn hcn
  have hndEq : nd' = pn := Option.some.inj (hnd'.symm.trans hq0i)
  have hcnDum : cn.dummy = true := by rw [← hddum, hndEq]; exact hd
  have hK : NodeKeys cg labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hcnL : (coordinateGraph P labeled).nodes[i]? = some cn := by
    rw [hc]; exact hcn
  have hbord0 : cn.node.border = 0 := pc_plain hK hcnL hcnDum
  have hnp : ¬ (cn.node.border = -2 ∨ cn.node.border = 2) := by
    rw [hbord0]; decide
  obtain ⟨hsame, _⟩ := (proxyWidths_rel hprox).2.2.2.2.2 i cn hcn hnp
  have hcnEq : cn = pn := Option.some.inj (hsame.symm.trans hq0i)
  exact ⟨cn, hcn, hcnDum, by rw [hcnEq], by rw [hcnEq]⟩

/-- Any proper rect whose path carries the group declaration is a member of
the group's `frameRect` hull. -/
private theorem rect_mem_frame_hull {cg : Graph} {run : Run} {gpos v : Nat}
    {pn : ProperNode}
    (hv : run.proper.nodes[v]? = some pn)
    (hpath : (cg.nodes.getD gpos default).decl ∈ pn.node.clusterPath) :
    Labels.rectAt run.proper run.xs run.ys v ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD gpos default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  have hmem : (pn, v) ∈ run.proper.nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hv
  have hcond : (pn, v).fst.node.clusterPath.contains
      (cg.nodes.getD gpos default).decl = true :=
    List.contains_iff_mem.mpr hpath
  apply List.mem_filterMap.mpr
  refine ⟨(pn, v), hmem, ?_⟩
  rw [hcond]
  simp
private theorem labeled_rank_aligned_copy {cg : Graph}
    {rr : RankImpl.RankResult} {normalized labeled : Proper}
    {labels : List MeasuredLabel}
    (hnormalize : normalize cg rr.ranks = .ok normalized)
    (hlabels : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    labeled.nodes.length = labeled.rank.length := by
  have h1 := addLabelNodes_node_length hlabels
  have h2 := congrArg List.length (Labels.addLabelNodes_metadata hlabels).2.1
  have h3 := (normalize_node_rank_alignment hnormalize).1
  omega

/-- Copied from `coord_rank_eq` (`DummyChainRankProof.lean`): coordinate ranks
agree with labeled ranks index-wise. -/
private theorem coord_rank_eq_copy {P : Params} {labeled : Proper} {run : Run}
    (hcoord : coordinateGraph P labeled = run.coordinateProper)
    (haligned : labeled.nodes.length = labeled.rank.length)
    {x : Nat} (hx : x < labeled.nodes.length) :
    rk run.coordinateProper.rank x = rk labeled.rank x := by
  have hxr : x < labeled.rank.length := by omega
  have hlab : labeled.rank[x]? = some (labeled.rank[x]'hxr) :=
    List.getElem?_eq_getElem hxr
  have hcoo : run.coordinateProper.rank[x]? = some (labeled.rank[x]'hxr) := by
    rw [← hcoord]
    exact coordinateGraph_rank_record hlab
  simp only [rk, List.getD_eq_getElem?_getD, hlab, hcoo, Option.getD_some]

/-- Copied from `prepared_path_eq` (`DummyChainRankProof.lean`): prepared
(materialization-input) nodes keep their labeled cluster path. -/
private theorem prepared_path_eq_copy {P : Params} {labeled : Proper}
    {j : Nat} {pn : ProperNode}
    (hlab : labeled.nodes[j]? = some pn) :
    ∃ qn, (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[j]? =
      some qn ∧ qn.node.clusterPath = pn.node.clusterPath := by
  have hj : j < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hlab).1
  have hlen1 : (sizeProperPorts P labeled).nodes.length = labeled.nodes.length :=
    sizeProperPorts_length P labeled
  have hs1 := sizeProperPorts_key P labeled j
  rw [hlab] at hs1
  obtain ⟨m1, hm1, htrip⟩ : ∃ m1, (sizeProperPorts P labeled).nodes[j]? = some m1 ∧
      (m1.dummy, m1.node.border, m1.node.clusterPath) =
        (pn.dummy, pn.node.border, pn.node.clusterPath) := by
    cases hs : (sizeProperPorts P labeled).nodes[j]? with
    | none => simp [hs] at hs1
    | some m1 =>
      simp only [hs, Option.map_some, Option.some.injEq] at hs1
      exact ⟨m1, rfl, hs1⟩
  have hp1 : m1.node.clusterPath = pn.node.clusterPath := by
    have h3 := congrArg (fun t : Bool × Int × List Nat => t.2.2) htrip
    simpa using h3
  have hm2 : (titleReservations (sizeProperPorts P labeled)).nodes[j]? =
      some (titleF m1) := by
    have hJ : j < ((sizeProperPorts P labeled).nodes.map titleF).length := by
      rw [List.length_map, hlen1]; exact hj
    rw [titleReservations_nodes, List.getElem?_append_left hJ, List.getElem?_map, hm1,
      Option.map_some]
  have hp2 : (titleF m1).node.clusterPath = pn.node.clusterPath := by
    rw [(titleF_keys m1).2.2.1]; exact hp1
  have hlen2 : (titleReservations (sizeProperPorts P labeled)).nodes.length =
      (sizeProperPorts P labeled).nodes.length +
        ((titleNodes (sizeProperPorts P labeled)).map copyF).length := by
    rw [titleReservations_nodes, List.length_append, List.length_map, List.length_map]
  have hj2 : j < (titleReservations (sizeProperPorts P labeled)).nodes.length := by
    omega
  obtain ⟨extra, hx, _⟩ :=
    addClusterBorders_extra (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW
  have hm3 : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW).nodes[j]? =
      (titleReservations (sizeProperPorts P labeled)).nodes[j]? := by
    rw [hx]; exact List.getElem?_append_left hj2
  have hm4 : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes[j]? =
      some (clearF (titleF m1)) := by
    rw [clearProxyExtents_nodes, List.getElem?_map, hm3, hm2, Option.map_some]
  have hp4 : (clearF (titleF m1)).node.clusterPath = pn.node.clusterPath := by
    rw [(clearF_keys (titleF m1)).2.2.1]; exact hp2
  exact ⟨_, hm4, hp4⟩

/-- Strict chain straddle for executed proper dummies: a dummy lies strictly
between its edge endpoint ranks (coordinate ranks), and both endpoint
candidate paths carry the owner. The non-strict form is
`dummy_chain_bracket`; strictness comes from the chain position being
strictly interior (an endpoint position would identify the dummy with a
non-dummy original). -/
private theorem dummy_chain_strict {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {i : Nat} (hi : i < run.proper.nodes.length)
    (hdummy : (run.proper.nodes.getD i default).dummy = true)
    {owner : Nat} (howner : owner ∈ (run.proper.nodes.getD i default).node.clusterPath) :
    ∃ (index : Nat) (edge : Edge),
      cg.edges[index]? = some edge ∧
      edge.tail ≠ edge.head ∧
      edge.tail < cg.nodes.length ∧ edge.head < cg.nodes.length ∧
      rk run.coordinateProper.rank edge.tail < rk run.coordinateProper.rank i ∧
      rk run.coordinateProper.rank i < rk run.coordinateProper.rank edge.head ∧
      ∃ (nA nB : Node),
        cg.nodes[edge.tail]? = some nA ∧ cg.nodes[edge.head]? = some nB ∧
        nA.clusterPath.contains owner = true ∧ nB.clusterPath.contains owner = true := by
  have hp : run.proper.nodes[i]? = some (run.proper.nodes.getD i default) := by
    simp [List.getD_eq_getElem?_getD, hi]
  obtain ⟨cn, hcn, hcnDum, _, hcnPath⟩ := proper_to_coordinate_dummy_copy hrun hp hdummy
  have hownerC : owner ∈ cn.node.clusterPath := by rw [hcnPath]; exact howner
  obtain ⟨rr, normalized, labeled, hrr, hnormalize, hlabels, hcoordRun, hpositions⟩ :=
    componentRun_labeled_chain_rank_positions hrun
  obtain ⟨rrC, normC, labC, index, edge, chain, position,
      hrrC, hnormC, hlabC, hcoordC, hedge, hchainC, hpos, hhead, hlast, _hrankC,
      _hfind, hleftC, hrightC⟩ :=
    componentRun_dummy_path_chain_source hrun hcn hcnDum hownerC
  have e1 : rr = rrC := Except.ok.inj (hrr.symm.trans hrrC)
  subst e1
  have e2 : normalized = normC := Except.ok.inj (hnormalize.symm.trans hnormC)
  subst e2
  have e3 : labeled = labC := Except.ok.inj (hlabels.symm.trans hlabC)
  subst e3
  have hindex : index < cg.edges.length := (List.getElem?_eq_some_iff.mp hedge).1
  have hwf : cg.wellformed = true := (normalize_node_rank_alignment hnormalize).2
  have hedgeMem : edge ∈ cg.edges := List.mem_of_getElem? hedge
  obtain ⟨htailLt, hheadLt, _⟩ := RankImpl.wellformed_spec hwf edge hedgeMem
  have hchainsEq : labeled.chains = normalized.chains :=
    (Labels.addLabelNodes_metadata hlabels).2.2.1
  have hfact := (normalize_ok hnormalize).2.2 index hindex edge hedge
  have hne : edge.tail ≠ edge.head := by
    intro heq
    have hif := hfact.2
    simp only [heq, ↓reduceIte] at hif
    rw [← hchainsEq] at hif
    have hempty : chain = [] := Option.some.inj (hchainC.symm.trans hif)
    rw [hempty] at hpos
    simp at hpos
  have hposLen : position < chain.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hlastElem : chain[chain.length - 1]? = some edge.head := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hlastLt : chain.length - 1 < chain.length :=
    (List.getElem?_eq_some_iff.mp hlastElem).1
  have hchainC' : normalized.chains[index]? = some chain := by
    rw [← (Labels.addLabelNodes_metadata hlabels).2.2.1]; exact hchainC
  -- labeled record of the dummy (for the endpoint-identity contradictions)
  have hcoordV0 : (coordinateGraph P labeled).nodes[i]? = some cn := by
    rw [hcoordRun]; exact hcn
  obtain ⟨mV, hmvV, hdmV⟩ : ∃ m, labeled.nodes[i]? = some m ∧ m.dummy = true := by
    rcases coordinateGraph_lookup P labeled hcoordV0 with
      ⟨m, hm, h1, _, _, _⟩ | ⟨h1, _⟩ | ⟨tq, q, hq, _, h1, _, _⟩
    · exact ⟨m, hm, h1.symm.trans hcnDum⟩
    · rw [h1] at hcnDum; exact absurd hcnDum (by decide)
    · have hkeys : NodeKeys cg labeled :=
        addLabelNodes_keys _ _ _ (normalize_keys hnormalize) hlabels
      obtain ⟨hs, hbq⟩ := titleNodes_spec hq
      have hk := sizeProperPorts_key P labeled q.2
      rw [hs] at hk
      cases hp2 : labeled.nodes[q.2]? with
      | none => simp [hp2] at hk
      | some mp =>
        simp only [hp2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨hk1, hk2, _⟩ := hk
        rcases hkeys q.2 mp hp2 with ⟨n, _, hmd, _, _⟩ | ⟨_, hbB, _⟩
        · rw [h1, hk1, hmd] at hcnDum; exact absurd hcnDum (by decide)
        · rw [hk2] at hbq; rw [hbB] at hbq; exact absurd hbq (by decide)
  -- endpoint original records
  obtain ⟨nA, hnA⟩ : ∃ n, cg.nodes[edge.tail]? = some n :=
    ⟨_, List.getElem?_eq_getElem htailLt⟩
  obtain ⟨nB, hnB⟩ : ∃ n, cg.nodes[edge.head]? = some n :=
    ⟨_, List.getElem?_eq_getElem hheadLt⟩
  have hlabT : labeled.nodes[edge.tail]? = some ⟨nA, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnA
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  have hlabH : labeled.nodes[edge.head]? = some ⟨nB, false, none, false⟩ := by
    have hn0 := normalize_node_record hnormalize hnB
    exact addLabelNodes_untouched_node hlabels hn0 rfl
  -- position cannot be the head end: that would identify the dummy with the
  -- non-dummy tail original
  -- position cannot be the tail end: that would identify the dummy with the
  -- non-dummy tail original
  have hposNe0 : position ≠ 0 := by
    intro hz
    have hiv : chain[0]? = some i := by
      have h := hpos
      rw [hz] at h
      exact h
    have h0tail : chain[0]? = some edge.tail := by
      cases chain with
      | nil => simp at hhead
      | cons a as => exact hhead
    have hiEq : i = edge.tail := Option.some.inj (hiv.symm.trans h0tail)
    have hmEq : mV = ⟨nA, false, none, false⟩ := by
      rw [hiEq] at hmvV
      exact Option.some.inj (hmvV.symm.trans hlabT)
    rw [hmEq] at hdmV
    exact Bool.false_ne_true hdmV
  -- position cannot be the head end: that would identify the dummy with the
  -- non-dummy head original
  have hposNeLast : position ≠ chain.length - 1 := by
    intro hz
    have hiv : chain[chain.length - 1]? = some i := by
      have h := hpos
      rw [hz] at h
      exact h
    have hiEq : i = edge.head := Option.some.inj (hiv.symm.trans hlastElem)
    have hmEq : mV = ⟨nB, false, none, false⟩ := by
      rw [hiEq] at hmvV
      exact Option.some.inj (hmvV.symm.trans hlabH)
    rw [hmEq] at hdmV
    exact Bool.false_ne_true hdmV
  -- strict labeled ranks from strictly interior position
  have hposLtLast : position < chain.length - 1 := by omega
  have hpositionValue : chain[position]'hposLen = i :=
    Option.some.inj ((List.getElem?_eq_getElem hposLen).symm.trans hpos)
  have hlastValue : chain[chain.length - 1]'hlastLt = edge.head :=
    Option.some.inj ((List.getElem?_eq_getElem hlastLt).symm.trans hlastElem)
  have hposBase := hpositions index edge chain hedge hchainC position hposLen
  have hlastBase := hpositions index edge chain hedge hchainC (chain.length - 1) hlastLt
  have hrankV : rk labeled.rank i = rk labeled.rank edge.tail + (position : Int) := by
    rw [← hpositionValue]; exact hposBase
  have hrankH : rk labeled.rank edge.head =
      rk labeled.rank edge.tail + ((chain.length - 1 : Nat) : Int) := by
    rw [← hlastValue]; exact hlastBase
  have hltLab1 : rk labeled.rank edge.tail < rk labeled.rank i := by omega
  have hltLab2 : rk labeled.rank i < rk labeled.rank edge.head := by omega
  -- transport to coordinate ranks
  have hlenN := normalize_nodes_length_le hnormalize
  have hlenL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hlabels
  have htailL : edge.tail < labeled.nodes.length := by omega
  have hheadL : edge.head < labeled.nodes.length := by omega
  have haligned := labeled_rank_aligned_copy hnormalize hlabels
  have hiL : i < labeled.nodes.length := (List.getElem?_eq_some_iff.mp hmvV).1
  have hcTail : rk run.coordinateProper.rank edge.tail = rk labeled.rank edge.tail :=
    coord_rank_eq_copy hcoordRun haligned htailL
  have hcHead : rk run.coordinateProper.rank edge.head = rk labeled.rank edge.head :=
    coord_rank_eq_copy hcoordRun haligned hheadL
  have hcI : rk run.coordinateProper.rank i = rk labeled.rank i :=
    coord_rank_eq_copy hcoordRun haligned hiL
  have hltC1 : rk run.coordinateProper.rank edge.tail < rk run.coordinateProper.rank i := by
    rw [hcTail, hcI]; exact hltLab1
  have hltC2 : rk run.coordinateProper.rank i < rk run.coordinateProper.rank edge.head := by
    rw [hcI, hcHead]; exact hltLab2
  -- endpoint paths carry the owner
  obtain ⟨qT, hqT, hpT⟩ := prepared_path_eq_copy hlabT
  obtain ⟨qH, hqH, hpH⟩ := prepared_path_eq_copy hlabH
  have hheadD : chain.headD i = edge.tail := by
    cases hcchain : chain with
    | nil => simp [hcchain] at hhead
    | cons a as =>
      simp only [List.headD]
      simpa [hcchain] using hhead
  have hlastD : chain.getLastD i = edge.head := by
    rw [List.getLastD_eq_getLast?, hlast, Option.getD_some]
  have hgetDT : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes.getD
      edge.tail default = qT := by
    rw [List.getD_eq_getElem?_getD, hqT, Option.getD_some]
  have hgetDH : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P labeled)) P.clusterBorderW)).nodes.getD
      edge.head default = qH := by
    rw [List.getD_eq_getElem?_getD, hqH, Option.getD_some]
  rw [hheadD, hgetDT] at hleftC
  rw [hlastD, hgetDH] at hrightC
  have hcontA : nA.clusterPath.contains owner = true := by
    rw [hpT] at hleftC
    exact List.contains_iff_mem.mpr hleftC
  have hcontB : nB.clusterPath.contains owner = true := by
    rw [hpH] at hrightC
    exact List.contains_iff_mem.mpr hrightC
  exact ⟨index, edge, hedge, hne, htailLt, hheadLt, hltC1, hltC2,
    nA, nB, hnA, hnB, hcontA, hcontB⟩

/-- Copied from `proper_top_coordinate_record` (`StrictMemberFrameProof.lean`):
the coordinate-graph record of a `-2` graph node. -/
private theorem proper_top_coordinate_record_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = -2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = -2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath := by
  obtain ⟨_, labeled, _, hc, _, hnodeRec, _⟩ := componentRun_ranked_node_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := coordinateGraph_marker_record (P := P) hrec (Or.inl hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1

/-- Copied from `proper_top_proper_clusterPath` (`StrictMemberFrameProof.lean`). -/
private theorem proper_top_proper_clusterPath_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = -2) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath := by
  obtain ⟨_, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inl hb)
  exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

/-- Copied from `run_rank_eq_coordinate` (`StrictMemberFrameProof.lean`). -/
private theorem run_rank_eq_coordinate_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (i : Nat) :
    rk run.proper.rank i = rk run.coordinateProper.rank i := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
  rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

/-- Copied from `proper_bottom_coordinate_record`
(`StrictMemberFrameProof.lean`). -/
private theorem proper_bottom_coordinate_record_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hnode : cg.nodes[v]? = some nd) (hgroup : nd.border = 2) :
    ∃ coord : ProperNode,
      run.coordinateProper.nodes[v]? = some coord ∧
      coord.node.border = 2 ∧ coord.dummy = false ∧
      coord.node.clusterPath = nd.clusterPath ∧ coord.node.h = 0 := by
  obtain ⟨_, labeled, _, hc, _, hnodeRec, _⟩ := componentRun_ranked_node_records hrun
  have hrec : labeled.nodes[v]? = some ⟨nd, false, none, false⟩ := hnodeRec v nd hnode
  have hmarker := coordinateGraph_marker_record (P := P) hrec (Or.inr hgroup) rfl
  rw [hc] at hmarker
  refine ⟨clearF (titleF ⟨nd, false, none, false⟩), hmarker, ?_, ?_, ?_, ?_⟩
  · have hb := (clearF_keys (titleF ⟨nd, false, none, false⟩)).2.1
    rw [hb, (titleF_keys _).2.1]
    exact hgroup
  · exact (clearF_keys _).1.trans (titleF_keys _).1
  · exact (clearF_keys _).2.2.1.trans (titleF_keys _).2.2.1
  · exact (clearF_keys _).2.2.2.trans
      ((titleF_keys ⟨nd, false, none, false⟩).2.2.2 (Or.inr hgroup))

/-- Copied from `proper_bottom_proper_node` (`StrictMemberFrameProof.lean`). -/
private theorem proper_bottom_proper_node_copy {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    {v : Nat} {coord : ProperNode}
    (hcoord : run.coordinateProper.nodes[v]? = some coord)
    (hb : coord.node.border = 2) (hcoordH : coord.node.h = 0) :
    ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
      p.node.clusterPath = coord.node.clusterPath ∧
      RouteImpl.nodeH run.proper v = 0 := by
  obtain ⟨owner, span, _, _, hproper, _, _⟩ :=
    componentRun_proxy_interval hrun hcoord (Or.inr hb)
  refine ⟨_, hproper, rfl, ?_⟩
  simp only [RouteImpl.nodeH, hproper]
  exact hcoordH

/-- Strict top rank for dummies: the group top marker ranks strictly below
every dummy whose path carries the declaration. From the strict chain
interior (dummy strictly above its tail) and the closed top closure
(`groupTopSubtreeRankCg`) applied to the tail endpoint. -/
private theorem dummyTopRankStrict {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v : Nat} {nd : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hbordV : nd.border = -2)
    (hvcg : v < (componentCandidate graph comp candidate).nodes.length)
    {d : Nat} (hd : d < run.proper.nodes.length)
    (hpath : (run.proper.nodes.getD d default).node.clusterPath.contains nd.decl = true)
    (hdum : (run.proper.nodes.getD d default).dummy = true) :
    rk run.coordinateProper.rank v < rk run.coordinateProper.rank d := by
  have howner : nd.decl ∈ (run.proper.nodes.getD d default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, hedge, hne, htailLt, hheadLt, hlt1, hlt2,
      nA, nB, hnA, hnB, hcontA, hcontB⟩ :=
    dummy_chain_strict hrun hd hdum howner
  obtain ⟨rr, hrr, hclose⟩ :=
    groupTopSubtreeRankCg hgraph hlines hwf hfp hcomp hrun hvGet hbordV
  have hgetDA : (componentCandidate graph comp candidate).nodes.getD edge.tail default = nA := by
    simp [List.getD_eq_getElem?_getD, hnA]
  have hgetDContains : ((componentCandidate graph comp candidate).nodes.getD
      edge.tail default).clusterPath.contains nd.decl = true := by
    rw [hgetDA]; exact hcontA
  have hleTail : rk rr.ranks v ≤ rk rr.ranks edge.tail :=
    hclose edge.tail htailLt hgetDContains
  obtain ⟨rrS, _, hrrS, hcS, _, hranksS, _, _⟩ :=
    rankSource_of_componentRun hgraph hcomp hrun
  have hrrEq : rr = rrS := Except.ok.inj (hrr.symm.trans hrrS)
  subst hrrEq
  have hVcoord : rk run.coordinateProper.rank v = rk rr.ranks v := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranksS hvcg
    rw [← hcS]; exact h1
  have hTcoord : rk run.coordinateProper.rank edge.tail = rk rr.ranks edge.tail := by
    have h1 := prepared_coordinate_original_rk (P := P) hrr hranksS htailLt
    rw [← hcS]; exact h1
  omega

/-- Strict bottom rank for dummies: every dummy whose path carries the group
declaration ranks strictly below the group's bottom marker. From the strict
chain interior (dummy strictly below its head) and the closed bottom closure
(`bottomOrigRankLe` with the closed `bottomNestedBottomRankLe`) applied to the
head endpoint. -/
private theorem dummyBottomRankStrict {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    (hlines : lines.length = inp.boxes.length)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {v t : Nat} {ndV ndT : Node}
    (hvGet : (componentCandidate graph comp candidate).nodes[v]? = some ndV)
    (htGet : (componentCandidate graph comp candidate).nodes[t]? = some ndT)
    (hbordV : ndV.border = 2) (hbordT : ndT.border = -2)
    (hdecl : ndV.decl = ndT.decl)
    {d : Nat} (hd : d < run.proper.nodes.length)
    (hpath : (run.proper.nodes.getD d default).node.clusterPath.contains ndT.decl = true)
    (hdum : (run.proper.nodes.getD d default).dummy = true) :
    rk run.coordinateProper.rank d < rk run.coordinateProper.rank v := by
  have howner : ndT.decl ∈ (run.proper.nodes.getD d default).node.clusterPath :=
    List.contains_iff_mem.mp hpath
  obtain ⟨index, edge, hedge, hne, htailLt, hheadLt, hlt1, hlt2,
      nA, nB, hnA, hnB, hcontA, hcontB⟩ :=
    dummy_chain_strict hrun hd hdum howner
  have hle := bottomOrigRankLe hgraph hlines hwf hframed hcomp hrun hvGet htGet
    hbordV hbordT hdecl bottomNestedBottomRankLe hnB hcontB
  omega

/-- Copied from `proper_top_decl_path` (`StrictMemberFrameProof.lean`). -/
private theorem proper_top_decl_path_copy {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hgroup : nd.border = -2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨original, horiginal, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨hdecl, box, hbox, hrole, hpath⟩ :=
    measuredGraph_group_origin hgraph hsource hgroup
  have hlast : nd.clusterPath.getLast? = some nd.decl := by
    rw [hpath]
    simp
  exact ⟨hlast, by rw [hpath]; simp⟩

/-- Copied from `proper_bottom_decl_path` (`StrictMemberFrameProof.lean`). -/
private theorem proper_bottom_decl_path_copy {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hborder : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl ∧ nd.clusterPath.contains nd.decl = true := by
  obtain ⟨original, horiginal, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨box, hbox, hrole, hpath, hw, hh⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hborder
  exact ⟨by rw [hpath]; simp, by rw [hpath]; simp⟩

/-- Vertical top strictness for a dummy: the group frame top lies strictly
below the dummy rect top. Mirrors the top half of
`memberFrameStrictVertical_of_executed`, with the member rank interval
replaced by the strict dummy top rank `hlt`. -/
private theorem dummyFrameTopYStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hlt : rk run.coordinateProper.rank gpos < rk run.coordinateProper.rank d) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate)
      run gpos).y < (Labels.rectAt run.proper run.xs run.ys d).y := by
  have hindexLt : gpos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  have hdLen : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnd).1
  obtain ⟨_, _, _, _, _, _, _, _, hcross, hproxy, hdrop, hrouteOk, _, hry, hyseq, _⟩ :=
    componentRun_spec hrun
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteOk).1).2.2.2.1
  have hgLen : gpos < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun gpos hindexLt
  obtain ⟨tcoord, htcoord, htb, htd, htpath⟩ :=
    proper_top_coordinate_record_copy hrun hg hgroup
  obtain ⟨tprop, htprop, htpropP⟩ := proper_top_proper_clusterPath_copy hrun htcoord htb
  have hdeclT : gn.clusterPath.contains gn.decl = true :=
    (proper_top_decl_path_copy execution.graph_eq hg hgroup).2
  have htcontains : tprop.node.clusterPath.contains gn.decl = true := by
    rw [htpropP, htpath]; exact hdeclT
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD gpos default =
      gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD
      gpos default).border = -2 := by
    rw [hgroupGet]; exact hgroup
  have htqmem : (tprop, gpos) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr htprop
  have htcontains' : (tprop, gpos).1.node.clusterPath.contains
      ((componentCandidate execution.graph comp candidate).nodes.getD gpos default).decl =
      true := by
    rw [hgroupGet]; exact htcontains
  have htopLe : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos).y ≤
      (Labels.rectAt run.proper run.xs run.ys gpos).y :=
    (frameRect_member_vertical (P := execution.params)
      (cg := componentCandidate execution.graph comp candidate) (run := run)
      (i := gpos) (q := (tprop, gpos)) hframeGroup htqmem htcontains').1
  obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov gpos hgLen
  obtain ⟨ltD, hlyD, _, hnnD⟩ := hcov d hdLen
  rw [run_rank_eq_coordinate_copy hrun gpos] at hlyT hnnT
  rw [run_rank_eq_coordinate_copy hrun d] at hlyD hnnD
  have hTopY : (Labels.rectAt run.proper run.xs run.ys gpos).y = run.ys.getD gpos 0 := rfl
  have hMemY : (Labels.rectAt run.proper run.xs run.ys d).y = run.ys.getD d 0 := rfl
  have hTopBand := (fbs_run_node_band hrun gpos hgLen).1
  have hMemBandLo := (fbs_run_node_band hrun d hdLen).1
  rw [run_rank_eq_coordinate_copy hrun gpos] at hTopBand
  rw [run_rank_eq_coordinate_copy hrun d] at hMemBandLo
  have hTopProxy : run.ys.getD gpos 0 =
      run.top.getD (rk run.coordinateProper.rank gpos).toNat 0 := by
    have h := componentRun_group_proxy_ys_eq_top hrun hg hgroup hindexLt
    rw [run_rank_eq_coordinate_copy hrun gpos] at h
    exact h
  have hltTD : (rk run.coordinateProper.rank gpos).toNat <
      (rk run.coordinateProper.rank d).toNat := by
    have h4 := hnnT
    have h5 := hnnD
    omega
  have hbandTD := rankAxis_band_top_strict hry _ _ _ _ hltTD hlyT hlyD
  have hHtNonneg : 0 ≤ CoordsImpl.layerHeight run.coordinateProper ltT :=
    CoordsImpl.layerHeight_nonneg _ _
  have hTopStrict : run.ys.getD gpos 0 < run.ys.getD d 0 := by
    have h1 := hTopProxy
    have h2 := hbandTD
    have h3 := hMemBandLo
    have h4 := hHtNonneg
    omega
  have h1 := htopLe
  have h2 := hTopY
  have h3 := hTopStrict
  have h4 := hMemY
  omega

/-- Vertical bottom strictness for a dummy: the dummy rect bottom lies
strictly above the group frame bottom. Mirrors the bottom half of
`memberFrameStrictVertical_of_executed`, with the member rank interval
replaced by the strict dummy bottom rank from `dummyBottomRankStrict`. -/
private theorem dummyFrameBotYStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    (hlines : execution.lines.length = inp.boxes.length)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true)
    (hpath : gn.decl ∈ nd.node.clusterPath) :
    (Labels.rectAt run.proper run.xs run.ys d).y +
      (Labels.rectAt run.proper run.xs run.ys d).h <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).y +
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run gpos).h := by
  have hbot : ∃ bottom : Node × Nat,
      (componentCandidate execution.graph comp candidate).nodes.zipIdx.find? (fun entry =>
        entry.1.border == 2 && entry.1.decl == gn.decl) = some bottom :=
    componentRun_cg_bottom_find execution.graph_eq hlines hcomp hg hgroup
  obtain ⟨bottom, hbottom⟩ := hbot
  have hbotMem : bottom ∈ (componentCandidate execution.graph comp candidate).nodes.zipIdx :=
    List.mem_of_find?_eq_some hbottom
  have hbotLookup : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
      some bottom.1 :=
    List.mem_zipIdx_iff_getElem?.mp hbotMem
  have hbotLt : bottom.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hbotLookup).1
  have hcond := List.find?_some hbottom
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  obtain ⟨hbordV, hdeclV⟩ := hcond
  have hdLen : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnd).1
  have hgetD : run.proper.nodes.getD d default = nd := by
    simp [List.getD_eq_getElem?_getD, hnd]
  have hpathC : (run.proper.nodes.getD d default).node.clusterPath.contains gn.decl = true := by
    rw [hgetD]
    exact List.contains_iff_mem.mpr hpath
  have hdumGet : (run.proper.nodes.getD d default).dummy = true := by
    rw [hgetD]; exact hdum
  have hR2 : rk run.coordinateProper.rank d < rk run.coordinateProper.rank bottom.2 :=
    dummyBottomRankStrict execution.graph_eq hlines hwf hframed hcomp hrun
      hbotLookup hg hbordV hgroup hdeclV hdLen hpathC hdumGet
  obtain ⟨_, _, _, _, _, _, _, _, hcross, hproxy, hdrop, hrouteOk, _, hry, hyseq, _⟩ :=
    componentRun_spec hrun
  have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
    rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteOk).1).2.2.2.1
  have hbotLen : bottom.2 < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun bottom.2 hbotLt
  obtain ⟨bcoord, hbcoord, hbb, hbd, hbpath, bh0⟩ :=
    proper_bottom_coordinate_record_copy hrun hbotLookup hbordV
  obtain ⟨bprop, hbprop, hbpropP, hnodeH⟩ :=
    proper_bottom_proper_node_copy hrun hbcoord hbb bh0
  have hdeclB : bottom.1.clusterPath.contains bottom.1.decl = true :=
    (proper_bottom_decl_path_copy execution.graph_eq hbotLookup hbordV).2
  have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD gpos default =
      gn := by
    simp only [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  have hbcontains : bprop.node.clusterPath.contains gn.decl = true := by
    have h1 : bprop.node.clusterPath = bottom.1.clusterPath := by
      rw [hbpropP, hbpath]
    rw [h1, ← hdeclV]; exact hdeclB
  have hbqmem : (bprop, bottom.2) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hbprop
  have hpath' : ((componentCandidate execution.graph comp candidate).nodes.getD
      gpos default).decl ∈ bprop.node.clusterPath := by
    rw [hgroupGet]
    exact List.contains_iff_mem.mp hbcontains
  have hbmem' : Labels.rectAt run.proper run.xs run.ys bottom.2 ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains
            ((componentCandidate execution.graph comp candidate).nodes.getD gpos default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) :=
    rect_mem_frame_hull hbprop hpath'
  have hBotYH : (Labels.rectAt run.proper run.xs run.ys bottom.2).y +
      (Labels.rectAt run.proper run.xs run.ys bottom.2).h = run.ys.getD bottom.2 0 := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
    simp [hnodeH]
  have hbget : run.coordinateProper.nodes.getD bottom.2 default = bcoord := by
    rw [List.getD_eq_getElem?_getD, hbcoord, Option.getD_some]
  have hcoordV : run.coordinateProper.nodes[bottom.2]? =
      some (run.coordinateProper.nodes.getD bottom.2 default) := by
    rw [hbget]; exact hbcoord
  have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
    obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
    rw [hy]; simp
  have hvY : bottom.2 < run.coordinateYs.length := by omega
  have hYsV : run.ys.getD bottom.2 0 =
      run.top.getD (rk run.coordinateProper.rank bottom.2).toNat 0 +
      CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank bottom.2).toNat []) := by
    have hpg := proxyYs_getD run.coordinateProper run.layers run.top run.coordinateYs
      hcoordV hvY
    have hbeqF : ((run.coordinateProper.nodes.getD bottom.2 default).node.border == -2) =
        false := by rw [hbget, hbb]; simp
    have hbeqT : ((run.coordinateProper.nodes.getD bottom.2 default).node.border == 2) =
        true := by rw [hbget, hbb]; simp
    simp only [hbeqF, ↓reduceIte, hbeqT, ↓reduceIte] at hpg
    rw [← hyseq]
    exact hpg
  obtain ⟨ltD, hlyD, _, hnnD⟩ := hcov d hdLen
  obtain ⟨ltB, hlyB, _, hnnB⟩ := hcov bottom.2 hbotLen
  rw [run_rank_eq_coordinate_copy hrun d] at hlyD hnnD
  rw [run_rank_eq_coordinate_copy hrun bottom.2] at hlyB hnnB
  have hltMB : (rk run.coordinateProper.rank d).toNat <
      (rk run.coordinateProper.rank bottom.2).toNat := by
    have h4 := hnnD
    have h5 := hnnB
    omega
  have hlyMD : run.layers.getD (rk run.coordinateProper.rank d).toNat [] = ltD := by
    rw [List.getD_eq_getElem?_getD, hlyD]; rfl
  have hbandMB := rankAxis_band_top_strict hry _ _ _ _ hltMB hlyD hlyB
  have hMemBandHi := (fbs_run_node_band hrun d hdLen).2
  rw [run_rank_eq_coordinate_copy hrun d] at hMemBandHi
  have hMemLtBot : run.ys.getD d 0 + RouteImpl.nodeH run.proper d <
      run.ys.getD bottom.2 0 := by
    have h1 := hMemBandHi
    have h2 := hbandMB
    have h3 := hYsV
    have hH : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
        (run.layers.getD (rk run.coordinateProper.rank bottom.2).toNat []) :=
      CoordsImpl.layerHeight_nonneg _ _
    rw [hlyMD] at h1
    omega
  have hMemBH : (Labels.rectAt run.proper run.xs run.ys d).y +
      (Labels.rectAt run.proper run.xs run.ys d).h =
      run.ys.getD d 0 + RouteImpl.nodeH run.proper d := rfl
  have hle := rect_bottom_le_boundsOf_bottom _ [] _ hbmem'
  have hframeBot : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom := by
    have hg2 : (componentCandidate execution.graph comp candidate).nodes.getD gpos default =
        gn := hgroupGet
    simp only [frameRect, hg2, hgroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    change (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
      if q.1.node.clusterPath.contains gn.decl then
        some (Labels.rectAt run.proper run.xs run.ys q.2)
      else none) []).minY +
      ((boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom - (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minY) = _
    omega
  have h1 := hMemBH
  have h2 := hMemLtBot
  have h3 := hBotYH
  have h4 := hle
  have hframeBotGetD : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run gpos).y +
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).h =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains
            ((componentCandidate execution.graph comp candidate).nodes.getD gpos default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).bottom :=
    hframeBot.trans (by rw [hgroupGet])
  have h5 := hframeBotGetD
  omega

/-- Marker rects with the group declaration as path-last belong to the
frame's horizontal hull. -/
private theorem marker_rect_mem_borders {cg : Graph} {run : Run} {gpos m : Nat}
    {n : ProperNode} {gn : Node}
    (hg : cg.nodes[gpos]? = some gn)
    (hmem : (n, m) ∈ run.proper.nodes.zipIdx)
    (hb : n.node.border = -1 ∨ n.node.border = 1)
    (hlast : n.node.clusterPath.getLast? = some gn.decl) :
    Labels.rectAt run.proper run.xs run.ys m ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) := by
  have hget : cg.nodes.getD gpos default = gn := by
    rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  apply List.mem_filterMap.mpr
  refine ⟨(n, m), hmem, ?_⟩
  have hcond : (((n, m).fst.node.border == -1 || (n, m).fst.node.border == 1) &&
      (n, m).fst.node.clusterPath.getLast? == some gn.decl) = true := by
    rcases hb with hb | hb <;> simp [hb, hlast]
  rw [hcond]
  simp

/-- The frame's horizontal edges are the hull edges over the side-marker
rects. -/
private theorem frameRect_horizontal_edges {P : Params} {cg : Graph} {run : Run}
    {gpos : Nat} {gn : Node}
    (hg : cg.nodes[gpos]? = some gn) (hgroup : gn.border = -2) :
    (frameRect P cg run gpos).x =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).minX ∧
    (frameRect P cg run gpos).x + (frameRect P cg run gpos).w =
      (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) []).right := by
  have hget : cg.nodes.getD gpos default = gn := by
    rw [List.getD_eq_getElem?_getD, hg, Option.getD_some]
  constructor
  · simp only [frameRect, hget, hgroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  · simp only [frameRect, hget, hgroup,
      show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    omega
  -- horizontal edges established

/-- Strict left bound for a dummy: the group frame left edge lies strictly
left of the dummy rect, via the left side marker at the dummy's rank. -/
private theorem dummyFrameLeftXStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true)
    (hpath : gn.decl ∈ nd.node.clusterPath)
    (hbracket : DummyMarkerBracket (componentCandidate execution.graph comp candidate) run) :
    (frameRect execution.params (componentCandidate execution.graph comp candidate) run gpos).x <
      (Labels.rectAt run.proper run.xs run.ys d).x := by
  obtain ⟨mL, mR, nL, nR, layer, hlayer, hcoordML, hcoordMR, hbL, hbR,
      hlastL, hlastR, hwidthL, hwidthR, hrankL, hrankR, li, mi, ri, hli, hmi, hri,
      hlt, hgt⟩ :=
    hbracket gpos gn hg hgroup d nd hnd hdum hpath
  obtain ⟨hproperML, hxML⟩ := componentRun_border_record hrun hcoordML (Or.inl hbL)
  obtain ⟨cn, hcn, hcnDum, hcnBord, hcnPath⟩ := proper_to_coordinate_dummy_copy hrun hnd hdum
  have hcnB0 : cn.node.border = 0 :=
    (componentRun_coordinate_bordersWellFormed execution.graph_eq hcomp hrun).2.2
      d cn hcn hcnDum
  obtain ⟨hproperD, hxD⟩ := componentRun_nonproxy_record hrun hcn (by rw [hcnB0]; decide)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  obtain ⟨_, _, _, hcS, hkeys, _, _, _⟩ :=
    rankSource_of_componentRun execution.graph_eq hcomp hrun
  have hshapeC := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (measuredGraph_shape execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hkeys hshapeC (by rw [hcS]; exact ha) (by rw [hcS]; exact hb)
      hba hbb hp
  have hsepL := cluster_all_pairs_separated hcross hunique _ hlayer
    li mi mL d _ _ hlt hli hmi hcoordML hcn
    (by rw [hbL]; decide) (by rw [hbL]; decide)
    (by rw [hcnB0]; decide) (by rw [hcnB0]; decide)
  have hmemML : (nL, mL) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproperML
  have hmemL : Labels.rectAt run.proper run.xs run.ys mL ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) :=
    marker_rect_mem_borders hg hmemML (Or.inl hbL) hlastL
  have hframeX := (frameRect_horizontal_edges (P := execution.params) (run := run)
    hg hgroup).1
  have hlo := boundsOf_minX_le_rect_x _ [] _ hmemL
  have hmStrict : (Labels.rectAt run.proper run.xs run.ys mL).x <
      (Labels.rectAt run.proper run.xs run.ys d).x := by
    have hmlW' : (0 : Int) ≤ nL.node.w :=
      (sizesNonneg_lookup hsizes mL nL hcoordML).1
    have hdW' : (0 : Int) ≤ cn.node.w :=
      (sizesNonneg_lookup hsizes d cn hcn).1
    have hloop1 : (0 : Int) ≤ (nL.node.loopExtent : Int) := Int.natCast_nonneg _
    have hloop2 : (0 : Int) ≤ (cn.node.loopExtent : Int) := Int.natCast_nonneg _
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcoordML, hcn] at hsepL
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproperML, hproperD, hxML, hxD] at hsepL ⊢
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsepL ⊢
    omega
  have h1 := hframeX
  have h2 := hlo
  have h3 := hmStrict
  omega

/-- Strict right bound for a dummy: the dummy rect right edge lies strictly
left of the group frame right edge, via the right side marker. -/
private theorem dummyFrameRightXStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {gpos : Nat} {gn : Node}
    (hg : (componentCandidate execution.graph comp candidate).nodes[gpos]? = some gn)
    (hgroup : gn.border = -2)
    {d : Nat} {nd : ProperNode}
    (hnd : run.proper.nodes[d]? = some nd)
    (hdum : nd.dummy = true)
    (hpath : gn.decl ∈ nd.node.clusterPath)
    (hbracket : DummyMarkerBracket (componentCandidate execution.graph comp candidate) run) :
    (Labels.rectAt run.proper run.xs run.ys d).x +
      (Labels.rectAt run.proper run.xs run.ys d).w <
      (frameRect execution.params (componentCandidate execution.graph comp candidate)
        run gpos).x +
        (frameRect execution.params (componentCandidate execution.graph comp candidate)
          run gpos).w := by
  obtain ⟨mL, mR, nL, nR, layer, hlayer, hcoordML, hcoordMR, hbL, hbR,
      hlastL, hlastR, hwidthL, hwidthR, hrankL, hrankR, li, mi, ri, hli, hmi, hri,
      hlt, hgt⟩ :=
    hbracket gpos gn hg hgroup d nd hnd hdum hpath
  obtain ⟨hproperMR, hxMR⟩ := componentRun_border_record hrun hcoordMR (Or.inr hbR)
  obtain ⟨cn, hcn, hcnDum, hcnBord, hcnPath⟩ := proper_to_coordinate_dummy_copy hrun hnd hdum
  have hcnB0 : cn.node.border = 0 :=
    (componentRun_coordinate_bordersWellFormed execution.graph_eq hcomp hrun).2.2
      d cn hcn hcnDum
  obtain ⟨hproperD, hxD⟩ := componentRun_nonproxy_record hrun hcn (by rw [hcnB0]; decide)
  obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _, _, _⟩ := componentRun_spec hrun
  obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
  have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  obtain ⟨_, _, _, hcS, hkeys, _, _, _⟩ :=
    rankSource_of_componentRun execution.graph_eq hcomp hrun
  have hshapeC := componentCandidate_shape (components_nodup execution.graph comp hcomp)
    (measuredGraph_shape execution.graph_eq) candidate
  have hunique : ∀ (a b : Nat) (na nb : ProperNode),
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      na.node.border = 3 → nb.node.border = 3 →
      na.node.clusterPath = nb.node.clusterPath → a = b := by
    intro a b na nb ha hb hba hbb hp
    exact pc_title_unique hkeys hshapeC (by rw [hcS]; exact ha) (by rw [hcS]; exact hb)
      hba hbb hp
  have hsepR := cluster_all_pairs_separated hcross hunique _ hlayer
    mi ri d mR _ _ hgt hmi hri hcn hcoordMR
    (by rw [hcnB0]; decide) (by rw [hcnB0]; decide)
    (by rw [hbR]; decide) (by rw [hbR]; decide)
  have hdW := (sizesNonneg_lookup hsizes d cn hcn).1
  have hnRW := (sizesNonneg_lookup hsizes mR nR hcoordMR).1
  have hmemMR : (nR, mR) ∈ run.proper.nodes.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hproperMR
  have hmemR : Labels.rectAt run.proper run.xs run.ys mR ∈
      (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some gn.decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2)
        else none) :=
    marker_rect_mem_borders hg hmemMR (Or.inr hbR) hlastR
  have hframeXW := (frameRect_horizontal_edges (P := execution.params) (run := run)
    hg hgroup).2
  have hloR := rect_right_le_boundsOf_right _ [] _ hmemR
  have hmStrictR : (Labels.rectAt run.proper run.xs run.ys d).x +
      (Labels.rectAt run.proper run.xs run.ys d).w <
      (Labels.rectAt run.proper run.xs run.ys mR).x +
        (Labels.rectAt run.proper run.xs run.ys mR).w := by
    have hdW' : (0 : Int) ≤ cn.node.w :=
      (sizesNonneg_lookup hsizes d cn hcn).1
    have hnRW' : (0 : Int) ≤ nR.node.w :=
      (sizesNonneg_lookup hsizes mR nR hcoordMR).1
    have hloopD : (0 : Int) ≤ (cn.node.loopExtent : Int) := Int.natCast_nonneg _
    have hloopR : (0 : Int) ≤ (nR.node.loopExtent : Int) := Int.natCast_nonneg _
    simp only [CoordsImpl.coordSep, CoordsImpl.nodeW, hcn, hcoordMR] at hsepR
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
      hproperD, hproperMR, hxD, hxMR] at hsepR ⊢
    simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hsepR ⊢
    omega
  have h1 := hframeXW
  have h2 := hloR
  have h3 := hmStrictR
  omega

/-- Executed strict dummy frame, linked form: every dummy proper node whose
cluster path carries a group declaration lies strictly inside that group's
frame at its own index. The vertical halves transport the strict dummy rank
straddle (`dummyTopRankStrict`, `dummyBottomRankStrict`) through the rank
tops; the horizontal halves transport the marker bracket (`DummyMarkerBracket`)
through same-rank separation. The only residual is the order-stage
`DummyMarkerBracket`. -/
theorem strictDummyFrame_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o)) (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (hbracket : DummyMarkerBracket (componentCandidate execution.graph comp candidate) run) :
    StrictDummyFrameLinked execution.params
      (componentCandidate execution.graph comp candidate) run := by
  intro gpos gn hg hgroup d nd hnd hdum hpath
  have hlines : execution.lines.length = inp.boxes.length := by
    have h := (mapM_getElem? _ _ _ execution.lines_eq).1
    simpa only [List.length_zipIdx] using h
  have hdLen : d < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hnd).1
  have hgetD : run.proper.nodes.getD d default = nd := by
    simp [List.getD_eq_getElem?_getD, hnd]
  have hpathC : (run.proper.nodes.getD d default).node.clusterPath.contains gn.decl = true := by
    rw [hgetD]
    exact List.contains_iff_mem.mpr hpath
  have hdumGet : (run.proper.nodes.getD d default).dummy = true := by
    rw [hgetD]; exact hdum
  have hindexLt : gpos < (componentCandidate execution.graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hg).1
  have hR1 : rk run.coordinateProper.rank gpos < rk run.coordinateProper.rank d :=
    dummyTopRankStrict execution.graph_eq hlines hwf hframed hcomp hrun hg hgroup
      hindexLt hdLen hpathC hdumGet
  have hTop := dummyFrameTopYStrict execution hrun hg hgroup hnd hR1
  have hBot := dummyFrameBotYStrict execution hwf hframed hcomp hrun hg hgroup hlines
    hnd hdum hpath
  have hLeft := dummyFrameLeftXStrict execution hcomp hrun hg hgroup hnd hdum hpath hbracket
  have hRight := dummyFrameRightXStrict execution hcomp hrun hg hgroup hnd hdum hpath
    hbracket
  refine ⟨hLeft, hRight, hTop, hBot⟩

end Elegant.Layered.PipelineImpl
