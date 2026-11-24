import Elegant.Layered.SideMarkerFactsProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.GroupBottomBoundaryProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Route
import Elegant.Layered.DummyChainRankProof
import Elegant.Layered.BottomSyntheticRankProof
import Elegant.Layered.BottomNestedRankProof
import Elegant.Layered.ForeignBottomInCandidateProof
import Elegant.Layered.BottomClearanceExistence
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.ComponentCoverage
import Elegant.Layered.CompoundPathFacts

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-!
# Side-marker anchor cover.

`SideMarkerAnchorCover` (`SideMarkerFactsProof.lean`) is the rank-assignment
half of the side-marker seam: for an executed `componentRun` on a component
candidate of a measured graph, any two proper nodes whose cluster paths carry
a declaration `decl` lie between the titled top and bottom markers of `decl`.

Proof outline, from executed-pipeline facts only:

* Lookup: `SideMarkerTopInCandidate` (residual below) recovers a candidate
  `-2` node `u` with `uNode.decl = decl` from one member. `titled_marker_record`
  lifts it to the titled top entry; `ForeignBottomInCandidate` (hypothesis,
  proved by another worker) supplies the candidate bottom, lifted the same
  way, which witnesses the `find?` on the titled graph. The routing mirrors
  `foreignRankPairAnchors` (`ForeignBorderAnchorsProof.lean`).
* Top bound: `TopMemberRankLe` (residual below) bounds every member below by
  the candidate top rank; title/coordinate/proper rank transports turn it
  into the titled-top `toNat` bound. `GroupTopSubtreeRankProper` cannot serve
  here: its `WellFormed` / `framedParents` / line-count premises are not
  available in this goal, so the `WellFormed`-free top bound is factored as a
  residual instead.
* Bottom bound: `BottomMemberRankCover` (residual below) bounds every member
  above by the candidate bottom rank. It is the `WellFormed`-free form of
  `bottomMemberRankLe` (`GroupBottomBoundaryProof.lean`): that theorem and
  its ingredients (`bottomOrigRankLe`, `BottomSyntheticRankLe`,
  `BottomNestedBottomRankLe`) thread line-count, `WellFormed`, and
  `framedParents` premises that this goal does not provide. The `find?`
  result is pinned to the candidate bottom index by bottom-marker uniqueness
  (one bottom per group box in `markExtras`), then the same transports apply.

All three residuals are pinned to the executed run, strictly simpler than the
goal, used below, and exercised by `proofs/wip/Probe/SideMarkerCoverProbe.lean`.
-/

/-- Residual (lookup): every declaration carried by an executed proper node
has its `-2` group marker in the same component candidate. The marker is
linked to the member by `Compound.constraints` edges (titles connect to every
plain node containing their declaration, nested members included), hence both
land in one reported component; only the lookup is assumed, no rank content. -/
def SideMarkerTopInCandidate : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {decl low : Nat} {lowNd : ProperNode},
      run.proper.nodes[low]? = some lowNd →
      lowNd.node.clusterPath.contains decl = true →
      ∃ (u : Nat) (uNode : Node),
        (componentCandidate graph comp candidate).nodes[u]? = some uNode ∧
        uNode.border = -2 ∧ uNode.decl = decl

/-- Residual (top rank bound): a candidate `-2` group top ranks at or below
every executed proper node whose cluster path carries its declaration. This is
the executed form of `GroupTopSubtreeRankProper` (`GroupTopRank.lean`), with
its line-count, `WellFormed`, and `framedParents` premises threaded through.
Only the `Int` inequality is assumed; title ranks, `find?`, and the bottom
bound are proved below. -/
def TopMemberRankLe : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u : Nat} {uNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    uNode.border = -2 →
    ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
    q.1.node.clusterPath.contains uNode.decl = true →
    rk run.proper.rank u ≤ rk run.proper.rank q.2

/-- Residual (bottom rank bound): every executed proper node whose cluster
path carries a group declaration ranks at or below the group's candidate
`border = 2` bottom marker. This is the executed form of `bottomMemberRankLe`
(`GroupBottomBoundaryProof.lean`), with its line-count, `WellFormed`, and
`framedParents` premises threaded through. Only the `Int` inequality is
assumed. -/
def BottomMemberRankCover : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    lines.length = inp.boxes.length →
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {v t : Nat} {ndV ndT : Node},
    (componentCandidate graph comp candidate).nodes[v]? = some ndV →
    (componentCandidate graph comp candidate).nodes[t]? = some ndT →
    ndV.border = 2 → ndT.border = -2 → ndV.decl = ndT.decl →
    ∀ (q : ProperNode × Nat), q ∈ run.proper.nodes.zipIdx →
    q.1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD t default).decl = true →
    rk run.coordinateProper.rank q.2 ≤ rk run.coordinateProper.rank v

/-- Executed top rank bound: a candidate `-2` group top ranks at or below
every executed proper node whose path carries its declaration. Discharges
`TopMemberRankLe` via the closed `groupTopSubtreeRankProper'`. -/
theorem topMemberRankLe : TopMemberRankLe := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run
    labels orderOptions hrun u uNode hu hb q hq hcontains
  have hqget : run.proper.nodes[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  have hi : q.2 < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hqget).1
  have huLt : u < (componentCandidate graph comp candidate).nodes.length :=
    (List.getElem?_eq_some_iff.mp hu).1
  have hget : run.proper.nodes.getD q.2 default = q.1 := by
    simp only [List.getD_eq_getElem?_getD, hqget, Option.getD_some]
  have hcontains' : (run.proper.nodes.getD q.2 default).node.clusterPath.contains
      uNode.decl = true := by
    rw [hget]
    exact hcontains
  exact groupTopSubtreeRankProper' hgraph hlines hwf hfp hcomp hrun hu hb huLt
    hi hcontains'

/-- Executed bottom rank bound: every executed proper node whose path carries
a group declaration ranks at or below the group's candidate `border = 2`
bottom marker. Discharges `BottomMemberRankCover` via the closed
`bottomMemberRankLe` with the proved synthetic and nested seams. -/
theorem bottomMemberRankCover : BottomMemberRankCover := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run
    labels orderOptions hrun v t ndV ndT hvGet htGet hbV hbT hdecl q hq hcontains
  have hsynth : ∀ (P : Params) (graph : Graph), BottomSyntheticRankLe P graph :=
    bottomSyntheticRankLe bottomDummyRankLe
  have hnest : ∀ (P : Params) (graph : Graph), BottomNestedBottomRankLe P graph :=
    bottomNestedBottomRankLe
  exact bottomMemberRankLe hgraph hlines hwf hfp hcomp hrun hvGet htGet hbV hbT
    hdecl hsynth hnest q hq hcontains

/-- `toNat` is monotone on nonnegative ranks. -/
private theorem smc_rkToNat_le {a b : Int} (ha : 0 ≤ a) (h : a ≤ b) :
    a.toNat ≤ b.toNat := by
  have h1 : (a.toNat : Int) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : Int) = b := Int.toNat_of_nonneg (Int.le_trans ha h)
  have h3 : (a.toNat : Int) ≤ (b.toNat : Int) := by omega
  exact Int.ofNat_le.mp h3

/-- A candidate `-2` node ends its cluster path in its declaration. -/
private theorem smc_top_getLast {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hb : uNode.border = -2) :
    uNode.clusterPath.getLast? = some uNode.decl := by
  obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hu (by omega)
  obtain ⟨_, _, _, _, hpath⟩ := measuredGraph_group_origin hgraph hsource hb
  rw [hpath]
  simp

/-- A candidate `border = 2` node ends its cluster path in its declaration. -/
private theorem smc_bottom_getLast {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} {candidate v : Nat} {nd : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[v]? = some nd)
    (hb : nd.border = 2) :
    nd.clusterPath.getLast? = some nd.decl := by
  obtain ⟨_, _, hsource⟩ := componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, _, _, hpath, _, _⟩ :=
    measuredGraph_bottom_origin hgraph (List.mem_of_getElem? hsource) hb
  rw [hpath]
  simp

/-- Title ranks agree with labeled ranks below the labeled length. -/
private theorem smc_titled_rk_eq (P : Params) (labeled : Proper) (i : Nat)
    (hi : i < labeled.nodes.length)
    (haligned : labeled.nodes.length = labeled.rank.length) :
    rk (titleReservations (sizeProperPorts P labeled)).rank i =
      rk labeled.rank i := by
  obtain ⟨extra, heq⟩ := titled_rank_prefix P labeled
  have hlt : i < labeled.rank.length := by omega
  have h1 : (titleReservations (sizeProperPorts P labeled)).rank[i]? =
      labeled.rank[i]? := by
    rw [heq, List.getElem?_append_left hlt]
  simp only [rk, List.getD_eq_getElem?_getD, h1]

/-- Labeled ranks agree with coordinate ranks at labeled indices. -/
private theorem smc_coord_rk_eq (P : Params) (labeled : Proper) (i : Nat)
    (hi : i < labeled.nodes.length)
    (haligned : labeled.nodes.length = labeled.rank.length) :
    rk (coordinateGraph P labeled).rank i = rk labeled.rank i := by
  have hlt : i < labeled.rank.length := by omega
  have hlook : labeled.rank[i]? = some labeled.rank[i] :=
    List.getElem?_eq_getElem hlt
  have hcoord := coordinateGraph_rank_record (P := P) hlook
  simp only [rk, List.getD_eq_getElem?_getD, hlook, hcoord, Option.getD_some]

/-- Every proper rank is nonnegative on a successful run. -/
private theorem smc_proper_rk_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run) (v : Nat)
    (hv : v < run.proper.nodes.length) : 0 ≤ rk run.proper.rank v := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hrouteEx, _, _, _, _⟩ :=
    componentRun_spec hrun
  have hcov :=
    (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hrouteEx).1).2.2.2.1
  obtain ⟨_, _, _, hnn⟩ := hcov v hv
  exact hnn

/-- A candidate lookup yields its component position and graph value. -/
private theorem smc_comp_origin {graph : Graph} {comp : List Nat}
    {candidate idx : Nat} {nd : Node}
    (h : (componentCandidate graph comp candidate).nodes[idx]? = some nd) :
    ∃ o, comp[idx]? = some o ∧ graph.nodes.getD o default = nd := by
  rw [componentCandidate_nodes] at h
  have h2 : (comp.map fun v => graph.nodes.getD v default)[idx]? = some nd := h
  rw [List.getElem?_map] at h2
  exact Option.map_eq_some_iff.mp h2

private theorem smc_filterMap_decl (boxesM : List ModelBox) (l : List (ModelBox × Nat)) : ((l.filterMap fun q => if q.1.role == .group then (some { decl := q.2, w := 0, h := 0, clusterPath := Compound.path boxesM q.1 ++ [q.2], border := 2 } : Option Node) else none).map (fun nd => nd.decl)) = ((l.filter fun q => q.1.role == .group).map (fun q => q.2)) := by
  rw [List.map_filterMap]
  have hpt : ∀ q : ModelBox × Nat, Option.map (fun nd => nd.decl) (if q.1.role == .group then (some { decl := q.2, w := 0, h := 0, clusterPath := Compound.path boxesM q.1 ++ [q.2], border := 2 } : Option Node) else none) = (if q.1.role == .group then some q.2 else none) := by
    intro q
    by_cases h : q.1.role == .group <;> simp [h]
  simp only [hpt]
  have hbridge : ∀ (l : List (ModelBox × Nat)), (l.filterMap fun q => if q.1.role == .group then (some q.2 : Option Nat) else none) = ((l.filter fun q => q.1.role == .group).map (fun q => q.2)) := by
    intro l
    induction l with
    | nil => rfl
    | cons q qs ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      split
      next h => simp_all
      next h => simp_all
  exact hbridge l

/-- Bottom extras carry distinct declarations: one bottom per group box. -/
private theorem smc_extras_decl_nodup (boxesM : List ModelBox) :
    ((markExtras boxesM).map (fun nd => nd.decl)).Nodup := by
  have heq : (markExtras boxesM).map (fun nd => nd.decl) =
      ((boxesM.zipIdx.filter fun q => q.1.role == .group).map (fun q => q.2)) := by
    have h0 := smc_filterMap_decl boxesM boxesM.zipIdx
    simpa [markExtras] using h0
  rw [heq]
  refine List.Nodup.sublist ((List.filter_sublist).map _) ?_
  rw [List.zipIdx_map_snd]
  exact List.nodup_range'

/-- Mapped originals never carry `border = 2`: `markOne` of a border-`0`
source node yields `0` or `-2`. -/
private theorem smc_mapped_border {boxesM : List ModelBox} {pad : Int}
    {titles : List (Int × Int)} {srcNodes : List Node}
    (hmeta : ∀ (i : Nat) (n : Node), srcNodes[i]? = some n → n.border = 0)
    {k : Nat} {m : Node}
    (hm : (srcNodes.zipIdx.map (markOne boxesM pad titles))[k]? = some m) :
    m.border = 0 ∨ m.border = -2 := by
  simp only [List.getElem?_map, List.getElem?_zipIdx] at hm
  cases hk : srcNodes[k]? with
  | none => simp [hk] at hm
  | some s =>
    simp only [hk, Option.map_some, Option.some.injEq] at hm
    subst hm
    have hb0 := hmeta k s hk
    unfold markOne
    cases hbx : boxesM[(s, k).2]? with
    | none =>
      have hbx' : boxesM[k]? = none := hbx
      simp [hbx', hb0]
    | some box =>
      have hbx' : boxesM[k]? = some box := hbx
      by_cases hg : (box.role == BoxRole.group) = true
      · simp [hbx', hg]
      · simp [hbx', hg, hb0]

/-- The titled `find?` bottom is the candidate bottom index: bottom markers
are unique per group box, and every titled path-match is one. Both bottoms
sit in the extras part at the same declaration position. -/
theorem titledBottomPin {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
    {u iB : Nat} {uNode bNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hBUlook : (componentCandidate graph comp candidate).nodes[iB]? = some bNode)
    (hBUbord : bNode.border = 2)
    (hBUdecl : bNode.decl = uNode.decl)
    {decl : Nat} (hdeclU : uNode.decl = decl)
    (hlastTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath.getLast? =
      some decl)
    {bot : ProperNode × Nat}
    (hbotFind : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
      (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
        entry.1.node.clusterPath ==
          (titleF ⟨uNode, false, none, false⟩).node.clusterPath)) =
      some bot) :
    bot.2 = iB := by
  have hbotMem : bot ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_of_find?_eq_some hbotFind
  have hbotPred := List.find?_some hbotFind
  simp only [Bool.and_eq_true, beq_iff_eq] at hbotPred
  obtain ⟨hbotB, hbotP⟩ := hbotPred
  have hbotLookup : (titleReservations (sizeProperPorts P labeled)).nodes[bot.2]? =
      some bot.1 :=
    List.mem_zipIdx_iff_getElem?.mp hbotMem
  rcases titled_node_origin hkeys hbotLookup with
    ⟨orig, horig, _, hbord, hpath⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = 2 := hbord.symm.trans hbotB
    have horigP : orig.node.clusterPath =
        (titleF ⟨uNode, false, none, false⟩).node.clusterPath :=
      hpath.symm.trans hbotP
    rcases hkeys bot.2 orig horig with
      ⟨nE, hnE, _, hnB, hnP⟩ | ⟨hdum, hb0, _⟩
    · have hnEB : nE.border = 2 := hnB.symm.trans horigB
      have hnEP : nE.clusterPath =
          (titleF ⟨uNode, false, none, false⟩).node.clusterPath :=
        hnP.symm.trans horigP
      have hlastE := smc_bottom_getLast hgraph hnE hnEB
      have hnEdecl : nE.decl = decl := by
        have hcongr := congrArg List.getLast? hnEP
        rw [hlastE, hlastTop] at hcongr
        exact Option.some.inj hcongr
      have hnBdecl : bNode.decl = decl := hBUdecl.trans hdeclU
      -- Both bottoms sit in the extras part, at the same position.
      obtain ⟨srcNodes, _, srcTitles, hprep, _, hmeta⟩ :=
        measuredGraph_prepared_source hgraph
      let boxesM := (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          ({ box with role := .node } : ModelBox) else box)
      have hmeta0 : ∀ (i : Nat) (n : Node), srcNodes[i]? = some n →
          n.border = 0 := fun i n hn => (hmeta i n hn).2
      have hnodes : graph.nodes =
          (srcNodes.zipIdx.map (markOne boxesM P.clusterPad srcTitles)) ++
          markExtras boxesM := by
        rw [hprep]
        rfl
      have hmappedLen : (srcNodes.zipIdx.map
          (markOne boxesM P.clusterPad srcTitles)).length = srcNodes.length := by
        simp
      obtain ⟨origE, hcompE, hvalE⟩ := smc_comp_origin hnE
      obtain ⟨origB, hcompB, hvalB⟩ := smc_comp_origin hBUlook
      have hlenE : origE < graph.nodes.length := by
        have hmemC : origE ∈ comp := List.mem_of_getElem? hcompE
        unfold components at hcomp
        obtain ⟨_, _, hrfl⟩ := List.mem_map.mp hcomp
        subst hrfl
        have hmemF : origE ∈ (List.range graph.nodes.length).filter _ :=
          List.mem_of_getElem? hcompE
        exact List.mem_range.mp (List.mem_filter.mp hmemF).1
      have hlenB : origB < graph.nodes.length := by
        have hmemC : origB ∈ comp := List.mem_of_getElem? hcompB
        unfold components at hcomp
        obtain ⟨_, _, hrfl⟩ := List.mem_map.mp hcomp
        subst hrfl
        have hmemF : origB ∈ (List.range graph.nodes.length).filter _ :=
          List.mem_of_getElem? hcompB
        exact List.mem_range.mp (List.mem_filter.mp hmemF).1
      have hgE : graph.nodes[origE]? = some nE := by
        rw [← hvalE, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlenE, Option.getD_some]
      have hgB : graph.nodes[origB]? = some bNode := by
        rw [← hvalB, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlenB, Option.getD_some]
      have hleE : (srcNodes.zipIdx.map
          (markOne boxesM P.clusterPad srcTitles)).length ≤ origE := by
        by_cases hlt : origE < (srcNodes.zipIdx.map
          (markOne boxesM P.clusterPad srcTitles)).length
        · have hmapped : (srcNodes.zipIdx.map
              (markOne boxesM P.clusterPad srcTitles))[origE]? = some nE := by
            rw [hnodes] at hgE
            rw [List.getElem?_append_left hlt] at hgE
            exact hgE
          have h02 := smc_mapped_border hmeta0 hmapped
          omega
        · omega
      have hleB : (srcNodes.zipIdx.map
          (markOne boxesM P.clusterPad srcTitles)).length ≤ origB := by
        by_cases hlt : origB < (srcNodes.zipIdx.map
          (markOne boxesM P.clusterPad srcTitles)).length
        · have hmapped : (srcNodes.zipIdx.map
              (markOne boxesM P.clusterPad srcTitles))[origB]? = some bNode := by
            rw [hnodes] at hgB
            rw [List.getElem?_append_left hlt] at hgB
            exact hgB
          have h02 := smc_mapped_border hmeta0 hmapped
          omega
        · omega
      have hEextras : (markExtras boxesM)[origE -
          (srcNodes.zipIdx.map (markOne boxesM P.clusterPad srcTitles)).length]? =
          some nE := by
        rw [hnodes] at hgE
        rw [List.getElem?_append_right hleE] at hgE
        exact hgE
      have hBextras : (markExtras boxesM)[origB -
          (srcNodes.zipIdx.map (markOne boxesM P.clusterPad srcTitles)).length]? =
          some bNode := by
        rw [hnodes] at hgB
        rw [List.getElem?_append_right hleB] at hgB
        exact hgB
      have hdeclEq : nE.decl = bNode.decl := hnEdecl.trans hnBdecl.symm
      have hpos : origE -
          (srcNodes.zipIdx.map (markOne boxesM P.clusterPad srcTitles)).length =
          origB - (srcNodes.zipIdx.map
            (markOne boxesM P.clusterPad srcTitles)).length :=
        nodup_map_inj_aux (fun nd : Node => nd.decl) (smc_extras_decl_nodup boxesM)
          hEextras hBextras hdeclEq
      have horigEq : origE = origB := by omega
      rw [horigEq] at hcompE
      exact nodup_map_inj_aux (fun x => x)
        (by simpa using components_nodup graph comp hcomp) hcompE hcompB rfl
    · omega
  · omega

/-- A titled `-2` anchor with the same path-last as the candidate top is the
candidate top index: titled owners are unique. -/
theorem titledTopPin {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {labeled : Proper}
    (hkeys : NodeKeys (componentCandidate graph comp candidate) labeled)
    (hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩)
    {u : Nat} {uNode : Node}
    (hu : (componentCandidate graph comp candidate).nodes[u]? = some uNode)
    (hbU : uNode.border = -2)
    {top : ProperNode × Nat}
    (htopMem : top ∈ (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx)
    (hbTop : top.1.node.border = -2)
    (hlastTop : top.1.node.clusterPath.getLast? = some uNode.decl) :
    top.2 = u := by
  have htopLookup : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htopMem
  have hrequested : (titleReservations (sizeProperPorts P labeled)).nodes[u]? =
      some (titleF ⟨uNode, false, none, false⟩) :=
    titled_marker_record (hrecords u uNode hu) (Or.inl hbU)
  have hrequestedBorder : (titleF ⟨uNode, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hbU
  have howner : top.1.node.clusterPath.getLast? =
      (titleF ⟨uNode, false, none, false⟩).node.clusterPath.getLast? := by
    have hpathTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath =
        uNode.clusterPath :=
      (titleF_keys _).2.2.1
    have hlastU : uNode.clusterPath.getLast? = some uNode.decl :=
      smc_top_getLast hgraph hu hbU
    rw [hpathTop, hlastU]
    exact hlastTop
  exact titled_group_owner_unique hgraph hcomp hkeys hrecords htopLookup hrequested
    hbTop hrequestedBorder howner

/-- The executed side-marker anchor cover. -/
theorem sideMarkerAnchorCover
    (hbot : ForeignBottomInCandidate)
    (hlookup : SideMarkerTopInCandidate)
    (htopmem : TopMemberRankLe)
    (hbotmem : BottomMemberRankCover) :
    SideMarkerAnchorCover := by
  intro P inp o lines graph hgraph hlines hwf hfp comp hcomp candidate run labels orderOptions
    hrun decl low high lowNd highNd hlow hcontainLow hhigh hcontainHigh
  -- Candidate top from the lookup residual.
  obtain ⟨u, uNode, hu, hbU, hdeclU⟩ := hlookup hgraph hlines hwf hfp hcomp hrun hlow hcontainLow
  -- Candidate bottom from the colocation hypothesis.
  obtain ⟨iB, bNode, hBUlook, hBUbord, hBUdecl, hBUpath⟩ :=
    hbot hgraph hcomp hrun hu hbU
  -- Labeled source with coordinate equation and rank alignment.
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have halignedT : (titleReservations (sizeProperPorts P labeled)).nodes.length =
      (titleReservations (sizeProperPorts P labeled)).rank.length :=
    titleReservations_node_rank_alignment P haligned
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have hrecords : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
        labeled.nodes[index]? = some ⟨node, false, none, false⟩ := by
    intro index node hnode
    exact addLabelNodes_untouched_node hl (normalize_node_record hn hnode) rfl
  have huLt : u < labeled.nodes.length :=
    (List.getElem?_eq_some_iff.mp (hrecords u uNode hu)).1
  have hiBLt : iB < labeled.nodes.length :=
    (List.getElem?_eq_some_iff.mp (hrecords iB bNode hBUlook)).1
  -- Titled top entry.
  have hlabU : labeled.nodes[u]? = some ⟨uNode, false, none, false⟩ :=
    hrecords u uNode hu
  have htopU : (titleReservations (sizeProperPorts P labeled)).nodes[u]? =
      some (titleF ⟨uNode, false, none, false⟩) :=
    titled_marker_record hlabU (Or.inl hbU)
  have htopIn : (titleF ⟨uNode, false, none, false⟩, u) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr htopU
  have hbordTop : (titleF ⟨uNode, false, none, false⟩).node.border = -2 :=
    (titleF_keys _).2.1.trans hbU
  have hlastTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath.getLast? =
      some decl := by
    have hpathTop : (titleF ⟨uNode, false, none, false⟩).node.clusterPath =
        uNode.clusterPath := (titleF_keys _).2.2.1
    have hlastU := smc_top_getLast hgraph hu hbU
    rw [hpathTop, hlastU, hdeclU]
  -- Titled bottom witness and the `find?` equation.
  have hlabB : labeled.nodes[iB]? = some ⟨bNode, false, none, false⟩ :=
    hrecords iB bNode hBUlook
  have hbotT : (titleReservations (sizeProperPorts P labeled)).nodes[iB]? =
      some (titleF ⟨bNode, false, none, false⟩) :=
    titled_marker_record hlabB (Or.inr hBUbord)
  have hmemB : (titleF ⟨bNode, false, none, false⟩, iB) ∈
      (titleReservations (sizeProperPorts P labeled)).nodes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hbotT
  have hpredB : (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
      entry.1.node.clusterPath ==
        (titleF ⟨uNode, false, none, false⟩).node.clusterPath)
      (titleF ⟨bNode, false, none, false⟩, iB) = true := by
    have e1 : (titleF ⟨bNode, false, none, false⟩).node.border = 2 :=
      (titleF_keys _).2.1.trans hBUbord
    have e2 : (titleF ⟨bNode, false, none, false⟩).node.clusterPath =
        (titleF ⟨uNode, false, none, false⟩).node.clusterPath := by
      rw [(titleF_keys _).2.2.1, (titleF_keys _).2.2.1, hBUpath]
    simp [e1, e2]
  obtain ⟨bot, hbotFind⟩ : ∃ x,
      ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF ⟨uNode, false, none, false⟩).node.clusterPath)) =
        some x := by
    cases h : ((titleReservations (sizeProperPorts P labeled)).nodes.zipIdx.find?
        (fun entry : ProperNode × Nat => entry.1.node.border == 2 &&
          entry.1.node.clusterPath ==
            (titleF ⟨uNode, false, none, false⟩).node.clusterPath)) with
    | none =>
      have hnone := (List.find?_eq_none.mp h) _ hmemB
      simp [hpredB] at hnone
    | some x => exact ⟨x, rfl⟩
  -- The `find?` result is the candidate bottom index: bottom markers are
  -- unique per group box, and every titled match is one.
  have huniq : bot.2 = iB :=
    titledBottomPin hgraph hcomp hkeys hu hBUlook hBUbord hBUdecl hdeclU
      hlastTop hbotFind
  -- Rank transports between titled, labeled, coordinate, and proper ranks.
  have hrkTopEq : rk (titleReservations (sizeProperPorts P labeled)).rank u =
      rk run.proper.rank u := by
    have e1 := smc_titled_rk_eq P labeled u huLt haligned
    have e2 := smc_coord_rk_eq P labeled u huLt haligned
    have e3 := proper_rank_eq_coordinate hrun
    rw [e1, e3, ← hcoord]
    exact e2.symm
  have hrkBotEq : rk (titleReservations (sizeProperPorts P labeled)).rank iB =
      rk run.proper.rank iB := by
    have e1 := smc_titled_rk_eq P labeled iB hiBLt haligned
    have e2 := smc_coord_rk_eq P labeled iB hiBLt haligned
    have e3 := proper_rank_eq_coordinate hrun
    rw [e1, e3, ← hcoord]
    exact e2.symm
  -- Top bound from the top-member residual.
  have hcontainLow' : (lowNd, low).1.node.clusterPath.contains uNode.decl = true := by
    rw [hdeclU]
    exact hcontainLow
  have hrkT : rk run.proper.rank u ≤ rk run.proper.rank low :=
    htopmem hgraph hlines hwf hfp hcomp hrun hu hbU (lowNd, low)
      (List.mem_zipIdx_iff_getElem?.mpr hlow) hcontainLow'
  have huProperLt : u < run.proper.nodes.length :=
    componentRun_original_nodes_covered hrun u
      (List.getElem?_eq_some_iff.mp hu).1
  have hnnT : 0 ≤ rk (titleReservations (sizeProperPorts P labeled)).rank u := by
    rw [hrkTopEq]
    exact smc_proper_rk_nonneg hrun u huProperLt
  have hloBnd : (rk (titleReservations (sizeProperPorts P labeled)).rank u).toNat ≤
      (rk run.proper.rank low).toNat := by
    have hrkT' : rk (titleReservations (sizeProperPorts P labeled)).rank u ≤
        rk run.proper.rank low := by
      rw [hrkTopEq]
      exact hrkT
    exact smc_rkToNat_le hnnT hrkT'
  -- Bottom bound from the proved member-rank bound at the pinned index.
  have hgetU : (componentCandidate graph comp candidate).nodes.getD u default =
      uNode := by
    rw [List.getD_eq_getElem?_getD, hu, Option.getD_some]
  have hcontainHigh' : (highNd, high).1.node.clusterPath.contains
      ((componentCandidate graph comp candidate).nodes.getD u default).decl =
      true := by
    rw [hgetU, hdeclU]
    exact hcontainHigh
  have hrkB : rk run.coordinateProper.rank high ≤
      rk run.coordinateProper.rank iB :=
    hbotmem hgraph hlines hwf hfp hcomp hrun hBUlook hu hBUbord hbU hBUdecl (highNd, high)
      (List.mem_zipIdx_iff_getElem?.mpr hhigh) hcontainHigh'
  have hhighLt : high < run.proper.nodes.length :=
    (List.getElem?_eq_some_iff.mp hhigh).1
  have hnnB : 0 ≤ rk run.proper.rank high :=
    smc_proper_rk_nonneg hrun high hhighLt
  have hrkBEq : rk (titleReservations (sizeProperPorts P labeled)).rank bot.2 =
      rk run.proper.rank iB := by
    rw [huniq]
    exact hrkBotEq
  have hhiBnd : (rk run.proper.rank high).toNat ≤
      (rk (titleReservations (sizeProperPorts P labeled)).rank bot.2).toNat := by
    have hrkB' : rk run.proper.rank high ≤
        rk (titleReservations (sizeProperPorts P labeled)).rank bot.2 := by
      rw [hrkBEq, proper_rank_eq_coordinate hrun]
      exact hrkB
    exact smc_rkToNat_le hnnB hrkB'
  exact ⟨labeled, hcoord, halignedT,
    (titleF ⟨uNode, false, none, false⟩, u), bot,
    htopIn, hbordTop, hlastTop, hbotFind, hloBnd, hhiBnd⟩


end Elegant.Layered.PipelineImpl
