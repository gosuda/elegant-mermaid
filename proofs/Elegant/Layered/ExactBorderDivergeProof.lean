import Elegant.Layered.ExactBorderChainXAlignedProof
import Elegant.Layered.DivergeTiedHeadsProof
import Elegant.Layered.BorderInnerFoldProof

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact border-diverge stability and side-chain shape.

Targets (premises of `X_foreignBorderChainXAligned_of_stable` in
`ExactBorderChainXAlignedProof`):

* `X_foreignSideChainShapeClosed_holds`: the executed side-chain shape
  (`ForeignSideChainShape`) for exact runs. Replays the plain closed proof
  (`foreignSideChainShape_executed` in `BorderInnerFoldProof`, assembling
  `foreignSideChainShape` from the five fields) over `componentRunX` through
  `componentRunX_spec` (`ExactFlatFacts`) and `componentRunX_eq_gen`
  (`ComponentRunGen`): the ordering stage (`OrderImpl.order` over
  `coordinateGen`) reads only ranks, `(dummy, border, clusterPath, decl)`,
  edges, and chains, all preserved by both size hooks
  (`sizeProperPorts_key`, `sizeProperPortsX_key`), so every generic ordering
  lemma applies unchanged; the border-construction facts are redone with the
  exact hook (`titleReservations (sizeProperPortsX P exact _)`).
* `X_foreignBorderDivergeStable_of_sweep`: the exact twin stability, reduced
  to the single tied-sweep premise `X_DivergeTiedSweepStable` below, mirroring
  the plain split (`foreignBorderDivergeStableSeparated_holds` proved, tied
  case from the sweep invariant via `foreignBorderDivergeStable_closed`).

Probe evidence: `wip/Probe/ExactChainAlignedTShapeProbe.lean` (flat and
nested groups, plain/zero/huge fixed sizes, TB and LR: every exact run has
`shapeVios=0` and `divergeVios=0`).
-/

/-- Exact twin of `DivergeTiedSweepStable` (`DivergeTiedHeadsProof`): in an
executed exact run, two side markers whose cluster paths are divergent keep
the same relative order on every layer pair they share, provided their
divergent heads tie under `siblingNumber` at some position function. Strictly
narrower than `X_ForeignBorderDivergeStable` (tied divergent pairs only: one
numeric equality, no layers or positions beyond the goal's own). -/
def X_DivergeTiedSweepStable (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      ∀ {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat},
        na.node.clusterPath = Pa ++ A :: r1 →
        nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
        ∀ {pos : Nat → Int},
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper pos) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper pos) B →
        ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
          l2[i']? = some a' → l2[j']? = some b' →
          (i < j ↔ i' < j')



/-! ## Exact construction facts (copies of the `XBC_` helpers in
`ExactBorderChainXAlignedProof`, which are private there and re-proved here
under the `xed_` prefix). -/

/-- `orientNode` keeps decl/border/clusterPath. -/
private theorem xed_orientNode_key (d : Direction) (n : Node) :
    (orientNode d n).decl = n.decl ∧ (orientNode d n).border = n.border ∧
      (orientNode d n).clusterPath = n.clusterPath := by
  cases d <;> exact ⟨rfl, rfl, rfl⟩

/-- Exact graphs keep the measured node count. -/
private theorem xed_exactGraph_length {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph) :
    graph.nodes.length = graph0.nodes.length := by
  unfold exactGraph at hgraphX
  obtain ⟨nodes, hmap, hrest⟩ := bind_ok hgraphX
  have hgeq : graph = { graph0 with nodes := nodes } := Except.ok.inj hrest.symm
  obtain ⟨hlen, _⟩ := mapM_getElem? _ _ _ hmap
  subst hgeq
  exact hlen

/-- Exact-graph nodes keep decl/border/clusterPath of the measured node. -/
private theorem xed_exactGraph_node {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {i : Nat} {n : Node} (h : graph.nodes[i]? = some n) :
    ∃ n0 : Node, graph0.nodes[i]? = some n0 ∧ n.decl = n0.decl ∧ n.border = n0.border ∧
      n.clusterPath = n0.clusterPath := by
  unfold exactGraph at hgraphX
  obtain ⟨nodes, hmap, hrest⟩ := bind_ok hgraphX
  have hgeq : graph = { graph0 with nodes := nodes } := Except.ok.inj hrest.symm
  have hnodes : nodes[i]? = some n := by subst hgeq; exact h
  obtain ⟨hlen, hrec⟩ := mapM_getElem? _ _ _ hmap
  have hi : i < graph0.nodes.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hnodes).1
    omega
  obtain ⟨n0, h0⟩ : ∃ n0, graph0.nodes[i]? = some n0 :=
    ⟨_, List.getElem?_eq_getElem hi⟩
  obtain ⟨b, hfb, hbnodes⟩ := hrec i n0 h0
  have hb : b = n := Option.some.inj (hbnodes.symm.trans hnodes)
  dsimp only at hfb
  cases hbx : inp.boxes[n0.decl]? with
  | none =>
    simp only [hbx] at hfb
    have hbn : b = n0 := (Except.ok.inj hfb.symm)
    exact ⟨n0, h0, by rw [← hb, hbn], by rw [← hb, hbn], by rw [← hb, hbn]⟩
  | some box =>
    simp only [hbx] at hfb
    by_cases hc : ((!exactIds.contains box.id &&
      !(box.role == .group && inp.fixedSizes.any (·.1 == box.id))) = true)
    · rw [ite_eq_left hc] at hfb
      have hbn : b = n0 := (Except.ok.inj hfb.symm)
      exact ⟨n0, h0, by rw [← hb, hbn], by rw [← hb, hbn], by rw [← hb, hbn]⟩
    · rw [ite_eq_right hc] at hfb
      cases hfind : inp.fixedSizes.find? (·.1 == box.id) with
      | none =>
        simp only [hfind] at hfb
        cases hfb
      | some fixed =>
        simp only [hfind] at hfb
        by_cases he1 : Loops.exactExtent P.slot
          (loopSizes graph0.edges measured n0.decl P.slot) < 0
        · rw [ite_eq_left he1] at hfb
          cases hfb
        · rw [ite_eq_right he1] at hfb
          generalize hsz : orientNode o.direction
            { n0 with w := fixed.2.w, h := fixed.2.h } = size at hfb
          by_cases he2 : I32_MAX < Loops.exactExtent P.slot
            (loopSizes graph0.edges measured n0.decl P.slot) ∨
            I32_MAX < size.w + 2 * Loops.exactExtent P.slot
              (loopSizes graph0.edges measured n0.decl P.slot)
          · rw [ite_eq_left he2] at hfb
            cases hfb
          · rw [ite_eq_right he2] at hfb
            have hbn : b = { size with loopExtent :=
              (Loops.exactExtent P.slot
                (loopSizes graph0.edges measured n0.decl P.slot)).toNat } :=
              Except.ok.inj hfb.symm
            obtain ⟨hd, hbdr, hp⟩ := xed_orientNode_key o.direction
              { n0 with w := fixed.2.w, h := fixed.2.h }
            rw [hsz] at hd hbdr hp
            exact ⟨n0, h0, by rw [← hb, hbn]; exact hd,
              by rw [← hb, hbn]; exact hbdr, by rw [← hb, hbn]; exact hp⟩
/-- `CgShape` transfers across the exact graph. -/
private theorem xed_exact_cgShape {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph) :
    CgShape graph := by
  have hs0 := measuredGraph_shape hgraph0
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨n0a, ha0, _, hb0a, hp0a⟩ := xed_exactGraph_node hgraphX ha
    obtain ⟨n0b, hb0, _, hb0b, hp0b⟩ := xed_exactGraph_node hgraphX hb
    have h1' : n0a.border = -2 := by rw [← hb0a]; exact h1
    have h2' : n0b.border = -2 := by rw [← hb0b]; exact h2
    have hp' : n0a.clusterPath = n0b.clusterPath := by rw [← hp0a, ← hp0b]; exact hp
    exact hs0.1 a b n0a n0b ha0 hb0 h1' h2' hp'
  · intro n hn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb0, _⟩ := xed_exactGraph_node hgraphX hi
    have h3 := hs0.2 n0 (List.mem_of_getElem? h0)
    rw [hb0]
    exact h3

/-- Marker shapes transfer across the exact graph component candidates. -/
private theorem xed_marker_shape {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} {candidate index : Nat} {node : Node}
    (hnode : (componentCandidate graph comp candidate).nodes[index]? = some node) :
    (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
      (node.border = -2 → node.clusterPath ≠ []) := by
  by_cases hplain : node.border = 0
  · exact ⟨Or.inl hplain, fun hgroup => by omega⟩
  · obtain ⟨original, _, hsource⟩ := componentCandidate_nonplain_source hnode hplain
    obtain ⟨n0, h0, _, hb0, hp0⟩ := xed_exactGraph_node hgraphX hsource
    have hm := measuredGraph_marker_shape hgraph0 h0
    refine ⟨?_, ?_⟩
    · rcases hm.1 with h0 | h0 | h0
      · exact Or.inl (by rw [hb0]; exact h0)
      · exact Or.inr (Or.inl (by rw [hb0]; exact h0))
      · exact Or.inr (Or.inr (by rw [hb0]; exact h0))
    · intro hgroup
      have hgroup0 : n0.border = -2 := by rw [← hb0]; exact hgroup
      have hne := hm.2 hgroup0
      rw [hp0]
      exact hne
/-- X copy of `sizeProperPorts_node_origin`: exact sizing keeps
dummy/border/clusterPath per index. -/
private theorem xed_sized_node_origin (P : Params) (exact : List Nat) (source : Proper)
    {index : Nat} {node : ProperNode}
    (hnode : (sizeProperPortsX P exact source).nodes[index]? = some node) :
    ∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath := by
  have hkey := sizeProperPortsX_key P exact source index
  rw [hnode] at hkey
  cases horiginal : source.nodes[index]? with
  | none => simp [horiginal] at hkey
  | some original =>
      simp only [horiginal, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkey
      exact ⟨original, rfl, hkey⟩

/-- X copy of `titleReservations_node_rank_alignment`. -/
private theorem xed_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
    (h : source.nodes.length = source.rank.length) :
    (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length := by
  rw [titleReservations_nodes]
  simp only [List.length_append, List.length_map, sizeProperPortsX_length]
  have hrank : (titleReservations (sizeProperPortsX P exact source)).rank =
      source.rank ++ (titleNodes (sizeProperPortsX P exact source)).map
        (fun entry => rk source.rank entry.2) := by
    unfold titleReservations titleNodes sizeProperPortsX
    rfl
  rw [hrank]
  simp only [List.length_append, List.length_map]
  omega
/-- X copy of `titled_node_origin`. -/
private theorem xed_titled_node_origin {cg : Graph} {P : Params} {exact : List Nat}
    {source : Proper}
    (hkeys : NodeKeys cg source) {index : Nat} {node : ProperNode}
    (hnode : (titleReservations (sizeProperPortsX P exact source)).nodes[index]? = some node) :
    (∃ original : ProperNode, source.nodes[index]? = some original ∧
      node.dummy = original.dummy ∧ node.node.border = original.node.border ∧
      node.node.clusterPath = original.node.clusterPath) ∨
    (node.dummy = false ∧ node.node.border = 3) := by
  rw [titleReservations_nodes] at hnode
  by_cases hi : index < (sizeProperPortsX P exact source).nodes.length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map] at hnode
    obtain ⟨sized, hsized, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨original, horiginal, hd, hb, hp⟩ :=
      xed_sized_node_origin P exact source hsized
    have ht := titleF_keys sized
    rw [heq] at ht
    exact Or.inl ⟨original, horiginal, ht.1.trans hd,
      ht.2.1.trans hb, ht.2.2.1.trans hp⟩
  · rw [List.getElem?_append_right (by
      simpa only [List.length_map] using Nat.le_of_not_gt hi),
      List.getElem?_map] at hnode
    obtain ⟨entry, hentry, heq⟩ := Option.map_eq_some_iff.mp hnode
    obtain ⟨hsized, hborder⟩ := titleNodes_spec hentry
    obtain ⟨original, horiginal, hd, hb, _⟩ :=
      xed_sized_node_origin P exact source hsized
    have hreal : original.dummy = false := by
      rcases hkeys entry.2 original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · exact hreal
      · rw [hplain] at hb
        omega
    right
    rw [← heq]
    exact ⟨hd.trans hreal, rfl⟩
/-- X titled border readiness. -/
private theorem xed_titled_ready {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, xed_titled_alignment P exact haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases xed_titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, _⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, _⟩ | ⟨_, hborder, _⟩
      · have hc := (hmarkers index before hbefore).1
        rw [hb, hborder]
        rcases hc with hc | hc | hc <;> omega
      · rw [hb, hborder]
        exact ⟨by decide, by decide⟩
    · rw [hb]
      exact ⟨by decide, by decide⟩
  · intro node hnode hgroup
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases xed_titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases xed_titled_node_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases xed_titled_node_origin hkeys hb with
        ⟨ob, hob, _, hbb, hpb⟩ | ⟨_, hbb⟩
      · apply labeled_topUnique hkeys hshape hoa hob
        · omega
        · omega
        · rw [← hpa, ← hpb]
          exact hpath
      · omega
    · omega
  · intro node hnode hdummy
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases xed_titled_node_origin hkeys hindex with
      ⟨original, horiginal, hd, hb, _⟩ | ⟨hd, _⟩
    · rcases hkeys index original horiginal with
        ⟨_, _, hreal, _, _⟩ | ⟨_, hplain, _⟩
      · rw [hreal] at hd
        rw [hd] at hdummy
        cases hdummy
      · exact hb.trans hplain
    · rw [hd] at hdummy
      cases hdummy
/-- X titled border readiness for an executed exact run. -/
private theorem xed_titled_border_ready {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraphX P (exactDecls exactIds inp) labeled =
      run.coordinateProper ∧
      OrderImpl.BorderConstructionReady
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoordL, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  exact ⟨labeled, hcoordL, xed_titled_ready
    (addLabelNodes_keys _ _ _ (normalize_keys hn) hl)
    (componentCandidate_shape (components_nodup graph comp hcomp)
      (xed_exact_cgShape hgraph0 hgraphX) candidate)
    (fun _ _ hnode => xed_marker_shape hgraph0 hgraphX hnode)
    haligned⟩

/-- X coordinate proper is borders-well-formed for an executed exact run. -/
private theorem xed_bordersWellFormed {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run) :
    OrderImpl.BordersWellFormed run.coordinateProper := by
  obtain ⟨labeled, hc, hready⟩ := xed_titled_border_ready hgraph0 hgraphX hcomp hrunX
  rw [← hc]
  unfold coordinateGraphX
  exact materializeDummyPaths_bordersWellFormed
    (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
/-! ## Ordering stability: separated case proved, tied case from the premise. -/

/-- X twin of `ForeignBorderDivergeStableSeparated`: divergent sibling blocks
keep their order on every layer pair of an exact run, when their divergent
heads are separated (both in `Sibling.clusterIds` with the same
`Sibling.parentOf`). Strictly narrower than `X_ForeignBorderDivergeStable`
(numeric separation only: no layers, no positions). -/
def X_ForeignBorderDivergeStableSeparated (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {l1 l2 : List Nat}, l1 ∈ run.layers → l2 ∈ run.layers →
    ∀ {a b a' b' : Nat} {na nb na' nb' : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      run.coordinateProper.nodes[a']? = some na' →
      run.coordinateProper.nodes[b']? = some nb' →
      (na'.node.border = -1 ∨ na'.node.border = 1) →
      (nb'.node.border = -1 ∨ nb'.node.border = 1) →
      na.node.clusterPath = na'.node.clusterPath →
      nb.node.clusterPath = nb'.node.clusterPath →
      Divergent na.node.clusterPath nb.node.clusterPath →
      (∀ {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat},
        na.node.clusterPath = Pa ++ A :: r1 →
        nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
        A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
        B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
        OrderImpl.Sibling.parentOf run.coordinateProper A =
          OrderImpl.Sibling.parentOf run.coordinateProper B) →
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j')

/-- Separated divergent sibling blocks keep their order on every layer pair of
an exact run: replay of `foreignBorderDivergeStableSeparated_holds` over
`componentRunX` through `componentRunX_spec` and `xed_bordersWellFormed`.
The ordering lemmas (`order_siblingForm`, `siblingNumber_ne`,
`normalise_pair_stable`) read only ranks, `(dummy, border, clusterPath)`,
edges, and chains, so they apply unchanged. -/
theorem X_foreignBorderDivergeStableSeparated_holds (exactIds : List String) :
    X_ForeignBorderDivergeStableSeparated exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX comp hcomp candidate run
    labels orderOptions hrunX l1 l2 hmem1 hmem2 a b a' b' na nb na' nb' hna hnb
    hb1 hb2 hna' hnb' hb1' hb2' hpathA hpathB
  intro hdiv hseps i j i' j' hi1 hj1 hi2 hj2
  obtain ⟨Pa, A, B, r1, r2, hA, hB, hAB⟩ := hdiv
  have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
    rw [← hpathA]; exact hA
  have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
    rw [← hpathB]; exact hB
  have hwf := xed_bordersWellFormed hgraph0 hgraphX hcomp hrunX
  have hda : na.dummy = false :=
    dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false :=
    dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false :=
    dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false :=
    dummy_false_of_border hwf hnb' hb2'
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  obtain ⟨hmA, hmB, hpar⟩ := hseps hA hB hAB
  have hL := (OrderImpl.order_valid_layering _ _ _ horder').2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2
  have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
    cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
    | nil => simp [hl] at hmA
    | cons _ _ => rfl
  obtain ⟨Y, hform⟩ := order_siblingForm run.coordinateProper orderOptions
    run.layers horder' hne
  have hnum : (OrderImpl.Sibling.siblingNumber run.coordinateProper
      (OrderImpl.Sibling.siblingOrders run.coordinateProper
        (OrderImpl.posOf run.coordinateProper Y))) A ≠
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) B :=
    OrderImpl.siblingNumber_ne run.coordinateProper
      (OrderImpl.posOf run.coordinateProper Y) hmA hmB hAB hpar
  rw [hform] at hmem1 hmem2
  obtain ⟨Y1, hY1, e1mem⟩ := List.mem_map.mp hmem1
  obtain ⟨Y2, hY2, e2mem⟩ := List.mem_map.mp hmem2
  obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hY1
  obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hY2
  have hg1 : Y.getD k1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hk1]
  have hg2 : Y.getD k2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hk2]
  have e1 : OrderImpl.siblingLayer run.coordinateProper
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 []) = l1 := by
    rw [hg1]; exact e1mem
  have e2 : OrderImpl.siblingLayer run.coordinateProper
      (OrderImpl.Sibling.siblingNumber run.coordinateProper
        (OrderImpl.Sibling.siblingOrders run.coordinateProper
          (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 []) = l2 := by
    rw [hg2]; exact e2mem
  exact normalise_pair_stable e1 e2 hna hnb hna' hnb' hda hdb hda' hdb'
    hA hB hpa' hpb' hAB hnum hnd1 hnd2 hi1 hj1 hi2 hj2
/-- Empty cluster ids force every sibling number to zero at any position
function: the order list is empty, so the lookup misses and `idxOf` on `[]`
is `0`. -/
private theorem xed_nums_zero_of_empty {p : Proper}
    (hempty : OrderImpl.Sibling.clusterIds p = []) (pos : Nat → Int) (c : Nat) :
    OrderImpl.Sibling.siblingNumber p
      (OrderImpl.Sibling.siblingOrders p pos) c = 0 := by
  have horders : OrderImpl.Sibling.siblingOrders p pos = [] := by
    unfold OrderImpl.Sibling.siblingOrders
    simp [hempty]
  simp [OrderImpl.Sibling.siblingNumber, horders]

/-- Tied divergent border markers keep their order on an exact run: the
absent-heads mechanism (both heads outside `clusterIds` with equal parents)
forces a tie at every position function, and the exact sweep residual
concludes. -/
private theorem xed_foreignBorderDivergeStable_tied {exactIds : List String}
    (hres : X_DivergeTiedSweepStable exactIds)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {l1 l2 : List Nat} (hmem1 : l1 ∈ run.layers) (hmem2 : l2 ∈ run.layers)
    {a b a' b' : Nat} {na nb na' nb' : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hb1 : na.node.border = -1 ∨ na.node.border = 1)
    (hb2 : nb.node.border = -1 ∨ nb.node.border = 1)
    (hna' : run.coordinateProper.nodes[a']? = some na')
    (hnb' : run.coordinateProper.nodes[b']? = some nb')
    (hb1' : na'.node.border = -1 ∨ na'.node.border = 1)
    (hb2' : nb'.node.border = -1 ∨ nb'.node.border = 1)
    (hpathA : na.node.clusterPath = na'.node.clusterPath)
    (hpathB : nb.node.clusterPath = nb'.node.clusterPath)
    {Pa : List Nat} {A B : Nat} {r1 r2 : List Nat}
    (hA : na.node.clusterPath = Pa ++ A :: r1)
    (hB : nb.node.clusterPath = Pa ++ B :: r2) (hAB : A ≠ B)
    (hmem : A ∉ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
      B ∉ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
      OrderImpl.Sibling.parentOf run.coordinateProper A =
        OrderImpl.Sibling.parentOf run.coordinateProper B)
    {i j i' j' : Nat} (hi1 : l1[i]? = some a) (hj1 : l1[j]? = some b)
    (hi2 : l2[i']? = some a') (hj2 : l2[j']? = some b') :
    (i < j ↔ i' < j') :=
  hres hgraph0 hgraphX hcomp hrunX hmem1 hmem2 hna hnb hb1 hb2 hna' hnb' hb1' hb2'
    hpathA hpathB hA hB hAB (pos := fun _ => 0)
    (siblingNumber_tie_of_absent hmem.1 hmem.2.1 hmem.2.2) hi1 hj1 hi2 hj2
/-- The full exact ordering-stage stability, closed modulo the single tied
sweep premise: either every divergent decomposition is separated (apply the
proved separated case), or the divergent heads tie or differ at the executed
numbers (the sweep residual or the distinct-numbers argument closes). -/
theorem X_foreignBorderDivergeStable_of_sweep (exactIds : List String)
    (hres : X_DivergeTiedSweepStable exactIds) :
    X_ForeignBorderDivergeStable exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX comp hcomp candidate run
    labels orderOptions hrunX l1 l2 hmem1 hmem2 a b a' b' na nb na' nb' hna hnb
    hb1 hb2 hna' hnb' hb1' hb2' hpathA hpathB hdiv i j i' j' hi1 hj1 hi2 hj2
  have hwf := xed_bordersWellFormed hgraph0 hgraphX hcomp hrunX
  have hda : na.dummy = false :=
    dummy_false_of_border hwf hna hb1
  have hdb : nb.dummy = false :=
    dummy_false_of_border hwf hnb hb2
  have hda' : na'.dummy = false :=
    dummy_false_of_border hwf hna' hb1'
  have hdb' : nb'.dummy = false :=
    dummy_false_of_border hwf hnb' hb2'
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  have hL := (OrderImpl.order_valid_layering _ _ _ horder').2
  have hnd1 : l1.Nodup := OrderImpl.layering_mem_nodup hL hmem1
  have hnd2 : l2.Nodup := OrderImpl.layering_mem_nodup hL hmem2
  by_cases hsep : (∀ (Pa : List Nat) (A B : Nat) (r1 r2 : List Nat),
    na.node.clusterPath = Pa ++ A :: r1 →
    nb.node.clusterPath = Pa ++ B :: r2 → A ≠ B →
    A ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    B ∈ OrderImpl.Sibling.clusterIds run.coordinateProper ∧
    OrderImpl.Sibling.parentOf run.coordinateProper A =
      OrderImpl.Sibling.parentOf run.coordinateProper B)
  · refine X_foreignBorderDivergeStableSeparated_holds exactIds hgraph0 hgraphX hcomp
      hrunX hmem1 hmem2 hna hnb hb1 hb2 hna' hnb' hb1' hb2' hpathA hpathB hdiv ?_
      hi1 hj1 hi2 hj2
    intro Pa A B r1 r2 hA hB hAB
    exact hsep Pa A B r1 r2 hA hB hAB
  · obtain ⟨Pa, A, B, r1, r2, hA, hB, hAB⟩ := hdiv
    have hpa' : na'.node.clusterPath = Pa ++ A :: r1 := by
      rw [← hpathA]; exact hA
    have hpb' : nb'.node.clusterPath = Pa ++ B :: r2 := by
      rw [← hpathB]; exact hB
    by_cases hempty : OrderImpl.Sibling.clusterIds run.coordinateProper = []
    · have h0 := fun c => xed_nums_zero_of_empty hempty (fun _ => 0) c
      have htie : OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper (fun _ => 0)) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper (fun _ => 0)) B := by
        rw [h0 A, h0 B]
      exact hres hgraph0 hgraphX hcomp hrunX hmem1 hmem2 hna hnb hb1 hb2 hna'
        hnb' hb1' hb2' hpathA hpathB hA hB hAB (pos := fun _ => 0) htie hi1 hj1
        hi2 hj2
    · have hne : (OrderImpl.Sibling.clusterIds run.coordinateProper).isEmpty = false := by
        cases hl : OrderImpl.Sibling.clusterIds run.coordinateProper with
        | nil => exact absurd hl hempty
        | cons _ _ => rfl
      obtain ⟨Y, hform⟩ := order_siblingForm run.coordinateProper orderOptions
        run.layers horder' hne
      by_cases htie : OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y)) A =
        OrderImpl.Sibling.siblingNumber run.coordinateProper
          (OrderImpl.Sibling.siblingOrders run.coordinateProper
            (OrderImpl.posOf run.coordinateProper Y)) B
      · exact hres hgraph0 hgraphX hcomp hrunX hmem1 hmem2 hna hnb hb1 hb2 hna'
          hnb' hb1' hb2' hpathA hpathB hA hB hAB htie hi1 hj1 hi2 hj2
      · rw [hform] at hmem1 hmem2
        obtain ⟨Y1, hY1, e1mem⟩ := List.mem_map.mp hmem1
        obtain ⟨Y2, hY2, e2mem⟩ := List.mem_map.mp hmem2
        obtain ⟨k1, hk1⟩ := List.mem_iff_getElem?.mp hY1
        obtain ⟨k2, hk2⟩ := List.mem_iff_getElem?.mp hY2
        have hg1 : Y.getD k1 [] = Y1 := by simp [List.getD_eq_getElem?_getD, hk1]
        have hg2 : Y.getD k2 [] = Y2 := by simp [List.getD_eq_getElem?_getD, hk2]
        have e1 : OrderImpl.siblingLayer run.coordinateProper
            (OrderImpl.Sibling.siblingNumber run.coordinateProper
              (OrderImpl.Sibling.siblingOrders run.coordinateProper
                (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k1 []) = l1 := by
          rw [hg1]; exact e1mem
        have e2 : OrderImpl.siblingLayer run.coordinateProper
            (OrderImpl.Sibling.siblingNumber run.coordinateProper
              (OrderImpl.Sibling.siblingOrders run.coordinateProper
                (OrderImpl.posOf run.coordinateProper Y))) (Y.getD k2 []) = l2 := by
          rw [hg2]; exact e2mem
        exact normalise_pair_stable e1 e2 hna hnb hna' hnb' hda hdb hda' hdb'
          hA hB hpa' hpb' hAB htie hnd1 hnd2 hi1 hj1 hi2 hj2
/-- X copy of `coordinateGraph_side_original`. -/
private theorem xed_side_original {P : Params} {exact : List Nat} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {side : ProperNode}
    (hside : (coordinateGraphX P exact source).nodes[index]? = some side)
    (hborder : side.node.border = -1 ∨ side.node.border = 1) :
    (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW).nodes[index]? = some side := by
  have hwf : OrderImpl.BordersWellFormed (coordinateGraphX P exact source) := by
    unfold coordinateGraphX
    exact materializeDummyPaths_bordersWellFormed
      (clearProxyExtents_bordersWellFormed
        (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))
  have hreal : side.dummy = false := by
    cases hd : side.dummy with
    | false => rfl
    | true =>
        have hz := hwf.2.2 index side hside hd
        rcases hborder with hborder | hborder <;> omega
  obtain ⟨cleared, hcleared, hd, _, _, heq⟩ :=
    materialize_lookup (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)) hside
  have hclearedReal : cleared.dummy = false := hd.symm.trans hreal
  have hsame : side = cleared := heq hclearedReal
  have hclearLookup : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some side := by
    rw [hsame]
    exact hcleared
  rw [clearProxyExtents_nodes, List.getElem?_map] at hclearLookup
  obtain ⟨original, horiginal, hclearEq⟩ := Option.map_eq_some_iff.mp hclearLookup
  have hb : side.node.border = original.node.border := by
    rw [← hclearEq]
    exact (clearF_keys original).2.1
  have hoside : original.node.border = -1 ∨ original.node.border = 1 := by
    rwa [hb] at hborder
  have hclearId : clearF original = original := by
    unfold clearF
    rcases hoside with hoside | hoside <;> simp [hoside]
  exact horiginal.trans (congrArg some (hclearId.symm.trans hclearEq))
/-- Canonical cluster path of an executed exact side marker: the title path of
its declaration. X replay of `sideChainCanon` (`ForeignSideChainShapeProof`):
side markers are emitted by `OrderImpl.addClusterBorders`, each marker's path
comes from its `-2` title anchor, and title paths are determined by the
declaration (`measuredGraph_group_origin` after `xed_exactGraph_node`). -/
private theorem xed_sideChainCanon {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {a : Nat} {na : ProperNode} {decl : Nat}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hside : na.node.border = -1 ∨ na.node.border = 1)
    (hlast : na.node.clusterPath.getLast? = some decl) :
    ∃ box : ModelBox,
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)[decl]? = some box ∧
      na.node.clusterPath = Compound.path (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box) box ++ [decl] := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoordL, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) :=
    xed_titled_ready hkeys
      (componentCandidate_shape (components_nodup graph comp hcomp)
        (xed_exact_cgShape hgraph0 hgraphX) candidate)
      (fun _ _ hnode => xed_marker_shape hgraph0 hgraphX hnode) haligned
  have hcoordinate : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[a]? =
      some na := by
    rw [hcoordL]; exact hna
  have horiginal := xed_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal) hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled)).nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases xed_titled_node_origin hkeys hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hkeys top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ := componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨n0, h0, hd0, hb0', hp0⟩ := xed_exactGraph_node hgraphX hsrcG
      have hgroup0 : n0.border = -2 := by rw [← hb0']; exact hbnB
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ := measuredGraph_group_origin hgraph0 h0 hgroup0
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hp0, hpathG, List.getLast?_append, ← hd0]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl := Option.some.inj (hnaLast.symm.trans hlast)
      have hdecl0 : n0.decl = decl := by rw [← hd0]; exact hdeclEq
      rw [hdecl0] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hp0, hpathG, hdecl0]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega
/-- X replay of `shape_path_consec`: consecutive exact side-chain markers share
the anchor's full cluster path. -/
private theorem xed_shape_path_consec {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1) :
    ∀ i : Nat, i + 1 < (sideChainNodes P run side decl).length →
      ((sideBase run).nodes.getD (sideChainNodes P run side decl)[i]! default).node.clusterPath =
        ((sideBase run).nodes.getD
          (sideChainNodes P run side decl)[i + 1]! default).node.clusterPath := by
  intro i hi
  have hi1 : i < (sideChainNodes P run side decl).length := by omega
  have hi2 : i + 1 < (sideChainNodes P run side decl).length := hi
  have hm1 : (sideChainNodes P run side decl)[i] ∈ sideChainNodes P run side decl :=
    List.getElem_mem hi1
  have hm2 : (sideChainNodes P run side decl)[i + 1] ∈
      sideChainNodes P run side decl :=
    List.getElem_mem hi2
  obtain ⟨na, hna, hba, _, hla⟩ := mem_sideChainNodes_forward hm1
  obtain ⟨nb, hnb, hbb, _, hlb⟩ := mem_sideChainNodes_forward hm2
  have hsa : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsb : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  obtain ⟨boxA, hboxA, hpathA⟩ := xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hna hsa hla
  obtain ⟨boxB, hboxB, hpathB⟩ := xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hnb hsb hlb
  have hbox : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hei1 : (sideChainNodes P run side decl)[i]! =
      (sideChainNodes P run side decl)[i] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1,
      Option.getD_some]
  have hei2 : (sideChainNodes P run side decl)[i + 1]! =
      (sideChainNodes P run side decl)[i + 1] := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2,
      Option.getD_some]
  have hgetA : (sideBase run).nodes.getD
      (sideChainNodes P run side decl)[i]! default = na := by
    rw [hei1, hnodes]
    exact borderEnv_getD_of_get? hna
  have hgetB : (sideBase run).nodes.getD
      (sideChainNodes P run side decl)[i + 1]! default = nb := by
    rw [hei2, hnodes]
    exact borderEnv_getD_of_get? hnb
  rw [hgetA, hgetB, hpathA, hpathB, hbox]
/-- X replay of `shape_chain_uniform`: all exact side-chain markers of one
declaration share the anchor's full cluster path. -/
private theorem xed_shape_chain_uniform {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1) :
    ∀ u ∈ sideChainNodes P run side decl, ∀ w ∈ sideChainNodes P run side decl,
      ((sideBase run).nodes.getD u default).node.clusterPath =
        ((sideBase run).nodes.getD w default).node.clusterPath := by
  intro u hu w hw
  obtain ⟨na, hna, hba, _, hla⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb, hnb, hbb, _, hlb⟩ := mem_sideChainNodes_forward hw
  have hsa : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsb : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  obtain ⟨boxA, hboxA, hpathA⟩ := xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hna hsa hla
  obtain ⟨boxB, hboxB, hpathB⟩ := xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hnb hsb hlb
  have hbox : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetA : (sideBase run).nodes.getD u default = na := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hna
  have hgetB : (sideBase run).nodes.getD w default = nb := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hnb
  rw [hgetA, hgetB, hpathA, hpathB, hbox]
/-- X replay of `shapeRankInjResidual`, part 1: equal pass ranks give equal
construction ranks. Pass ranks transport to layer indices (`rank_orient`),
which are construction ranks (`layerPositions_spec`), which agree with the
`addClusterBorders` ranks. -/
private theorem xed_rankInj_constructionEq {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat} {k : Nat}
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    {u w : Nat} (hu : u ∈ sideChainNodes P run side decl)
    (hw : w ∈ sideChainNodes P run side decl)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hrk : (sideCtx P run pos k).rank[u]! = (sideCtx P run pos k).rank[w]!) :
    rk (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank u =
    rk (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank w := by
  obtain ⟨_, _, _, _, _⟩ := mem_sideChainNodes_forward hu
  obtain ⟨_, _, _, _, _⟩ := mem_sideChainNodes_forward hw
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨lvu, hmlu, hviu⟩ := List.mem_flatten.mp (sideChainNodes_flat hu)
  obtain ⟨lvw, hmlw, hviw⟩ := List.mem_flatten.mp (sideChainNodes_flat hw)
  obtain ⟨iu, hiu⟩ := List.mem_iff_getElem?.mp hmlu
  obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.mp hmlw
  have hru : (sideCtx P run pos k).rank[u]! =
      (if 2 ≤ k then run.layers.length - 1 - iu else iu) :=
    CoordsImpl.rank_orient hLmk hiu hviu
  have hrw : (sideCtx P run pos k).rank[w]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) :=
    CoordsImpl.rank_orient hLmk hiw hviw
  have hivlt : iu < run.layers.length := (List.getElem?_eq_some_iff.mp hiu).1
  have hiwlt : iw < run.layers.length := (List.getElem?_eq_some_iff.mp hiw).1
  have hiuw : iu = iw := by
    by_cases h2k : 2 ≤ k
    · simp only [h2k, ite_true] at hru hrw
      omega
    · simp only [h2k, ite_false] at hru hrw
      omega
  have hiu' : run.layers[iw]? = some lvu := by
    rw [← hiuw]; exact hiu
  have hluvw : lvu = lvw :=
    Option.some.inj (hiu'.symm.trans hiw)
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨_, hpos'⟩ := hlp
  obtain ⟨_, hrkLayer, _⟩ := CoordsImpl.layerPositions_spec hpos'
  have hRKu : rk (sideBase run).rank u = (iw : Int) :=
    hrkLayer iw lvw u (by rw [← hluvw]; exact hiu') (by rw [← hluvw]; exact hviu)
  have hRKw : rk (sideBase run).rank w = (iw : Int) :=
    hrkLayer iw lvw w hiw hviw
  have h1 : (sideBase run).rank = run.coordinateProper.rank := rfl
  have h2 : (coordinateGraphX P exact labeled).rank =
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).rank := rfl
  rw [hcoordL] at h2
  have hrankEq : (sideBase run).rank =
      (OrderImpl.addClusterBorders (titleReservations (sizeProperPortsX P exact labeled))
        P.clusterBorderW).rank :=
    h1.trans h2
  rw [← hrankEq]
  exact hRKu.trans hRKw.symm
/-- X replay of `shapeRankInjResidual`, part 2: equal construction ranks force
equal indices. Same-side markers with the same path share one `BInv` extra
key, and keys are nodup (`executed_border_binv`), so the indices agree. -/
private theorem xed_shapeRankInj_of_constructionEq {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat}
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    {u w : Nat} {na nb : ProperNode}
    (_hu : u ∈ sideChainNodes P run side decl)
    (_hw : w ∈ sideChainNodes P run side decl)
    (hna : run.coordinateProper.nodes[u]? = some na)
    (hnb : run.coordinateProper.nodes[w]? = some nb)
    (hba : na.node.border = side) (hbb : nb.node.border = side)
    (hside : side = -1 ∨ side = 1)
    (hRKc : rk (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank u =
    rk (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank w)
    (huni : ((sideBase run).nodes.getD u default).node.clusterPath =
      ((sideBase run).nodes.getD w default).node.clusterPath) :
    u = w := by
  obtain ⟨es, hinv⟩ := executed_border_binv P.clusterBorderW hready
  have haddedU : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[u]? = some na := by
    have hcoordU : (coordinateGraphX P exact labeled).nodes[u]? = some na := by
      rw [hcoordL]; exact hna
    have hbordU : na.node.border = -1 ∨ na.node.border = 1 := by
      rw [hba]; exact hside
    exact xed_side_original hready hcoordU hbordU
  have haddedW : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[w]? = some nb := by
    have hcoordW : (coordinateGraphX P exact labeled).nodes[w]? = some nb := by
      rw [hcoordL]; exact hnb
    have hbordW : nb.node.border = -1 ∨ nb.node.border = 1 := by
      rw [hbb]; exact hside
    exact xed_side_original hready hcoordW hbordW
  have hsideU : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsideW : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  have hN : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      (titleReservations (sizeProperPortsX P exact labeled)).rank.length :=
    hready.2.2.2.1
  rcases OrderImpl.binv_lookup hinv haddedU with ⟨_, hnodeU⟩ | ⟨hleU, ea, hea, heqU⟩
  · have hmemU : na ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes :=
      List.mem_of_getElem? hnodeU
    rcases hsideU with hs | hs
    · exact ((hready.1 na hmemU).1 hs).elim
    · exact ((hready.1 na hmemU).2 hs).elim
  rcases OrderImpl.binv_lookup hinv haddedW with ⟨_, hnodeW⟩ | ⟨hleW, eb, heb, heqW⟩
  · have hmemW : nb ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes :=
      List.mem_of_getElem? hnodeW
    rcases hsideW with hs | hs
    · exact ((hready.1 nb hmemW).1 hs).elim
    · exact ((hready.1 nb hmemW).2 hs).elim
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetU : (sideBase run).nodes.getD u default = na := by
    rw [hnodes]; exact borderEnv_getD_of_get? hna
  have hgetW : (sideBase run).nodes.getD w default = nb := by
    rw [hnodes]; exact borderEnv_getD_of_get? hnb
  have hpath : na.node.clusterPath = nb.node.clusterPath := by
    rw [hgetU, hgetW] at huni
    exact huni
  have hlenEq : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes.length =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank.length := by
    rw [hinv.nodes, hinv.rank, List.length_append, List.length_append,
      List.length_map, List.length_map, hN]
  have hub : u < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank.length := by
    have hulen : u < (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes.length :=
      (List.getElem?_eq_some_iff.mp haddedU).1
    omega
  have hwb : w < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank.length := by
    have hwlen : w < (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes.length :=
      (List.getElem?_eq_some_iff.mp haddedW).1
    omega
  have hgu : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[u]? = some ea.2 := by
    have hle : (titleReservations (sizeProperPortsX P exact labeled)).rank.length ≤ u := by
      rw [← hN]; exact hleU
    rw [hinv.rank, List.getElem?_append_right hle, ← hN, List.getElem?_map, hea,
      Option.map_some]
  have hgw : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[w]? = some eb.2 := by
    have hle : (titleReservations (sizeProperPortsX P exact labeled)).rank.length ≤ w := by
      rw [← hN]; exact hleW
    rw [hinv.rank, List.getElem?_append_right hle, ← hN, List.getElem?_map, heb,
      Option.map_some]
  have hrEntry : ea.2 = eb.2 := by
    have hrw' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[u] =
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[w] := by
      rw [← RankImpl.rk_of_lt hub, ← RankImpl.rk_of_lt hwb]
      exact hRKc
    have e1 : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[u] = ea.2 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hub]; exact hgu)
    have e2 : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).rank[w] = eb.2 :=
      Option.some.inj (by rw [← List.getElem?_eq_getElem hwb]; exact hgw)
    exact e1.symm.trans (hrw'.trans e2)
  have hkey : OrderImpl.extraKey ea = OrderImpl.extraKey eb := by
    have hb : ea.1.node.border = eb.1.node.border := by
      rw [heqU, heqW, hba, hbb]
    have hp : ea.1.node.clusterPath = eb.1.node.clusterPath := by
      rw [heqU, heqW]; exact hpath
    unfold OrderImpl.extraKey
    simp only [Prod.mk.injEq]
    exact ⟨hb, hp, hrEntry⟩
  have hinj : u - (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      w - (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨hai, hax⟩ := List.getElem?_eq_some_iff.mp hea
    obtain ⟨hbi, hbx⟩ := List.getElem?_eq_some_iff.mp heb
    have hpa := List.pairwise_iff_getElem.mp hinv.keys
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hcon := hpa _ _ (by simpa using hai) (by simpa using hbi) hlt
      simp [hax, hbx, hkey] at hcon
    · have hcon := hpa _ _ (by simpa using hbi) (by simpa using hai) hlt
      simp [hax, hbx, hkey] at hcon
  omega
/-- X replay of `shapeRankInj_executed`: at most one exact side marker per
pass rank. -/
private theorem xed_shapeRankInj_executed {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeRankInjResidual P run side decl pos k := by
  intro u hu w hw hrk
  obtain ⟨na, hna, hba, _, _⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb, hnb, hbb, _, _⟩ := mem_sideChainNodes_forward hw
  obtain ⟨labeled, hcoordL, hready⟩ :=
    xed_titled_border_ready hgraph0 hgraphX hcomp hrunX
  have hRKc := xed_rankInj_constructionEq labeled hcoordL hu hw hpos hrk
  have huni := xed_shape_chain_uniform hgraph0 hgraphX hcomp hrunX hside u hu w hw
  exact xed_shapeRankInj_of_constructionEq labeled hcoordL hready hu hw hna hnb
    hba hbb hside hRKc huni
/-- X replay of `shapeRankConsec`, head: layer indices, construction ranks,
added markers, and the shared anchor path. -/
private theorem xed_consec_prep {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat} {k : Nat}
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {u v : Nat} {na nb : ProperNode}
    (hu : u ∈ sideChainNodes P run side decl)
    (hv : v ∈ sideChainNodes P run side decl)
    (hna : run.coordinateProper.nodes[u]? = some na)
    (hnb : run.coordinateProper.nodes[v]? = some nb)
    (hba : na.node.border = side) (hbb : nb.node.border = side)
    (hside : side = -1 ∨ side = 1) :
    ∃ iu iw : Nat, (sideCtx P run pos k).rank[u]! =
      (if 2 ≤ k then run.layers.length - 1 - iu else iu) ∧
      (sideCtx P run pos k).rank[v]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) ∧
      rk (sideBase run).rank u = (iu : Int) ∧
      rk (sideBase run).rank v = (iw : Int) ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[u]? = some na ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some nb := by
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨lvu, hmlu, hviu⟩ := List.mem_flatten.mp (sideChainNodes_flat hu)
  obtain ⟨lvw, hmlw, hviw⟩ := List.mem_flatten.mp (sideChainNodes_flat hv)
  obtain ⟨iu, hiu⟩ := List.mem_iff_getElem?.mp hmlu
  obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.mp hmlw
  have hru : (sideCtx P run pos k).rank[u]! =
      (if 2 ≤ k then run.layers.length - 1 - iu else iu) :=
    CoordsImpl.rank_orient hLmk hiu hviu
  have hrw : (sideCtx P run pos k).rank[v]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) :=
    CoordsImpl.rank_orient hLmk hiw hviw
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨_, hpos'⟩ := hlp
  obtain ⟨_, hrkLayer, _⟩ := CoordsImpl.layerPositions_spec hpos'
  have hRKu : rk (sideBase run).rank u = (iu : Int) :=
    hrkLayer iu lvu u hiu hviu
  have hRKw : rk (sideBase run).rank v = (iw : Int) :=
    hrkLayer iw lvw v hiw hviw
  have haddedU : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[u]? = some na := by
    have hcoordU : (coordinateGraphX P exact labeled).nodes[u]? = some na := by
      rw [hcoordL]; exact hna
    have hbordU : na.node.border = -1 ∨ na.node.border = 1 := by
      rw [hba]; exact hside
    exact xed_side_original hready hcoordU hbordU
  have haddedW : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some nb := by
    have hcoordW : (coordinateGraphX P exact labeled).nodes[v]? = some nb := by
      rw [hcoordL]; exact hnb
    have hbordW : nb.node.border = -1 ∨ nb.node.border = 1 := by
      rw [hbb]; exact hside
    exact xed_side_original hready hcoordW hbordW
  exact ⟨iu, iw, hru, hrw, hRKu, hRKw, haddedU, haddedW⟩

/-- Shared anchor path from two exact side markers, from execution evidence. -/
private theorem xed_shape_chain_uniform' {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {u w : Nat} {na nb : ProperNode}
    (hu : u ∈ sideChainNodes P run side decl)
    (hw : w ∈ sideChainNodes P run side decl)
    (hna : run.coordinateProper.nodes[u]? = some na)
    (hnb : run.coordinateProper.nodes[w]? = some nb) :
    na.node.clusterPath = nb.node.clusterPath := by
  obtain ⟨na', hna', hba', _, hla⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb', hnb', hbb', _, hlb⟩ := mem_sideChainNodes_forward hw
  have ea : na' = na := Option.some.inj (hna'.symm.trans hna)
  have eb : nb' = nb := Option.some.inj (hnb'.symm.trans hnb)
  rw [← ea, ← eb]
  have hsa : na'.node.border = -1 ∨ na'.node.border = 1 := by
    rw [hba']; exact hside
  have hsb : nb'.node.border = -1 ∨ nb'.node.border = 1 := by
    rw [hbb']; exact hside
  obtain ⟨boxA, hboxA, hpathA⟩ :=
    xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hna' hsa hla
  obtain ⟨boxB, hboxB, hpathB⟩ :=
    xed_sideChainCanon hgraph0 hgraphX hcomp hrunX hnb' hsb hlb
  have hbox : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
  rw [hpathA, hpathB, hbox]
/-- X copy of `coordinateGraph_side_record`: emitted side markers survive the
proxy/materialize stages of `coordinateGraphX`. -/
private theorem xed_side_record {P : Params} {exact : List Nat} {source : Proper}
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW).nodes[index]? =
        some node)
    (hdummy : node.dummy = false)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    (coordinateGraphX P exact source).nodes[index]? = some node := by
  have hnotProxy :
      (node.node.border == -2 || node.node.border == 2) = false := by
    rcases hborder with hborder | hborder <;> simp [hborder]
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact source)) P.clusterBorderW)).nodes[index]? =
        some node := by
    simp only [clearProxyExtents, List.getElem?_map, hnode, Option.map_some]
    simp only [hnotProxy, Bool.false_eq_true, ↓reduceIte]
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some,
    Nat.zero_add, hdummy, Bool.false_eq_true, ↓reduceIte]

/-- X copy of `coordinateGraph_side_rank_bounds`. -/
private theorem xed_side_rank_bounds {P : Params} {exact : List Nat} {source : Proper}
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact source)))
    {index : Nat} {node : ProperNode}
    (hnode : (coordinateGraphX P exact source).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    ∃ top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2),
      ∃ bottom : ProperNode × Nat,
        ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find? fun entry =>
          entry.1.node.border == 2 &&
            entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom ∧
        node.node.clusterPath = top.1.node.clusterPath ∧
        0 ≤ rk (coordinateGraphX P exact source).rank index ∧
        (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤
          (rk (coordinateGraphX P exact source).rank index).toNat ∧
        (rk (coordinateGraphX P exact source).rank index).toNat ≤
          (rk (titleReservations (sizeProperPortsX P exact source)).rank bottom.2).toNat := by
  have horiginal := xed_side_original hready hnode hside
  exact addClusterBorders_side_rank_bounds _ _ hready horiginal hside
/-- X copy of `coordinateGraph_rank_pair`: every rank in a title anchor's span
is occupied by an emitted left/right marker pair of `coordinateGraphX`. -/
private theorem xed_rank_pair (P : Params) (exact : List Nat) (source : Proper)
    (haligned : (titleReservations (sizeProperPortsX P exact source)).nodes.length =
      (titleReservations (sizeProperPortsX P exact source)).rank.length)
    {top bottom : ProperNode × Nat}
    (htop : top ∈ (titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx)
    (hborder : top.1.node.border = -2)
    (hbottom : ((titleReservations (sizeProperPortsX P exact source)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == top.1.node.clusterPath) = some bottom)
    {rank : Nat}
    (hlo : (rk (titleReservations (sizeProperPortsX P exact source)).rank top.2).toNat ≤ rank)
    (hhi : rank ≤ (rk (titleReservations (sizeProperPortsX P exact source)).rank
      bottom.2).toNat) :
    ∃ left right : Nat,
      (coordinateGraphX P exact source).nodes[left]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := -1 }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).nodes[right]? =
        some ⟨{ decl := top.1.node.decl
                w := P.clusterBorderW
                h := 0
                clusterPath := top.1.node.clusterPath
                border := 1
                loopExtent := top.1.node.loopExtent }, false, none, false⟩ ∧
      (coordinateGraphX P exact source).rank[left]? = some (rank : Int) ∧
      (coordinateGraphX P exact source).rank[right]? = some (rank : Int) := by
  obtain ⟨left, right, hl, hr, hrl, hrr⟩ :=
    addClusterBorders_rank_pair (titleReservations (sizeProperPortsX P exact source))
      P.clusterBorderW haligned htop hborder hbottom hlo hhi
  refine ⟨left, right, xed_side_record hl rfl (Or.inl rfl),
    xed_side_record hr rfl (Or.inr rfl), ?_, ?_⟩
  · exact hrl
  · exact hrr
/-- X replay of `shapeRankConsec`, anchor part: the two markers share one `-2`
anchor; both construction ranks lie in its span, transported to layer indices. -/
private theorem xed_consec_anchorBounds {P : Params} {exact : List Nat}
    {run : Run} {side : Int}
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (hsb : (sideBase run).rank = (coordinateGraphX P exact labeled).rank)
    {u v : Nat} {na nb : ProperNode} {iu iw : Nat}
    (hna : run.coordinateProper.nodes[u]? = some na)
    (hnb : run.coordinateProper.nodes[v]? = some nb)
    (hba : na.node.border = side) (hbb : nb.node.border = side)
    (hside : side = -1 ∨ side = 1)
    (haddedU : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[u]? = some na)
    (haddedW : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some nb)
    (hpath : na.node.clusterPath = nb.node.clusterPath)
    (hRKu : rk (sideBase run).rank u = (iu : Int))
    (hRKw : rk (sideBase run).rank v = (iw : Int)) :
    ∃ topA : ProperNode × Nat, ∃ bottomU : ProperNode × Nat,
      topA ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.filter
        (fun entry => entry.1.node.border == -2) ∧
      ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find? fun entry =>
        entry.1.node.border == 2 &&
          entry.1.node.clusterPath == topA.1.node.clusterPath) = some bottomU ∧
      na.node.clusterPath = topA.1.node.clusterPath ∧
      (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        topA.2).toNat ≤ iu ∧
      iu ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        bottomU.2).toNat ∧
      (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        topA.2).toNat ≤ iw ∧
      iw ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        bottomU.2).toNat := by
  have hsideU : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have hsideW : nb.node.border = -1 ∨ nb.node.border = 1 := by
    rw [hbb]; exact hside
  obtain ⟨topA, htopA, hpathA, hpathB⟩ := chainMarkers_shareAnchor
    P.clusterBorderW hready haddedU haddedW hsideU hsideW hpath
  have hcoordU : (coordinateGraphX P exact labeled).nodes[u]? = some na := by
    rw [hcoordL]; exact hna
  have hcoordW : (coordinateGraphX P exact labeled).nodes[v]? = some nb := by
    rw [hcoordL]; exact hnb
  obtain ⟨topU, htopU, bottomU, hfindU, hpathU, _, hloU, hhiU⟩ :=
    xed_side_rank_bounds hready hcoordU hsideU
  obtain ⟨topV, htopV, bottomV, hfindV, hpathV, _, hloV, hhiV⟩ :=
    xed_side_rank_bounds hready hcoordW hsideW
  obtain ⟨hmemA, hcondA⟩ := List.mem_filter.mp htopA
  obtain ⟨hmemU, hcondU⟩ := List.mem_filter.mp htopU
  obtain ⟨hmemV, hcondV⟩ := List.mem_filter.mp htopV
  have hgetA : (titleReservations (sizeProperPortsX P exact labeled)).nodes[topA.2]? =
      some topA.1 := List.mem_zipIdx_iff_getElem?.mp hmemA
  have hgetU' : (titleReservations (sizeProperPortsX P exact labeled)).nodes[topU.2]? =
      some topU.1 := List.mem_zipIdx_iff_getElem?.mp hmemU
  have hgetV' : (titleReservations (sizeProperPortsX P exact labeled)).nodes[topV.2]? =
      some topV.1 := List.mem_zipIdx_iff_getElem?.mp hmemV
  have hbA : topA.1.node.border = -2 := by simpa using hcondA
  have hbU : topU.1.node.border = -2 := by simpa using hcondU
  have hbV : topV.1.node.border = -2 := by simpa using hcondV
  have hpathUA : topU.1.node.clusterPath = topA.1.node.clusterPath :=
    hpathU.symm.trans hpathA
  have hpathVA : topV.1.node.clusterPath = topA.1.node.clusterPath :=
    hpathV.symm.trans hpathB
  have heqU : topU.2 = topA.2 :=
    titled_anchor_unique hready hgetU' hgetA hbU hbA hpathUA
  have heqV : topV.2 = topA.2 :=
    titled_anchor_unique hready hgetV' hgetA hbV hbA hpathVA
  rw [heqU] at hloU
  rw [hpathUA] at hfindU
  rw [heqV] at hloV
  rw [hpathVA] at hfindV
  have hbotEq : bottomU = bottomV :=
    Option.some.inj (hfindU.symm.trans hfindV)
  rw [← hbotEq] at hhiV
  have hcuN : (rk (coordinateGraphX P exact labeled).rank u).toNat = iu := by
    have hcu : rk (coordinateGraphX P exact labeled).rank u = (iu : Int) := by
      rw [← hsb]; exact hRKu
    omega
  have hcvN : (rk (coordinateGraphX P exact labeled).rank v).toNat = iw := by
    have hcv : rk (coordinateGraphX P exact labeled).rank v = (iw : Int) := by
      rw [← hsb]; exact hRKw
    omega
  have hbU' : (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
      topA.2).toNat ≤ iu ∧
      iu ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        bottomU.2).toNat := by omega
  have hbV' : (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
      topA.2).toNat ≤ iw ∧
      iw ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        bottomU.2).toNat := by omega
  exact ⟨topA, bottomU, htopA, hfindU, hpathA, hbU'.1, hbU'.2, hbV'.1, hbV'.2⟩
/-- X replay of `shapeRankConsec`, middle: every rank between the anchor span
holds a chain marker with the matching pass rank. -/
private theorem xed_middle_rank {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat} {k : Nat}
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (hsb : (sideBase run).rank = (coordinateGraphX P exact labeled).rank)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hside : side = -1 ∨ side = 1)
    {na : ProperNode} {topA : ProperNode × Nat} {bottomU : ProperNode × Nat}
    (htopA : topA ∈ (titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.filter
      (fun entry => entry.1.node.border == -2))
    (hfindU : ((titleReservations (sizeProperPortsX P exact labeled)).nodes.zipIdx.find?
      fun entry => entry.1.node.border == 2 &&
        entry.1.node.clusterPath == topA.1.node.clusterPath) = some bottomU)
    (hpathA : na.node.clusterPath = topA.1.node.clusterPath)
    (hla : na.node.clusterPath.getLast? = some decl) :
    ∀ mid : Nat, (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        topA.2).toNat ≤ mid →
      mid ≤ (rk (titleReservations (sizeProperPortsX P exact labeled)).rank
        bottomU.2).toNat →
      ∃ m, m ∈ sideChainNodes P run side decl ∧
        (sideCtx P run pos k).rank[m]! =
          (if 2 ≤ k then run.layers.length - 1 - mid else mid) := by
  have htopmem : topA ∈ (titleReservations
      (sizeProperPortsX P exact labeled)).nodes.zipIdx :=
    (List.mem_filter.mp htopA).1
  have hborder : topA.1.node.border = -2 := by
    simpa using (List.mem_filter.mp htopA).2
  have hN : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
      (titleReservations (sizeProperPortsX P exact labeled)).rank.length :=
    hready.2.2.2.1
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨_, hpos'⟩ := hlp
  obtain ⟨_, hrkLayer, hcov⟩ := CoordsImpl.layerPositions_spec hpos'
  intro mid hmidlo hmidhi
  obtain ⟨mleft, mright, hmln, hmrn, hmlr, hmrr⟩ :=
    xed_rank_pair P _ _ hready.2.2.2.1 htopmem hborder hfindU hmidlo hmidhi
  have hlastA : topA.1.node.clusterPath.getLast? = some decl := by
    rw [← hpathA]; exact hla
  obtain ⟨m, hmemM, hmrank⟩ :
      ∃ m, m ∈ sideChainNodes P run side decl ∧
        (coordinateGraphX P exact labeled).rank[m]? = some ((mid : Nat) : Int) := by
    rcases hside with hneg | hposS
    · refine ⟨mleft, ?_, hmlr⟩
      rw [hcoordL] at hmln
      rw [mem_sideChainNodes hpos]
      refine ⟨_, hmln, ?_, ?_, ?_⟩
      · rw [hneg]
      · rfl
      · exact hlastA
    · refine ⟨mright, ?_, hmrr⟩
      rw [hcoordL] at hmrn
      rw [mem_sideChainNodes hpos]
      refine ⟨_, hmrn, ?_, ?_, ?_⟩
      · rw [hposS]
      · rfl
      · exact hlastA
  have hmrankS : (sideBase run).rank[m]? = some ((mid : Nat) : Int) := by
    rw [hsb]; exact hmrank
  have hmlenR : m < (sideBase run).rank.length :=
    (List.getElem?_eq_some_iff.mp hmrankS).1
  have hRKm : rk (sideBase run).rank m = ((mid : Nat) : Int) := by
    rw [RankImpl.rk_of_lt hmlenR]
    exact Option.some.inj
      ((List.getElem?_eq_getElem hmlenR).symm.trans hmrankS)
  have hmlt : m < (sideBase run).nodes.length := by
    obtain ⟨nm, hnm, _, _, _⟩ := mem_sideChainNodes_forward hmemM
    have hb : m < run.coordinateProper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hnm).1
    rw [hnodes]; exact hb
  obtain ⟨lm, hmlm, hvim⟩ := List.mem_flatten.mp (hcov m hmlt)
  obtain ⟨im, him⟩ := List.mem_iff_getElem?.mp hmlm
  have hRi : rk (sideBase run).rank m = (im : Int) :=
    hrkLayer im lm m him hvim
  have himEq : im = mid := by omega
  have hpm : (sideCtx P run pos k).rank[m]! =
      (if 2 ≤ k then run.layers.length - 1 - im else im) :=
    CoordsImpl.rank_orient hLmk him hvim
  rw [himEq] at hpm
  exact ⟨m, hmemM, hpm⟩
/-- X replay of `shapeRankConsec_executed`: pass ranks of one exact side chain
form an interval with no gaps. -/
private theorem xed_shapeRankConsec_executed {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeRankConsecResidual P run side decl pos k := by
  intro u hu v hv hlt hnone
  obtain ⟨na, hna, hba, _, hla⟩ := mem_sideChainNodes_forward hu
  obtain ⟨nb, hnb, hbb, _, _⟩ := mem_sideChainNodes_forward hv
  obtain ⟨labeled, hcoordL, hready⟩ :=
    xed_titled_border_ready hgraph0 hgraphX hcomp hrunX
  have h1 : (sideBase run).rank = run.coordinateProper.rank := rfl
  have hsb : (sideBase run).rank =
      (coordinateGraphX P (exactDecls exactIds inp) labeled).rank := by
    rw [h1, ← hcoordL]
  obtain ⟨iu, iw, hru, hrw, hRKu, hRKw, haddedU, haddedW⟩ :=
    xed_consec_prep labeled hcoordL hready hpos hu hv hna hnb hba hbb hside
  have hpath := xed_shape_chain_uniform' hgraph0 hgraphX hcomp hrunX hside hu hv hna hnb
  obtain ⟨topA, bottomU, htopA, hfindU, hpathA, hloU, hhiU, hloV, hhiV⟩ :=
    xed_consec_anchorBounds labeled hcoordL hready hsb hna hnb hba hbb hside
      haddedU haddedW hpath hRKu hRKw
  have hmiddle := xed_middle_rank (k := k) labeled hcoordL hready hsb hpos hside
    htopA hfindU hpathA hla
  by_cases h2k : 2 ≤ k
  · rw [ite_eq_left h2k] at hru hrw
    by_cases heq : (sideCtx P run pos k).rank[u]! + 1 =
        (sideCtx P run pos k).rank[v]!
    · exact heq
    · have hge : iu ≥ iw + 2 := by omega
      obtain ⟨m, hmemM, hpm⟩ := hmiddle (iw + 1) (by omega) (by omega)
      simp only [h2k, ite_true] at hpm
      have hlt1 : (sideCtx P run pos k).rank[u]! <
          (sideCtx P run pos k).rank[m]! := by omega
      have hlt2 : (sideCtx P run pos k).rank[m]! <
          (sideCtx P run pos k).rank[v]! := by omega
      exact (hnone m hmemM ⟨hlt1, hlt2⟩).elim
  · rw [ite_eq_right h2k] at hru hrw
    by_cases heq : (sideCtx P run pos k).rank[u]! + 1 =
        (sideCtx P run pos k).rank[v]!
    · exact heq
    · have hge : iw ≥ iu + 2 := by omega
      obtain ⟨m, hmemM, hpm⟩ := hmiddle (iu + 1) (by omega) (by omega)
      simp only [h2k, ite_false] at hpm
      have hlt1 : (sideCtx P run pos k).rank[u]! <
          (sideCtx P run pos k).rank[m]! := by omega
      have hlt2 : (sideCtx P run pos k).rank[m]! <
          (sideCtx P run pos k).rank[v]! := by omega
      exact (hnone m hmemM ⟨hlt1, hlt2⟩).elim
/-- X replay of the left-link half of `shapeIncidentLinksOfForm`: a left
`borderLinks` edge joins two left markers; the end opposite the touched chain
marker is itself a chain marker. -/
private theorem xed_linksOfForm_left {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (_hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (_hside : side = -1 ∨ side = 1)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl)
    {na : ProperNode} (hna : run.coordinateProper.nodes[v]? = some na)
    {q : ProperNode × Nat} {w' : Int} {m : Nat} {e : ProperEdge}
    (haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some na)
    (hformL : e.tail = m ∧ e.head = m + 2 ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[m]? =
        some (OrderImpl.borderLeft q w') ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[m + 2]? =
        some (OrderImpl.borderLeft q w'))
    (htouch : e.tail = v ∨ e.head = v) :
    CoordsImpl.borderChain (sideBase run) e = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd e v = u ∧ u ≠ v := by
  obtain ⟨nva, hva, hbva, hwa, hvaLast⟩ := mem_sideChainNodes_forward hv
  have heqv : nva = na := Option.some.inj (hva.symm.trans hna)
  obtain ⟨ht, hh, h1, h2⟩ := hformL
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hSmL : ∀ (idx : Nat) (h : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[idx]? =
          some (OrderImpl.borderLeft q w')),
      (sideBase run).nodes[idx]? = some (OrderImpl.borderLeft q w') := by
    intro idx h
    have hLm : (coordinateGraphX P exact labeled).nodes[idx]? =
        some (OrderImpl.borderLeft q w') :=
      xed_side_record h rfl (Or.inl rfl)
    rw [hnodes, ← hcoordL]; exact hLm
  have hC1L : ((OrderImpl.borderLeft q w').node.border == -1 ||
      (OrderImpl.borderLeft q w').node.border == 1) = true := by
    show (((-1 : Int) == -1) || ((-1 : Int) == 1)) = true
    decide
  have e2L : ((OrderImpl.borderLeft q w').node.border ==
      (OrderImpl.borderLeft q w').node.border) = true := by
    show (((-1 : Int) == (-1 : Int))) = true
    decide
  have e3L : ((OrderImpl.borderLeft q w').node.clusterPath ==
      (OrderImpl.borderLeft q w').node.clusterPath) = true := by simp
  have hbc : CoordsImpl.borderChain (sideBase run) e = true := by
    have htail : (sideBase run).nodes[e.tail]? =
        some (OrderImpl.borderLeft q w') := by
      rw [ht]; exact hSmL m h1
    have hhead : (sideBase run).nodes[e.head]? =
        some (OrderImpl.borderLeft q w') := by
      rw [hh]; exact hSmL (m + 2) h2
    unfold CoordsImpl.borderChain
    simp only [htail, hhead]
    rw [hC1L, e2L, e3L]; rfl
  rcases htouch with htv | hhv
  · have hvm : v = m := by omega
    have hrecV : na = OrderImpl.borderLeft q w' := by
      rw [hvm] at haddedV
      exact Option.some.inj (haddedV.symm.trans h1)
    have hsideEq : side = -1 := by rw [← hbva, heqv, hrecV]; rfl
    have hW : w' = P.clusterBorderW := by
      have h1w : na.node.w = w' := by rw [hrecV]; rfl
      have hwa' : na.node.w = P.clusterBorderW := heqv ▸ hwa
      exact h1w.symm.trans hwa'
    have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
      have hpq : na.node.clusterPath = q.1.node.clusterPath := by rw [hrecV]; rfl
      have hlastA : na.node.clusterPath.getLast? = some decl := heqv ▸ hvaLast
      rw [← hpq]; exact hlastA
    have hmemU : m + 2 ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      have hUm : run.coordinateProper.nodes[m + 2]? =
          some (OrderImpl.borderLeft q w') := by
        have hLm : (coordinateGraphX P exact labeled).nodes[m + 2]? =
            some (OrderImpl.borderLeft q w') :=
          xed_side_record h2 rfl (Or.inl rfl)
        rw [← hcoordL]; exact hLm
      exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
    have hother : CoordsImpl.otherEnd e v = m + 2 := by
      have hcond : (e.tail == v) = true := by rw [htv]; exact beq_self_eq_true' _
      unfold CoordsImpl.otherEnd
      rw [hcond]
      exact hh
    exact ⟨hbc, m + 2, hmemU, hother, by omega⟩
  · have hvm : v = m + 2 := by omega
    have hrecV : na = OrderImpl.borderLeft q w' := by
      rw [hvm] at haddedV
      exact Option.some.inj (haddedV.symm.trans h2)
    have hsideEq : side = -1 := by
      rw [← hbva, heqv, hrecV]
      rfl
    have hW : w' = P.clusterBorderW := by
      have h1w : na.node.w = w' := by
        rw [hrecV]
        rfl
      have hwa' : na.node.w = P.clusterBorderW := heqv ▸ hwa
      exact h1w.symm.trans hwa'
    have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
      have hpq : na.node.clusterPath = q.1.node.clusterPath := by
        rw [hrecV]
        rfl
      have hlastA : na.node.clusterPath.getLast? = some decl := heqv ▸ hvaLast
      rw [← hpq]; exact hlastA
    have hmemU : m ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      have hUm : run.coordinateProper.nodes[m]? =
          some (OrderImpl.borderLeft q w') := by
        have hLm : (coordinateGraphX P exact labeled).nodes[m]? =
            some (OrderImpl.borderLeft q w') :=
          xed_side_record h1 rfl (Or.inl rfl)
        rw [← hcoordL]; exact hLm
      exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
    have hother : CoordsImpl.otherEnd e v = m := by
      have hne : e.tail ≠ v := by omega
      have hcond : (e.tail == v) = false := beq_eq_false_iff_ne.mpr hne
      unfold CoordsImpl.otherEnd
      rw [hcond]
      exact ht
    exact ⟨hbc, m, hmemU, hother, by omega⟩
/-- X replay of the right-link half of `shapeIncidentLinksOfForm`. -/
private theorem xed_linksOfForm_right {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (_hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (_hside : side = -1 ∨ side = 1)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl)
    {na : ProperNode} (hna : run.coordinateProper.nodes[v]? = some na)
    {q : ProperNode × Nat} {w' : Int} {m : Nat} {e : ProperEdge}
    (haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some na)
    (hformR : e.tail = m + 1 ∧ e.head = m + 1 + 2 ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[m + 1]? =
        some (OrderImpl.borderRight q w') ∧
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[m + 1 + 2]? =
        some (OrderImpl.borderRight q w'))
    (htouch : e.tail = v ∨ e.head = v) :
    CoordsImpl.borderChain (sideBase run) e = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd e v = u ∧ u ≠ v := by
  obtain ⟨nva, hva, hbva, hwa, hvaLast⟩ := mem_sideChainNodes_forward hv
  have heqv : nva = na := Option.some.inj (hva.symm.trans hna)
  obtain ⟨ht, hh, h1, h2⟩ := hformR
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hSmR : ∀ (idx : Nat) (h : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[idx]? =
          some (OrderImpl.borderRight q w')),
      (sideBase run).nodes[idx]? = some (OrderImpl.borderRight q w') := by
    intro idx h
    have hLm : (coordinateGraphX P exact labeled).nodes[idx]? =
        some (OrderImpl.borderRight q w') :=
      xed_side_record h rfl (Or.inr rfl)
    rw [hnodes, ← hcoordL]; exact hLm
  have hC1R : ((OrderImpl.borderRight q w').node.border == -1 ||
      (OrderImpl.borderRight q w').node.border == 1) = true := by
    show (((1 : Int) == -1) || ((1 : Int) == 1)) = true
    decide
  have e2R : ((OrderImpl.borderRight q w').node.border ==
      (OrderImpl.borderRight q w').node.border) = true := by
    show (((1 : Int) == (1 : Int))) = true
    decide
  have e3R : ((OrderImpl.borderRight q w').node.clusterPath ==
      (OrderImpl.borderRight q w').node.clusterPath) = true := by simp
  have hbc : CoordsImpl.borderChain (sideBase run) e = true := by
    have htail : (sideBase run).nodes[e.tail]? =
        some (OrderImpl.borderRight q w') := by
      rw [ht]; exact hSmR (m + 1) h1
    have hhead : (sideBase run).nodes[e.head]? =
        some (OrderImpl.borderRight q w') := by
      rw [hh]; exact hSmR (m + 1 + 2) h2
    unfold CoordsImpl.borderChain
    simp only [htail, hhead]
    rw [hC1R, e2R, e3R]; rfl
  rcases htouch with htv | hhv
  · have hvm : v = m + 1 := by omega
    have hrecV : na = OrderImpl.borderRight q w' := by
      rw [hvm] at haddedV
      exact Option.some.inj (haddedV.symm.trans h1)
    have hsideEq : side = 1 := by rw [← hbva, heqv, hrecV]; rfl
    have hW : w' = P.clusterBorderW := by
      have h1w : na.node.w = w' := by rw [hrecV]; rfl
      have hwa' : na.node.w = P.clusterBorderW := heqv ▸ hwa
      exact h1w.symm.trans hwa'
    have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
      have hpq : na.node.clusterPath = q.1.node.clusterPath := by rw [hrecV]; rfl
      have hlastA : na.node.clusterPath.getLast? = some decl := heqv ▸ hvaLast
      rw [← hpq]; exact hlastA
    have hmemU : m + 1 + 2 ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      have hUm : run.coordinateProper.nodes[m + 1 + 2]? =
          some (OrderImpl.borderRight q w') := by
        have hLm : (coordinateGraphX P exact labeled).nodes[m + 1 + 2]? =
            some (OrderImpl.borderRight q w') :=
          xed_side_record h2 rfl (Or.inr rfl)
        rw [← hcoordL]; exact hLm
      exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
    have hother : CoordsImpl.otherEnd e v = m + 1 + 2 := by
      have hcond : (e.tail == v) = true := by rw [htv]; exact beq_self_eq_true' _
      unfold CoordsImpl.otherEnd
      rw [hcond]
      exact hh
    exact ⟨hbc, m + 1 + 2, hmemU, hother, by omega⟩
  · have hvm : v = m + 1 + 2 := by omega
    have hrecV : na = OrderImpl.borderRight q w' := by
      rw [hvm] at haddedV
      exact Option.some.inj (haddedV.symm.trans h2)
    have hsideEq : side = 1 := by
      rw [← hbva, heqv, hrecV]
      rfl
    have hW : w' = P.clusterBorderW := by
      have h1w : na.node.w = w' := by
        rw [hrecV]
        rfl
      have hwa' : na.node.w = P.clusterBorderW := heqv ▸ hwa
      exact h1w.symm.trans hwa'
    have hlastQ : q.1.node.clusterPath.getLast? = some decl := by
      have hpq : na.node.clusterPath = q.1.node.clusterPath := by
        rw [hrecV]
        rfl
      have hlastA : na.node.clusterPath.getLast? = some decl := heqv ▸ hvaLast
      rw [← hpq]; exact hlastA
    have hmemU : m + 1 ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      have hUm : run.coordinateProper.nodes[m + 1]? =
          some (OrderImpl.borderRight q w') := by
        have hLm : (coordinateGraphX P exact labeled).nodes[m + 1]? =
            some (OrderImpl.borderRight q w') :=
          xed_side_record h1 rfl (Or.inr rfl)
        rw [← hcoordL]; exact hLm
      exact ⟨_, hUm, by rw [hsideEq]; rfl, hW, hlastQ⟩
    have hother : CoordsImpl.otherEnd e v = m + 1 := by
      have hne : e.tail ≠ v := by omega
      have hcond : (e.tail == v) = false := beq_eq_false_iff_ne.mpr hne
      unfold CoordsImpl.otherEnd
      rw [hcond]
      exact ht
    exact ⟨hbc, m + 1, hmemU, hother, by omega⟩
/-- X replay of `shapeIncidentLinksOfForm`: a `borderLinks` edge touching an
exact chain marker reaches another chain marker. -/
private theorem xed_linksOfForm {P : Params} {exact : List Nat}
    {run : Run} {side : Int} {decl : Nat} {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (labeled : Proper)
    (hcoordL : coordinateGraphX P exact labeled = run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P exact labeled)))
    (hside : side = -1 ∨ side = 1)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl)
    {e : ProperEdge}
    (hlink : IsLinkOut (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW) e)
    (htouch : e.tail = v ∨ e.head = v) :
    CoordsImpl.borderChain (sideBase run) e = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd e v = u ∧ u ≠ v := by
  obtain ⟨na, hna, hba, _, _⟩ := mem_sideChainNodes_forward hv
  have hcoordV : (coordinateGraphX P exact labeled).nodes[v]? = some na := by
    rw [hcoordL]; exact hna
  have hbordV : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P exact labeled)) P.clusterBorderW).nodes[v]? = some na :=
    xed_side_original hready hcoordV hbordV
  obtain ⟨q, w', m, _, _, hform⟩ := hlink
  rcases hform with ⟨ht, hh, h1, h2⟩ | ⟨ht, hh, h1, h2⟩
  · exact xed_linksOfForm_left hpos labeled hcoordL hready hside hv hna
      haddedV ⟨ht, hh, h1, h2⟩ htouch
  · exact xed_linksOfForm_right hpos labeled hcoordL hready hside hv hna
      haddedV ⟨ht, hh, h1, h2⟩ htouch
/-- X copy of `shape_side_width`: every side marker emitted by
`addClusterBorders` over the exact titled source carries the border width. -/
private theorem xed_side_width (source : Proper) (width : Int)
    (hready : OrderImpl.BorderConstructionReady source)
    {index : Nat} {node : ProperNode}
    (hnode : (OrderImpl.addClusterBorders source width).nodes[index]? = some node)
    (hside : node.node.border = -1 ∨ node.node.border = 1) :
    node.node.w = width := by
  have hP : ∀ n ∈ (OrderImpl.addClusterBorders source width).nodes,
      n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width := by
    rw [OrderImpl.addClusterBorders_eq]
    apply OrderImpl.foldl_inv
      (fun cur : Proper => ∀ n ∈ cur.nodes,
        n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
    · intro n hn hs
      rcases hs with hs | hs
      · exact ((hready.1 n hn).1 hs).elim
      · exact ((hready.1 n hn).2 hs).elim
    · intro state hstate entry hentry
      unfold OrderImpl.borderStep
      split
      · exact hstate
      · apply OrderImpl.foldl_inv
          (fun cur : Proper => ∀ n ∈ cur.nodes,
            n.node.border = -1 ∨ n.node.border = 1 → n.node.w = width)
        · exact hstate
        · intro st hst off _
          intro n hn hs
          have hn' : n ∈ st.nodes ++
              [OrderImpl.borderLeft entry width,
                OrderImpl.borderRight entry width] := hn
          rcases List.mem_append.mp hn' with hold | hnew
          · exact hst n hold hs
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
            rcases hnew with rfl | rfl <;> rfl
  exact hP node (List.mem_of_getElem? hnode) hside
/-- X replay of `shape_consec_edge`: rank-adjacent exact side markers are
joined by a context edge. Needs only `xed_shape_chain_uniform`. -/
private theorem xed_shape_consec_edge {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ∀ v ∈ sideChainNodes P run side decl, ∀ w ∈ sideChainNodes P run side decl,
      (sideCtx P run pos k).rank[v]! + 1 = (sideCtx P run pos k).rank[w]! →
      ∃ e : Nat, e < (sideCtx P run pos k).edges.size ∧
        (((sideCtx P run pos k).edges[e]!.head = v ∧
          (sideCtx P run pos k).edges[e]!.tail = w) ∨
          ((sideCtx P run pos k).edges[e]!.tail = v ∧
            (sideCtx P run pos k).edges[e]!.head = w)) := by
  intro v hv w hw hrkvw
  have hL : CoordsImpl.Lay (sideCtx P run pos k) := (clusterCtx_facts hpos).1
  have hLmk : CoordsImpl.Lay (CoordsImpl.mkCtx P.nodeGap (sideBase run) run.layers
      (CoordsImpl.typeOneConflicts (sideBase run) pos) k) :=
    (CoordsImpl.layout_facts
      (marked := CoordsImpl.typeOneConflicts (sideBase run) pos) (k := k) hpos).1
  obtain ⟨na, hna, hba, _, hla⟩ := mem_sideChainNodes_forward hv
  obtain ⟨nb, hnb, hbb, _, hlb⟩ := mem_sideChainNodes_forward hw
  have huni := xed_shape_chain_uniform hgraph0 hgraphX hcomp hrunX hside v hv w hw
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetA : (sideBase run).nodes.getD v default = na := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hna
  have hgetB : (sideBase run).nodes.getD w default = nb := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hnb
  have hpath : na.node.clusterPath = nb.node.clusterPath := by
    rw [hgetA, hgetB] at huni
    exact huni
  have hfv : v ∈ run.layers.flatten := sideChainNodes_flat hv
  have hfw : w ∈ run.layers.flatten := sideChainNodes_flat hw
  obtain ⟨lv, hmlv, hvlv⟩ := List.mem_flatten.mp hfv
  obtain ⟨lw, hmlw, hwlw⟩ := List.mem_flatten.mp hfw
  obtain ⟨iv, hiv⟩ := List.mem_iff_getElem?.mp hmlv
  obtain ⟨iw, hiw⟩ := List.mem_iff_getElem?.mp hmlw
  have hivlt : iv < run.layers.length := (List.getElem?_eq_some_iff.mp hiv).1
  have hiwlt : iw < run.layers.length := (List.getElem?_eq_some_iff.mp hiw).1
  have hrv : (sideCtx P run pos k).rank[v]! =
      (if 2 ≤ k then run.layers.length - 1 - iv else iv) := by
    have h := CoordsImpl.rank_orient hLmk hiv hvlv
    exact h
  have hrw : (sideCtx P run pos k).rank[w]! =
      (if 2 ≤ k then run.layers.length - 1 - iw else iw) := by
    have h := CoordsImpl.rank_orient hLmk hiw hwlw
    exact h
  have hsign : (na.node.border == -1 || na.node.border == 1) = true := by
    rcases hside with h | h <;> simp [hba, h]
  have heq : na.node.border = nb.node.border := by rw [hba, hbb]
  have harr : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
  by_cases h2k : 2 ≤ k
  · simp only [h2k, ite_true] at hrv hrw
    have hcon : iw + 1 = iv := by omega
    have h2 : run.layers[iw + 1]? = some lv := by rw [hcon]; exact hiv
    have hpair : (lw, lv) ∈ run.layers.zip run.layers.tail := by
      have hex : ∃ i, run.layers[i]? = some lw ∧ run.layers[i + 1]? = some lv :=
        ⟨iw, hiw, h2⟩
      exact (mem_zip_tail_iff (l := run.layers) (a := lw) (b := lv)).mpr hex
    obtain ⟨ed, hedmem, hedt, hedh⟩ :=
      border_alignment_chain_edge hpair hwlw hvlv hnb hna
        (by rcases hside with h | h <;> simp [hbb, h]) (heq.symm) (hpath.symm)
    obtain ⟨eidx, heidx⟩ := List.mem_iff_getElem?.mp hedmem
    obtain ⟨heilt, _⟩ := List.getElem?_eq_some_iff.mp heidx
    have hXe : (sideCtx P run pos k).edges[eidx]! = ed := by
      have heidx' : (sideBase run).edges[eidx]? = some ed := heidx
      rw [harr, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, heidx']
      rfl
    have hsz : eidx < (sideCtx P run pos k).edges.size := by
      rw [harr, List.size_toArray]
      exact heilt
    exact ⟨eidx, hsz, Or.inl ⟨by rw [hXe]; exact hedh, by rw [hXe]; exact hedt⟩⟩
  · simp only [h2k, ite_false] at hrv hrw
    have hcon : iv + 1 = iw := by omega
    have h2 : run.layers[iv + 1]? = some lw := by rw [hcon]; exact hiw
    have hpair : (lv, lw) ∈ run.layers.zip run.layers.tail := by
      have hex : ∃ i, run.layers[i]? = some lv ∧ run.layers[i + 1]? = some lw :=
        ⟨iv, hiv, h2⟩
      exact (mem_zip_tail_iff (l := run.layers) (a := lv) (b := lw)).mpr hex
    obtain ⟨ed, hedmem, hedt, hedh⟩ :=
      border_alignment_chain_edge hpair hvlv hwlw hna hnb hsign heq hpath
    obtain ⟨eidx, heidx⟩ := List.mem_iff_getElem?.mp hedmem
    obtain ⟨heilt, _⟩ := List.getElem?_eq_some_iff.mp heidx
    have hXe : (sideCtx P run pos k).edges[eidx]! = ed := by
      have heidx' : (sideBase run).edges[eidx]? = some ed := heidx
      rw [harr, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, heidx']
      rfl
    have hsz : eidx < (sideCtx P run pos k).edges.size := by
      rw [harr, List.size_toArray]
      exact heilt
    exact ⟨eidx, hsz, Or.inr ⟨by rw [hXe]; exact hedt, by rw [hXe]; exact hedh⟩⟩
/-- X replay of `shape_incident_pair`: an exact alignment-pair edge touching
a chain marker reaches another chain marker. Needs `xed_side_width`. -/
private theorem xed_shape_incident_pair {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {a b : Nat} {na nb : ProperNode}
    (hna : run.coordinateProper.nodes[a]? = some na)
    (hnb : run.coordinateProper.nodes[b]? = some nb)
    (hab : a ≠ b)
    (hcond : (((run.coordinateProper.nodes.getD a default).node.border == -1 ||
      (run.coordinateProper.nodes.getD a default).node.border == 1) &&
      (run.coordinateProper.nodes.getD a default).node.border ==
        (run.coordinateProper.nodes.getD b default).node.border &&
      (run.coordinateProper.nodes.getD a default).node.clusterPath ==
        (run.coordinateProper.nodes.getD b default).node.clusterPath) = true)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl)
    (hmem : v = a ∨ v = b) :
    CoordsImpl.borderChain (sideBase run)
      ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd
        ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge)
        v = u ∧ u ≠ v := by
  obtain ⟨_, hlp, _⟩ := CoordsImpl.checkLayers_parts hpos
  obtain ⟨pos', hpos'⟩ := hlp
  obtain ⟨_, _, hcov⟩ := CoordsImpl.layerPositions_spec hpos'
  obtain ⟨labeled, hcoordL, hready⟩ :=
    xed_titled_border_ready hgraph0 hgraphX hcomp hrunX
  obtain ⟨nva, hva, hbva, _, hvaLast⟩ := mem_sideChainNodes_forward hv
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hga : run.coordinateProper.nodes.getD a default = na :=
    borderEnv_getD_of_get? hna
  have hgb : run.coordinateProper.nodes.getD b default = nb :=
    borderEnv_getD_of_get? hnb
  rw [hga, hgb] at hcond
  have hC12 : ((na.node.border == -1 || na.node.border == 1) &&
      na.node.border == nb.node.border) = true :=
    (Bool.and_eq_true_iff.mp hcond).1
  have hC3 : (na.node.clusterPath == nb.node.clusterPath) = true :=
    (Bool.and_eq_true_iff.mp hcond).2
  have hC1 : (na.node.border == -1 || na.node.border == 1) = true :=
    (Bool.and_eq_true_iff.mp hC12).1
  have hC2 : (na.node.border == nb.node.border) = true :=
    (Bool.and_eq_true_iff.mp hC12).2
  have hpath : na.node.clusterPath = nb.node.clusterPath := by
    simp only [beq_iff_eq] at hC3
    exact hC3
  have hbordeq : na.node.border = nb.node.border := by
    simp only [beq_iff_eq] at hC2
    exact hC2
  have htail : ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge).tail = a := rfl
  have hhead : ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge).head = b := rfl
  have hgaS : (sideBase run).nodes.getD a default = na := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hna
  have hgbS : (sideBase run).nodes.getD b default = nb := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hnb
  have hsa : (sideBase run).nodes[a]? = some na := by
    rw [hnodes]
    exact hna
  have hsb : (sideBase run).nodes[b]? = some nb := by
    rw [hnodes]
    exact hnb
  rcases hmem with hvaA | hvaB
  · have hva' : run.coordinateProper.nodes[a]? = some nva := by
      have h := hva
      rw [hvaA] at h
      exact h
    have heqv : nva = na := Option.some.inj (hva'.symm.trans hna)
    have hsideA : na.node.border = side := heqv ▸ hbva
    have hsideB : nb.node.border = side := hbordeq ▸ hsideA
    have hlastB : nb.node.clusterPath.getLast? = some decl := by
      rw [← hpath]
      exact heqv ▸ hvaLast
    have hbordB : nb.node.border = -1 ∨ nb.node.border = 1 := by
      rw [hsideB]
      exact hside
    have hcoordB : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[b]? =
        some nb := by
      rw [hcoordL]
      exact hnb
    have haddedB : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).nodes[b]? = some nb :=
      xed_side_original hready hcoordB hbordB
    have hsideW : nb.node.w = P.clusterBorderW :=
      xed_side_width _ _ hready haddedB hbordB
    have hbmem : b ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      exact ⟨nb, hnb, hsideB, hsideW, hlastB⟩
    have e2 : (na.node.border == nb.node.border) = true := by
      simp only [beq_iff_eq, hbordeq]
    have e3 : (na.node.clusterPath == nb.node.clusterPath) = true := by
      simp only [beq_iff_eq, hpath]
    have hbc : CoordsImpl.borderChain (sideBase run)
        ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = true := by
      unfold CoordsImpl.borderChain
      simp only [hsa, hsb]
      simp [hC1, e2, e3]
    have hother : CoordsImpl.otherEnd
        ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) v = b := by
      unfold CoordsImpl.otherEnd
      simp only [hvaA]
      simp
    have hne : b ≠ v := by
      rw [hvaA]
      exact Ne.symm hab
    exact ⟨hbc, b, hbmem, hother, hne⟩
  · have hva' : run.coordinateProper.nodes[b]? = some nva := by
      have h := hva
      rw [hvaB] at h
      exact h
    have heqv : nva = nb := Option.some.inj (hva'.symm.trans hnb)
    have hsideB : nb.node.border = side := heqv ▸ hbva
    have hsideA : na.node.border = side := hbordeq.trans hsideB
    have hlastA : na.node.clusterPath.getLast? = some decl := by
      rw [hpath]
      exact heqv ▸ hvaLast
    have hbordA : na.node.border = -1 ∨ na.node.border = 1 := by
      rw [hsideA]
      exact hside
    have hcoordA : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[a]? =
        some na := by
      rw [hcoordL]
      exact hna
    have haddedA : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).nodes[a]? = some na :=
      xed_side_original hready hcoordA hbordA
    have hsideW : na.node.w = P.clusterBorderW :=
      xed_side_width _ _ hready haddedA hbordA
    have hamem : a ∈ sideChainNodes P run side decl := by
      rw [mem_sideChainNodes hpos]
      exact ⟨na, hna, hsideA, hsideW, hlastA⟩
    have e2 : (na.node.border == nb.node.border) = true := by
      simp only [beq_iff_eq, hbordeq]
    have e3 : (na.node.clusterPath == nb.node.clusterPath) = true := by
      simp only [beq_iff_eq, hpath]
    have hbc : CoordsImpl.borderChain (sideBase run)
        ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = true := by
      unfold CoordsImpl.borderChain
      simp only [hsa, hsb]
      simp [hC1, e2, e3]
    have hneAB : (a == b) = false := by simp [hab]
    have hother : CoordsImpl.otherEnd
        ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) v = a := by
      simp [CoordsImpl.otherEnd, hvaB, hneAB]
    have hne : a ≠ v := by
      rw [hvaB]
      exact hab
    exact ⟨hbc, a, hamem, hother, hne⟩
/-- X copy of `borderInnerTitledBound_executed`: the exact titled-source
edges never reach an appended side marker. Same construction-phase proof
over `sizeProperPortsX` (node-count preservation via `sizeProperPortsX_length`). -/
private theorem xed_borderInnerTitledBound_executed
    {P : Params} {exact : List Nat} {cg : Graph} {labels : List MeasuredLabel}
    {ranks : List Int} {normalized labeled : Proper}
    (hn : NormalizeImpl.normalize cg ranks = .ok normalized)
    (hl : Labels.addLabelNodes cg normalized (componentLabels cg labels) = .ok labeled) :
    ∀ e ∈ (titleReservations (sizeProperPortsX P exact labeled)).edges,
      e.tail < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length ∧
      e.head < (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
  intro e he
  have hE : (titleReservations (sizeProperPortsX P exact labeled)).edges =
      labeled.edges := rfl
  have hEL : e ∈ labeled.edges := hE ▸ he
  have hEN : e ∈ normalized.edges := by
    have hEq := (Labels.addLabelNodes_metadata hl).1
    rw [hEq] at hEL
    exact hEL
  obtain ⟨ht, hh⟩ := normalize_edges_bound (rr := ⟨ranks, false⟩) hn e hEN
  have hLL : normalized.nodes.length = labeled.nodes.length :=
    addLabelNodes_node_length hl
  have hSP : (sizeProperPortsX P exact labeled).nodes.length = labeled.nodes.length :=
    sizeProperPortsX_length P exact labeled
  have hT : labeled.nodes.length ≤
      (titleReservations (sizeProperPortsX P exact labeled)).nodes.length := by
    have hlen : (titleReservations (sizeProperPortsX P exact labeled)).nodes.length =
        labeled.nodes.length +
          ((titleNodes (sizeProperPortsX P exact labeled)).map copyF).length := by
      rw [titleReservations_nodes, List.length_append, List.length_map, hSP]
    omega
  omega
/-- X replay of `shapeIncidentInherited_of_parts`: the exact inherited half
from its two construction halves (`xed_linksOfForm` over
`addClusterBorders_links_form`; titled edges excluded by the bound). -/
private theorem xed_shapeIncidentInherited_of_parts {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (_hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (_hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (_hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (_hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {_k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {labeled : Proper}
    (hcoordL : coordinateGraphX P (exactDecls exactIds inp) labeled =
      run.coordinateProper)
    (hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)))
    (hbound : BorderInnerTitledBoundResidual
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))) :
    ShapeIncidentInheritedResidual P run side decl := by
  intro v hv e he htouch
  obtain ⟨na, hna, hba, _, _⟩ := mem_sideChainNodes_forward hv
  have hcoordV : (coordinateGraphX P (exactDecls exactIds inp) labeled).nodes[v]? =
      some na := by
    rw [hcoordL]; exact hna
  have hbordV : na.node.border = -1 ∨ na.node.border = 1 := by
    rw [hba]; exact hside
  have haddedV : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled))
      P.clusterBorderW).nodes[v]? = some na :=
    xed_side_original hready hcoordV hbordV
  have hedges : run.coordinateProper.edges =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).edges := by
    rw [← hcoordL]; rfl
  have hlenE : e < (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled))
      P.clusterBorderW).edges.length := by
    have hlenEq' := congrArg List.length hedges
    omega
  have heEq : run.coordinateProper.edges[e]! =
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).edges[e]! := by
    rw [hedges]
  have hmemE : (OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled))
      P.clusterBorderW).edges[e]! ∈
      (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).edges := by
    rw [getElem!_pos ((OrderImpl.addClusterBorders (titleReservations
      (sizeProperPortsX P (exactDecls exactIds inp) labeled))
      P.clusterBorderW).edges) e hlenE]
    exact List.getElem_mem hlenE
  have hdisj := addClusterBorders_links_form _ _ hready.2.2.2.1 _ hmemE
  rcases hdisj with htitled | hlink
  · obtain ⟨htail, hhead⟩ := hbound _ htitled
    have htouch' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).edges[e]!.tail = v ∨
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPortsX P (exactDecls exactIds inp) labeled))
          P.clusterBorderW).edges[e]!.head = v := by
      rw [← heEq]; exact htouch
    obtain ⟨es, hinv⟩ := executed_border_binv P.clusterBorderW hready
    rcases OrderImpl.binv_lookup hinv haddedV with ⟨_, hnodeV⟩ | ⟨hleV, _, _, _⟩
    · have hmemV := List.mem_of_getElem? hnodeV
      rcases hbordV with hs | hs
      · exact ((hready.1 na hmemV).1 hs).elim
      · exact ((hready.1 na hmemV).2 hs).elim
    · have hF : False := by omega
      exact hF.elim
  · have htouch' : (OrderImpl.addClusterBorders (titleReservations
        (sizeProperPortsX P (exactDecls exactIds inp) labeled))
        P.clusterBorderW).edges[e]!.tail = v ∨
        (OrderImpl.addClusterBorders (titleReservations
          (sizeProperPortsX P (exactDecls exactIds inp) labeled))
          P.clusterBorderW).edges[e]!.head = v := by
      rw [← heEq]; exact htouch
    have hclose := xed_linksOfForm hpos labeled hcoordL hready hside hv hlink htouch'
    rw [← heEq] at hclose
    exact hclose
/-- X replay of `shapeIncidentInherited_executed`: the exact inherited half,
with the titled-edge bound discharged by `xed_borderInnerTitledBound_executed`
on the same ranked source the readiness bundle comes from. -/
private theorem xed_shapeIncidentInherited_executed {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ShapeIncidentInheritedResidual P run side decl := by
  obtain ⟨ranks, p0, labeled, q0, hn, hl, hcoordL, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled)) :=
    xed_titled_ready hkeys
      (componentCandidate_shape (components_nodup graph comp hcomp)
        (xed_exact_cgShape hgraph0 hgraphX) candidate)
      (fun _ _ hnode => xed_marker_shape hgraph0 hgraphX hnode)
      haligned
  exact xed_shapeIncidentInherited_of_parts (_k := k) hgraph0 hgraphX hcomp hrunX hside hpos
    hcoordL hready (xed_borderInnerTitledBound_executed hn hl)
/-- X inherited-half transport: a context edge below the coordinate-edge
count is a coordinate edge, so the inherited residual applies. -/
private theorem xed_shape_incident_inheritedAt {P : Params} {run : Run}
    {side : Int} {decl : Nat} {pos : Array Nat} {k : Nat}
    (hinh : ShapeIncidentInheritedResidual P run side decl)
    {v : Nat} (hv : v ∈ sideChainNodes P run side decl) {e : Nat}
    (hlt : e < run.coordinateProper.edges.length)
    (he : e < (sideCtx P run pos k).edges.size)
    (htouch : (sideCtx P run pos k).edges[e]!.tail = v ∨
      (sideCtx P run pos k).edges[e]!.head = v) :
    CoordsImpl.borderChain (sideBase run) (sideCtx P run pos k).edges[e]! = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u ∧ u ≠ v := by
  have harr : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
  have hsize : (sideCtx P run pos k).edges.size = (sideBase run).edges.length := by
    rw [harr, List.size_toArray]
  have he_base : e < (sideBase run).edges.length := hsize ▸ he
  have hbase_eq := sideBase_edges_append run
  have h_eq_opt : (sideBase run).edges[e]? = run.coordinateProper.edges[e]? := by
    rw [hbase_eq, List.getElem?_append_left hlt]
  have h_eq_ctx_base : (sideCtx P run pos k).edges[e]! =
      (sideBase run).edges[e]! := by
    rw [harr, List.getElem!_toArray]
  have h_eq_base_coord : (sideBase run).edges[e]! =
      run.coordinateProper.edges[e]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, h_eq_opt]
  have h_eq_ctx_coord : (sideCtx P run pos k).edges[e]! =
      run.coordinateProper.edges[e]! := by
    rw [h_eq_ctx_base, h_eq_base_coord]
  have htouch' : run.coordinateProper.edges[e]!.tail = v ∨
      run.coordinateProper.edges[e]!.head = v :=
    h_eq_ctx_coord ▸ htouch
  obtain ⟨hbc, u, hu, hu_other, hne⟩ := hinh v hv e hlt htouch'
  have hbc' : CoordsImpl.borderChain (sideBase run)
      (sideCtx P run pos k).edges[e]! = true := by
    rw [h_eq_ctx_coord]
    exact hbc
  have hu_other' : CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u := by
    rw [h_eq_ctx_coord]
    exact hu_other
  exact ⟨hbc', u, hu, hu_other', hne⟩
/-- X pair-edge extraction: a context edge at/after the coordinate-edge count
is the alignment-pair edge of two consecutive-layer nodes, with its filter
condition and endpoint incidence. -/
private theorem xed_pair_witness {P : Params} {run : Run}
    {_side : Int} {_decl : Nat} {pos : Array Nat} {k : Nat}
    {v e : Nat}
    (hle : run.coordinateProper.edges.length ≤ e)
    (he_base : e < (sideBase run).edges.length)
    (_he : e < (sideCtx P run pos k).edges.size)
    (htouch : (sideCtx P run pos k).edges[e]!.tail = v ∨
      (sideCtx P run pos k).edges[e]!.head = v) :
    ∃ (ls : List Nat × List Nat) (idx a b : Nat),
      run.layers[idx]? = some ls.1 ∧
      run.layers[idx + 1]? = some ls.2 ∧
      a ∈ ls.1 ∧ b ∈ ls.2 ∧
      Eq (((run.coordinateProper.nodes.getD a default).node.border == -1 ||
          (run.coordinateProper.nodes.getD a default).node.border == 1) &&
          (run.coordinateProper.nodes.getD a default).node.border ==
            (run.coordinateProper.nodes.getD b default).node.border &&
          (run.coordinateProper.nodes.getD a default).node.clusterPath ==
            (run.coordinateProper.nodes.getD b default).node.clusterPath) true ∧
      ({ tail := a, head := b, decl := (run.coordinateProper.nodes.getD a default).node.decl, original := 0 } : ProperEdge) = (sideCtx P run pos k).edges[e]! ∧
      (v = a ∨ v = b) := by
  have harr : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
  have hbase_eq := sideBase_edges_append run
  have h_eq_opt_base : (sideBase run).edges[e]? =
      (((run.layers.zip run.layers.tail).flatMap fun ls : List Nat × List Nat =>
        ls.1.flatMap fun a => ls.2.filterMap fun b =>
          let na := (run.coordinateProper.nodes.getD a default).node
          let nb := (run.coordinateProper.nodes.getD b default).node
          if (na.border == -1 || na.border == 1) && na.border == nb.border &&
              na.clusterPath == nb.clusterPath then
            some ({ tail := a, head := b, decl := na.decl, original := 0 } : ProperEdge)
          else none))[e - run.coordinateProper.edges.length]? := by
    rw [hbase_eq, List.getElem?_append_right hle]
  have h_side_orig : (sideBase run).edges[e]? =
      some ((sideBase run).edges[e]'he_base) :=
    List.getElem?_eq_getElem he_base
  have h_side_some : (((run.layers.zip run.layers.tail).flatMap fun ls : List Nat × List Nat =>
        ls.1.flatMap fun a => ls.2.filterMap fun b =>
          let na := (run.coordinateProper.nodes.getD a default).node
          let nb := (run.coordinateProper.nodes.getD b default).node
          if (na.border == -1 || na.border == 1) && na.border == nb.border &&
              na.clusterPath == nb.clusterPath then
            some ({ tail := a, head := b, decl := na.decl, original := 0 } : ProperEdge)
          else none))[e - run.coordinateProper.edges.length]? =
      some ((sideBase run).edges[e]'he_base) := by
    rw [← h_eq_opt_base]
    exact h_side_orig
  generalize hed_def : ((sideBase run).edges[e]'he_base) = ed
  have hed_mem : ed ∈
      ((run.layers.zip run.layers.tail).flatMap fun ls : List Nat × List Nat =>
        ls.1.flatMap fun a => ls.2.filterMap fun b =>
          let na := (run.coordinateProper.nodes.getD a default).node
          let nb := (run.coordinateProper.nodes.getD b default).node
          if (na.border == -1 || na.border == 1) && na.border == nb.border &&
              na.clusterPath == nb.clusterPath then
            some ({ tail := a, head := b, decl := na.decl, original := 0 } : ProperEdge)
          else none) := by
    rw [← hed_def]
    exact List.mem_of_getElem? h_side_some
  obtain ⟨ls, hls_mem, hed_ls⟩ := List.mem_flatMap.mp hed_mem
  obtain ⟨a, ha_mem, hed_a⟩ := List.mem_flatMap.mp hed_ls
  obtain ⟨b, hb_mem, hfb⟩ := List.mem_filterMap.mp hed_a
  dsimp only at hfb
  have hC : Eq (((run.coordinateProper.nodes.getD a default).node.border == -1 ||
      (run.coordinateProper.nodes.getD a default).node.border == 1) &&
      (run.coordinateProper.nodes.getD a default).node.border ==
        (run.coordinateProper.nodes.getD b default).node.border &&
      (run.coordinateProper.nodes.getD a default).node.clusterPath ==
        (run.coordinateProper.nodes.getD b default).node.clusterPath) true := by
    by_cases hc : (((run.coordinateProper.nodes.getD a default).node.border == -1 ||
        (run.coordinateProper.nodes.getD a default).node.border == 1) &&
        (run.coordinateProper.nodes.getD a default).node.border ==
          (run.coordinateProper.nodes.getD b default).node.border &&
        (run.coordinateProper.nodes.getD a default).node.clusterPath ==
          (run.coordinateProper.nodes.getD b default).node.clusterPath) = true
    · exact hc
    · rw [ite_eq_right hc] at hfb
      exact absurd hfb (by simp)
  have hed_eq : ({ tail := a, head := b, decl := (run.coordinateProper.nodes.getD a default).node.decl, original := 0 } : ProperEdge) = ed := by
    rw [ite_eq_left hC] at hfb
    exact Option.some.inj hfb
  have h_eq_ctx_base : (sideCtx P run pos k).edges[e]! =
      (sideBase run).edges[e]! := by
    rw [harr, List.getElem!_toArray]
  have h_eq_base_ed : (sideBase run).edges[e]! = ed := by
    rw [List.getElem!_eq_getElem?_getD, h_side_orig, Option.getD_some]
    exact hed_def
  have h_eq_ctx_ed : (sideCtx P run pos k).edges[e]! = ed := by
    rw [h_eq_ctx_base, h_eq_base_ed]
  have hmem : v = a ∨ v = b := by
    have htouch_ed : ed.tail = v ∨ ed.head = v := by
      rw [← h_eq_ctx_ed]
      exact htouch
    rw [← hed_eq] at htouch_ed
    have htail : ({ tail := a, head := b, decl := (run.coordinateProper.nodes.getD a default).node.decl, original := 0 } : ProperEdge).tail = a := rfl
    have hhead : ({ tail := a, head := b, decl := (run.coordinateProper.nodes.getD a default).node.decl, original := 0 } : ProperEdge).head = b := rfl
    rw [htail, hhead] at htouch_ed
    rcases htouch_ed with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  obtain ⟨idx, hi_l1, hi_l2⟩ := mem_zip_tail_iff.mp hls_mem
  have h_eq_pair_ctx : ({ tail := a, head := b, decl := (run.coordinateProper.nodes.getD a default).node.decl, original := 0 } : ProperEdge) = (sideCtx P run pos k).edges[e]! := by
    rw [hed_eq, h_eq_ctx_ed]
  exact ⟨ls, idx, a, b, hi_l1, hi_l2, ha_mem, hb_mem, hC, h_eq_pair_ctx, hmem⟩
/-- X node existence and distinctness for a pair edge: consecutive-layer
membership puts both endpoints in range, and layer positions separate them. -/
private theorem xed_pair_nodes_distinct {_P : Params} {run : Run} {pos : Array Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    {ls : List Nat × List Nat} {idx a b : Nat}
    (hi_l1 : run.layers[idx]? = some ls.1)
    (hi_l2 : run.layers[idx + 1]? = some ls.2)
    (ha_mem : a ∈ ls.1) (hb_mem : b ∈ ls.2) :
    ∃ na nb : ProperNode,
      run.coordinateProper.nodes[a]? = some na ∧
      run.coordinateProper.nodes[b]? = some nb ∧ a ≠ b := by
  have hparts := CoordsImpl.checkLayers_parts hpos
  obtain ⟨hrange, hlp, _⟩ := hparts
  obtain ⟨pos', hlp'⟩ := hlp
  have hspec := CoordsImpl.layerPositions_spec hlp'
  obtain ⟨_, hrk_spec, _⟩ := hspec
  have h_l1_mem : ls.1 ∈ run.layers := List.mem_of_getElem? hi_l1
  have h_l2_mem : ls.2 ∈ run.layers := List.mem_of_getElem? hi_l2
  obtain ⟨ja, hja⟩ := List.mem_iff_getElem?.mp ha_mem
  obtain ⟨jb, hjb⟩ := List.mem_iff_getElem?.mp hb_mem
  have ha_lt : a < run.coordinateProper.nodes.length := by
    have h1 : a < (sideBase run).nodes.length :=
      CoordsImpl.layers_mem_lt hrange h_l1_mem hja
    have heq : (sideBase run).nodes.length =
        run.coordinateProper.nodes.length := rfl
    omega
  have hb_lt : b < run.coordinateProper.nodes.length := by
    have h1 : b < (sideBase run).nodes.length :=
      CoordsImpl.layers_mem_lt hrange h_l2_mem hjb
    have heq : (sideBase run).nodes.length =
        run.coordinateProper.nodes.length := rfl
    omega
  obtain ⟨na, hna⟩ : ∃ na : ProperNode,
      run.coordinateProper.nodes[a]? = some na :=
    ⟨_, List.getElem?_eq_getElem ha_lt⟩
  obtain ⟨nb, hnb⟩ : ∃ nb : ProperNode,
      run.coordinateProper.nodes[b]? = some nb :=
    ⟨_, List.getElem?_eq_getElem hb_lt⟩
  have hab : a ≠ b := by
    intro hcon
    have hrk_a : rk (sideBase run).rank a = (idx : Int) :=
      hrk_spec idx ls.1 a hi_l1 ha_mem
    have ha_in_l2 : a ∈ ls.2 := hcon ▸ hb_mem
    have hrk_a2 : rk (sideBase run).rank a = ((idx + 1 : Nat) : Int) :=
      hrk_spec (idx + 1) ls.2 a hi_l2 ha_in_l2
    omega
  exact ⟨na, nb, hna, hnb, hab⟩
/-- X replay of the `incident_border` field: inherited edges through
`xed_shape_incident_inheritedAt`, pair edges through `xed_pair_witness`,
`xed_pair_nodes_distinct`, and `xed_shape_incident_pair`. -/
private theorem xed_shape_incident_border {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ∀ v ∈ sideChainNodes P run side decl, ∀ e : Nat,
    e < (sideCtx P run pos k).edges.size →
    ((sideCtx P run pos k).edges[e]!.tail = v ∨
      (sideCtx P run pos k).edges[e]!.head = v) →
    CoordsImpl.borderChain (sideBase run) (sideCtx P run pos k).edges[e]! = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u ∧ u ≠ v := by
  intro v hv e he htouch
  have harr : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
  have hsize : (sideCtx P run pos k).edges.size = (sideBase run).edges.length := by
    rw [harr, List.size_toArray]
  by_cases hlt : e < run.coordinateProper.edges.length
  · exact xed_shape_incident_inheritedAt
      (xed_shapeIncidentInherited_executed (k := k) hgraph0 hgraphX hcomp hrunX hside hpos)
      hv hlt he htouch
  · have hle : run.coordinateProper.edges.length ≤ e := by omega
    have he_base : e < (sideBase run).edges.length := hsize ▸ he
    obtain ⟨ls, idx, a, b, hi_l1, hi_l2, ha_mem, hb_mem, hC, h_eq_pair_ctx, hmem⟩ :=
      xed_pair_witness (_side := side) (_decl := decl) hle he_base he htouch
    obtain ⟨na, nb, hna, hnb, hab⟩ :=
      xed_pair_nodes_distinct (_P := P) hpos hi_l1 hi_l2 ha_mem hb_mem
    have hgetD_a : run.coordinateProper.nodes.getD a default = na :=
      borderEnv_getD_of_get? hna
    have hed_eq' : ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = (sideCtx P run pos k).edges[e]! := by
      rw [← h_eq_pair_ctx, ← hgetD_a]
    obtain ⟨hbc_pair, u, hu, hu_other_pair, hne⟩ :=
      xed_shape_incident_pair hgraph0 hgraphX hcomp hrunX hside hpos hna hnb hab hC hv hmem
    have hbc_ctx : CoordsImpl.borderChain (sideBase run)
        (sideCtx P run pos k).edges[e]! = true := by
      rw [← hed_eq']
      exact hbc_pair
    have hu_other_ctx : CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u := by
      rw [← hed_eq']
      exact hu_other_pair
    exact ⟨hbc_ctx, u, hu, hu_other_ctx, hne⟩
/-- X replay of `foreignSideChainShape_executed`: the exact executed side
chain satisfies `ForeignSideChainShape` from the five replayed fields. -/
private theorem xed_foreignSideChainShape_executed {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos) :
    ForeignSideChainShape P run side decl pos k := by
  refine ⟨xed_shapeRankInj_executed hgraph0 hgraphX hcomp hrunX hside hpos,
    xed_shapeRankConsec_executed hgraph0 hgraphX hcomp hrunX hside hpos, ?_, ?_, ?_⟩
  · intro i hi
    exact xed_shape_path_consec hgraph0 hgraphX hcomp hrunX hside i hi
  · intro v hv e he htouch
    exact xed_shape_incident_border hgraph0 hgraphX hcomp hrunX hside hpos v hv e he htouch
  · intro v hv w hw hrk
    exact xed_shape_consec_edge hgraph0 hgraphX hcomp hrunX hside hpos v hv w hw hrk

/-- Executed exact side-chain shape: every exact run closes
`ForeignSideChainShape`, with execution evidence only. No `WellFormed` or
`framedParents` premise: the plain closed proof (`foreignSideChainShape` over
`shapeRankInjResidual`, `shapeIncidentInherited_of_parts` with
`borderInnerTitledBound_executed`, and `shapeRankConsec`) needs none, so the
exact replay needs none either. -/
theorem X_foreignSideChainShapeClosed_holds (exactIds : List String) :
    X_ForeignSideChainShapeClosed exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX comp hcomp candidate run
    labels orderOptions hrunX side decl hside pos k hpos
  exact xed_foreignSideChainShape_executed hgraph0 hgraphX hcomp hrunX hside hpos
end PipelineImpl
end Layered
end Elegant
