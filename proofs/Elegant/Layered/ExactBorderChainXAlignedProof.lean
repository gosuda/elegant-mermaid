import Elegant.Layered.ForeignBorderChainXAlignedClosed
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactPipeline
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.ExactFlatC7CaptionScope

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact border-chain alignment.

Target: `X_foreignBorderChainXAligned_of_stable` below: the X mirror
`X_ForeignBorderChainXAligned exactIds` replayed over `componentRunX`.

Replay map (plain `foreignBorderChainXAligned'` in
`ForeignBorderChainXAlignedClosed.lean`):
* width-reading facts: border markers are synthetic, emitted by
  `addClusterBorders` with width `P.clusterBorderW` after the size hook, so
  the size hook (`sizeProperPortsX` keeps dummy/border/clusterPath per
  `sizeProperPortsX_key`, and changes widths of fixed border-`0` nodes only)
  cannot move them: `XBC_sized_node_origin`, `XBC_side_width`.
* position-reading facts: placement runs before the exact reserve stage and
  `componentRunX_spec` exposes the same placement conjuncts
  (`crossCoordsClusterWith`, `proxyWidths`): `XBC_border_record`,
  `XBC_sideBlocked`, and the final interval transport.
* ordering fact: `ForeignBorderDivergeStable` quantifies over the plain
  `componentRun`, so it cannot be applied to an exact run; the exact twin
  `X_ForeignBorderDivergeStable` is the premise of the generic transfer.
  The framed proof instead derives divergence stability for the executed run.
* shape fact: the executed side-chain shape
  (`X_ForeignSideChainShapeClosed`) concerns only ranks, edges, and paths.
  `X_foreignSideChainShapeClosed_holds` proves it from execution alone.
-/

/-- X twin of `ForeignBorderDivergeStable`: divergent sibling blocks keep one
left-to-right order on every layer pair of an exact run. Mirrors the plain
def field by field, with the `measuredGraph`-then-`exactGraph` pipeline and
`componentRunX` over `exactDecls exactIds inp`. -/
def X_ForeignBorderDivergeStable (exactIds : List String) : Prop :=
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
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j')
/-- Per-run suffix of `X_ForeignBorderDivergeStable`: the executed divergent
marker order of one run. The public `..._of_local_stable` alignment takes
this shape so a caller can discharge stability per run without the global
premise. -/
abbrev X_ForeignBorderDivergeStableRun (run : Run) : Prop :=
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
      ∀ {i j i' j' : Nat}, l1[i]? = some a → l1[j]? = some b →
        l2[i']? = some a' → l2[j']? = some b' →
        (i < j ↔ i' < j')
/-- Per-run suffix of `X_ForeignSideChainShapeClosed`: the side-chain shape
of one executed run. -/
abbrev X_ForeignSideChainShapeRun (P : Params) (run : Run) : Prop :=
  ∀ {side : Int} {decl : Nat}, side = -1 ∨ side = 1 →
    ∀ {pos : Array Nat} {k : Nat},
    CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
    ForeignSideChainShape P run side decl pos k



/-- X mirror of `ForeignSideChainShape` closure: the executed side-chain shape
for exact runs. Single-fact residual (ranks/edges/paths only). -/
def X_ForeignSideChainShapeClosed (exactIds : List String) : Prop :=
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
    ∀ {side : Int} {decl : Nat}, side = -1 ∨ side = 1 →
    ∀ {pos : Array Nat} {k : Nat},
    CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos →
    ForeignSideChainShape P run side decl pos k

/-- X mirror of `ForeignBorderSideUps`: the side chains form single alignment
blocks, over the exact pipeline. -/
def X_ForeignBorderSideUps (exactIds : List String) : Prop :=
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
    ∀ {decl : Nat} {side : Int}, side = -1 ∨ side = 1 →
    ∀ {k : Nat}, k < 4 →
    ∀ {pos : Array Nat},
    CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos →
    ∃ chain ordered : List Nat,
      (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl) ∧
      ∀ (hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
      Elegant.Layered.BorderChainUps P.nodeGap P.clusterPad (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
        k chain ordered hL

/-- `orientNode` keeps decl/border/clusterPath. -/
private theorem XBC_orientNode_key (d : Direction) (n : Node) :
    (orientNode d n).decl = n.decl ∧ (orientNode d n).border = n.border ∧
      (orientNode d n).clusterPath = n.clusterPath := by
  cases d <;> exact ⟨rfl, rfl, rfl⟩

/-- Exact-graph nodes keep decl/border/clusterPath of the measured node. -/
private theorem XBC_exactGraph_node {P : Params} {exactIds : List String} {inp : Input}
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
            obtain ⟨hd, hbdr, hp⟩ := XBC_orientNode_key o.direction
              { n0 with w := fixed.2.w, h := fixed.2.h }
            rw [hsz] at hd hbdr hp
            exact ⟨n0, h0, by rw [← hb, hbn]; exact hd,
              by rw [← hb, hbn]; exact hbdr, by rw [← hb, hbn]; exact hp⟩

/-- Exact graphs keep the measured node count. -/
private theorem XBC_exactGraph_length {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph) :
    graph.nodes.length = graph0.nodes.length := by
  unfold exactGraph at hgraphX
  obtain ⟨nodes, hmap, hrest⟩ := bind_ok hgraphX
  have hgeq : graph = { graph0 with nodes := nodes } := Except.ok.inj hrest.symm
  obtain ⟨hlen, _⟩ := mapM_getElem? _ _ _ hmap
  subst hgeq
  exact hlen

/-- `CgShape` transfers across the exact graph. -/
private theorem XBC_exact_cgShape {P : Params} {exactIds : List String} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph) :
    CgShape graph := by
  have hs0 := measuredGraph_shape hgraph0
  refine ⟨?_, ?_⟩
  · intro a b na nb ha hb h1 h2 hp
    obtain ⟨n0a, ha0, _, hb0a, hp0a⟩ := XBC_exactGraph_node hgraphX ha
    obtain ⟨n0b, hb0, _, hb0b, hp0b⟩ := XBC_exactGraph_node hgraphX hb
    have h1' : n0a.border = -2 := by rw [← hb0a]; exact h1
    have h2' : n0b.border = -2 := by rw [← hb0b]; exact h2
    have hp' : n0a.clusterPath = n0b.clusterPath := by rw [← hp0a, ← hp0b]; exact hp
    exact hs0.1 a b n0a n0b ha0 hb0 h1' h2' hp'
  · intro n hn
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hn
    obtain ⟨n0, h0, _, hb0, _⟩ := XBC_exactGraph_node hgraphX hi
    have h3 := hs0.2 n0 (List.mem_of_getElem? h0)
    rw [hb0]
    exact h3

/-- Marker shapes transfer across the exact graph component candidates. -/
private theorem XBC_marker_shape {P : Params} {exactIds : List String} {inp : Input}
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
    obtain ⟨n0, h0, _, hb0, hp0⟩ := XBC_exactGraph_node hgraphX hsource
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
private theorem XBC_sized_node_origin (P : Params) (exact : List Nat) (source : Proper)
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
private theorem XBC_titled_alignment (P : Params) (exact : List Nat) {source : Proper}
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
private theorem XBC_titled_node_origin {cg : Graph} {P : Params} {exact : List Nat}
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
      XBC_sized_node_origin P exact source hsized
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
      XBC_sized_node_origin P exact source hsized
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
private theorem XBC_titled_ready {cg : Graph} {P : Params} {exact : List Nat} {source : Proper}
    (hkeys : NodeKeys cg source) (hshape : CgShape cg)
    (hmarkers : ∀ (index : Nat) (node : Node), cg.nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []))
    (haligned : source.nodes.length = source.rank.length) :
    OrderImpl.BorderConstructionReady (titleReservations (sizeProperPortsX P exact source)) := by
  refine ⟨?_, ?_, ?_, XBC_titled_alignment P exact haligned, ?_⟩
  · intro node hnode
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hnode
    rcases XBC_titled_node_origin hkeys hindex with
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
    rcases XBC_titled_node_origin hkeys hindex with
      ⟨original, horiginal, _, hb, hp⟩ | ⟨_, hb⟩
    · rcases hkeys index original horiginal with
        ⟨before, hbefore, _, hborder, hpath⟩ | ⟨_, hborder, _⟩
      · have hbeforeGroup : before.border = -2 := by omega
        rw [hp, hpath]
        exact (hmarkers index before hbefore).2 hbeforeGroup
      · omega
    · omega
  · intro a b na nb ha hb hgroupA hgroupB hpath
    rcases XBC_titled_node_origin hkeys ha with
      ⟨oa, hoa, _, hba, hpa⟩ | ⟨_, hba⟩
    · rcases XBC_titled_node_origin hkeys hb with
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
    rcases XBC_titled_node_origin hkeys hindex with
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
private theorem XBC_titled_border_ready {P : Params} {exactIds : List String} {inp : Input}
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
  exact ⟨labeled, hcoordL, XBC_titled_ready
    (addLabelNodes_keys _ _ _ (normalize_keys hn) hl)
    (componentCandidate_shape (components_nodup graph comp hcomp)
      (XBC_exact_cgShape hgraph0 hgraphX) candidate)
    (fun _ _ hnode => XBC_marker_shape hgraph0 hgraphX hnode)
    haligned⟩
/-- X coordinate proper is borders-well-formed for an executed exact run. -/
private theorem XBC_bordersWellFormed {P : Params} {exactIds : List String} {inp : Input}
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
  obtain ⟨labeled, hc, hready⟩ := XBC_titled_border_ready hgraph0 hgraphX hcomp hrunX
  rw [← hc]
  unfold coordinateGraphX
  exact materializeDummyPaths_bordersWellFormed
    (clearProxyExtents_bordersWellFormed
      (OrderImpl.addClusterBorders_bordersWellFormed _ _ hready))

/-- X copy of `coordinateGraph_side_original`. -/
private theorem XBC_side_original {P : Params} {exact : List Nat} {source : Proper}
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

/-- X copy of `addClusterBorders_side_width`: every side marker emitted by
`addClusterBorders` carries the border width. Markers are synthetic, so the
exact size hook cannot move them. -/
private theorem XBC_addClusterBorders_side_width (source : Proper) (width : Int)
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

/-- X border records transfer coordinates unchanged: the reserve stage shifts
only `ys`/`top`, and `proxyWidths` leaves border markers alone. -/
private theorem XBC_border_record {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {v : Nat} {node : ProperNode}
    (hv : run.coordinateProper.nodes[v]? = some node)
    (hborder : node.node.border = -1 ∨ node.node.border = 1) :
    run.proper.nodes[v]? = some node ∧
      run.xs.getD v 0 = run.coordinateXs.getD v 0 := by
  obtain ⟨_, _, _, q0, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hnotProxy : ¬ (node.node.border = -2 ∨ node.node.border = 2) := by
    rcases hborder with hborder | hborder <;> omega
  obtain ⟨hnode, hx⟩ := (proxyWidths_rel hproxy).2.2.2.2.2 v node hv hnotProxy
  refine ⟨?_, ?_⟩
  · rw [← hdrop]
    exact hnode
  · simp only [List.getD_eq_getElem?_getD, hx, Option.getD_some]

/-- X copy of `foreignSideMarkingCrossed`, generalized off the unused run
hypothesis: the marking conclusion follows from the layer check and the
border-border non-crossing residual alone. -/
private theorem XBC_foreignSideMarkingCrossed {P : Params} {run : Run} {pos : Array Nat}
    {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (_hk : k < 4)
    (hcross : ForeignBorderEdgesNoncrossing P run pos k) :
    ForeignSideMarkingCrossed P run pos k := by
  unfold ForeignSideMarkingCrossed
  intro e f w x a b he hf he_or hf_or hfb hr1 hr2 hr3 hp1 hp2
  by_cases hbe : CoordsImpl.borderChain (sideBase run)
      ((sideCtx P run pos k).edges[e]!) = true
  · exact False.elim
      (hcross e f w x a b he hf he_or hf_or hbe hfb hr1 hr2 hr3 hp1 hp2)
  · exact marked_of_interleave_noborder hpos he hf he_or hf_or hfb
       (Bool.eq_false_of_ne_true hbe) hr1 hr2 hr3 hp1 hp2

/-- X copy of `foreignSideFoldBound`, generalized off the unused run
hypothesis: the fold bound follows from the chain shape and the marking
residual alone. Neither fact reads node widths or `xs` positions. -/
private theorem XBC_foreignSideFoldBound {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat} {k : Nat}
    (_hside : side = -1 ∨ side = 1) (_hk : k < 4)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hshape : ForeignSideChainShape P run side decl pos k)
    (hmark : ForeignSideMarkingCrossed P run pos k) :
    ForeignSideFoldBound P run side decl pos k := by
  unfold ForeignSideFoldBound
  intro v hv pred hpred x hx last w hpick
  have hfacts : CoordsImpl.Lay (sideCtx P run pos k) ∧
      CoordsImpl.EdgeOK (sideCtx P run pos k) :=
    Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos
  obtain ⟨hL, hE⟩ := hfacts
  obtain ⟨e, hesz, hemem, hmarked, hw, hwflat, hrank, _hlast⟩ :=
    alignPick_unmarked_edge (c := sideCtx P run pos k) hE hpick
  have hvF : v ∈ (sideCtx P run pos k).layers.flatten := by
    have hmem : v ∈ run.layers.flatten := sideChainNodes_flat hv
    have hctx : (sideCtx P run pos k).layers =
      CoordsImpl.passLayers run.layers k := rfl
    rw [hctx]
    exact (CoordsImpl.passLayers_perm run.layers k).mem_iff.mpr hmem
  obtain ⟨hxF, hrankx, hposx⟩ :=
    prefix_mem_pos_lt (c := sideCtx P run pos k) hL hvF hx
  unfold chainPred at hpred
  have hpmem : pred ∈ sideChainNodes P run side decl :=
    List.mem_of_find?_eq_some hpred
  have hpspec : decide ((sideCtx P run pos k).rank[pred]! + 1 =
      (sideCtx P run pos k).rank[v]!) = true := by
    simpa using List.find?_some hpred
  have hprk : (sideCtx P run pos k).rank[pred]! + 1 =
      (sideCtx P run pos k).rank[v]! :=
    of_decide_eq_true hpspec
  have hpredF : pred ∈ (sideCtx P run pos k).layers.flatten := by
    have hmem : pred ∈ run.layers.flatten := sideChainNodes_flat hpmem
    have hctx : (sideCtx P run pos k).layers =
      CoordsImpl.passLayers run.layers k := rfl
    rw [hctx]
    exact (CoordsImpl.passLayers_perm run.layers k).mem_iff.mpr hmem
  obtain ⟨f, hfsz, hfor⟩ := hshape.consec_edge pred hpmem v hv hprk
  have htouchF : (sideCtx P run pos k).edges[f]!.tail = pred ∨
      (sideCtx P run pos k).edges[f]!.head = pred := by
    rcases hfor with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inr h1
    · exact Or.inl h1
  have hincF := hshape.incident_border pred hpmem f hfsz htouchF
  obtain ⟨hbc, -, -, -⟩ := hincF
  have hfor' : ((sideCtx P run pos k).edges[f]!.tail = pred ∧
      (sideCtx P run pos k).edges[f]!.head = v ∨
    (sideCtx P run pos k).edges[f]!.tail = v ∧
      (sideCtx P run pos k).edges[f]!.head = pred) := by
    rcases hfor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h1, h2⟩
  have hmem2 := CoordsImpl.mem_upperEdges hemem
  obtain ⟨-, hcase⟩ := hmem2
  rcases Int.lt_trichotomy ((sideCtx P run pos k).pos[w]! : Int)
    ((sideCtx P run pos k).pos[pred]! : Int) with hgoal | heqI | hltI
  · exact hgoal
  · have heq : (sideCtx P run pos k).pos[pred]! =
        (sideCtx P run pos k).pos[w]! := by
      exact_mod_cast heqI.symm
    obtain ⟨Lw, hwLget, hwLv⟩ := hL.loc hwflat
    obtain ⟨Lp, hpLget, hpLv⟩ := hL.loc hpredF
    have hrankw : (sideCtx P run pos k).rank[w]! =
        (sideCtx P run pos k).rank[pred]! := by omega
    rw [hrankw] at hwLget
    have hLL : Lp = Lw := by
      rw [hpLget] at hwLget
      exact Option.some_inj.mp hwLget
    rw [hLL, heq] at hpLv
    rw [hpLv] at hwLv
    have hwp : w = pred := Option.some_inj.mp hwLv.symm
    have hxp : x ≠ pred := by
      intro hcon
      rw [hcon] at hrankx
      omega
    rcases hcase with ⟨hheadx, h2⟩ | ⟨htailx, -⟩
    · have htx : (sideCtx P run pos k).edges[e]!.tail ≠ x := by
        intro hcon
        rw [hcon] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == x) = false := by
        simpa using htx
      have htail : (sideCtx P run pos k).edges[e]!.tail = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hnt] at hw
        simpa using hw
      have htouch : (sideCtx P run pos k).edges[e]!.tail = pred ∨
          (sideCtx P run pos k).edges[e]!.head = pred :=
        Or.inl (htail.trans hwp)
      have hinc := hshape.incident_border pred hpmem e hesz htouch
      obtain ⟨-, u, hu, huother, -⟩ := hinc
      have hbeq : ((sideCtx P run pos k).edges[e]!.tail == pred) = true := by
        have htp : (sideCtx P run pos k).edges[e]!.tail = pred :=
          htail.trans hwp
        simpa using htp
      have hueqx : CoordsImpl.otherEnd ((sideCtx P run pos k).edges[e]!)
          pred = x := by
        unfold CoordsImpl.otherEnd
        rw [hbeq]
        simp only [ite_true]
        exact hheadx
      have hueq : u = x := huother.symm.trans hueqx
      rw [hueq] at hu
      have hxv : x = v := hshape.rank_inj x hu v hv hrankx
      rw [hxv] at hposx
      exact False.elim (absurd hposx (Nat.lt_irrefl _))
    · have hbeq : ((sideCtx P run pos k).edges[e]!.tail == x) = true := by
        simpa using htailx
      have hhw : (sideCtx P run pos k).edges[e]!.head = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hbeq] at hw
        simpa using hw
      have htouch : (sideCtx P run pos k).edges[e]!.tail = pred ∨
          (sideCtx P run pos k).edges[e]!.head = pred :=
        Or.inr (hhw.trans hwp)
      have hinc := hshape.incident_border pred hpmem e hesz htouch
      obtain ⟨-, u, hu, huother, -⟩ := hinc
      have htne : (sideCtx P run pos k).edges[e]!.tail ≠ pred := by
        rw [htailx]
        exact hxp
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == pred) = false := by
        simpa using htne
      have hueqx : CoordsImpl.otherEnd ((sideCtx P run pos k).edges[e]!)
          pred = x := by
        unfold CoordsImpl.otherEnd
        rw [hnt]
        simp only [Bool.false_eq_true, ite_false]
        exact htailx
      have hueq : u = x := huother.symm.trans hueqx
      rw [hueq] at hu
      have hxv : x = v := hshape.rank_inj x hu v hv hrankx
      rw [hxv] at hposx
      exact False.elim (absurd hposx (Nat.lt_irrefl _))
  · have hposxI : ((sideCtx P run pos k).pos[x]! : Int) <
        ((sideCtx P run pos k).pos[v]! : Int) := by
      exact_mod_cast hposx
    rcases hcase with ⟨hheadx, h2⟩ | ⟨htailx, -⟩
    · have htx : (sideCtx P run pos k).edges[e]!.tail ≠ x := by
        intro hcon
        rw [hcon] at h2
        exact absurd h2 (Nat.lt_irrefl _)
      have hnt : ((sideCtx P run pos k).edges[e]!.tail == x) = false := by
        simpa using htx
      have htail : (sideCtx P run pos k).edges[e]!.tail = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hnt] at hw
        simpa using hw
      have heD : ((sideCtx P run pos k).edges[e]!.tail = w ∧
          (sideCtx P run pos k).edges[e]!.head = x ∨
        (sideCtx P run pos k).edges[e]!.tail = x ∧
          (sideCtx P run pos k).edges[e]!.head = w) :=
        Or.inl ⟨htail, hheadx⟩
      have hmarked2 := hmark e f w x pred v hesz hfsz heD hfor' hbc hrank
        hprk hrankx hltI hposxI
      rw [hmarked2] at hmarked
      simp at hmarked
    · have hbeq : ((sideCtx P run pos k).edges[e]!.tail == x) = true := by
        simpa using htailx
      have hhw : (sideCtx P run pos k).edges[e]!.head = w := by
        unfold CoordsImpl.otherEnd at hw
        rw [hbeq] at hw
        simpa using hw
      have heD : ((sideCtx P run pos k).edges[e]!.tail = w ∧
          (sideCtx P run pos k).edges[e]!.head = x ∨
        (sideCtx P run pos k).edges[e]!.tail = x ∧
          (sideCtx P run pos k).edges[e]!.head = w) :=
        Or.inr ⟨htailx, hhw⟩
      have hmarked2 := hmark e f w x pred v hesz hfsz heD hfor' hbc hrank
        hprk hrankx hltI hposxI
      rw [hmarked2] at hmarked
      simp at hmarked

/-- X alignment-fold bound with the marking discharged. -/
private theorem XBC_foreignSideFoldBound' {P : Params} {run : Run} {side : Int} {decl : Nat}
    {pos : Array Nat} {k : Nat}
    (_hside : side = -1 ∨ side = 1) (hk : k < 4)
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hshape : ForeignSideChainShape P run side decl pos k)
    (hcross : ForeignBorderEdgesNoncrossing P run pos k) :
    ForeignSideFoldBound P run side decl pos k :=
  XBC_foreignSideFoldBound _hside hk hpos hshape
    (XBC_foreignSideMarkingCrossed hpos hk hcross)

/-- X border-border non-crossing for an executed exact run. The only open
content is the exact twin `X_ForeignBorderDivergeStable`; every other step
reads only ranks, layers, positions, and cluster paths. -/
private theorem XBC_borderEdgesNoncrossing_executed {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hstabLocal : X_ForeignBorderDivergeStableRun run) :
    ForeignBorderEdgesNoncrossing P run pos k := by
  intro e f w x a b he hf he_or hf_or hbe hbf hr1 hr2 hr3 hp1 hp2
  obtain ⟨hL, hE⟩ :=
    Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos
  have hLay : CoordsImpl.Lay (sideCtx P run pos k) := hL
  have hEdge : CoordsImpl.EdgeOK (sideCtx P run pos k) := hE
  have hperm := CoordsImpl.passLayers_perm run.layers k
  have hctxL : (sideCtx P run pos k).layers = CoordsImpl.passLayers run.layers k := rfl
  have torun : ∀ v : Nat, v ∈ (sideCtx P run pos k).layers.flatten →
      v ∈ run.layers.flatten := by
    intro v hv
    rw [hctxL] at hv
    exact hperm.mem_iff.mp hv
  obtain ⟨hte_fl, hhe_fl, -⟩ := hEdge e he
  obtain ⟨htf_fl, hhf_fl, -⟩ := hEdge f hf
  have hew : (sideCtx P run pos k).edges[e]!.tail = w ∨
      (sideCtx P run pos k).edges[e]!.head = w := by
    rcases he_or with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hex : (sideCtx P run pos k).edges[e]!.tail = x ∨
      (sideCtx P run pos k).edges[e]!.head = x := by
    rcases he_or with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hea : (sideCtx P run pos k).edges[f]!.tail = a ∨
      (sideCtx P run pos k).edges[f]!.head = a := by
    rcases hf_or with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have heb : (sideCtx P run pos k).edges[f]!.tail = b ∨
      (sideCtx P run pos k).edges[f]!.head = b := by
    rcases hf_or with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmw : w ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hew with h | h
    · rw [← h]; exact hte_fl
    · rw [← h]; exact hhe_fl
  have hmx : x ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hex with h | h
    · rw [← h]; exact hte_fl
    · rw [← h]; exact hhe_fl
  have hma : a ∈ (sideCtx P run pos k).layers.flatten := by
    rcases hea with h | h
    · rw [← h]; exact htf_fl
    · rw [← h]; exact hhf_fl
  have hmb : b ∈ (sideCtx P run pos k).layers.flatten := by
    rcases heb with h | h
    · rw [← h]; exact htf_fl
    · rw [← h]; exact hhf_fl
  obtain ⟨hrank_w, lw, iw, jw, hiw, hjw, hposw, _hvalw, hrkw⟩ :=
    nodeTransport hpos hLay (torun w hmw)
  obtain ⟨hrank_a, la, ia, ja, hia, hja, hposa, _hvala, hrka⟩ :=
    nodeTransport hpos hLay (torun a hma)
  obtain ⟨hrank_x, lx, ix, jx, hix, hjx, hposx, _hvalx, hrkx⟩ :=
    nodeTransport hpos hLay (torun x hmx)
  obtain ⟨hrank_b, lb, ib, jb, hib, hjb, hposb, _hvalb, hrkb⟩ :=
    nodeTransport hpos hLay (torun b hmb)
  have hr1I : ((sideCtx P run pos k).rank[w]! : Int) + 1 =
      ((sideCtx P run pos k).rank[x]! : Int) := by exact_mod_cast hr1
  have hr2I : ((sideCtx P run pos k).rank[a]! : Int) + 1 =
      ((sideCtx P run pos k).rank[b]! : Int) := by exact_mod_cast hr2
  have hr3I : ((sideCtx P run pos k).rank[x]! : Int) =
      ((sideCtx P run pos k).rank[b]! : Int) := by exact_mod_cast hr3
  have hiw_eq : iw = ia := by
    have hlow : ((sideCtx P run pos k).rank[w]! : Int) =
        ((sideCtx P run pos k).rank[a]! : Int) := by omega
    rw [hrank_w, hrank_a] at hlow
    by_cases hk2 : 2 ≤ k
    · rw [ite_eq_left hk2, ite_eq_left hk2] at hlow
      omega
    · rw [ite_eq_right hk2, ite_eq_right hk2] at hlow
      omega
  have hix_eq : ix = ib := by
    have hhigh : ((sideCtx P run pos k).rank[x]! : Int) =
        ((sideCtx P run pos k).rank[b]! : Int) := by omega
    rw [hrank_x, hrank_b] at hhigh
    by_cases hk2 : 2 ≤ k
    · rw [ite_eq_left hk2, ite_eq_left hk2] at hhigh
      omega
    · rw [ite_eq_right hk2, ite_eq_right hk2] at hhigh
      omega
  subst hiw_eq
  subst hix_eq
  have hlla : lw = la := Option.some.inj (hiw.symm.trans hia)
  have hllb : lx = lb := Option.some.inj (hix.symm.trans hib)
  subst hlla
  subst hllb
  have hbw : jw < lw.length := (List.getElem?_eq_some_iff.mp hjw).1
  have hba : ja < lw.length := (List.getElem?_eq_some_iff.mp hja).1
  have hbx : jx < lx.length := (List.getElem?_eq_some_iff.mp hjx).1
  have hbb : jb < lx.length := (List.getElem?_eq_some_iff.mp hjb).1
  have tLo : (k % 2 = 1 → jw < ja) ∧ (k % 2 ≠ 1 → ja < jw) := by
    constructor
    · intro hkodd
      rw [ite_eq_left hkodd] at hposw hposa
      omega
    · intro hne
      rw [ite_eq_right hne] at hposw hposa
      omega
  have tHi : (k % 2 = 1 → jb < jx) ∧ (k % 2 ≠ 1 → jx < jb) := by
    constructor
    · intro hkodd
      rw [ite_eq_left hkodd] at hposx hposb
      omega
    · intro hne
      rw [ite_eq_right hne] at hposx hposb
      omega
  have hERec : ∃ se Ce nw nx, (sideBase run).nodes[w]? = some nw ∧
      (sideBase run).nodes[x]? = some nx ∧ (se = -1 ∨ se = 1) ∧
      nw.node.border = se ∧ nx.node.border = se ∧
      nw.node.clusterPath = Ce ∧ nx.node.clusterPath = Ce := by
    cases htE : (sideBase run).nodes[(sideCtx P run pos k).edges[e]!.tail]? with
    | none =>
      have hfalse : CoordsImpl.borderChain (sideBase run)
          (sideCtx P run pos k).edges[e]! = false := by
        unfold CoordsImpl.borderChain
        rw [htE]
      rw [hfalse] at hbe
      simp at hbe
    | some nt =>
      cases hhE : (sideBase run).nodes[(sideCtx P run pos k).edges[e]!.head]? with
      | none =>
        have hfalse : CoordsImpl.borderChain (sideBase run)
            (sideCtx P run pos k).edges[e]! = false := by
          unfold CoordsImpl.borderChain
          rw [htE, hhE]
        rw [hfalse] at hbe
        simp at hbe
      | some nh =>
        obtain ⟨s, C, hs, hst, hsh, hpt, hph⟩ := borderChain_side_endpoints htE hhE hbe
        rcases he_or with ⟨hte, hhe⟩ | ⟨hte, hhe⟩
        · rw [hte] at htE
          rw [hhe] at hhE
          exact ⟨s, C, nt, nh, htE, hhE, hs, hst, hsh, hpt, hph⟩
        · rw [hhe] at hhE
          rw [hte] at htE
          exact ⟨s, C, nh, nt, hhE, htE, hs, hsh, hst, hph, hpt⟩
  obtain ⟨se, Ce, nw, nx, hnw, hnx, hse_or, hsew, hsex, hpew, hpex⟩ := hERec
  have hFRec : ∃ sf Cf na nb, (sideBase run).nodes[a]? = some na ∧
      (sideBase run).nodes[b]? = some nb ∧ (sf = -1 ∨ sf = 1) ∧
      na.node.border = sf ∧ nb.node.border = sf ∧
      na.node.clusterPath = Cf ∧ nb.node.clusterPath = Cf := by
    cases htF : (sideBase run).nodes[(sideCtx P run pos k).edges[f]!.tail]? with
    | none =>
      have hfalse : CoordsImpl.borderChain (sideBase run)
          (sideCtx P run pos k).edges[f]! = false := by
        unfold CoordsImpl.borderChain
        rw [htF]
      rw [hfalse] at hbf
      simp at hbf
    | some nt =>
      cases hhF : (sideBase run).nodes[(sideCtx P run pos k).edges[f]!.head]? with
      | none =>
        have hfalse : CoordsImpl.borderChain (sideBase run)
            (sideCtx P run pos k).edges[f]! = false := by
          unfold CoordsImpl.borderChain
          rw [htF, hhF]
        rw [hfalse] at hbf
        simp at hbf
      | some nh =>
        obtain ⟨s, C, hs, hst, hsh, hpt, hph⟩ := borderChain_side_endpoints htF hhF hbf
        rcases hf_or with ⟨hta, hha⟩ | ⟨hta, hha⟩
        · rw [hta] at htF
          rw [hha] at hhF
          exact ⟨s, C, nt, nh, htF, hhF, hs, hst, hsh, hpt, hph⟩
        · rw [hha] at hhF
          rw [hta] at htF
          exact ⟨s, C, nh, nt, hhF, htF, hs, hsh, hst, hph, hpt⟩
  have hnw' : run.coordinateProper.nodes[w]? = some nw := hnw
  have hnx' : run.coordinateProper.nodes[x]? = some nx := hnx
  obtain ⟨sf, Cf, na, nb, hna, hnb, hsf_or, hsfa, hsfb, hpfa, hpfb⟩ := hFRec
  have hna' : run.coordinateProper.nodes[a]? = some na := hna
  have hnb' : run.coordinateProper.nodes[b]? = some nb := hnb
  have hwf := XBC_bordersWellFormed hgraph0 hgraphX hcomp hrunX
  have hdnw : nw.dummy = false :=
    dummy_false_of_border hwf hnw' (by rw [hsew]; exact hse_or)
  have hdnx : nx.dummy = false :=
    dummy_false_of_border hwf hnx' (by rw [hsex]; exact hse_or)
  have hdna : na.dummy = false :=
    dummy_false_of_border hwf hna' (by rw [hsfa]; exact hsf_or)
  have hdnb : nb.dummy = false :=
    dummy_false_of_border hwf hnb' (by rw [hsfb]; exact hsf_or)
  obtain ⟨_, _, _, _, _, _, _, ⟨ord, horder, hlayers⟩, _, _, _, _, _, _⟩ :=
    componentRunX_spec hrunX
  have horder' : OrderImpl.order run.coordinateProper orderOptions = .ok run.layers := by
    unfold OrderImpl.order
    rw [horder]
    dsimp only
    rw [hlayers]
  have hwa : w ≠ a := by
    intro h
    rw [h] at hp1
    omega
  have hxb : x ≠ b := by
    intro h
    rw [h] at hp2
    omega
  have hmem_lo : lw ∈ run.layers := List.mem_of_getElem? hiw
  have hmem_hi : lx ∈ run.layers := List.mem_of_getElem? hix
  rcases list_prefix_trichotomy Ce Cf with hpre | hpre | hdiv
  · have hpre' : nw.node.clusterPath <+: na.node.clusterPath := by
      rw [hpew, hpfa]; exact hpre
    have hpreU' : nx.node.clusterPath <+: nb.node.clusterPath := by
      rw [hpex, hpfb]; exact hpre
    have oeLo := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hwf lw hmem_lo jw ja w a nw na hjw hja hnw' hna' hwa hdnw hdna hpre'
    have oeHi := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hwf lx hmem_hi jx jb x b nx nb hjx hjb hnx' hnb' hxb hdnx hdnb hpreU'
    rcases hse_or with hse | hse
    · by_cases hkodd : k % 2 = 1
      · have gHi : jx < jb := oeHi.1 (by rw [hsex, hse])
        have u := tHi.1 hkodd
        omega
      · have gLo : jw < ja := oeLo.1 (by rw [hsew, hse])
        have l := tLo.2 hkodd
        omega
    · by_cases hkodd : k % 2 = 1
      · have gLo : ja < jw := oeLo.2 (by rw [hsew, hse])
        have l := tLo.1 hkodd
        omega
      · have gHi : jb < jx := oeHi.2 (by rw [hsex, hse])
        have u := tHi.2 hkodd
        omega
  · have haw : a ≠ w := Ne.symm hwa
    have hbx' : b ≠ x := Ne.symm hxb
    have hpre' : na.node.clusterPath <+: nw.node.clusterPath := by
      rw [hpfa, hpew]; exact hpre
    have hpreU' : nb.node.clusterPath <+: nx.node.clusterPath := by
      rw [hpfb, hpex]; exact hpre
    have oeLo := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hwf lw hmem_lo ja jw a w na nw hja hjw hna' hnw' haw hdna hdnw hpre'
    have oeHi := OrderImpl.order_border_ends run.coordinateProper orderOptions
      run.layers horder' hwf lx hmem_hi jb jx b x nb nx hjb hjx hnb' hnx' hbx' hdnb hdnx hpreU'
    rcases hsf_or with hsf | hsf
    · by_cases hkodd : k % 2 = 1
      · have gLo : ja < jw := oeLo.1 (by rw [hsfa, hsf])
        have l := tLo.1 hkodd
        omega
      · have gHi : jb < jx := oeHi.1 (by rw [hsfb, hsf])
        have u := tHi.2 hkodd
        omega
    · by_cases hkodd : k % 2 = 1
      · have gHi : jx < jb := oeHi.2 (by rw [hsfb, hsf])
        have u := tHi.1 hkodd
        omega
      · have gLo : jw < ja := oeLo.2 (by rw [hsfa, hsf])
        have l := tHi.2 hkodd
        omega
  · have hdiv' : Divergent nw.node.clusterPath na.node.clusterPath := by
      rw [hpew, hpfa]; exact hdiv
    have hiff := hstabLocal hmem_lo hmem_hi
      hnw' hna' (by rw [hsew]; exact hse_or) (by rw [hsfa]; exact hsf_or)
      hnx' hnb' (by rw [hsex]; exact hse_or) (by rw [hsfb]; exact hsf_or)
      (hpew.trans hpex.symm) (hpfa.trans hpfb.symm) hdiv' hjw hja hjx hjb
    by_cases hkodd : k % 2 = 1
    · have l := tLo.1 hkodd
      have u := tHi.1 hkodd
      omega
    · have l := tLo.2 hkodd
      have u := tHi.2 hkodd
      omega

/-- Per-run core of `XBC_sideUps_closed`: the side-ups suffix from the
per-run diverge stability and the per-run side-chain shape. -/
private theorem XBC_sideUps_run {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (hstabLocal : X_ForeignBorderDivergeStableRun run)
    (hshapeLocal : X_ForeignSideChainShapeRun P run) :
    ∀ {decl : Nat} {side : Int}, side = -1 ∨ side = 1 →
    ∀ {k : Nat}, k < 4 →
    ∀ {pos : Array Nat},
    CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos →
    ∃ chain ordered : List Nat,
      (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl) ∧
      ∀ (hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
      Elegant.Layered.BorderChainUps P.nodeGap P.clusterPad (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
        k chain ordered hL := by
  intro decl side hside k hk pos hpos
  have hpos' : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos := hpos
  have hsh : ForeignSideChainShape P run side decl pos k := hshapeLocal hside hpos'
  have hcross : ForeignBorderEdgesNoncrossing P run pos k :=
    XBC_borderEdgesNoncrossing_executed hgraph0 hgraphX hcomp hrunX hpos' hstabLocal
  have hfo : ForeignSideFoldBound P run side decl pos k :=
    XBC_foreignSideFoldBound' hside hk hpos' hsh hcross
  refine ⟨sideChainNodes P run side decl, sideOrdered P run pos k side decl,
    ?_, ?_⟩
  · intro a
    exact mem_sideChainNodes hpos
  · intro hL
    have hocc : OccurringBorderChain (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨sideChainNodes_nodup (P := P) (run := run) (side := side) (decl := decl) hpos',
        fun v hv => sideChainNodes_flat_ctx hv, hsh.rank_inj, hsh.rank_consec⟩
    have hF : ExecutedChainFacts (sideBase run) (sideCtx P run pos k)
        (sideChainNodes P run side decl) :=
      ⟨fun v hv => sideChain_border_val hside hpos' hv, hsh.path_consec,
        hsh.incident_border, hsh.consec_edge, hfo⟩
    have hedges : (sideCtx P run pos k).edges.size = (sideBase run).edges.length ∧
        ∀ i, i < (sideBase run).edges.length →
          (sideCtx P run pos k).edges[i]! = (sideBase run).edges[i]! :=
      executedClusterCtx_edges
    have hmarked : (sideCtx P run pos k).marked =
        CoordsImpl.typeOneConflicts (sideBase run) pos := rfl
    have hE : CoordsImpl.EdgeOK (sideCtx P run pos k) :=
      (Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad) hpos').2
    have hpickFacts : BorderChainPickFacts (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPickFacts_of_executedChainFacts hF hedges hmarked hE
    have hpick : BorderChainPick (sideCtx P run pos k)
        (sideChainNodes P run side decl) hocc :=
      borderChainPick_of_facts hpickFacts
    have hord := sideOrdered_ctx P run pos k side decl
    exact borderChainUps_of_pick hL hocc hord hpick

/-- X side chains form single alignment blocks, closed for executed exact runs:
replay of the plain closed proof with the exact twin stability and the
executed shape residual. -/
private theorem XBC_sideUps_closed {exactIds : List String}
    (hstabX : X_ForeignBorderDivergeStable exactIds)
    (hshapeX : X_ForeignSideChainShapeClosed exactIds) :
    X_ForeignBorderSideUps exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX comp hcomp candidate run labels
    orderOptions hrunX decl side hside k hk pos hpos
  exact XBC_sideUps_run hgraph0 hgraphX hcomp hrunX
    (hstabX hgraph0 hgraphX hcomp hrunX)
    (hshapeX hgraph0 hgraphX hcomp hrunX) hside hk hpos
/-- X side chains are single alignment blocks over the exact pipeline. -/
private theorem XBC_sideBlocked {exactIds : List String}
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (_hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (_hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (_hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (hupLocal : ∀ {decl : Nat} {side : Int}, side = -1 ∨ side = 1 →
      ∀ {k : Nat}, k < 4 →
      ∀ {pos : Array Nat},
      CoordsImpl.checkLayers
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos →
      ∃ chain ordered : List Nat,
        (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
          na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
          na.node.clusterPath.getLast? = some decl) ∧
        ∀ (hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
          (CoordsImpl.typeOneConflicts
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
        Elegant.Layered.BorderChainUps P.nodeGap P.clusterPad (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
          (CoordsImpl.typeOneConflicts
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
          k chain ordered hL)
    {decl : Nat} {side : Int} (hside : side = -1 ∨ side = 1)
    {k : Nat} (hk : k < 4) :
    ∀ {pos : Array Nat}
    (_hpos : CoordsImpl.checkLayers
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos)
    (_hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
      (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
      (CoordsImpl.typeOneConflicts
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
    ∃ chain : List Nat,
      (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
        na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
        na.node.clusterPath.getLast? = some decl) ∧
      (chain ≠ [] → Elegant.Layered.BorderChainBlock P.nodeGap P.clusterPad
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
        (CoordsImpl.typeOneConflicts
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k chain) := by
  intro pos hpos hL
  obtain ⟨chain, ordered, hiff, hupsK⟩ := hupLocal hside hk hpos
  have hflat : ∀ v ∈ chain, v ∈ run.layers.flatten := by
    intro v hv
    rw [hiff] at hv
    obtain ⟨na, hna, _, _, _⟩ := hv
    have hlt : v < run.coordinateProper.nodes.length :=
      (List.getElem?_eq_some_iff.mp hna).1
    obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _⟩, _, hproxy, hdrop, hroute, _, _⟩ :=
      componentRunX_spec hrunX
    have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
      rw [← hdrop]
      exact (proxyWidths_rel hproxy).2.2.1
    have hltP : v < run.proper.nodes.length := by rw [hlenEq]; exact hlt
    have hcov :=
      (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
    obtain ⟨l, hly, hmem, _⟩ := hcov v hltP
    exact List.mem_flatten.mpr ⟨l, List.mem_of_getElem? hly, hmem⟩
  refine ⟨chain, hiff, fun hne => ?_⟩
  exact Elegant.Layered.borderChainBlock_of_ups (ng := P.nodeGap) (cp := P.clusterPad)
    (p := run.coordinateProper) (layers := run.layers) (k := k)
    (chain := chain) (ordered := ordered) (pos := pos)
    hk hne hflat hpos hL (hupsK hL)

/-- Per-run core of `XBC_chainAligned_of_ups`: two same-side border markers
of one declaration share one closed `x`-interval from the per-run side-ups
fact. -/
private theorem XBC_chainAligned_run {P : Params} {exactIds : List String}
    {inp : Input} {o : Options} {lines : List (List Measure.Line)}
    {measured : List MeasuredLabel} {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (hupLocal : ∀ {decl : Nat} {side : Int}, side = -1 ∨ side = 1 →
      ∀ {k : Nat}, k < 4 →
      ∀ {pos : Array Nat},
      CoordsImpl.checkLayers
        (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers = .ok pos →
      ∃ chain ordered : List Nat,
        (∀ a, a ∈ chain ↔ ∃ na, run.coordinateProper.nodes[a]? = some na ∧
          na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
          na.node.clusterPath.getLast? = some decl) ∧
        ∀ (hL : CoordsImpl.Lay (CoordsImpl.clusterCtx P.nodeGap P.clusterPad
          (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
          (CoordsImpl.typeOneConflicts
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k)),
        Elegant.Layered.BorderChainUps P.nodeGap P.clusterPad (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
          (CoordsImpl.typeOneConflicts
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
          k chain ordered hL) :
    ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b := by
  intro a b na nb ha hb hsideA hsideB hborder howner
  obtain ⟨hproperA, hxsA⟩ := XBC_border_record hrunX ha hsideA
  obtain ⟨hproperB, hxsB⟩ := XBC_border_record hrunX hb hsideB
  obtain ⟨labeled, hcoordL, hready⟩ :=
    XBC_titled_border_ready hgraph0 hgraphX hcomp hrunX
  have hbwf : OrderImpl.BordersWellFormed run.coordinateProper :=
    XBC_bordersWellFormed hgraph0 hgraphX hcomp hrunX
  have hneA : na.node.clusterPath ≠ [] := hbwf.1 a na ha hsideA
  cases hlast : na.node.clusterPath.getLast? with
  | none =>
    exact absurd (List.getLast?_eq_none_iff.mp hlast) hneA
  | some decl =>
    have hlastB : nb.node.clusterPath.getLast? = some decl := by
      rw [← howner]; exact hlast
    have hcoordA : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
          P.clusterBorderW).nodes[a]? =
        some na :=
      XBC_side_original hready (by rw [hcoordL]; exact ha) hsideA
    have hwA : na.node.w = P.clusterBorderW :=
      XBC_addClusterBorders_side_width _ _ hready hcoordA hsideA
    have hcoordB : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPortsX P (exactDecls exactIds inp) labeled))
          P.clusterBorderW).nodes[b]? =
        some nb :=
      XBC_side_original hready (by rw [hcoordL]; exact hb) hsideB
    have hwB : nb.node.w = P.clusterBorderW :=
      XBC_addClusterBorders_side_width _ _ hready hcoordB hsideB
    obtain ⟨_, _, _, _, _, _, _, _, hcross, _, _, _, _, _⟩ :=
      componentRunX_spec hrunX
    obtain ⟨pos, hcl, hcase⟩ := Elegant.Layered.crossCoordsClusterWith_ok hcross
    rcases hcase with ⟨hempty, _⟩ | ⟨x0, x1, x2, x3, hp0, hp1, hp2, hp3, hbal⟩
    · have halt : a < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp ha).1
      omega
    · have halt : a < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp ha).1
      have hblt : b < run.coordinateProper.nodes.length :=
        (List.getElem?_eq_some_iff.mp hb).1
      have hpass : ∀ {k : Nat}, k < 4 → ∀ {x : Array Int},
          CoordsImpl.clusterPass P.nodeGap P.clusterPad
            (CoordsImpl.borderAlignment run.coordinateProper run.layers) run.layers
            (CoordsImpl.typeOneConflicts
              (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos) k =
            .ok x → x[a]! = x[b]! := by
        intro k hk x hx
        obtain ⟨chain, hiff, hblock⟩ :=
          XBC_sideBlocked (decl := decl) (side := na.node.border) hgraph0 hgraphX hcomp
            hrunX hupLocal hsideA hk hcl
            ((Elegant.Layered.clusterCtx_facts (ng := P.nodeGap) (cp := P.clusterPad)
              (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
              (layers := run.layers)
              (marked := CoordsImpl.typeOneConflicts
                (CoordsImpl.borderAlignment run.coordinateProper run.layers) pos)
              (k := k) hcl).1)
        have hmemA : a ∈ chain :=
          (hiff a).mpr ⟨na, ha, rfl, hwA, hlast⟩
        have hmemB : b ∈ chain :=
          (hiff b).mpr ⟨nb, hb, hborder.symm, hwB, hlastB⟩
        have hne : chain ≠ [] := List.ne_nil_of_mem hmemA
        obtain ⟨r, hrchain, hrr, hrrin, hmem⟩ := hblock hne
        obtain ⟨_, hnr, _, _, _⟩ := (hiff r).mp hrchain
        have hrlt : r < run.coordinateProper.nodes.length :=
          (List.getElem?_eq_some_iff.mp hnr).1
        have hplen : (CoordsImpl.borderAlignment run.coordinateProper run.layers).nodes.length =
            run.coordinateProper.nodes.length := rfl
        have ea := Elegant.Layered.cluster_pass_block_x_eq
          (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
          hcl hx hrr hrrin (hmem a hmemA)
          (by rw [hplen]; exact halt) (by rw [hplen]; exact hrlt)
        have eb := Elegant.Layered.cluster_pass_block_x_eq
          (p := CoordsImpl.borderAlignment run.coordinateProper run.layers)
          hcl hx hrr hrrin (hmem b hmemB)
          (by rw [hplen]; exact hblt) (by rw [hplen]; exact hrlt)
        rw [ea, eb]
      have e0 := hpass (k := 0) (by decide) (x := x0) hp0
      have e1 := hpass (k := 1) (by decide) (x := x1) hp1
      have e2 := hpass (k := 2) (by decide) (x := x2) hp2
      have e3 := hpass (k := 3) (by decide) (x := x3) hp3
      have hbal' : run.coordinateXs[a]! = run.coordinateXs[b]! :=
        Elegant.Layered.balance_block_x_eq hbal halt hblt e0 e1 e2 e3
      have hxs : run.coordinateXs.getD a 0 = run.coordinateXs.getD b 0 := by
        have ea' : run.coordinateXs[a]! = run.coordinateXs.getD a 0 := by
          rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rfl
        have eb' : run.coordinateXs[b]! = run.coordinateXs.getD b 0 := by
          rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          rfl
        rw [← ea', ← eb', hbal']
      have hnW : RouteImpl.nodeW run.proper a = RouteImpl.nodeW run.proper b := by
        simp only [RouteImpl.nodeW, hproperA, hproperB, hwA, hwB]
      have hleft : RouteImpl.leftOf run.proper run.xs a =
          RouteImpl.leftOf run.proper run.xs b := by
        unfold RouteImpl.leftOf RouteImpl.xAt
        rw [hxsA, hxsB, hxs, hnW]
      exact ⟨hleft, by rw [hleft, hnW]⟩
/-- X cross-coordinate placement: two same-side border markers of one
declaration share one closed `x`-interval over the exact pipeline. Proved
outright from the exact side-ups. -/
private theorem XBC_chainAligned_of_ups {exactIds : List String}
    (hupX : X_ForeignBorderSideUps exactIds) :
    X_ForeignBorderChainXAligned exactIds := by
  intro P inp o lines measured graph0 graph hgraph0 hgraphX _hlines _hwf _hframed
    comp hcomp candidate run labels orderOptions hrunX a b na nb ha hb hsideA hsideB
    hborder howner
  exact XBC_chainAligned_run hgraph0 hgraphX hcomp hrunX
    (hupX hgraph0 hgraphX hcomp hrunX) ha hb hsideA hsideB hborder howner

/-- Per-run exact alignment: with only the per-run diverge stability and the
per-run side-chain shape, two same-side markers of one declaration share one
closed `x`-interval. Used where the executed run discharges the layer
conditions locally instead of the global `X_ForeignBorderDivergeStable`. -/
theorem X_foreignBorderChainXAligned_of_local_stable {P : Params}
    {exactIds : List String} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hgraph0 : measuredGraph P inp o lines = .ok graph0)
    (hgraphX : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrunX : componentRunX P (exactDecls exactIds inp)
      (componentCandidate graph comp candidate) labels orderOptions = .ok run)
    (hstabLocal : X_ForeignBorderDivergeStableRun run)
    (hshapeLocal : X_ForeignSideChainShapeRun P run) :
    ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b :=
  XBC_chainAligned_run hgraph0 hgraphX hcomp hrunX
    (XBC_sideUps_run hgraph0 hgraphX hcomp hrunX hstabLocal hshapeLocal)

/-- Derive scoped exact alignment from global exact divergence stability and
the executed side-chain shape. -/
theorem X_foreignBorderChainXAligned_of_stable (exactIds : List String)
    (hstabX : X_ForeignBorderDivergeStable exactIds)
    (hshapeX : X_ForeignSideChainShapeClosed exactIds) :
    X_ForeignBorderChainXAligned exactIds :=
  XBC_chainAligned_of_ups (XBC_sideUps_closed hstabX hshapeX)
end PipelineImpl

end Layered
end Elegant
