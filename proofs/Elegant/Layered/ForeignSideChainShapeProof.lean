import Elegant.Layered.ForeignBorderSideUpsProof
import Elegant.Layered.SideMarkerPathsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Proving the side-chain shape fields.

`ForeignSideChainShape` (`ForeignBorderSideUpsProof`) packages the five
structural inputs of `ExecutedChainFacts` for the executed side chain. This
module proves them field by field from the `OrderImpl.addClusterBorders`
construction, in the order `path_consec`, `rank_inj`, `rank_adj`,
`consec_edge`, `incident_border`. A field that does not close stays as its
own one-line named residual. `ForeignSideFoldBound` is out of scope (another
worker owns it).
-/

/-- Canonical cluster path of an executed side marker (copy of the private
`SideMarkerPathsProof.sideMarkerCanon` under a new name): the title path of
its declaration. Side markers are emitted by `OrderImpl.addClusterBorders`;
`addClusterBorders_side_source` carries each marker's path from its `-2`
title anchor, and title paths are determined by the declaration
(`measuredGraph_group_origin`). -/
private theorem sideChainCanon {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
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
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  have hready : OrderImpl.BorderConstructionReady
      (titleReservations (sizeProperPorts P labeled)) :=
    titled_border_ready hkeys hshape hmarkers haligned
  have hcoordinate : (coordinateGraph P labeled).nodes[a]? = some na := by
    rw [hcoord]; exact hna
  have horiginal := coordinateGraph_side_original hready hcoordinate hside
  obtain ⟨top, htop, _, _, hpath⟩ :=
    addClusterBorders_side_source _ _ hready (List.mem_of_getElem? horiginal)
      hside
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp htop
  have hget : (titleReservations (sizeProperPorts P labeled)).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp hmem
  have hbord : top.1.node.border = -2 := by simpa using hcond
  rcases titled_node_origin hkeys hget with
    ⟨orig, horig, _, hbb, hpp⟩ | ⟨_, hb3⟩
  · have horigB : orig.node.border = -2 := by rw [← hbb]; exact hbord
    rcases hkeys top.2 orig horig with
      ⟨bn, hbn, _, hbnb, hnp⟩ | ⟨_, hb0, _⟩
    · have hbnB : bn.border = -2 := by rw [← hbnb]; exact horigB
      obtain ⟨_, _, hsrcG⟩ := componentCandidate_nonplain_source hbn (by omega)
      obtain ⟨_, boxG, hboxG, _, hpathG⟩ :=
        measuredGraph_group_origin hgraph hsrcG hbnB
      have hlastG : bn.clusterPath.getLast? = some bn.decl := by
        rw [hpathG, List.getLast?_append]; simp
      have hnaLast : na.node.clusterPath.getLast? = some bn.decl := by
        rw [hpath, hpp, hnp]; exact hlastG
      have hdeclEq : bn.decl = decl :=
        Option.some.inj (hnaLast.symm.trans hlast)
      rw [hdeclEq] at hboxG
      refine ⟨boxG, hboxG, ?_⟩
      rw [hpath, hpp, hnp, hpathG, hdeclEq]
    · rw [hb0] at horigB; omega
  · rw [hb3] at hbord; omega

/-! ## Field 1: consecutive markers share the full cluster path -/

/-- Forward chain membership needs no layer cover: a member carries a
matching record. (The full iff `mem_sideChainNodes` additionally needs the
`checkLayers` cover for the backward direction.) -/
theorem mem_sideChainNodes_forward {P : Params} {run : Run} {side : Int} {decl : Nat}
    {a : Nat} (hmem : a ∈ sideChainNodes P run side decl) :
    ∃ na, run.coordinateProper.nodes[a]? = some na ∧
      na.node.border = side ∧ na.node.w = P.clusterBorderW ∧
      na.node.clusterPath.getLast? = some decl := by
  unfold sideChainNodes at hmem
  rw [List.mem_filter] at hmem
  obtain ⟨_, hpred⟩ := hmem
  cases hna : run.coordinateProper.nodes[a]? with
  | none => simp [hna] at hpred
  | some na =>
    simp only [hna, Bool.and_eq_true, beq_iff_eq] at hpred
    obtain ⟨hb, hw, hlast⟩ := hpred
    exact ⟨na, rfl, hb, hw, hlast⟩

/-- `ForeignSideChainShape.path_consec`: consecutive side-chain markers share
the anchor's full cluster path. Each marker's path is the canonical title
path of the shared declaration (`sideChainCanon`), and the box at one
declaration index is unique. -/
theorem shape_path_consec {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
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
  obtain ⟨boxA, hboxA, hpathA⟩ := sideChainCanon hgraph hcomp hrun hna hsa hla
  obtain ⟨boxB, hboxB, hpathB⟩ := sideChainCanon hgraph hcomp hrun hnb hsb hlb
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

/-! ## Field order note and uniformity -/

/-- Full path uniformity: all side-chain markers of one declaration share
the anchor's full cluster path. Direct from `sideChainCanon`: the box at one
declaration index is unique. `shape_path_consec` is the consecutive case. -/
theorem shape_chain_uniform {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
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
  obtain ⟨boxA, hboxA, hpathA⟩ := sideChainCanon hgraph hcomp hrun hna hsa hla
  obtain ⟨boxB, hboxB, hpathB⟩ := sideChainCanon hgraph hcomp hrun hnb hsb hlb
  have hbox : boxA = boxB := Option.some.inj (hboxA.symm.trans hboxB)
  have hnodes : (sideBase run).nodes = run.coordinateProper.nodes := rfl
  have hgetA : (sideBase run).nodes.getD u default = na := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hna
  have hgetB : (sideBase run).nodes.getD w default = nb := by
    rw [hnodes]
    exact borderEnv_getD_of_get? hnb
  rw [hgetA, hgetB, hpathA, hpathB, hbox]

/-! ## Field 3 verdict: `rank_adj` restated as no-gap `rank_consec` -/

/-- The old all-pairs `rank_adj` field (`ForeignSideChainShape.rank_adj`,
inherited from `OccurringBorderChain.rank_adj`) requires any two distinct
chain nodes to sit on adjacent ranks. It fails on every executed chain of
length three or more with consecutive ranks: evaluation runs on the real
`componentRun` pipeline (five inputs: nested/crossing/sibling/diamond/LR)
shows 80 nonempty side chains, e.g. `chain = [9, 11, 13, 15, 17]` with
`preds` all true (each marker's `chainPred` is its predecessor, so ranks are
consecutive and distinct). The first and last markers are four ranks apart,
refuting the all-pairs claim. The corrected field is the no-gap form below
(`rank_consec` mirroring `OccurringBorderChain.rank_consec` and
`ForeignSideChainShape.rank_consec`): neighbours in rank order sit on adjacent
ranks. Status: TRUE on all probed chains (consecutive distinct ranks, no gaps)
but unproved. Blocker: same emission-offset inversion as `rank_inj` (a marker's
rank must determine its emission offset within its anchor's span via a fold
invariant over `borderInner` that has no lemma), plus contiguity of the anchor's
span (one marker per rank of the group's span, as `addClusterBorders` emits).
No proof of the false all-pairs statement is attempted (`ex falso` would poison
every consumer). -/
def ShapeRankConsecResidual (P : Params) (run : Run) (side : Int) (decl : Nat)
    (pos : Array Nat) (k : Nat) : Prop :=
  ∀ u ∈ sideChainNodes P run side decl,
    ∀ v ∈ sideChainNodes P run side decl,
    (sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[v]! →
    (∀ w ∈ sideChainNodes P run side decl,
      ¬ ((sideCtx P run pos k).rank[u]! < (sideCtx P run pos k).rank[w]! ∧
        (sideCtx P run pos k).rank[w]! < (sideCtx P run pos k).rank[v]!)) →
    (sideCtx P run pos k).rank[u]! + 1 = (sideCtx P run pos k).rank[v]!
/-! ## Field 2 verdict: `rank_inj` stays open -/

/-- One-line residual for `ForeignSideChainShape.rank_inj` (at most one
side marker per rank): same side, same declaration, same pass rank forces
the same node. Status: TRUE on all probed chains (consecutive distinct
ranks) but unproved. Two blockers, both in the border-construction phase.
Blocker 1 (anchor uniqueness): same-path markers must share one `-2` title
anchor; the only uniqueness lemma (`labeled_topUnique`) is for the labeled
graph, and no `NodeKeys`-through-`titleReservations` transport exists.
Blocker 2 (emission offset inversion): a marker's rank must determine its
emission offset within its anchor's span, which needs a fold invariant over
`borderInner` (`rank = lo + offset`, one left/right per offset) that has no
lemma. `shape_chain_uniform` above is the completed first half (same path). -/
def ShapeRankInjResidual (P : Params) (run : Run) (side : Int) (decl : Nat)
    (pos : Array Nat) (k : Nat) : Prop :=
  ∀ u ∈ sideChainNodes P run side decl,
    ∀ w ∈ sideChainNodes P run side decl,
    (sideCtx P run pos k).rank[u]! = (sideCtx P run pos k).rank[w]! → u = w

/-- Zip-with-tail membership: `(a, b)` is a consecutive pair of `l` iff they
sit at consecutive indices. -/
theorem mem_zip_tail_iff {α : Type} {l : List α} {a b : α} :
    (a, b) ∈ l.zip l.tail ↔ ∃ i, l[i]? = some a ∧ l[i + 1]? = some b := by
  induction l with
  | nil => simp
  | cons c rest ih =>
    cases rest with
    | nil => simp
    | cons d rest' =>
      simp only [List.tail, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | h)
        · exact ⟨0, by simp, by simp⟩
        · obtain ⟨i, hi⟩ := ih.mp h
          exact ⟨i + 1, by simpa using hi.1, by simpa using hi.2⟩
      · rintro ⟨i, h1, h2⟩
        cases i with
        | zero =>
          simp at h1 h2
          left
          exact ⟨h1.symm, h2.symm⟩
        | succ i =>
          right
          exact ih.mpr ⟨i, by simpa using h1, by simpa using h2⟩

/-- `ForeignSideChainShape.consec_edge`: rank-adjacent side markers are
joined by a context edge. Both markers share the anchor path (uniformity);
their pass ranks transport to consecutive original layers (`rank_orient`
plus `Lay.loc`), where `border_alignment_chain_edge` supplies the pair edge. -/
theorem shape_consec_edge {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
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
  have huni := shape_chain_uniform hgraph hcomp hrun hside v hv w hw
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


/-- The executed border-aligned edge list splits into the coordinate edges
and the alignment pairs. -/
theorem sideBase_edges_append (run : Run) :
    (sideBase run).edges = run.coordinateProper.edges ++
      ((run.layers.zip run.layers.tail).flatMap fun ls =>
        ls.1.flatMap fun a => ls.2.filterMap fun b =>
          let na := (run.coordinateProper.nodes.getD a default).node
          let nb := (run.coordinateProper.nodes.getD b default).node
          if (na.border == -1 || na.border == 1) && na.border == nb.border &&
              na.clusterPath == nb.clusterPath then
            some ({ tail := a, head := b, decl := na.decl, original := 0 } : ProperEdge)
          else none) := rfl

/-- Border-construction readiness for the executed titled source, packaged
with the labeled graph it comes from. -/
theorem shape_ready {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ∃ labeled : Proper, coordinateGraph P labeled = run.coordinateProper ∧
      OrderImpl.BorderConstructionReady
        (titleReservations (sizeProperPorts P labeled)) := by
  obtain ⟨_, _, labeled, _, hn, hl, hcoord, _⟩ := componentRun_ranked_source hrun
  have hkeys : NodeKeys (componentCandidate graph comp candidate) labeled :=
    addLabelNodes_keys _ _ _ (normalize_keys hn) hl
  have haligned : labeled.nodes.length = labeled.rank.length := by
    rw [← addLabelNodes_node_length hl, (Labels.addLabelNodes_metadata hl).2.1]
    exact (normalize_node_rank_alignment hn).1
  have hshape : CgShape (componentCandidate graph comp candidate) :=
    componentCandidate_shape (components_nodup graph comp hcomp)
      (measuredGraph_shape hgraph) candidate
  have hmarkers : ∀ (index : Nat) (node : Node),
      (componentCandidate graph comp candidate).nodes[index]? = some node →
      (node.border = 0 ∨ node.border = -2 ∨ node.border = 2) ∧
        (node.border = -2 → node.clusterPath ≠ []) :=
    fun index node hnode => componentCandidate_marker_shape hgraph hnode
  exact ⟨labeled, hcoord,
    titled_border_ready hkeys hshape hmarkers haligned⟩

/-- Every side marker emitted by `addClusterBorders` carries the border
width (copy of the private `ForeignBorderAlignRankProof`
`addClusterBorders_side_width` under a new name). -/
theorem shape_side_width (source : Proper) (width : Int)
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

/-- Alignment-pair edges stay inside the side chain: a border-alignment pair
joins same-side markers of one cluster path (its filter condition), and the
far end inherits chain membership. The inherited (non-pair) edges are out of
scope here. -/
theorem shape_incident_pair {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
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
  obtain ⟨labeled, hcoordL, hready⟩ := shape_ready hgraph hcomp hrun
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
  -- The edge record and its endpoints.
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
  -- Case split on which endpoint is the chain node.
  rcases hmem with hvaA | hvaB
  · -- v = a: far end is b.
    have hva' : run.coordinateProper.nodes[a]? = some nva := by
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
    have hcoordB : (coordinateGraph P labeled).nodes[b]? = some nb := by
      rw [hcoordL]
      exact hnb
    have haddedB : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).nodes[b]? = some nb :=
      coordinateGraph_side_original hready hcoordB hbordB
    have hsideW : nb.node.w = P.clusterBorderW :=
      shape_side_width _ _ hready haddedB hbordB
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
  · -- v = b: far end is a.
    have hva' : run.coordinateProper.nodes[b]? = some nva := by
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
    have hcoordA : (coordinateGraph P labeled).nodes[a]? = some na := by
      rw [hcoordL]
      exact hna
    have haddedA : (OrderImpl.addClusterBorders
        (titleReservations (sizeProperPorts P labeled))
        P.clusterBorderW).nodes[a]? = some na :=
      coordinateGraph_side_original hready hcoordA hbordA
    have hsideW : na.node.w = P.clusterBorderW :=
      shape_side_width _ _ hready haddedA hbordA
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

/-! ## Field 5 verdict: alignment pairs proved; inherited edges stay open -/

/-- One-line residual for the inherited half of
`ForeignSideChainShape.incident_border`: coordinate-graph edges (titled
edges and `borderLinks` synthetics) touching a side marker are border-chain
edges whose far end is another chain node. The alignment-pair half is proved
above (`shape_incident_pair`); the context-edge index transports through
`List.getElem!_toArray`. Two blockers, both in the border-construction
phase. Blocker 1 (titled-edge exclusion): a titled edge touching an appended
marker must be ruled out by endpoint bounds, and no endpoint-bound lemma
for titled edges exists. Blocker 2 (`borderLinks` fold-step inversion):
identifying which fold step emitted an edge, and that its endpoints share
that step's anchor template, needs a fold invariant over `borderStep` that
has no lemma. -/
def ShapeIncidentInheritedResidual (P : Params) (run : Run) (side : Int) (decl : Nat) : Prop :=
  ∀ v ∈ sideChainNodes P run side decl, ∀ e : Nat,
    e < run.coordinateProper.edges.length →
    (run.coordinateProper.edges[e]!.tail = v ∨
      run.coordinateProper.edges[e]!.head = v) →
    CoordsImpl.borderChain (sideBase run) (run.coordinateProper.edges[e]!) = true ∧
    ∃ u ∈ sideChainNodes P run side decl,
      CoordsImpl.otherEnd (run.coordinateProper.edges[e]!) v = u ∧ u ≠ v

/-! ## Assembly: the side-chain shape from proved fields and residuals -/

/-- Assembly: the executed side chain satisfies `ForeignSideChainShape` from
the proved consecutive-path/edge lemmas and the three one-line residuals.
`rank_inj` is the injection residual, `rank_consec` the no-gap residual;
`path_consec` and `consec_edge` are proved above (`shape_path_consec`,
`shape_consec_edge`); `incident_border` splits into the inherited half
(`hinh`, transported through `toArray`/`append`) and the pair half
(`shape_incident_pair` after `flatMap`/`filterMap` extraction). -/
theorem foreignSideChainShape {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run)
    {side : Int} {decl : Nat} (hside : side = -1 ∨ side = 1)
    {pos : Array Nat} {k : Nat}
    (hpos : CoordsImpl.checkLayers (sideBase run) run.layers = .ok pos)
    (hinj : ShapeRankInjResidual P run side decl pos k)
    (hinh : ShapeIncidentInheritedResidual P run side decl)
    (hconsec : ShapeRankConsecResidual P run side decl pos k) :
    ForeignSideChainShape P run side decl pos k := by
  refine ⟨hinj, hconsec, ?_, ?_, ?_⟩
  · intro i hi
    exact shape_path_consec hgraph hcomp hrun hside i hi
  · intro v hv e he htouch
    have harr : (sideCtx P run pos k).edges = (sideBase run).edges.toArray := rfl
    have hsize : (sideCtx P run pos k).edges.size = (sideBase run).edges.length := by
      rw [harr, List.size_toArray]
    by_cases hlt : e < run.coordinateProper.edges.length
    · -- Inherited half: transport through `toArray`/`append` to `hinh`.
      have he_base : e < (sideBase run).edges.length := hsize ▸ he
      have h_eq_opt : (sideBase run).edges[e]? =
          run.coordinateProper.edges[e]? := by
        rw [sideBase_edges_append, List.getElem?_append_left hlt]
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
    · -- Pair half: `e` lies beyond the inherited edges; extract `a, b` from
      -- `flatMap`/`filterMap` and apply `shape_incident_pair`.
      have hle : run.coordinateProper.edges.length ≤ e := by omega
      have he_base : e < (sideBase run).edges.length := hsize ▸ he
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
      -- `ed` is the pair edge at `e`; it is also `sideCtx[e]!`.
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
      -- The `filterMap` condition holds; otherwise `hfb` would be `none`.
      -- Stated with prefix `Eq` so no infix `=` appears in the type.
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
      -- `sideCtx[e]! = ed` through `toArray` and `getD`.
      have h_eq_ctx_base : (sideCtx P run pos k).edges[e]! =
          (sideBase run).edges[e]! := by
        rw [harr, List.getElem!_toArray]
      have h_eq_base_ed : (sideBase run).edges[e]! = ed := by
        rw [List.getElem!_eq_getElem?_getD, h_side_orig, Option.getD_some]
        exact hed_def
      have h_eq_ctx_ed : (sideCtx P run pos k).edges[e]! = ed := by
        rw [h_eq_ctx_base, h_eq_base_ed]
      -- Endpoints give `hmem`; nodes exist via `layersInRange`.
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
      have hparts := CoordsImpl.checkLayers_parts hpos
      obtain ⟨hrange, hlp, _⟩ := hparts
      obtain ⟨pos', hlp'⟩ := hlp
      have hspec := CoordsImpl.layerPositions_spec hlp'
      obtain ⟨_, hrk_spec, _⟩ := hspec
      -- `ls` gives consecutive layers via `mem_zip_tail_iff` (in this file).
      obtain ⟨idx, hi_l1, hi_l2⟩ := mem_zip_tail_iff.mp hls_mem
      -- Nodes exist: layers are in range (`layers_mem_lt`).
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
      -- Distinct endpoints via `layerPositions` ranks.
      have hab : a ≠ b := by
        intro hcon
        have hrk_a : rk (sideBase run).rank a = (idx : Int) :=
          hrk_spec idx ls.1 a hi_l1 ha_mem
        have ha_in_l2 : a ∈ ls.2 := hcon ▸ hb_mem
        have hrk_a2 : rk (sideBase run).rank a = ((idx + 1 : Nat) : Int) :=
          hrk_spec (idx + 1) ls.2 a hi_l2 ha_in_l2
        omega
      -- `shape_incident_pair` gives the pair-edge conclusion for `{a,b}`.
      obtain ⟨hbc_pair, u, hu, hu_other_pair, hne⟩ :=
        shape_incident_pair hgraph hcomp hrun hside hpos hna hnb hab hC hv hmem
      -- Transport `{a,b}` edge to `sideCtx[e]!` via `ed`.
      have hgetD_a : run.coordinateProper.nodes.getD a default = na :=
        borderEnv_getD_of_get? hna
      have hed_eq' : ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = ed := by
        rw [← hed_eq, ← hgetD_a]
      have h_eq_pair_ctx : ({ tail := a, head := b, decl := na.node.decl, original := 0 } : ProperEdge) = (sideCtx P run pos k).edges[e]! := by
        rw [hed_eq', h_eq_ctx_ed]
      have hbc_ctx : CoordsImpl.borderChain (sideBase run)
          (sideCtx P run pos k).edges[e]! = true := by
        rw [← h_eq_pair_ctx]
        exact hbc_pair
      have hu_other_ctx : CoordsImpl.otherEnd (sideCtx P run pos k).edges[e]! v = u := by
        rw [← h_eq_pair_ctx]
        exact hu_other_pair
      exact ⟨hbc_ctx, u, hu, hu_other_ctx, hne⟩
  · intro v hv w hw hrk
    exact shape_consec_edge hgraph hcomp hrun hside hpos v hv w hw hrk
end Elegant.Layered.PipelineImpl
