import Elegant.Layered.RouteNonforwardLabelClearProof
import Elegant.Layered.FlatC6Loops
import Elegant.Layered.LabelsC7RunLocal
import Elegant.Layered.StrictMemberFrameProof
import Elegant.Layered.ChildFrameStrictRankProof
import Elegant.Layered.MemberInFrame
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts
import Elegant.Layered.CompoundPathFacts
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.SizingFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.GroupFrameSizingFacts
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.LoopRectRealQProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Loop footprint vs group hulls

Proves `LoopFootprintGroupHullClear` for an executed component run: the loop
footprint of a self-loop owner is disjoint from, or strictly contains, every
in-bounds group frame.

Case split (all probe-tested on seven executed layouts, 0 violations):
* `pos = t` (loop on the group itself): the footprint starts exactly at the
  hull's right edge, disjoint by `x` (`loopFootprint_self_pos` below).
* `pos` strictly above `t`: the hull strictly contains the footprint. The
  left/top/bottom strictness is the proved member/group strictness; the right
  strictness is the open hull-right x-extent bound (`LoopHullRightCover`).
* `pos` strictly inside `t`: the nested hull is contained in `t`'s hull, so it
  sits left of the footprint's left edge (disjoint by `x`).
* `pos` foreign to `t`: the frame and the hull are disjoint by the foreign
  span seams (derived inside from the accepted `ForeignBorderChainXAligned`
  seam); `y`-separation and left `x`
  separation transport to the footprint for free, while right `x` separation
  needs the neighbor-extent bound (`LoopHullRightNeighborCover`).
-/

/-- Residual (coordinate width reservation): the executed ancestor-group hull
right edge strictly covers the loop footprint's right edge. One inequality of
the ancestor `StrictInside` (the open hull-right x-extent bound named in
`RouteRunClearCases`); no disjunction, no foreign case. Probe:
`LoopHullProbe3`, `R1cover = true` on every ancestor pair (seven inputs ×
five candidates). -/
def LoopHullRightCover (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → np.decl ∈ nt.clusterPath →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w <
        (frameRect P cg run pos).x + (frameRect P cg run pos).w

/-- Residual (right-neighbor extent): when the loop owner's frame lies left of
a foreign group hull with overlapping `y`, the footprint's right edge stays
left of that hull. One implication; the `y`-disjoint and left cases need no
bound. Probe: `LoopHullProbe3`, `R3c = true` wherever `FrightLE ∧ yOvl`. -/
def LoopHullRightNeighborCover (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (t : Nat) (nt : Node), cg.nodes[t]? = some nt →
    (∃ e ∈ cg.edges, e.tail = t ∧ e.head = t) →
    ∀ (pos : Nat) (np : Node), cg.nodes[pos]? = some np → np.border = -2 →
      pos ≠ t → nt.decl ≠ np.decl →
      np.decl ∉ nt.clusterPath → nt.decl ∉ np.clusterPath →
      (frameRect P cg run t).x + (frameRect P cg run t).w ≤
        (frameRect P cg run pos).x →
      ¬ ((loopFootprint cg run labels t).y + (loopFootprint cg run labels t).h ≤
          (frameRect P cg run pos).y ∨
        (frameRect P cg run pos).y + (frameRect P cg run pos).h ≤
          (loopFootprint cg run labels t).y) →
      (loopFootprint cg run labels t).x + (loopFootprint cg run labels t).w ≤
        (frameRect P cg run pos).x

/-- The loop footprint of `v` is disjoint from its own frame, at any `Params`
(the frame ignores its `Params` argument). Copy of the public
`FlatC6LoopProof.loopFootprint_self_disjoint`, generalized over `P`. -/
theorem loopFootprint_self_pos {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} (v : Nat) :
    Disjoint (loopFootprint cg run labels v) (frameRect P cg run v) := by
  have hPP : frameRect P cg run v = frameRect default cg run v := rfl
  rw [hPP]
  unfold Disjoint Rect.meetsInterior loopFootprint
  rintro ⟨hx, -⟩
  dsimp only at hx
  omega

/-- Transitivity of non-strict containment. -/
theorem Rect.Contained.trans' {a b c : Rect}
    (hab : a.Contained b) (hbc : b.Contained c) : a.Contained c := by
  unfold Rect.Contained at *
  omega

/-- Transitivity of strict containment. -/
theorem Rect.StrictInside.trans' {a b c : Rect}
    (hab : a.StrictInside b) (hbc : b.StrictInside c) : a.StrictInside c := by
  unfold Rect.StrictInside at *
  omega

/-- Strict-inside implies non-strict containment. -/
theorem Rect.StrictInside.toContained' {a b : Rect}
    (h : a.StrictInside b) : a.Contained b := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- A loop tail is in bounds. -/
theorem loopTail_bounded {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat}
    {t : Nat}
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = t ∧ e.head = t) :
    t < (componentCandidate execution.graph comp candidate).nodes.length := by
  obtain ⟨e, hmem, ht, -⟩ := het
  have hbd := sceneExecution_edges_bounded execution
  have hb := candidate_edge_endpoints_bounded_general execution.graph comp
    candidate hcomp hbd hmem
  omega

/-- Candidate lookup projects to the global lookup. -/
theorem graphLookup_cand {g : Graph} {comp : List Nat} {candidate idx key : Nat}
    {nd : Node}
    (hkey : comp[idx]? = some key) (hg : g.nodes[key]? = some nd) :
    (componentCandidate g comp candidate).nodes[idx]? = some nd := by
  have h : (componentCandidate g comp candidate).nodes[idx]? =
      some ((g.nodes.getD key default)) := by
    rw [componentCandidate_nodes]
    dsimp only [componentGraph]
    rw [List.getElem?_map, hkey]
    simp only [Option.map_some]
  rw [List.getD_eq_getElem?_getD, hg, Option.getD_some] at h
  exact h

/-- Global lookup lifts from the candidate lookup. -/
theorem candLookup_graph {g : Graph} {comp : List Nat} {candidate i key : Nat}
    {nd : Node}
    (hcg : (componentCandidate g comp candidate).nodes[i]? = some nd)
    (hkey : comp[i]? = some key)
    (hlen : key < g.nodes.length) :
    g.nodes[key]? = some nd := by
  have h := hcg
  rw [componentCandidate_nodes] at h
  dsimp only [componentGraph] at h
  simp only [List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD] at h
  cases hgopt : g.nodes[key]? with
  | none =>
      rw [List.getElem?_eq_none_iff] at hgopt
      omega
  | some node =>
      rw [hgopt] at h
      simp only [Option.getD_some] at h
      exact h

/-- A plain or group candidate node carries its global key as declaration. -/
theorem candNode_decl_eq_key {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate i key : Nat} {nd : Node}
    (hcg : (componentCandidate execution.graph comp candidate).nodes[i]? = some nd)
    (hkey : comp[i]? = some key)
    (hkeyLen : key < inp.boxes.length) :
    nd.decl = key := by
  have hgl : key < execution.graph.nodes.length :=
    sceneExecution_graph_len execution hkeyLen
  have hgg : execution.graph.nodes[key]? = some nd :=
    candLookup_graph hcg hkey hgl
  rcases component_node_border_plain_or_group execution hkeyLen hgg with h0 | h2
  · obtain ⟨box, -, hdecl, -⟩ := execution.plain_node_path_source hgg h0
    exact hdecl
  · obtain ⟨box, -, hdecl, -⟩ := execution.group_node_path_source hgg h2
    exact hdecl

/-- Distinct candidate indices have distinct declarations. -/
theorem candDecl_ne_of_idx_ne {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate t pos keyt keyp : Nat} {nt np : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    (hkeyt : comp[t]? = some keyt) (hlent : keyt < inp.boxes.length)
    (hng : (componentCandidate execution.graph comp candidate).nodes[pos]? = some np)
    (hkeyp : comp[pos]? = some keyp) (hlenp : keyp < inp.boxes.length)
    (hne : pos ≠ t) : np.decl ≠ nt.decl := by
  intro hcon
  have ht_eq := candNode_decl_eq_key execution hnt hkeyt hlent
  have hp_eq := candNode_decl_eq_key execution hng hkeyp hlenp
  have hkk : keyt = keyp := by omega
  have hmap : comp[t]? = comp[pos]? := by rw [hkeyt, hkeyp, hkk]
  have hlen : t < comp.length := (List.getElem?_eq_some_iff.mp hkeyt).1
  have hnod := components_nodup execution.graph comp hcomp
  exact hne (((List.Nodup.getElem?_inj hlen hnod).mp hmap).symm)


/-- Parent-link references for one walk step: from a grouped child key, find
the framed parent box, its component index, and its candidate node (a group).
Packages `framedParents_parent`, component membership, and the paired-marker
top record, following the `frameRect_member_contained` setup. -/
theorem setupParentLink {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate key_t : Nat} {box_t : ModelBox}
    (hkeyLen : key_t < inp.boxes.length)
    (hkeyIn : key_t ∈ comp)
    (hchildBox : inp.boxes[key_t]? = some box_t)
    (hparentNe : box_t.parent ≠ "") :
    ∃ (parentKey : Nat) (parentBox : ModelBox) (parentIdx : Nat) (top : Node),
      inp.boxes[parentKey]? = some parentBox ∧
      box_t.parent = parentBox.id ∧
      comp[parentIdx]? = some parentKey ∧
      (componentCandidate execution.graph comp candidate).nodes[parentIdx]? =
        some top ∧
      top.border = -2 ∧ top.decl = parentKey := by
  obtain ⟨pb, hpbMem, hpid, hpgroup, hpnotfixed⟩ := framedParents_parent hframed
    (List.mem_of_getElem? hchildBox) hparentNe
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hpbMem
  obtain ⟨mt, hmt⟩ : ∃ mt, execution.graph.nodes[key_t]? = some mt :=
    ⟨_, List.getElem?_eq_getElem
      (sceneExecution_graph_len execution hkeyLen)⟩
  have hparentRef : box_t.parent = pb.id := hpid.symm
  have hparentIn : pi ∈ comp := member_parent_key_in_component execution hwf
    hframed hcomp hkeyLen hkeyIn hmt hchildBox hpi hparentRef hparentNe
  obtain ⟨parentIdx, hparentIdx⟩ := List.mem_iff_getElem?.mp hparentIn
  have hfPb : ((fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source) pb) = pb := by
    simp [hpnotfixed]
  have hdemP : (inp.boxes.map (fun source : ModelBox =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == source.id) then
        { source with role := .node } else source))[pi]? = some pb := by
    rw [List.getElem?_map, hpi]
    simp only [Option.map_some, hfPb]
  have hpkLines : pi < execution.lines.length := by
    rw [boxLines_length execution.lines_eq]
    exact (List.getElem?_eq_some_iff.mp hpi).1
  obtain ⟨top, -, htopLookup, -, htopBorder, -, -, -, -, -, -, -⟩ :=
    measuredGraph_paired_markers execution.graph_eq hpkLines hdemP hpgroup
  have htopCg : (componentCandidate execution.graph comp
      candidate).nodes[parentIdx]? = some top :=
    graphLookup_cand hparentIdx htopLookup
  have hpiLen : pi < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hpi).1
  have htopDeclEq : top.decl = pi :=
    candNode_decl_eq_key execution htopCg hparentIdx hpiLen
  exact ⟨pi, pb, parentIdx, top, hpi, hparentRef, hparentIdx, htopCg,
    htopBorder, htopDeclEq⟩

/-- Index inequality lifts through distinct global keys. -/
theorem walkIdx_ne {comp : List Nat}
    {a b ka kb : Nat}
    (ha : comp[a]? = some ka) (hb : comp[b]? = some kb)
    (hne : ka ≠ kb) : a ≠ b := by
  intro hcon
  subst hcon
  exact hne (Option.some.inj (ha.symm.trans hb))

/-- First link, plain owner: the parent hull strictly contains the loop
footprint. Left/top/bottom from the proved plain strictness, right from the
residual cover. -/
theorem stepPlainStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {tIdx parentIdx : Nat} {nt top : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[tIdx]? =
      some nt)
    (hnt0 : nt.border = 0)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = tIdx ∧ e.head = tIdx)
    (htop : (componentCandidate execution.graph comp candidate).nodes[parentIdx]? =
      some top)
    (htop2 : top.border = -2)
    (hinside : nt.clusterPath.contains top.decl = true)
    (hright : LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured) :
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run
      parentIdx).StrictInside
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured tIdx) := by
  have hnePI : parentIdx ≠ tIdx := by
    intro hcon
    subst hcon
    have heq : top = nt := Option.some.inj (htop.symm.trans hnt)
    have hb : top.border = nt.border := congrArg Node.border heq
    omega
  have hSI := execution.component_member_strictInside' hwf hcomp hrun htop
    htop2 hnt hnt0 hinside
  have hmemAnc : top.decl ∈ nt.clusterPath := by
    have h := hinside
    rw [List.contains_eq_mem, decide_eq_true_eq] at h
    exact h
  have hR1 := hright tIdx nt hnt het parentIdx top htop htop2 hnePI hmemAnc
  have hdim := componentRun_dims_nonneg hrun
  have htLen := loopTail_bounded execution hcomp het
  have hcov := componentRun_original_nodes_covered hrun tIdx htLen
  have hFw := (frameRect_dims_nonneg execution.params
    (componentCandidate execution.graph comp candidate) run tIdx hdim
    hcov).1
  have hPP : frameRect execution.params
      (componentCandidate execution.graph comp candidate) run tIdx =
      frameRect default
        (componentCandidate execution.graph comp candidate) run tIdx := rfl
  rw [hPP] at hSI hFw
  unfold Rect.StrictInside at hSI
  unfold Rect.StrictInside
  unfold loopFootprint at hR1
  unfold loopFootprint
  dsimp only at hSI hR1 ⊢
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hSI
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- First link, group owner: the parent hull strictly contains the loop
footprint. Hull-in-hull from the proved group strictness (rank residuals
discharged), right edge from the residual cover. -/
theorem stepGroupStrict {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {tIdx parentIdx key_t parentKey : Nat} {nt top : Node}
    {childBox parentBox : ModelBox}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[tIdx]? =
      some nt)
    (hnt2 : nt.border = -2)
    (hkeyt : comp[tIdx]? = some key_t)
    (hlen_t : key_t < inp.boxes.length)
    (hchildBox : inp.boxes[key_t]? = some childBox)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = tIdx ∧ e.head = tIdx)
    (htop : (componentCandidate execution.graph comp candidate).nodes[parentIdx]? =
      some top)
    (htop2 : top.border = -2)
    (hkeyp : comp[parentIdx]? = some parentKey)
    (hlen_p : parentKey < inp.boxes.length)
    (hparentBox : inp.boxes[parentKey]? = some parentBox)
    (hparentRef : childBox.parent = parentBox.id)
    (hparentNe : childBox.parent ≠ "")
    (hinside : nt.clusterPath.contains top.decl = true)
    (hright : LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run
      execution.measured) :
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run
      parentIdx).StrictInside
      (loopFootprint (componentCandidate execution.graph comp candidate) run
        execution.measured tIdx) := by
  have hstep := Compound.path_of_parent (inputModel inp o) hwf hparentBox
    hchildBox hparentRef hparentNe
  have hkeyNe : parentKey ≠ key_t := by
    intro hcon
    subst hcon
    have hsame : parentBox = childBox :=
      Option.some.inj (hparentBox.symm.trans hchildBox)
    rw [hsame] at hstep
    have hlenEq := congrArg List.length hstep
    simp only [List.length_append, List.length_singleton] at hlenEq
    omega
  have hnePI : parentIdx ≠ tIdx := walkIdx_ne hkeyp hkeyt hkeyNe
  have htopLe := childTopRankLe_executed execution hwf hframed hcomp hrun hnt
    hnt2
  have hbotLe := childBottomRankLe_executed execution hwf hframed hcomp hrun
    hnt hnt2
  have htopDeclEq : top.decl = parentKey :=
    candNode_decl_eq_key execution htop hkeyp hlen_p
  have hntDeclEq : nt.decl = key_t :=
    candNode_decl_eq_key execution hnt hkeyt hlen_t
  rw [← htopDeclEq] at hparentBox
  rw [← hntDeclEq] at hchildBox
  have hSI := execution.component_child_frame_strictInside' hwf hcomp hrun
    htop htop2 hnt hnt2 hparentBox hchildBox hparentRef hparentNe htopLe
    hbotLe
  have hmemAnc : top.decl ∈ nt.clusterPath := by
    have h := hinside
    rw [List.contains_eq_mem, decide_eq_true_eq] at h
    exact h
  have hR1 := hright tIdx nt hnt het parentIdx top htop htop2 hnePI hmemAnc
  have hdim := componentRun_dims_nonneg hrun
  have htLen := loopTail_bounded execution hcomp het
  have hcov := componentRun_original_nodes_covered hrun tIdx htLen
  have hFw := (frameRect_dims_nonneg execution.params
    (componentCandidate execution.graph comp candidate) run tIdx hdim
    hcov).1
  have hPP : frameRect execution.params
      (componentCandidate execution.graph comp candidate) run tIdx =
      frameRect default
        (componentCandidate execution.graph comp candidate) run tIdx := rfl
  rw [hPP] at hSI hFw
  unfold Rect.StrictInside at hSI
  unfold Rect.StrictInside
  unfold loopFootprint at hR1
  unfold loopFootprint
  dsimp only at hSI hR1 ⊢
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hSI
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The cluster path of a parentless box is empty. -/
theorem path_nil_of_parent_empty (boxes : List ModelBox) (box : ModelBox)
    (h : box.parent = "") : Compound.path boxes box = [] := by
  unfold Compound.path
  rw [h]
  cases hl : boxes.length with
  | zero => rfl
  | succ n => rfl

/-- One walk step at the cluster-path level: the child path is the parent
path extended by the parent key and the child declaration. -/
theorem walkClStep {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} {candidate cIdx parentIdx ckey parentKey : Nat}
    {c top : Node} {box_c parentBox : ModelBox}
    (hcg : (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
      some c)
    (hckey : comp[cIdx]? = some ckey)
    (hbox : inp.boxes[ckey]? = some box_c)
    (hcG : c.border = -2)
    (hpCg : (componentCandidate execution.graph comp
      candidate).nodes[parentIdx]? = some top)
    (hpKey : comp[parentIdx]? = some parentKey)
    (hpBox : inp.boxes[parentKey]? = some parentBox)
    (hpRef : box_c.parent = parentBox.id)
    (hpNe : box_c.parent ≠ "")
    (hpG : top.border = -2) :
    c.clusterPath = top.clusterPath ++ [c.decl] := by
  have hlen_c : ckey < execution.graph.nodes.length :=
    sceneExecution_graph_len execution
      (List.getElem?_eq_some_iff.mp hbox).1
  have hgc : execution.graph.nodes[ckey]? = some c :=
    candLookup_graph hcg hckey hlen_c
  obtain ⟨b1, hb1, -, hpathc⟩ := execution.group_node_path_source hgc hcG
  have hb1eq : b1 = box_c := Option.some.inj (hb1.symm.trans hbox)
  have hlen_p : parentKey < execution.graph.nodes.length :=
    sceneExecution_graph_len execution
      (List.getElem?_eq_some_iff.mp hpBox).1
  have hgp : execution.graph.nodes[parentKey]? = some top :=
    candLookup_graph hpCg hpKey hlen_p
  obtain ⟨b2, hb2, -, hpathp⟩ :=
    execution.group_node_path_source hgp hpG
  have hb2eq : b2 = parentBox := Option.some.inj (hb2.symm.trans hpBox)
  have hstep := Compound.path_of_parent (inputModel inp o) hwf hpBox hbox
    hpRef hpNe
  have hcDecl : c.decl = ckey := candNode_decl_eq_key execution hcg hckey
    (List.getElem?_eq_some_iff.mp hbox).1
  rw [hb1eq] at hpathc
  rw [hb2eq] at hpathp
  have hstep2 : Compound.path inp.boxes box_c =
      Compound.path inp.boxes parentBox ++ [parentKey] := hstep
  rw [hstep2, ← hpathp, ← hcDecl] at hpathc
  exact hpathc


/-- A grouped child has a parent: otherwise its cluster path would be a
singleton, forcing the ancestor target to coincide with it. -/
theorem walkParentNe {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate cIdx tgt ckey tkey : Nat} {c nt : Node} {box_c : ModelBox}
    (hcg : (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
      some c)
    (hckey : comp[cIdx]? = some ckey)
    (hbox : inp.boxes[ckey]? = some box_c)
    (hcG : c.border = -2)
    (htgt : (componentCandidate execution.graph comp candidate).nodes[tgt]? =
      some nt)
    (htkey : comp[tgt]? = some tkey)
    (hlenp : tkey < inp.boxes.length)
    (hmem : nt.decl ∈ c.clusterPath)
    (hne : tgt ≠ cIdx) :
    box_c.parent ≠ "" := by
  intro hcon
  have hpath := path_nil_of_parent_empty inp.boxes box_c hcon
  have hlen_c : ckey < execution.graph.nodes.length :=
    sceneExecution_graph_len execution
      (List.getElem?_eq_some_iff.mp hbox).1
  have hgc : execution.graph.nodes[ckey]? = some c :=
    candLookup_graph hcg hckey hlen_c
  obtain ⟨b1, hb1, -, hpathc⟩ := execution.group_node_path_source hgc hcG
  have hb1eq : b1 = box_c := Option.some.inj (hb1.symm.trans hbox)
  have hcDecl : c.decl = ckey := candNode_decl_eq_key execution hcg hckey
    (List.getElem?_eq_some_iff.mp hbox).1
  rw [hb1eq, hpath] at hpathc
  have hpathc' : c.clusterPath = [ckey] := hpathc
  rw [hpathc'] at hmem
  have hsing : nt.decl = ckey := List.mem_singleton.mp hmem
  have hpDecl : nt.decl = tkey :=
    candNode_decl_eq_key execution htgt htkey hlenp
  have hkk : tkey = ckey := by omega
  have hmap : comp[tgt]? = comp[cIdx]? := by rw [htkey, hckey, hkk]
  have hlen : tgt < comp.length := (List.getElem?_eq_some_iff.mp htkey).1
  have hnod := components_nodup execution.graph comp hcomp
  exact hne ((List.Nodup.getElem?_inj hlen hnod).mp hmap)


/-- Strict hull nesting along the ancestor chain: every strict group ancestor
hull strictly contains the descendant group hull. Fuel induction on the
cluster-path length; each step is a direct group-in-group strictness with
discharged rank residuals. -/
theorem walkStrictFromAux {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {pos pkey : Nat} {np : Node}
    (hpos : (componentCandidate execution.graph comp candidate).nodes[pos]? =
      some np)
    (hpkey : comp[pos]? = some pkey)
    (hlenp : pkey < inp.boxes.length) :
    ∀ (fuel : Nat) (cIdx : Nat) (c : Node) (ckey : Nat) (box_c : ModelBox),
      (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
        some c →
      c.border = -2 →
      comp[cIdx]? = some ckey →
      ckey < inp.boxes.length →
      inp.boxes[ckey]? = some box_c →
      np.decl ∈ c.clusterPath →
      pos ≠ cIdx →
      c.clusterPath.length ≤ fuel →
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run
        pos).StrictInside
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run cIdx) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cIdx c ckey box_c hc hcG hckey hlen_c hbox hmem hne hfuel
      have hempty : c.clusterPath = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hfuel)
      rw [hempty] at hmem
      simp at hmem
  | succ n ih =>
      intro cIdx c ckey box_c hc hcG hckey hlen_c hbox hmem hne hfuel
      have hparentNe := walkParentNe execution hcomp hc hckey hbox hcG hpos
        hpkey hlenp hmem hne
      obtain ⟨parentKey, parentBox, parentIdx, top, hparentBox, hparentRef,
        hparentIdx, htopCg, htopBorder, htopDeclEq⟩ :=
        setupParentLink execution hwf hframed hcomp hlen_c
          (List.mem_of_getElem? hckey) hbox hparentNe
      have hcDecl : c.decl = ckey :=
        candNode_decl_eq_key execution hc hckey hlen_c
      have hparentBoxD : inp.boxes[top.decl]? = some parentBox := by
        rw [htopDeclEq]
        exact hparentBox
      have hchildBoxD : inp.boxes[c.decl]? = some box_c := by
        rw [hcDecl]
        exact hbox
      have htopLe := childTopRankLe_executed execution hwf hframed hcomp hrun
        hc hcG
      have hbotLe := childBottomRankLe_executed execution hwf hframed hcomp
        hrun hc hcG
      have hlink := execution.component_child_frame_strictInside' hwf hcomp
        hrun htopCg htopBorder hc hcG hparentBoxD hchildBoxD hparentRef
        hparentNe htopLe hbotLe
      by_cases h : parentKey = pkey
      · have hmap : comp[parentIdx]? = comp[pos]? := by
          rw [hparentIdx, hpkey, h]
        have hlen : parentIdx < comp.length :=
          (List.getElem?_eq_some_iff.mp hparentIdx).1
        have hnod := components_nodup execution.graph comp hcomp
        have hPI : parentIdx = pos :=
          (List.Nodup.getElem?_inj hlen hnod).mp hmap
        subst hPI
        exact hlink
      · have hne' : pos ≠ parentIdx := by
          intro hcon
          have e2 := hpkey
          rw [hcon] at e2
          exact h (Option.some.inj (hparentIdx.symm.trans e2))
        have hcl := walkClStep execution hwf hc hckey hbox hcG htopCg
          hparentIdx hparentBox hparentRef hparentNe htopBorder
        rw [hcl, List.mem_append] at hmem
        have hmem' : np.decl ∈ top.clusterPath := by
          rcases hmem with h | h
          · exact h
          · exfalso
            have hEq : np.decl = c.decl := List.mem_singleton.mp h
            have hpDecl : np.decl = pkey :=
              candNode_decl_eq_key execution hpos hpkey hlenp
            have hkk : pkey = ckey := by rw [← hpDecl, hEq, hcDecl]
            have hmap : comp[pos]? = comp[cIdx]? := by
              rw [hpkey, hckey, hkk]
            have hlen : pos < comp.length :=
              (List.getElem?_eq_some_iff.mp hpkey).1
            have hnod := components_nodup execution.graph comp hcomp
            exact hne ((List.Nodup.getElem?_inj hlen hnod).mp hmap)
        have hfuel' : top.clusterPath.length ≤ n := by
          have hlenEq := congrArg List.length hcl
          simp only [List.length_append, List.length_singleton] at hlenEq
          omega
        have hlen_p : parentKey < inp.boxes.length :=
          (List.getElem?_eq_some_iff.mp hparentBox).1
        have hih := ih parentIdx top parentKey parentBox htopCg htopBorder
          hparentIdx hlen_p hparentBox hmem' hne' hfuel'
        exact Rect.StrictInside.trans' hih hlink

/-- Strict hull nesting for a strict group ancestor. -/
theorem walkStrictFrom {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {pos pkey : Nat} {np : Node}
    (hpos : (componentCandidate execution.graph comp candidate).nodes[pos]? =
      some np)
    (hpkey : comp[pos]? = some pkey)
    (hlenp : pkey < inp.boxes.length)
    {cIdx ckey : Nat} {c : Node} {box_c : ModelBox}
    (hc : (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
      some c)
    (hcG : c.border = -2)
    (hckey : comp[cIdx]? = some ckey)
    (hlen_c : ckey < inp.boxes.length)
    (hbox : inp.boxes[ckey]? = some box_c)
    (hmem : np.decl ∈ c.clusterPath)
    (hne : pos ≠ cIdx) :
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run
      pos).StrictInside
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run cIdx) :=
  walkStrictFromAux execution hwf hframed hcomp hrun hpos hpkey hlenp
    c.clusterPath.length cIdx c ckey box_c hc hcG hckey hlen_c hbox hmem hne
    (Nat.le_refl _)

/-- Contained hull nesting along the ancestor chain: every ancestor group hull
contains the descendant group hull. Fuel induction; each step is a direct
group-in-group strictness weakened to containment. -/
theorem walkContainedUpAux {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t tkey : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? =
      some nt)
    (htkey : comp[t]? = some tkey)
    (hlen_t : tkey < inp.boxes.length) :
    ∀ (fuel : Nat) (cIdx : Nat) (c : Node) (ckey : Nat) (box_c : ModelBox),
      (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
        some c →
      c.border = -2 →
      comp[cIdx]? = some ckey →
      ckey < inp.boxes.length →
      inp.boxes[ckey]? = some box_c →
      nt.decl ∈ c.clusterPath →
      t ≠ cIdx →
      c.clusterPath.length ≤ fuel →
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run
        t).Contained
        (frameRect execution.params
          (componentCandidate execution.graph comp candidate) run cIdx) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cIdx c ckey box_c hc hcG hckey hlen_c hbox hmem hne hfuel
      have hempty : c.clusterPath = [] :=
        List.length_eq_zero_iff.mp (Nat.le_zero.mp hfuel)
      rw [hempty] at hmem
      simp at hmem
  | succ n ih =>
      intro cIdx c ckey box_c hc hcG hckey hlen_c hbox hmem hne hfuel
      have hparentNe := walkParentNe execution hcomp hc hckey hbox hcG hnt
        htkey hlen_t hmem hne
      obtain ⟨parentKey, parentBox, parentIdx, top, hparentBox, hparentRef,
        hparentIdx, htopCg, htopBorder, htopDeclEq⟩ :=
        setupParentLink execution hwf hframed hcomp hlen_c
          (List.mem_of_getElem? hckey) hbox hparentNe
      have hcDecl : c.decl = ckey :=
        candNode_decl_eq_key execution hc hckey hlen_c
      have hparentBoxD : inp.boxes[top.decl]? = some parentBox := by
        rw [htopDeclEq]
        exact hparentBox
      have hchildBoxD : inp.boxes[c.decl]? = some box_c := by
        rw [hcDecl]
        exact hbox
      have htopLe := childTopRankLe_executed execution hwf hframed hcomp hrun
        hc hcG
      have hbotLe := childBottomRankLe_executed execution hwf hframed hcomp
        hrun hc hcG
      have hlinkS := execution.component_child_frame_strictInside' hwf hcomp
        hrun htopCg htopBorder hc hcG hparentBoxD hchildBoxD hparentRef
        hparentNe htopLe hbotLe
      have hlink := Rect.StrictInside.toContained' hlinkS
      by_cases h : parentKey = tkey
      · have hmap : comp[parentIdx]? = comp[t]? := by
          rw [hparentIdx, htkey, h]
        have hlen : parentIdx < comp.length :=
          (List.getElem?_eq_some_iff.mp hparentIdx).1
        have hnod := components_nodup execution.graph comp hcomp
        have hPI : parentIdx = t :=
          (List.Nodup.getElem?_inj hlen hnod).mp hmap
        subst hPI
        exact hlink
      · have hne' : t ≠ parentIdx := by
          intro hcon
          have e2 := htkey
          rw [hcon] at e2
          exact h (Option.some.inj (hparentIdx.symm.trans e2))
        have hcl := walkClStep execution hwf hc hckey hbox hcG htopCg
          hparentIdx hparentBox hparentRef hparentNe htopBorder
        rw [hcl, List.mem_append] at hmem
        have hmem' : nt.decl ∈ top.clusterPath := by
          rcases hmem with h | h
          · exact h
          · exfalso
            have hEq : nt.decl = c.decl := List.mem_singleton.mp h
            have htDecl : nt.decl = tkey :=
              candNode_decl_eq_key execution hnt htkey hlen_t
            have hkk : tkey = ckey := by rw [← htDecl, hEq, hcDecl]
            have hmap : comp[t]? = comp[cIdx]? := by
              rw [htkey, hckey, hkk]
            have hlen : t < comp.length :=
              (List.getElem?_eq_some_iff.mp htkey).1
            have hnod := components_nodup execution.graph comp hcomp
            exact hne ((List.Nodup.getElem?_inj hlen hnod).mp hmap)
        have hfuel' : top.clusterPath.length ≤ n := by
          have hlenEq := congrArg List.length hcl
          simp only [List.length_append, List.length_singleton] at hlenEq
          omega
        have hlen_p : parentKey < inp.boxes.length :=
          (List.getElem?_eq_some_iff.mp hparentBox).1
        have hih := ih parentIdx top parentKey parentBox htopCg htopBorder
          hparentIdx hlen_p hparentBox hmem' hne' hfuel'
        exact Rect.Contained.trans' hih hlink

/-- Contained hull nesting for a nested group. -/
theorem walkContainedUp {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {t tkey : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? =
      some nt)
    (htkey : comp[t]? = some tkey)
    (hlen_t : tkey < inp.boxes.length)
    {cIdx ckey : Nat} {c : Node} {box_c : ModelBox}
    (hc : (componentCandidate execution.graph comp candidate).nodes[cIdx]? =
      some c)
    (hcG : c.border = -2)
    (hckey : comp[cIdx]? = some ckey)
    (hlen_c : ckey < inp.boxes.length)
    (hbox : inp.boxes[ckey]? = some box_c)
    (hmemT : nt.decl ∈ c.clusterPath)
    (hne : t ≠ cIdx) :
    (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run
      t).Contained
      (frameRect execution.params
        (componentCandidate execution.graph comp candidate) run cIdx) :=
  walkContainedUpAux execution hwf hframed hcomp hrun hnt htkey hlen_t
    c.clusterPath.length cIdx c ckey box_c hc hcG hckey hlen_c hbox hmemT hne
    (Nat.le_refl _)

/-- Members of a reported component are valid graph node indices. -/
theorem lh_compMemLt {g : Graph} {comp : List Nat} (hcomp : comp ∈ components g)
    {x : Nat} (hx : x ∈ comp) : x < g.nodes.length := by
  unfold components at hcomp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hcomp
  exact List.mem_range.mp (List.mem_filter.mp hx).1

/-- `findIdx?` hits are in bounds. -/
theorem lh_findIdxLt {α : Type} {p : α → Bool} :
    ∀ (l : List α) (i : Nat), l.findIdx? p = some i → i < l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons x xs ih =>
    intro i h
    rw [List.findIdx?_cons] at h
    split at h
    · simp at h
      subst h
      simp
    · cases hx : xs.findIdx? p with
      | none => rw [hx] at h; simp at h
      | some j =>
        rw [hx] at h
        simp at h
        have hbound := ih j hx
        have hlen : (x :: xs).length = xs.length + 1 := List.length_cons ..
        omega

/-- Raw route edges reference in-bounds boxes. -/
theorem lh_edgeOfLt {inp : Input} {r : ModelRoute} {i : Nat} {e : Edge}
    (h : edgeOf inp r i = .ok e) :
    e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  unfold edgeOf at h
  cases h1 : inp.boxes.findIdx? (fun b => b.id == r.fromId) with
  | none => rw [h1] at h; simp at h
  | some a =>
    cases h2 : inp.boxes.findIdx? (fun b => b.id == r.toId) with
    | none => rw [h1, h2] at h; simp at h
    | some b =>
      rw [h1, h2] at h
      simp at h
      cases h
      exact ⟨lh_findIdxLt inp.boxes a h1, lh_findIdxLt inp.boxes b h2⟩

/-- Raw graph edges reference in-bounds boxes. -/
theorem lh_rawBounds (inp : Input) :
    ∀ (rs : List ModelRoute) (k : Nat) (es : List Edge),
      graphEdgesFrom inp k rs = .ok es →
      ∀ e ∈ es, e.tail < inp.boxes.length ∧ e.head < inp.boxes.length := by
  intro rs
  induction rs with
  | nil =>
    intro k es h e he
    simp only [graphEdgesFrom] at h
    simp at h
    subst h
    simp at he
  | cons r rs ih =>
    intro k es h e he
    unfold graphEdgesFrom at h
    obtain ⟨edge, hedge, h⟩ := bind_ok h
    obtain ⟨edges, hedges, h⟩ := bind_ok h
    have hr := Except.ok.inj h
    subst hr
    rcases List.mem_cons.mp he with rfl | he'
    · exact lh_edgeOfLt hedge
    · exact ih (k + 1) edges hedges e he'

/-- A self-pair aliases to itself. -/
theorem lh_endpointSelf (boxes : List ModelBox) (source : Bool) (v : Nat) :
    Compound.endpoint boxes source v v = v := by
  cases hb : boxes[v]? <;> simp [Compound.endpoint, hb]

/-- `bottomIndex` is strictly increasing past a group box. -/
theorem lh_bottomIndexLt {boxes : List ModelBox} {i j : Nat} (hij : i < j)
    (_hi : i < boxes.length) {bi : ModelBox} (hbi : boxes[i]? = some bi)
    (hg : bi.role == .group) :
    Compound.bottomIndex boxes i < Compound.bottomIndex boxes j := by
  unfold Compound.bottomIndex
  have h1 : (boxes.take j).take i ++ (boxes.take j).drop i = boxes.take j :=
    List.take_append_drop i (boxes.take j)
  have h2 : (boxes.take j).take i = boxes.take i := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hij)]
  have h3 := congrArg (List.filter (fun box : ModelBox => box.role == .group)) h1
  rw [List.filter_append, h2] at h3
  have hmem : bi ∈ (boxes.take j).drop i := by
    have h0 : ((boxes.take j).drop i)[0]? = some bi := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_take, ite_eq_left hij, hbi]
    exact List.mem_of_getElem? h0
  have hfilter : 0 < (((boxes.take j).drop i).filter
      (fun box : ModelBox => box.role == .group)).length := by
    apply List.length_pos_of_mem
    exact List.mem_filter.mpr ⟨hmem, hg⟩
  rw [h3.symm, List.length_append]
  omega

set_option maxHeartbeats 1000000 in
/-- Distinct raw endpoints cannot alias to the same out-of-bounds index. -/
theorem lh_selfBottomNe {boxes : List ModelBox} {a b k : Nat}
    (ha : a < boxes.length) (hb : b < boxes.length) (hab : a ≠ b)
    (ea : Compound.endpoint boxes true a b = k)
    (eb : Compound.endpoint boxes false b a = k)
    (hk : ¬ k < boxes.length) : False := by
  cases hma : boxes[a]? with
  | none =>
    simp only [Compound.endpoint, hma] at ea
    exact hk (by rw [← ea]; exact ha)
  | some ba =>
    cases hmb : boxes[b]? with
    | none =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      exact hk (by rw [← eb]; exact hb)
    | some bb =>
      simp only [Compound.endpoint, hma, hmb] at ea eb
      split at ea
      · exact hk (by rw [← ea]; exact ha)
      · split at ea
        · exact hk (by rw [← ea]; exact ha)
        · rename_i hc1 hc2
          split at eb
          · exact hk (by rw [← eb]; exact hb)
          · split at eb
            · exact hk (by rw [← eb]; exact hb)
            · rename_i hc3 _
              have hgrpA : (ba.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc1
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              have hgrpB : (bb.role == .group) = true := by
                have hf := Bool.eq_false_iff.mpr hc3
                have hp := (Bool.or_eq_false_iff.mp hf).1
                simpa using hp.symm
              rcases Nat.lt_or_ge a b with hcmp | hcmp
              · have hbound := lh_bottomIndexLt hcmp ha hma hgrpA
                rw [ea, eb] at hbound
                exact absurd hbound (Nat.lt_irrefl k)
              · have hblt : b < a := by omega
                have hbound := lh_bottomIndexLt hblt hb hmb hgrpB
                rw [eb, ea] at hbound
                exact absurd hbound (Nat.lt_irrefl k)

/-- Endpoint projection of the pristine form of an edge (tail). -/
theorem lh_origTail (e : Edge) :
    e.original.tail = if e.reversed then e.head else e.tail := by
  cases h : e.reversed <;> simp [Edge.original, h]

/-- Endpoint projection of the pristine form of an edge (head). -/
theorem lh_origHead (e : Edge) :
    e.original.head = if e.reversed then e.tail else e.head := by
  cases h : e.reversed <;> simp [Edge.original, h]


theorem lh_globalSelfLoopLt {inp : Input} {mapped : List ModelBox} {rawG : Graph}
    (hmapLen : mapped.length = inp.boxes.length)
    (hbounds : ∀ e ∈ rawG.edges,
      e.tail < inp.boxes.length ∧ e.head < inp.boxes.length)
    {e : Edge} (hmem : e ∈ rawG.edges.map (Compound.aliasEdge mapped))
    (hself : e.tail = e.head) : e.tail < inp.boxes.length := by
  obtain ⟨e₀, hmem₀, heq⟩ := List.mem_map.mp hmem
  have hb := hbounds e₀ hmem₀
  have ha : e₀.tail < mapped.length := by omega
  have hbb : e₀.head < mapped.length := by omega
  have hAt : (Compound.aliasEdge mapped e₀).tail =
      Compound.endpoint mapped true e₀.tail e₀.head := rfl
  have hAh : (Compound.aliasEdge mapped e₀).head =
      Compound.endpoint mapped false e₀.head e₀.tail := rfl
  rw [heq] at hAt hAh
  rw [← hself] at hAh
  by_cases hEE : e₀.tail = e₀.head
  · rw [hEE] at hAt
    have hE := lh_endpointSelf mapped true e₀.head
    omega
  · by_cases hk : e.tail < inp.boxes.length
    · exact hk
    · have hk' : ¬ e.tail < mapped.length := by omega
      exact False.elim (lh_selfBottomNe ha hbb hEE hAt.symm hAh.symm hk')
/-- A candidate self-loop pins a below-boxes global key with the loop node. -/
theorem lh_loopOwnerKey {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate t : Nat} {nt : Node}
    (hnt : (componentCandidate execution.graph comp candidate).nodes[t]? = some nt)
    {e' : Edge} (hmem : e' ∈ (componentCandidate execution.graph comp candidate).edges)
    (htail : e'.tail = t) (hhead : e'.head = t) :
    ∃ k, comp[t]? = some k ∧ k < inp.boxes.length ∧
      execution.graph.nodes[k]? = some nt := by
  have hnod := components_nodup execution.graph comp hcomp
  have hbd := sceneExecution_edges_bounded execution
  obtain ⟨source, hsource, htailMem, hsrcEq⟩ :=
    componentCandidate_semantic_source hmem
  obtain ⟨comp', hcomp'm, htail', hhead'⟩ :=
    components_edge_endpoints hbd (List.mem_append_left _ hsource)
  have hsame : comp = comp' :=
    components_shared_member_eq hcomp hcomp'm htailMem htail'
  have hheadMem : source.head ∈ comp := by rw [hsame]; exact hhead'
  have horgT : e'.original.tail = t := by
    cases h : e'.reversed
    · have hO : e'.original =
          { tail := e'.tail, head := e'.head, minLen := e'.minLen, decl := e'.decl,
            reversed := false } := by
        simp [Edge.original, h]
      rw [hO]
      exact htail
    · have hO : e'.original =
          { tail := e'.head, head := e'.tail, minLen := e'.minLen, decl := e'.decl,
            reversed := false } := by
        simp [Edge.original, h]
      rw [hO]
      exact hhead
  have horgH : e'.original.head = t := by
    cases h : e'.reversed
    · have hO : e'.original =
          { tail := e'.tail, head := e'.head, minLen := e'.minLen, decl := e'.decl,
            reversed := false } := by
        simp [Edge.original, h]
      rw [hO]
      exact hhead
    · have hO : e'.original =
          { tail := e'.head, head := e'.tail, minLen := e'.minLen, decl := e'.decl,
            reversed := false } := by
        simp [Edge.original, h]
      rw [hO]
      exact htail
  have hidxT : comp.idxOf source.original.tail = t := by
    have h1 := congrArg Edge.tail hsrcEq
    rw [horgT] at h1
    exact h1.symm
  have hidxH : comp.idxOf source.original.head = t := by
    have h1 := congrArg Edge.head hsrcEq
    rw [horgH] at h1
    exact h1.symm
  have hmemT : source.original.tail ∈ comp := by
    cases h : source.reversed
    · simp [Edge.original, h]; exact htailMem
    · simp [Edge.original, h]; exact hheadMem
  have hmemH : source.original.head ∈ comp := by
    cases h : source.reversed
    · simp [Edge.original, h]; exact hheadMem
    · simp [Edge.original, h]; exact htailMem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemT
  have hjLt : j < comp.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjEq : comp[j] = source.original.tail :=
    Option.some.inj ((List.getElem?_eq_getElem hjLt).symm.trans hj)
  have hjt : j = t := by
    have h1 : comp.idxOf comp[j] = j := hnod.idxOf_getElem j hjLt
    rw [hjEq] at h1
    omega
  obtain ⟨j', hj'⟩ := List.mem_iff_getElem?.mp hmemH
  have hjLt' : j' < comp.length := (List.getElem?_eq_some_iff.mp hj').1
  have hjEq' : comp[j'] = source.original.head :=
    Option.some.inj ((List.getElem?_eq_getElem hjLt').symm.trans hj')
  have hjt' : j' = t := by
    have h1 : comp.idxOf comp[j'] = j' := hnod.idxOf_getElem j' hjLt'
    rw [hjEq'] at h1
    omega
  have hab : source.original.tail = source.original.head := by
    have e1 : comp[t]? = some source.original.tail := by
      rw [← hjt]
      exact hj
    have e2 : comp[t]? = some source.original.head := by
      rw [← hjt']
      exact hj'
    exact Option.some.inj (e1.symm.trans e2)
  have hselfSrc : source.tail = source.head := by
    cases h : source.reversed
    · simp [Edge.original, h] at hab
      exact hab
    · simp [Edge.original, h] at hab
      exact hab.symm
  obtain ⟨metric, labels, rawG, hm, hl, heRaw, hslot, hprepare, _hreserve⟩ :=
    measuredGraph_loop_reservation_before_prepare execution.graph_eq
  have heRaw' : graphEdgesFrom inp 0 inp.routes = .ok rawG.edges := heRaw
  have hbounds : ∀ e ∈ rawG.edges,
      e.tail < inp.boxes.length ∧ e.head < inp.boxes.length :=
    fun e he => lh_rawBounds inp inp.routes 0 rawG.edges heRaw' e he
  have hmemSrc : source ∈ rawG.edges.map (Compound.aliasEdge
      (inp.boxes.map fun box =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
          { box with role := .node } else box)) := by
    rw [hprepare] at hsource
    exact hsource
  have hkLt : source.tail < inp.boxes.length :=
    lh_globalSelfLoopLt (by simp) hbounds hmemSrc hselfSrc
  have hkEq : source.original.tail = source.tail := by
    cases h : source.reversed
    · simp [Edge.original, h]
    · simp [Edge.original, h, hselfSrc]
  have hjtK : j = t := by omega
  have hkt : comp[t]? = some source.tail := by
    rw [hkEq] at hj
    rw [hjtK] at hj
    exact hj
  refine ⟨source.tail, hkt, hkLt, ?_⟩
  have hglen : source.tail < execution.graph.nodes.length :=
    lh_compMemLt hcomp (List.mem_of_getElem? hkt)
  exact candLookup_graph hnt hkt hglen

/-- Copy of `PartPositiveContentProof.portGap_pos` (untracked draft; kept as a
private copy so this file imports only tracked modules): `portGap` is positive
in both profiles. -/
private theorem lh_portGap_pos {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 < P.portGap := by
  obtain ⟨B, hb, rfl⟩ := checkedParams_some h
  have hP : (B.forKind profile kind).portGap = B.portGap := rfl
  have hB : B.portGap = LayoutConst.port_gap.get profile := by
    unfold baseParams at hb
    have heq := Option.some.inj hb
    have hcon := congrArg Params.portGap heq
    simpa using hcon.symm
  rw [hP, hB]
  cases profile <;> decide

/-- Copy of `PartPositiveContentProof.sizeProperPorts_floor`: port sizing
floors every plain anchor at `portGap`. -/
private theorem lh_sizeProperPorts_floor {P : Params} (hpg : 0 < P.portGap) {p : Proper}
    {v : Nat} {nd : ProperNode} (hn : p.nodes[v]? = some nd)
    (hnd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ sized, (sizeProperPorts P p).nodes[v]? = some sized ∧
      sized.edge = nd.edge ∧ sized.node.border = 0 ∧ sized.dummy = false ∧
      P.portGap ≤ sized.node.w ∧ sized.node.h = nd.node.h ∧
      nd.node.w ≤ sized.node.w := by
  unfold sizeProperPorts
  simp only [List.getElem?_map, List.getElem?_zipIdx, hn, Option.map_some]
  split
  · next h => simp [hnd, hb] at h
  · refine ⟨_, rfl, rfl, hb, hnd, ?_, rfl, ?_⟩
    · apply Int.le_trans _ (Int.le_max_right _ _)
      have hk : (1 : Int) ≤
          (((max ((p.edges.filter fun edge => edge.head == 0 + v).map (·.tail)).eraseDups.length
            ((p.edges.filter fun edge => edge.tail == 0 + v).map (·.head)).eraseDups.length
            + 1 : Nat)) : Int) := by
        have h0 : (0 : Int) ≤
            (((max ((p.edges.filter fun edge => edge.head == 0 + v).map (·.tail)).eraseDups.length
            ((p.edges.filter fun edge => edge.tail == 0 + v).map (·.head)).eraseDups.length
            : Nat)) : Int) := Int.natCast_nonneg _
        omega
      calc P.portGap = 1 * P.portGap := (Int.one_mul _).symm
        _ ≤ _ * P.portGap := Int.mul_le_mul_of_nonneg_right hk (Int.le_of_lt hpg)
    · exact Int.le_max_left _ _

/-- Copy of `PartPositiveContentProof.coordinateGraph_floor`: the sizing floor
survives title reservation, border insertion, and display-path materialization. -/
private theorem lh_coordinateGraph_floor {P : Params} (hpg : 0 < P.portGap) {p : Proper}
    {v : Nat} {nd : ProperNode} (hp : p.nodes[v]? = some nd)
    (hnd : nd.dummy = false) (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraph P p).nodes[v]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧ out.dummy = false ∧
      P.portGap ≤ out.node.w ∧ out.node.h = nd.node.h ∧
      nd.node.w ≤ out.node.w := by
  obtain ⟨sized, hs, he, hb', hd, hfloor, hh, hw⟩ :=
    lh_sizeProperPorts_floor hpg hp hnd hb
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPorts P p)).nodes[v]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPorts P p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW).nodes[v]? =
        some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPorts P p)) P.clusterBorderW)).nodes[v]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraph materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split
  · next h => simp [hd] at h
  · exact ⟨_, rfl, he, hb', hd, hfloor, hh, hw⟩

/-- Copy of `PartPositiveContentProof.runProperFloor`: executed-run width floor
at a plain candidate index. Order-generic and fixed-size-generic. -/
private theorem lh_runProperFloor {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) (hpg : 0 < P.portGap)
    {v : Nat} {node : Node} (hnode : cg.nodes[v]? = some node)
    (hb : node.border = 0) :
    ∃ out, run.proper.nodes[v]? = some out ∧ out.node.border = 0 ∧
    P.portGap ≤ out.node.w := by
  obtain ⟨_ranks, p0, labeled, _q0, hn, hl, hc, _, _, _hproxy, _hdrop, _, _, _, _, _⟩ :=
    componentRun_spec h
  have hp0 : p0.nodes[v]? = some ⟨node, false, none, false⟩ :=
    normalize_node_record hn hnode
  have hlabeled : labeled.nodes[v]? = some ⟨node, false, none, false⟩ :=
    addLabelNodes_untouched_node hl hp0 rfl
  obtain ⟨out, hout, _hedge, hbout, _hdout, hfloor, _hhout, _hwout⟩ :=
    lh_coordinateGraph_floor hpg hlabeled rfl hb
  rw [hc] at hout
  have hproper : run.proper.nodes[v]? = some out :=
    componentRun_plain_node_dims h hout hbout
  exact ⟨out, hproper, hbout, hfloor⟩

/-- Plain self-loop owner frame positivity: the frame is the node rectangle,
whose width is floored at the positive `portGap`. -/
private theorem lh_plainOwner_frame_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb : node.border = 0) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w := by
  have hpg : 0 < execution.params.portGap := lh_portGap_pos execution.checked
  obtain ⟨out, hout, _hbout, hfloor⟩ := lh_runProperFloor hrun hpg hnode hb
  have hget : (componentCandidate execution.graph comp candidate).nodes.getD v default =
      node := by
    rw [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hfr : frameRect execution.params
        (componentCandidate execution.graph comp candidate) run v =
      nodeRect (componentCandidate execution.graph comp candidate) run v :=
    frameRect_of_border_zero hget hb
  have hgetP : run.proper.nodes.getD v default = out := by
    rw [List.getD_eq_getElem?_getD, hout, Option.getD_some]
  have hnr : (nodeRect (componentCandidate execution.graph comp candidate) run v).w =
      out.node.w := by
    simp only [nodeRect, hgetP]
  rw [hfr, hnr]
  omega

/-- Copy of the `fold_max_width_nonneg` helper private to
`PartFrameWitnessProof` (needed by the group-owner width proof below). -/
private theorem lh_fold_max_width_nonneg_aux (ls : List Measure.Line) :
    ∀ acc : Int, 0 ≤ acc →
      0 ≤ ls.foldl (fun w line => max w line.width) acc := by
  intro acc ha
  induction ls generalizing acc with
  | nil => simpa using ha
  | cons _ _ ih =>
    simp only [List.foldl_cons]
    exact ih _ (Int.le_trans ha (Int.le_max_left _ _))

private theorem lh_fold_max_width_nonneg (ls : List Measure.Line) :
    0 ≤ ls.foldl (fun w line => max w line.width) 0 :=
  lh_fold_max_width_nonneg_aux ls 0 (Int.le_refl _)

/-- Group self-loop owner frame positivity: height from the title reservation,
width from the side borders. Adapted from `PartFrameWitnessProof.top_frame_pos`
with `hrun` generalized to any `orderOptions` (every lemma it uses —
`componentRun_group_frame_height_ge`, `measured_component_caption_border_interval`
— is order-generic). -/
private theorem lh_groupOwner_frame_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb : node.border = -2) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w ∧
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h := by
  obtain ⟨orig, horig, hsource⟩ :=
    componentCandidate_nonplain_source hnode (by omega)
  obtain ⟨_, _, _, _, hpath⟩ :=
    measuredGraph_group_origin execution.graph_eq hsource hb
  have hself : node.clusterPath.contains node.decl = true := by rw [hpath]; simp
  have howner : node.clusterPath.getLast? = some node.decl := by rw [hpath]; simp
  have hkeyD : comp.getD v 0 = orig := by simp [List.getD, horig]
  obtain ⟨_, capH⟩ := actual_title_caption_fit execution.graph_eq hnode hb
  rw [hkeyD] at capH
  have hpad : 0 < execution.params.clusterPad :=
    checkedParams_clusterPad_pos execution.checked
  have hlineH : 0 < execution.params.lineH :=
    checkedParams_lineH_pos execution.checked
  have hnodepos : 0 < node.h := by
    cases hdir : o.direction with
    | TB =>
      simp only [hdir] at capH
      have h1 : (1 : Int) ≤ max 1 (((execution.lines.getD orig []).length : Int)) :=
        Int.le_max_left _ _
      have h2 : (1 : Int) * execution.params.lineH ≤
          max 1 (((execution.lines.getD orig []).length : Int)) *
            execution.params.lineH :=
        Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hlineH)
      omega
    | BT =>
      simp only [hdir] at capH
      have h1 : (1 : Int) ≤ max 1 (((execution.lines.getD orig []).length : Int)) :=
        Int.le_max_left _ _
      have h2 : (1 : Int) * execution.params.lineH ≤
          max 1 (((execution.lines.getD orig []).length : Int)) *
            execution.params.lineH :=
        Int.mul_le_mul_of_nonneg_right h1 (Int.le_of_lt hlineH)
      omega
    | LR =>
      simp only [hdir] at capH
      have hf := lh_fold_max_width_nonneg (execution.lines.getD orig [])
      omega
    | RL =>
      simp only [hdir] at capH
      have hf := lh_fold_max_width_nonneg (execution.lines.getD orig [])
      omega
  have hge := componentRun_group_frame_height_ge hrun hnode hb hself
    (th := node.h - execution.params.clusterPad) (by omega)
  have hle : node.h ≤ (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h := by omega
  have hposH : 0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).h :=
    Int.lt_of_lt_of_le hnodepos hle
  obtain ⟨_, left, right, _, hleft, hright, _, _⟩ :=
    measured_component_caption_border_interval execution.graph_eq hcomp hrun hnode hb
  let borders := run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some node.decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none
  have hleftMem : Labels.rectAt run.proper run.xs run.ys left ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, left), List.mem_zipIdx_iff_getElem?.mpr hleft, ?_⟩
    simp [titleF, hb, howner]
  have hrightMem : Labels.rectAt run.proper run.xs run.ys right ∈ borders := by
    apply List.mem_filterMap.mpr
    refine ⟨(_, right), List.mem_zipIdx_iff_getElem?.mpr hright, ?_⟩
    simp [titleF, hb, howner]
  have hframeW : (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w =
      (boundsOf borders []).right - (boundsOf borders []).minX :=
    frameRect_group_width_eq_horizontal_span hnode hb
  have hhi := rect_right_le_boundsOf_right borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hlo := boundsOf_minX_le_rect_x borders []
    (Labels.rectAt run.proper run.xs run.ys right) hrightMem
  have hwR : (Labels.rectAt run.proper run.xs run.ys right).w =
      execution.params.clusterBorderW := by
    simp only [Labels.rectAt, Labels.labelRect, RouteImpl.nodeW, hright,
      OrderImpl.borderRight]
  have hcbw : 1 ≤ execution.params.clusterBorderW :=
    checkedParams_clusterBorderW_ge_one execution.checked
  have hposW : 0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w := by
    rw [hframeW]
    omega
  exact ⟨hposW, hposH⟩

/-- Every self-loop owner has a positive-width frame: plain owners via the
port-gap floor, group owners via the border-marker hull. Used for the owner
width positivity in the foreign case. -/
private theorem lh_loopOwner_frame_pos {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    {v : Nat} {node : Node}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (het : ∃ e ∈ (componentCandidate execution.graph comp candidate).edges,
      e.tail = v ∧ e.head = v) :
    0 < (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run v).w := by
  obtain ⟨e', hmem, htail, hhead⟩ := het
  obtain ⟨key_t, hkeyt, hkeytLt, hntG⟩ :=
    lh_loopOwnerKey execution hcomp hnode hmem htail hhead
  rcases component_node_border_plain_or_group execution hkeytLt hntG with hb0 | hb2
  · exact lh_plainOwner_frame_pos execution hrun hnode hb0
  · exact (lh_groupOwner_frame_pos execution hcomp hrun hnode hb2).1

/-- Executed loop-footprint group-hull clearance. -/
theorem loopFootprintGroupHullClear_of_run
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      orderOptions = .ok run)
    (hx : ForeignBorderChainXAligned)
    (hright : LoopHullRightCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured)
    (hrightN : LoopHullRightNeighborCover execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured) :
    LoopFootprintGroupHullClear execution.params
      (componentCandidate execution.graph comp candidate) run execution.measured := by
  intro t pos het hpos gn hg hgrp
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hgroups : ForeignBorderSpansSeparated :=
    foreignBorderSpansSeparated foreignClusterRankSpans' foreignBorderLayerOrder' hx
  have hothers : ForeignNonGroupSpansClear :=
    foreignNonGroupSpansClear bracketMarkersAtRank' plainClearOfSideMarker' halign
  have hforeign : ForeignSpansClear execution.params
      (componentCandidate execution.graph comp candidate) run :=
    foreignSpansClear_of_run hgroups hothers execution.graph_eq hlines hwf hframed
      hcomp hrun
  have htLen : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    loopTail_bounded execution hcomp het
  have hcgLen : (componentCandidate execution.graph comp candidate).nodes.length =
      comp.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have htLt : t < (componentCandidate execution.graph comp candidate).nodes.length :=
    htLen
  have hposComp : pos < comp.length := hcgLen ▸ hpos
  obtain ⟨nt, hnt⟩ : ∃ n,
      (componentCandidate execution.graph comp candidate).nodes[t]? = some n :=
    ⟨_, List.getElem?_eq_getElem htLt⟩
  obtain ⟨e', hmem, htail, hhead⟩ := het
  obtain ⟨key_t, hkeyt, hkeytLt, hntG⟩ :=
    lh_loopOwnerKey execution hcomp hnt hmem htail hhead
  have htb : nt.border = 0 ∨ nt.border = -2 :=
    component_node_border_plain_or_group execution hkeytLt hntG
  have hboxT : inp.boxes[key_t]? = some (inp.boxes[key_t]) :=
    List.getElem?_eq_getElem hkeytLt
  obtain ⟨key_p, hpkey⟩ : ∃ k, comp[pos]? = some k :=
    ⟨_, List.getElem?_eq_getElem hposComp⟩
  have hglen : key_p < execution.graph.nodes.length :=
    lh_compMemLt hcomp (List.mem_of_getElem? hpkey)
  have hgg : execution.graph.nodes[key_p]? = some gn :=
    candLookup_graph hg hpkey hglen
  obtain ⟨box_p, hbox_p, hdecl_p, hpath_p⟩ :=
    execution.group_node_path_source hgg hgrp
  have hlenP : key_p < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox_p).1
  by_cases htp : pos = t
  · subst htp
    exact Or.inl (fun hm =>
      (loopFootprint_self_pos _) ((Rect.meetsInterior_comm _ _).mp hm))
  · have hdeclNe : gn.decl ≠ nt.decl :=
      candDecl_ne_of_idx_ne execution hcomp hnt hkeyt hkeytLt hg hpkey hlenP htp
    by_cases hanc : nt.clusterPath.contains gn.decl = true
    · rcases htb with h0 | h2
      · exact Or.inr
          (stepPlainStrict execution hwf hcomp hrun hnt h0
            ⟨e', hmem, htail, hhead⟩ hg hgrp hanc hright)
      · have hmemAnc : gn.decl ∈ nt.clusterPath := by
          have h := hanc
          rw [List.contains_eq_mem, decide_eq_true_eq] at h
          exact h
        have hpareNe : (inp.boxes[key_t]).parent ≠ "" :=
          walkParentNe execution hcomp hnt hkeyt hboxT h2 hg hpkey hlenP hmemAnc htp
        obtain ⟨parentKey, parentBox, parentIdx, top, hparentBox, hparentRef,
            hparentIdx, htopCg, htopBorder, htopDeclEq⟩ :=
          setupParentLink execution hwf hframed hcomp hkeytLt
            (List.mem_of_getElem? hkeyt) hboxT hpareNe
        have hcl := walkClStep (parentBox := parentBox) execution hwf hnt hkeyt
          hboxT h2 htopCg hparentIdx hparentBox hparentRef hpareNe htopBorder
        have htopG : execution.graph.nodes[parentKey]? = some top :=
          candLookup_graph htopCg hparentIdx
            (lh_compMemLt hcomp (List.mem_of_getElem? hparentIdx))
        obtain ⟨box_top, hbox_top, hdecl_top, hpath_top⟩ :=
          execution.group_node_path_source htopG htopBorder
        have htopMemSelf : top.decl ∈ top.clusterPath := by
          rw [hpath_top, hdecl_top]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        have hinsideTop : nt.clusterPath.contains top.decl = true := by
          have hmem : top.decl ∈ nt.clusterPath := by
            rw [hcl]
            exact List.mem_append_left _ htopMemSelf
          rw [List.contains_eq_mem, decide_eq_true_eq]
          exact hmem
        have hlenPk : parentKey < inp.boxes.length :=
          (List.getElem?_eq_some_iff.mp hparentBox).1
        have hstep := stepGroupStrict execution hwf hframed hcomp hrun hnt h2
          hkeyt hkeytLt hboxT ⟨e', hmem, htail, hhead⟩ htopCg htopBorder hparentIdx
          hlenPk hparentBox hparentRef hpareNe hinsideTop hright
        by_cases hpp : parentIdx = pos
        · subst hpp
          exact Or.inr hstep
        · have hmemTop : gn.decl ∈ top.clusterPath := by
            rw [hcl] at hmemAnc
            rcases List.mem_append.mp hmemAnc with hL | hR
            · exact hL
            · have hEq : gn.decl = nt.decl := List.mem_singleton.mp hR
              exact absurd hEq hdeclNe
          have hchain := walkStrictFrom execution hwf hframed hcomp hrun hg
            hpkey hlenP htopCg htopBorder hparentIdx hlenPk hparentBox hmemTop
            (Ne.symm hpp)
          exact Or.inr (Rect.StrictInside.trans' hchain hstep)
    · by_cases hnest : gn.clusterPath.contains nt.decl = true
      · have hmemT : nt.decl ∈ gn.clusterPath := by
          have h := hnest
          rw [List.contains_eq_mem, decide_eq_true_eq] at h
          exact h
        have hcont := walkContainedUp (tkey := key_t) execution hwf hframed hcomp hrun
          hnt hkeyt hkeytLt hg hgrp hpkey hlenP hbox_p hmemT (Ne.symm htp)
        have hPPt : frameRect execution.params
            (componentCandidate execution.graph comp candidate) run t =
            frameRect default
              (componentCandidate execution.graph comp candidate) run t := rfl
        have hle : (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).x +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).w ≤
            (loopFootprint (componentCandidate execution.graph comp candidate) run
              execution.measured t).x := by
          have h4 := hcont.2.1
          rw [hPPt] at h4
          unfold loopFootprint
          dsimp only
          omega
        exact Or.inl (not_meetsInterior_of_right_le hle)
      · have hnestF : gn.clusterPath.contains nt.decl = false := by
          cases h : gn.clusterPath.contains nt.decl <;> simp_all
        have hancF : nt.clusterPath.contains gn.decl = false := by
          cases h : nt.clusterPath.contains gn.decl <;> simp_all
        have hD := hforeign pos t gn nt hg hnt hgrp hdeclNe hancF hnestF
        have hD' : Disjoint
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t)
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos) :=
          fun hm => hD ((Rect.meetsInterior_comm _ _).mp hm)
        have hfpY : (loopFootprint
            (componentCandidate execution.graph comp candidate) run
            execution.measured t).y =
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t).y := rfl
        have hfpH : (loopFootprint
            (componentCandidate execution.graph comp candidate) run
            execution.measured t).h =
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t).h := rfl
        by_cases hyl : (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t).y +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t).h ≤
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).y
        · have hle : (loopFootprint
              (componentCandidate execution.graph comp candidate) run
              execution.measured t).y +
            (loopFootprint
              (componentCandidate execution.graph comp candidate) run
              execution.measured t).h ≤
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).y := by
            rw [hfpY, hfpH]; exact hyl
          have hnm : ¬ (loopFootprint
              (componentCandidate execution.graph comp candidate) run
              execution.measured t).meetsInterior (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos) :=
            not_meetsInterior_of_below hle
          exact Or.inl (fun hm => hnm ((Rect.meetsInterior_comm _ _).mp hm))
        · by_cases hyu : (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).y +
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run pos).h ≤
            (frameRect execution.params
              (componentCandidate execution.graph comp candidate) run t).y
          · have hle2 : (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos).y +
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos).h ≤
              (loopFootprint
                (componentCandidate execution.graph comp candidate) run
                execution.measured t).y := by
              rw [hfpY]; exact hyu
            have hnm : ¬ (loopFootprint
                (componentCandidate execution.graph comp candidate) run
                execution.measured t).meetsInterior (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos) :=
              not_meetsInterior_of_above hle2
            exact Or.inl (fun hm => hnm ((Rect.meetsInterior_comm _ _).mp hm))
          · have hdim := componentRun_dims_nonneg hrun
            have hcovT := componentRun_original_nodes_covered hrun t htLen
            have hcovP := componentRun_original_nodes_covered hrun pos hpos
            have hFw := (frameRect_dims_nonneg execution.params
              (componentCandidate execution.graph comp candidate) run t hdim
              hcovT).1
            have hHw := (frameRect_dims_nonneg execution.params
              (componentCandidate execution.graph comp candidate) run pos hdim
              hcovP).1
            have hFwn : 0 < (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run t).w :=
              lh_loopOwner_frame_pos execution hcomp hrun hnt ⟨e', hmem, htail, hhead⟩
            by_cases hyM : max (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).y
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).y <
                min ((frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).y +
                  (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).h)
                ((frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).y +
                  (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).h)
            · by_cases hFL : (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).x +
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).w ≤
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).x
              · have hyOvl : ¬ ((loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).y +
                  (loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).h ≤
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).y ∨
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).y +
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).h ≤
                  (loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).y) := by
                  rw [hfpY, hfpH]
                  intro hCon
                  rcases hCon with h1 | h2
                  · exact hyl h1
                  · exact hyu h2
                have hni1 : gn.decl ∉ nt.clusterPath := by
                  intro hm
                  have hT : nt.clusterPath.contains gn.decl = true := by
                    rw [List.contains_eq_mem, decide_eq_true_eq]
                    exact hm
                  rw [hT] at hancF
                  exact Bool.noConfusion hancF
                have hni2 : nt.decl ∉ gn.clusterPath := by
                  intro hm
                  have hT : gn.clusterPath.contains nt.decl = true := by
                    rw [List.contains_eq_mem, decide_eq_true_eq]
                    exact hm
                  rw [hT] at hnestF
                  exact Bool.noConfusion hnestF
                have hR3 := hrightN t nt hnt ⟨e', hmem, htail, hhead⟩ pos gn hg hgrp htp
                  hdeclNe.symm hni1 hni2 hFL hyOvl
                have hleR : (loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).x +
                  (loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).w ≤
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).x := hR3
                exact Or.inl (not_meetsInterior_of_left_le hleR)
              · have hfx : (loopFootprint
                  (componentCandidate execution.graph comp candidate) run
                  execution.measured t).x =
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).x +
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).w := rfl
                by_cases hHL : (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).x +
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run pos).w ≤
                (frameRect execution.params
                  (componentCandidate execution.graph comp candidate) run t).x
                · have hle2 : (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).x +
                  (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).w ≤
                  (loopFootprint
                    (componentCandidate execution.graph comp candidate) run
                    execution.measured t).x := by
                    rw [hfx]; omega
                  exact Or.inl (not_meetsInterior_of_right_le hle2)
                · by_cases hHwP : 0 < (frameRect execution.params
                    (componentCandidate execution.graph comp candidate) run pos).w
                  · have hxM : max (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run t).x
                      (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).x <
                      min ((frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run t).x +
                      (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run t).w)
                      ((frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).x +
                      (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).w) := by
                      omega
                    have hM : (frameRect execution.params
                        (componentCandidate execution.graph comp candidate) run t).meetsInterior
                        (frameRect execution.params
                        (componentCandidate execution.graph comp candidate) run pos) :=
                      ⟨hxM, hyM⟩
                    exact False.elim (hD' hM)
                  · have hHw0 : (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).w = 0 := by
                      omega
                    have hle2 : (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).x +
                      (frameRect execution.params
                      (componentCandidate execution.graph comp candidate) run pos).w ≤
                      (loopFootprint
                      (componentCandidate execution.graph comp candidate) run
                      execution.measured t).x := by
                      rw [hfx]; omega
                    exact Or.inl (not_meetsInterior_of_right_le hle2)
            · have hnm : ¬ (loopFootprint
                (componentCandidate execution.graph comp candidate) run
                execution.measured t).meetsInterior (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run pos) := by
                intro hm
                obtain ⟨-, hyM'⟩ := hm
                exact hyM (by omega)
              exact Or.inl (fun hm => hnm ((Rect.meetsInterior_comm _ _).mp hm))
