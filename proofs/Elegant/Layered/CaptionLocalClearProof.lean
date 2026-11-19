 import Elegant.Layered.PartCaptionRunClearProof
 import Elegant.Layered.StrictMemberFrameProof
 import Elegant.Layered.BottomClearanceNesting
 import Elegant.Layered.BottomSeamsRank
 import Elegant.Layered.GroupWidthFacts
 import Elegant.Layered.CoordGraph
 import Elegant.Layered.ForeignBorderSpansProof
 import Elegant.Layered.RouteProxyStart
 import Elegant.Layered.GroupFrameSizingFacts
 import Elegant.Layered.PipelineFacts
 import Elegant.Layered.CaptionWidthFacts
 import Elegant.Layered.LabelsC8bFacts
 import Elegant.Layered.ParentContainmentFacts
 import Elegant.Layered.CgShape
 import Elegant.Layered.FrameClearanceFacts
 import Elegant.Layered.Coords
 import Elegant.Layered.Order
 import Elegant.Layered.ExecutedFrameClearanceFacts
 import Elegant.Layered.Pipeline

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Executed caption-local clearance

`PartCaptionRunClearProof.CaptionLocalClear` quantifies over any `P`, input and
lines. This module states the executed form (with `P := execution.params` and
`lines := execution.lines`) and proves it case by case:

* (1) self strictness: the top edge is `captionSelfTop` (proved, no residual);
  the left/right edges are `CaptionSelfSidesStrict` and the bottom edge is
  `CaptionSelfBottomStrict` (narrow residuals: two and one inequalities).
* (2a) same declaration: a `-2` position names the same group frame, so (1)
  applies (proved); a non-`-2` position with the same declaration (the bottom
  marker) is `CaptionSameDeclMarkerDisjoint` (residual: one disjointness).
* (2b) member or descendant (`fNode.clusterPath.contains tNode.decl`, distinct
  declarations) is `CaptionMemberDescDisjoint` (residual: one disjointness).
* (2c) ancestor (`tNode.clusterPath.contains fNode.decl`, distinct
  declarations) is proved from (1) plus `CaptionAncestorFrameStrict`, the
  frame-only nesting conclusion for that pair (residual: no caption content).

Each residual is strictly simpler than the target conjunct it serves (a
strict subset of the inequalities, or a single case with caption content
removed). All five are exercised by
`proofs/wip/Probe/PartCaptionRunClear.lean` (11 inputs, 6 direction/profile
configs): 510 self-strict pairs, 2400 related pairs (of which 180
ancestor-frame, 180 descendant-frame and 1530 member), zero violations.

Note on `ChildFrameStrictVertical`: case (2c) assumes the frame-nesting
conclusion `CaptionAncestorFrameStrict` directly instead. Applying
`SceneExecution.component_child_frame_strictInside` would additionally need
the `ModelBox` parent evidence (`hparentBox`/`hchildBox`/`hparentRef`), a
member-free discharge of `ParentFrameRightEdgePos`, and induction over the
ancestor chain; none of that is available, so the designated single-pair
residual cannot be connected and the nesting conclusion is assumed as the
narrower frame-only residual.
-/

/-- Residual (1, horizontal): the transported caption keeps a positive gap
from the left and right edges of its own group frame. Two of the four
`StrictInside` inequalities. Probe: 510 self-strict pairs, zero violations.
Missing: strict title-copy-vs-side-marker separation on the title layer
(`cluster_all_pairs_separated` applied to the title copy and the side
markers, combined with side-marker containment). -/
def CaptionSelfSidesStrict (P : Params) (cg : Graph) (run : Run)
    (o : Options) (lines : List (List Measure.Line)) (comp : List Nat) : Prop :=
  ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles P cg run →
    cg.nodes[i]? = some tNode → tNode.border = -2 →
    (frameRect P cg run i).x < (transportCaption P o lines comp i stored0).x ∧
    (transportCaption P o lines comp i stored0).x +
        (transportCaption P o lines comp i stored0).w <
      (frameRect P cg run i).x + (frameRect P cg run i).w

/-- Residual (1, bottom): the transported caption ends strictly above the
bottom edge of its own group frame. One of the four `StrictInside`
inequalities. Probe: 510 self-strict pairs, zero violations. Missing:
title-band-bottom strictly above the bottom-marker rank
(`rankAxis_band_top_strict` with the title layer and the bottom layer). -/
def CaptionSelfBottomStrict (P : Params) (cg : Graph) (run : Run)
    (o : Options) (lines : List (List Measure.Line)) (comp : List Nat) : Prop :=
  ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles P cg run →
    cg.nodes[i]? = some tNode → tNode.border = -2 →
    (transportCaption P o lines comp i stored0).y +
        (transportCaption P o lines comp i stored0).h <
      (frameRect P cg run i).y + (frameRect P cg run i).h

/-- Residual (2a, marker): a same-declaration position that is not a group
frame (the bottom marker) is disjoint from the transported caption. One
case, one disjointness. Probe: covered by the 2400 related pairs, zero
violations. Missing: the bottom-marker band lies strictly below the title
band at a zero-height marker rect. -/
def CaptionSameDeclMarkerDisjoint (P : Params) (cg : Graph) (run : Run)
    (o : Options) (lines : List (List Measure.Line)) (comp : List Nat) : Prop :=
  ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
    (i, stored0) ∈ componentTitles P cg run →
    cg.nodes[i]? = some tNode → tNode.border = -2 →
    ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
      cg.nodes[pos]? = some fNode → tNode.decl = fNode.decl →
      fNode.border ≠ -2 →
      frameRect P cg run pos = g0 →
      Disjoint g0 (transportCaption P o lines comp i stored0)

 /-- Residual (2b-desc): a descendant-group position (path contains the title
 group, distinct declarations, not a plain member) is disjoint from the
 transported caption. Plain members (`border = 0`) are handled by the proved
 `captionPlainMemberClear_proved`; this residual covers the remaining
 descendant frames. One case, one disjointness. Probe: 180 descendant-frame
 pairs, zero violations. Missing: descendant top rank above parent top rank
 (transitive child-interval induction) plus descendant-hull rank lower bound. -/
 def CaptionMemberDescDisjoint (P : Params) (cg : Graph) (run : Run)
     (o : Options) (lines : List (List Measure.Line)) (comp : List Nat) : Prop :=
   ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
     (i, stored0) ∈ componentTitles P cg run →
     cg.nodes[i]? = some tNode → tNode.border = -2 →
     ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
       cg.nodes[pos]? = some fNode →
       tNode.decl ≠ fNode.decl →
       fNode.clusterPath.contains tNode.decl = true →
       fNode.border ≠ 0 →
       frameRect P cg run pos = g0 →
       Disjoint g0 (transportCaption P o lines comp i stored0)

 /-- Residual (2c, frame nesting): an ancestor position frames the child group
 frame strictly. Pure frames, no caption content, hence strictly simpler than
 the target conjunct. Probe: 180 ancestor-frame pairs, zero violations.
 Missing: transitive ancestor nesting (induction over the ancestor chain with
 single-step `component_child_frame_strictInside`, box-parent derivation from
 `clusterPath` containment, and a member-free `ParentFrameRightEdgePos`
 discharge). -/
 def CaptionAncestorFrameStrict (P : Params) (cg : Graph) (run : Run) : Prop :=
   ∀ (i pos : Nat) (tNode fNode : Node),
     cg.nodes[i]? = some tNode → tNode.border = -2 →
     cg.nodes[pos]? = some fNode →
     tNode.decl ≠ fNode.decl →
     tNode.clusterPath.contains fNode.decl = true →
     (frameRect P cg run pos).StrictInside (frameRect P cg run i)

/-- Strict-inside transitivity for the ancestor case. -/
theorem captionStrictInside_trans {o m i : Rect}
    (h1 : o.StrictInside m) (h2 : m.StrictInside i) : o.StrictInside i := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Copy of the private `PartCaptionRunClearProof.strictInside_contained`:
strict inside implies containment. -/
private theorem strictInside_contained_copy {o i : Rect}
    (h : o.StrictInside i) : o.Contained i := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

 /-! ## Private transports (copies of private lemmas elsewhere)

 Copies are required because private lemmas cannot be imported; each copy is
 proved exactly as the original. -/

 /-- Copied from `StrictMemberFrameProof.run_rank_eq_coordinate` (itself copied
 from the private `GroupTopFacts.group_top_rank_eq_coordinate`): executed
 proper rank equals coordinate rank. -/
 private theorem run_rank_eq_coordinate_copy {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     (i : Nat) :
     rk run.proper.rank i = rk run.coordinateProper.rank i := by
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
   rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

 /-- Copied from the private `GroupTopFacts.group_top_coordinate_record`:
 coordinate record of a `-2` graph node. -/
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

 /-- Copied from the private `GroupTopFacts.group_top_proper_clusterPath`. -/
 private theorem proper_top_proper_clusterPath_copy {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     {v : Nat} {coord : ProperNode}
     (hcoord : run.coordinateProper.nodes[v]? = some coord)
     (hb : coord.node.border = -2) :
     ∃ p : ProperNode, run.proper.nodes[v]? = some p ∧
       p.node.clusterPath = coord.node.clusterPath := by
   obtain ⟨_, span, _, _, hproper, _, _⟩ := componentRun_proxy_interval hrun hcoord (Or.inl hb)
   exact ⟨{ coord with node := { coord.node with w := span.hi - span.lo } }, hproper, rfl⟩

 /-- Copied from the private `GroupTopFacts.group_top_decl_path`. -/
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

 /-- Copied from the private
 `PartCaptionRunClearProof.captionTitles_keys_nodup`: titles install at most
 one rect per component index. -/
 private theorem captionTitles_keys_nodup_copy (P : Params) (cg : Graph) (run : Run) :
     ((componentTitles P cg run).map Prod.fst).Nodup := by
   let emit : Node × Nat → Option (Nat × Rect) := fun top => do
     if top.1.border != -2 then none else do
       let title ← run.proper.nodes.zipIdx.find? (fun q =>
         q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath)
       let frame := frameRect P cg run top.2
       pure (top.2, Rect.mk
         (run.xs.getD title.2 0 - Int.fdiv title.1.node.w 2)
         (frame.y + P.clusterPad) top.1.w (top.1.h - P.clusterPad))
   have identity : ∀ top caption, emit top = some caption → caption.1 = top.2 := by
     intro top caption he
     unfold emit at he
     split at he
     · contradiction
     · cases hf : run.proper.nodes.zipIdx.find? (fun q =>
         q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
       | none => simp [hf] at he
       | some title =>
         simp [hf] at he
         subst caption
         rfl
   have hindices : (cg.nodes.zipIdx.map Prod.snd).Nodup := by
     rw [List.zipIdx_map_snd]
     exact List.nodup_range'
   have hp := List.pairwise_map.mp hindices
   change ((componentTitles P cg run).map Prod.fst).Pairwise (· ≠ ·)
   rw [List.pairwise_map]
   change (cg.nodes.zipIdx.filterMap emit).Pairwise (fun a b => a.1 ≠ b.1)
   apply List.Pairwise.filterMap emit _ hp
   intro a b hne ca hca cb hcb
   rw [identity a ca hca, identity b cb hcb]
   exact hne

 /-! ## The top band contains the caption

 Proved first since R2, R3 and R4 all use the upper bound. Only the upper
 bound is established (the caption bottom lies at or before the top band
 bottom); the lower edge of the caption is not bounded and is not needed,
 since everything compared against the caption lies strictly below it. -/

 /-- The transported caption ends at or before the bottom of its own top
 marker rank band, and the group frame starts at or before the band top.
 The band height covers the node height because the border-`3` title
 reservation (same height) sits in the top layer at the title rank, which
 equals the top rank. -/
 theorem captionInTopBand_executed {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {i : Nat} {stored0 : Rect} {tNode : Node}
     (hmem : (i, stored0) ∈ componentTitles execution.params
       (componentCandidate execution.graph comp candidate) run)
     (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
     (hborder : tNode.border = -2) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y ≤
       run.top.getD (rk run.coordinateProper.rank i).toNat 0 ∧
     (transportCaption execution.params o execution.lines comp i stored0).y +
       (transportCaption execution.params o execution.lines comp i stored0).h ≤
       run.top.getD (rk run.coordinateProper.rank i).toNat 0 +
         CoordsImpl.layerHeight run.coordinateProper
           (run.layers.getD (rk run.coordinateProper.rank i).toNat []) := by
   have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   have rEqT := run_rank_eq_coordinate_copy hrun i
   obtain ⟨tcoord, htcoord, htb, htd, htpath⟩ :=
     proper_top_coordinate_record_copy hrun hnode hborder
   obtain ⟨tprop, htprop, htpropP⟩ :=
     proper_top_proper_clusterPath_copy hrun htcoord htb
   have hdeclT : tNode.clusterPath.contains tNode.decl = true :=
     (proper_top_decl_path_copy execution.graph_eq hnode hborder).2
   have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD i default = tNode := by
     simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD i default).border = -2 := by
     rw [hgroupGet]
     exact hborder
   have htcontains : tprop.node.clusterPath.contains tNode.decl = true := by
     rw [htpropP, htpath]
     exact hdeclT
   have htqmem : (tprop, i) ∈ run.proper.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr htprop
   have htcontains' : (tprop, i).1.node.clusterPath.contains
       ((componentCandidate execution.graph comp candidate).nodes.getD i default).decl = true := by
     rw [hgroupGet]
     exact htcontains
   have htopLe : (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y ≤
       (Labels.rectAt run.proper run.xs run.ys i).y :=
     (frameRect_member_vertical hframeGroup htqmem htcontains').1
   have hTopY : (Labels.rectAt run.proper run.xs run.ys i).y = run.ys.getD i 0 := rfl
   have hTopProxy : run.ys.getD i 0 =
       run.top.getD (rk run.proper.rank i).toNat 0 :=
     componentRun_group_proxy_ys_eq_top hrun hnode hborder hindexLt
   have hframeLe : (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y ≤
       run.top.getD (rk run.coordinateProper.rank i).toNat 0 := by
     rw [← rEqT]
     omega
   obtain ⟨titleP, _, _, _, _, hplaceP⟩ :=
     componentRun_group_caption_placement_source hrun hnode hborder
   have hnodup := captionTitles_keys_nodup_copy execution.params
     (componentCandidate execution.graph comp candidate) run
   have huniq : stored0 = Rect.mk
       (run.xs.getD titleP.2 0 - Int.fdiv titleP.1.node.w 2)
       ((frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
         execution.params.clusterPad) tNode.w (tNode.h - execution.params.clusterPad) :=
     captionTitles_at_inj hnodup hmem hplaceP
   have hy0 : stored0.y =
       (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
         execution.params.clusterPad := congrArg Rect.y huniq
   have hth : (transportCapSize execution.params o execution.lines comp i).2 +
       execution.params.clusterPad ≤ tNode.h := by
     have hfit2 := (actual_title_caption_fit execution.graph_eq hnode hborder).2
     cases hdir : o.direction <;> simp_all [transportCapSize, titleCaptionSize]
   obtain ⟨v, hcoordV, hproperV⟩ :=
     componentRun_group_title_width_source hrun hnode hborder
   obtain ⟨rrB, labeledB, bottomB, hrrB, hcB, hkB, hreadyB, hrecordsB, hranksB, htitledB, hbottomB⟩ :=
     componentRun_group_bottom_source execution.graph_eq hcomp hrun hnode hborder
   have halignedB := source_alignment_of_titled hreadyB.2.2.2.1
   have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
     (measuredGraph_shape execution.graph_eq) candidate
   have htitleCoord : (coordinateGraph execution.params labeledB).nodes[v]? = some
       (copyF (⟨tNode, false, none, false⟩, i)) := by
     rw [hcB]
     exact hcoordV
   have htitleBorder3 : (copyF (⟨tNode, false, none, false⟩, i)).node.border = 3 := rfl
   have htitlePath : (copyF (⟨tNode, false, none, false⟩, i)).node.clusterPath =
       tNode.clusterPath := rfl
   obtain ⟨origIdx, original, horiginal, hOrigBorder, _, _, hpathEq, htitleRank⟩ :=
     coordinateGraph_title_rank_source hkB hshape halignedB htitleCoord htitleBorder3
   have hidxEq : origIdx = i := labeled_topUnique hkB hshape horiginal
     (hrecordsB i tNode hnode) hOrigBorder hborder (hpathEq.symm.trans htitlePath)
   have hsourceBound : i < labeledB.rank.length := by
     have hn := (List.getElem?_eq_some_iff.mp (hrecordsB i tNode hnode)).1
     have hlen := halignedB
     omega
   have hsourceRank : labeledB.rank[i]? = some labeledB.rank[i] :=
     List.getElem?_eq_getElem hsourceBound
   have htitledRank := titled_rank_record (P := execution.params) hsourceRank
   have hsourceToTitled : rk labeledB.rank i =
       rk (titleReservations (sizeProperPorts execution.params labeledB)).rank i := by
     simp only [rk, List.getD_eq_getElem?_getD, hsourceRank, htitledRank, Option.getD_some]
   have htopRank := prepared_titled_original_rk (P := execution.params) hrrB hranksB hindexLt
   have eTop : rk run.coordinateProper.rank i = rk rrB.ranks i := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hindexLt
     rw [hcB] at h2
     exact h2
   have htitleRankEq : rk run.coordinateProper.rank v = rk run.coordinateProper.rank i := by
     have h1 : rk (coordinateGraph execution.params labeledB).rank v =
         rk labeledB.rank origIdx := htitleRank
     rw [hcB] at h1
     rw [hidxEq] at h1
     rw [h1, hsourceToTitled, htopRank.1, ← eTop]
   have rEqV := run_rank_eq_coordinate_copy hrun v
   have hvLen : v < run.proper.nodes.length :=
     (List.getElem?_eq_some_iff.mp hproperV).1
   have hindexLen : i < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun i hindexLt
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
     componentRun_spec hrun
   have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
   have hrkEq : rk run.proper.rank v = rk run.proper.rank i := by
     rw [rEqV, rEqT]
     exact htitleRankEq
   have htoNatEq : (rk run.proper.rank v).toNat = (rk run.proper.rank i).toNat := by
     rw [hrkEq]
   obtain ⟨lvV, hlyV, hvInV, _⟩ := hcov v hvLen
   rw [htoNatEq] at hlyV
   have hmemTop : v ∈ run.layers.getD (rk run.proper.rank i).toNat [] := by
     have hget : run.layers.getD (rk run.proper.rank i).toNat [] = lvV := by
       simp only [List.getD_eq_getElem?_getD, hlyV, Option.getD_some]
     rw [hget]
     exact hvInV
   have hnodeH : CoordsImpl.nodeH run.coordinateProper v = tNode.h := by
     simp [CoordsImpl.nodeH, hcoordV, copyF]
   have hbandH : tNode.h ≤ CoordsImpl.layerHeight run.coordinateProper
       (run.layers.getD (rk run.proper.rank i).toNat []) := by
     have hge := CoordsImpl.layerHeight_ge (p := run.coordinateProper) hmemTop
     rw [hnodeH] at hge
     exact hge
   constructor
   · exact hframeLe
   · have hcap : (transportCaption execution.params o execution.lines comp i stored0).y +
         (transportCaption execution.params o execution.lines comp i stored0).h =
         (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
           execution.params.clusterPad +
           (transportCapSize execution.params o execution.lines comp i).2 := by
       show stored0.y + (transportCapSize execution.params o execution.lines comp i).2 = _
       rw [hy0]
     have hbandH' : tNode.h ≤ CoordsImpl.layerHeight run.coordinateProper
         (run.layers.getD (rk run.coordinateProper.rank i).toNat []) := by
       rw [← rEqT]
       exact hbandH
     omega

 /-! ## Proved rank-band cases -/

 /-- Case (2b-member), proved: a plain member sits on a rank strictly below
 the top marker's rank (`ranked_compound_member_interval`), so its frame top
 lies at or below the next band top, which `rankAxis_band_top_strict` puts
 strictly below the caption bottom (`captionInTopBand_executed`). -/
 theorem captionPlainMemberClear_proved {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {i : Nat} {stored0 : Rect} {tNode : Node}
     (hmem : (i, stored0) ∈ componentTitles execution.params
       (componentCandidate execution.graph comp candidate) run)
     (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
     (hborder : tNode.border = -2)
     {pos : Nat} {fNode : Node} {g0 : Rect}
     (hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode)
     (_hne : tNode.decl ≠ fNode.decl)
     (hplain : fNode.border = 0)
     (hpath : fNode.clusterPath.contains tNode.decl = true)
     (hframe : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = g0) :
     Disjoint g0 (transportCaption execution.params o execution.lines comp i stored0) := by
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   obtain ⟨rr, labeled, hrr, hc, hk, hranks, hrecords, hshape⟩ :=
     rankSource_of_componentRun execution.graph_eq hcomp hrun
   obtain ⟨bottom, hbottom⟩ :=
     componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hborder
   have hinterv := ranked_compound_member_interval hrr
     (List.mk_mem_zipIdx_iff_getElem?.mpr hnode) hborder hbottom
     (List.mk_mem_zipIdx_iff_getElem?.mpr hfn) hplain hpath
   have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   have hmemberLt : pos < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hfn).1
   have eTop : rk run.coordinateProper.rank i = rk rr.ranks i := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hindexLt
     rw [hc] at h2
     exact h2
   have eMember : rk run.coordinateProper.rank pos = rk rr.ranks pos := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hmemberLt
     rw [hc] at h2
     exact h2
   have rEqT := run_rank_eq_coordinate_copy hrun i
   have rEqM := run_rank_eq_coordinate_copy hrun pos
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
     componentRun_spec hrun
   have hindexLen : i < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun i hindexLt
   have hmemberLen : pos < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun pos hmemberLt
   have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
   obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov pos hmemberLen
   rw [rEqT] at hlyT hnnT
   rw [rEqM] at hlyM hnnM
   have hltTM : (rk run.coordinateProper.rank i).toNat <
       (rk run.coordinateProper.rank pos).toNat := by
     have h1 := eTop
     have h2 := eMember
     have h3 : rk rr.ranks i + 1 ≤ rk rr.ranks pos := hinterv.1
     have h4 := hnnT
     have h5 := hnnM
     omega
   have hbandTM := rankAxis_band_top_strict hry _ _ _ _ hltTM hlyT hlyM
   have hMemBandLo := (fbs_run_node_band hrun pos hmemberLen).1
   rw [rEqM] at hMemBandLo
   have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
     simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
   have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
   have hmemberGet : (componentCandidate execution.graph comp candidate).nodes.getD pos default = fNode := by
     simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
   have hfr : frameRect execution.params (componentCandidate execution.graph comp candidate) run pos =
       nodeRect (componentCandidate execution.graph comp candidate) run pos := by
     unfold frameRect
     simp only []
     rw [hmemberGet, hplain]
     rfl
   have hgy : (nodeRect (componentCandidate execution.graph comp candidate) run pos).y =
       run.ys.getD pos 0 := rfl
   rw [← hframe, hfr]
   unfold Disjoint
   intro hcon
   obtain ⟨-, hy⟩ := hcon
   rw [hltTget] at hcap
   omega
 /-- Copied from the private `GroupBottomBoundaryProof.bottom_marker_coordinate_record`. -/
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

 /-- Copied from the private `GroupBottomBoundaryProof.bottom_marker_proper_node`. -/
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

 /-- Copied from the private `GroupBottomBoundaryProof.bottom_marker_path`. -/
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

 /-- Case (1-bottom), proved: the group frame bottom lies at or below the
 bottom marker's band, whose rank is strictly below the top rank
 (`componentRun_group_top_lt_bottom`), so the frame bottom is strictly
 below the caption bottom (`captionInTopBand_executed`). -/
 theorem captionSelfBottom_proved {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run) :
     CaptionSelfBottomStrict execution.params
       (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
   intro i stored0 tNode hmem hnode hborder
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   have hindexLt : i < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnode).1
   obtain ⟨bottom, hbottom⟩ :=
     componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hborder
   have hbordV : bottom.1.border = 2 := by
     have hcond := List.find?_some hbottom
     simp only [Bool.and_eq_true, beq_iff_eq] at hcond
     exact hcond.1
   have hdeclV : bottom.1.decl = tNode.decl := by
     have hcond := List.find?_some hbottom
     simp only [Bool.and_eq_true, beq_iff_eq] at hcond
     exact hcond.2
   have hnodeB : (componentCandidate execution.graph comp candidate).nodes[bottom.2]? =
       some bottom.1 :=
     List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hbottom)
   have hbotLt : bottom.2 < (componentCandidate execution.graph comp candidate).nodes.length :=
     (List.getElem?_eq_some_iff.mp hnodeB).1
   obtain ⟨rrB, _, hrrB, hcB, _, _, hranksB, hlt⟩ :=
     componentRun_group_top_lt_bottom execution.graph_eq hcomp hrun
   have htopLtBot := hlt i tNode bottom hnode hborder hbottom
   have eTop : rk run.coordinateProper.rank i = rk rrB.ranks i := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hindexLt
     rw [hcB] at h2
     exact h2
   have eBottom : rk run.coordinateProper.rank bottom.2 = rk rrB.ranks bottom.2 := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrrB hranksB hbotLt
     rw [hcB] at h2
     exact h2
   have rEqT := run_rank_eq_coordinate_copy hrun i
   have rEqB := run_rank_eq_coordinate_copy hrun bottom.2
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
     componentRun_spec hrun
   have hindexLen : i < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun i hindexLt
   have hbotLen : bottom.2 < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun bottom.2 hbotLt
   have hcov := (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov i hindexLen
   obtain ⟨ltB, hlyB, _, hnnB⟩ := hcov bottom.2 hbotLen
   rw [rEqT] at hlyT hnnT
   rw [rEqB] at hlyB hnnB
   have hltTB : (rk run.coordinateProper.rank i).toNat <
       (rk run.coordinateProper.rank bottom.2).toNat := by
     have h1 := eTop
     have h2 := eBottom
     have h3 : rk rrB.ranks i + 1 ≤ rk rrB.ranks bottom.2 := htopLtBot
     have h4 := hnnT
     have h5 := hnnB
     omega
   have hbandTB := rankAxis_band_top_strict hry _ _ _ _ hltTB hlyT hlyB
   obtain ⟨bcoord, hbcoord, hbb, hbd, hbpath, bh0⟩ :=
     proper_bottom_coordinate_record_copy hrun hnodeB hbordV
   obtain ⟨bprop, hbprop, hbpropP, hnodeH⟩ :=
     proper_bottom_proper_node_copy hrun hbcoord hbb bh0
   have hdeclB : bottom.1.clusterPath.contains bottom.1.decl = true :=
     (proper_bottom_decl_path_copy execution.graph_eq hnodeB hbordV).2
   have hbcontains : bprop.node.clusterPath.contains tNode.decl = true := by
     rw [hbpropP, hbpath, ← hdeclV]
     exact hdeclB
   have hbqmem : (bprop, bottom.2) ∈ run.proper.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr hbprop
   have hbmem : Labels.rectAt run.proper run.xs run.ys (bprop, bottom.2).2 ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := by
     apply List.mem_filterMap.mpr
     refine ⟨(bprop, bottom.2), hbqmem, ?_⟩
     rw [ite_eq_left hbcontains]
   have hbmem' : Labels.rectAt run.proper run.xs run.ys bottom.2 ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := hbmem
   have hBotYH : (Labels.rectAt run.proper run.xs run.ys bottom.2).y +
       (Labels.rectAt run.proper run.xs run.ys bottom.2).h = run.ys.getD bottom.2 0 := by
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.yAt]
     simp [hnodeH]
   have hbget : run.coordinateProper.nodes.getD bottom.2 default = bcoord := by
     simp only [List.getD_eq_getElem?_getD, hbcoord, Option.getD_some]
   have hcoordV : run.coordinateProper.nodes[bottom.2]? =
       some (run.coordinateProper.nodes.getD bottom.2 default) := by
     rw [hbget]
     exact hbcoord
   have hcyLen : run.coordinateYs.length = run.coordinateProper.nodes.length := by
     obtain ⟨_, _, _, _, _, _, hy⟩ := CoordsImpl.rankCoordsWith_spec hry
     rw [hy]
     simp
   have hvY : bottom.2 < run.coordinateYs.length := by
     have h1 := (List.getElem?_eq_some_iff.mp hbcoord).1
     omega
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
   have hgroupGet : (componentCandidate execution.graph comp candidate).nodes.getD i default =
       tNode := by
     simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : ((componentCandidate execution.graph comp candidate).nodes.getD i default).border =
       -2 := by
     rw [hgroupGet]
     exact hborder
   have hle := rect_bottom_le_boundsOf_bottom _ [] _ hbmem'
   have hframeBot : (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).y +
       (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).h =
       (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) []).bottom := by
     have hg : (componentCandidate execution.graph comp candidate).nodes.getD i default = tNode :=
       hgroupGet
     simp only [frameRect, hg, hborder,
       show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
     change (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) []).minY +
       ((boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) []).bottom - (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains tNode.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) []).minY) = _
     omega
   have hcap := (captionInTopBand_executed execution hcomp hrun hmem hnode hborder).2
   have hltTget : run.layers.getD (rk run.coordinateProper.rank i).toNat [] = ltT := by
     simp only [List.getD_eq_getElem?_getD, hlyT, Option.getD_some]
   have hHbot : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
       (run.layers.getD (rk run.coordinateProper.rank bottom.2).toNat []) :=
     CoordsImpl.layerHeight_nonneg _ _
   rw [hltTget] at hcap
   omega
theorem captionSelfClear_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    {i : Nat} {stored0 : Rect} {tNode : Node}
    (hmem : (i, stored0) ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    (hside : CaptionSelfSidesStrict execution.params
       (componentCandidate execution.graph comp candidate) run o execution.lines comp) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).StrictInside
       (transportCaption execution.params o execution.lines comp i stored0) := by
   have htop : (frameRect execution.params
       (componentCandidate execution.graph comp candidate) run i).y <
       (transportCaption execution.params o execution.lines comp i stored0).y :=
     captionSelfTop execution.graph_eq execution.checked _hcomp hrun hmem hnode hborder
   have hside' := hside i stored0 tNode hmem hnode hborder
   have hbot' := captionSelfBottom_proved execution _hcomp hrun i stored0 tNode hmem hnode hborder
   exact ⟨hside'.1, hside'.2, htop, hbot'⟩

/-- Case (2a): same declaration. A `-2` position names the same group frame,
so self strictness (1) applies; any other same-declaration position is the
marker residual. -/
theorem captionSameDeclClear_executed
    {i : Nat} {stored0 : Rect} {tNode : Node}
    {P : Params} {cg : Graph} {run : Run}
    {o : Options} {lines : List (List Measure.Line)} {comp : List Nat}
    (hself : (frameRect P cg run i).StrictInside
      (transportCaption P o lines comp i stored0))
    (hmark : CaptionSameDeclMarkerDisjoint P cg run o lines comp)
    (hmem : (i, stored0) ∈ componentTitles P cg run)
    (hnode : cg.nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    {pos : Nat} {fNode : Node} {g0 : Rect}
    (hfn : cg.nodes[pos]? = some fNode)
    (hsame : tNode.decl = fNode.decl)
    (hframe : frameRect P cg run pos = g0) :
    Disjoint g0 (transportCaption P o lines comp i stored0) ∨
    g0.StrictInside (transportCaption P o lines comp i stored0) := by
  by_cases hf : fNode.border = -2
  · have hEq : frameRect P cg run pos = frameRect P cg run i := by
      have e1 : cg.nodes.getD pos default = fNode := by
        simp only [List.getD_eq_getElem?_getD, hfn, Option.getD_some]
      have e2 : cg.nodes.getD i default = tNode := by
        simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
      simp only [frameRect, e1, e2, hf, hborder, hsame,
        show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
    subst hframe
    rw [hEq]
    exact Or.inr hself
  · exact Or.inl (hmark _ _ _ hmem hnode hborder _ _ _ hfn hsame hf hframe)

 /-- Case (2b-desc): descendant (non-member) position, by the residual.
 Plain members go through the proved `captionPlainMemberClear_proved`. -/
 theorem captionMemberDescClear_executed
     {i : Nat} {stored0 : Rect} {tNode : Node}
     {P : Params} {cg : Graph} {run : Run}
     {o : Options} {lines : List (List Measure.Line)} {comp : List Nat}
     (hmemdesc : CaptionMemberDescDisjoint P cg run o lines comp)
     (hmem : (i, stored0) ∈ componentTitles P cg run)
     (hnode : cg.nodes[i]? = some tNode)
     (hborder : tNode.border = -2)
     {pos : Nat} {fNode : Node} {g0 : Rect}
     (hfn : cg.nodes[pos]? = some fNode)
     (hne : tNode.decl ≠ fNode.decl)
     (hmemrel : fNode.clusterPath.contains tNode.decl = true)
     (hnonplain : fNode.border ≠ 0)
     (hframe : frameRect P cg run pos = g0) :
     Disjoint g0 (transportCaption P o lines comp i stored0) ∨
     g0.StrictInside (transportCaption P o lines comp i stored0) :=
   Or.inl (hmemdesc _ _ _ hmem hnode hborder _ _ _ hfn hne hmemrel hnonplain hframe)

/-- Case (2c): ancestor position. The ancestor frame strictly contains the
child frame (residual), the child frame strictly contains the caption by
(1), so the ancestor frame strictly contains the caption. -/
theorem captionAncestorClear_executed
    {i : Nat} {stored0 : Rect} {tNode : Node}
    {P : Params} {cg : Graph} {run : Run}
    {o : Options} {lines : List (List Measure.Line)} {comp : List Nat}
    (hself : (frameRect P cg run i).StrictInside
      (transportCaption P o lines comp i stored0))
    (hnest : CaptionAncestorFrameStrict P cg run)
    (hnode : cg.nodes[i]? = some tNode)
    (hborder : tNode.border = -2)
    {pos : Nat} {fNode : Node} {g0 : Rect}
    (hfn : cg.nodes[pos]? = some fNode)
    (hne : tNode.decl ≠ fNode.decl)
    (hancrel : tNode.clusterPath.contains fNode.decl = true)
    (hframe : frameRect P cg run pos = g0) :
    Disjoint g0 (transportCaption P o lines comp i stored0) ∨
    g0.StrictInside (transportCaption P o lines comp i stored0) := by
  have hnest' := hnest i pos tNode fNode hnode hborder hfn hne hancrel
  rw [hframe] at hnest'
  exact Or.inr (captionStrictInside_trans hnest' hself)
theorem captionLocalClear_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (_hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (hside : CaptionSelfSidesStrict execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hmark : CaptionSameDeclMarkerDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hmemdesc : CaptionMemberDescDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hnest : CaptionAncestorFrameStrict execution.params
      (componentCandidate execution.graph comp candidate) run) :
    (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles execution.params
        (componentCandidate execution.graph comp candidate) run →
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      (frameRect execution.params (componentCandidate execution.graph comp candidate) run i).StrictInside
        (transportCaption execution.params o execution.lines comp i stored0)) ∧
    (∀ (i : Nat) (stored0 : Rect) (tNode : Node),
      (i, stored0) ∈ componentTitles execution.params
        (componentCandidate execution.graph comp candidate) run →
      (componentCandidate execution.graph comp candidate).nodes[i]? = some tNode →
      tNode.border = -2 →
      ∀ (pos : Nat) (fNode : Node) (g0 : Rect),
        (componentCandidate execution.graph comp candidate).nodes[pos]? = some fNode →
        (tNode.decl = fNode.decl ∨
          fNode.clusterPath.contains tNode.decl = true ∨
          tNode.clusterPath.contains fNode.decl = true) →
        frameRect execution.params (componentCandidate execution.graph comp candidate) run pos = g0 →
        Disjoint g0 (transportCaption execution.params o execution.lines comp i stored0) ∨
        g0.StrictInside (transportCaption execution.params o execution.lines comp i stored0)) := by
  constructor
  · intro i stored0 tNode hmem hnode hborder
    exact captionSelfClear_executed execution _hcomp hrun hmem hnode hborder hside
  · intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel
    intro hframe
    have hself := captionSelfClear_executed execution _hcomp hrun hmem hnode hborder hside
    rcases hrel with hsame | hft | htf
    · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hsame hframe
    · by_cases hne : tNode.decl = fNode.decl
      · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hne hframe
      · by_cases hplain : fNode.border = 0
        · exact Or.inl (captionPlainMemberClear_proved execution _hcomp hrun hmem hnode hborder
            hfn hne hplain hft hframe)
        · exact captionMemberDescClear_executed hmemdesc hmem hnode hborder hfn hne hft hplain hframe
    · by_cases hne : tNode.decl = fNode.decl
      · exact captionSameDeclClear_executed hself hmark hmem hnode hborder hfn hne hframe
      · by_cases hft : fNode.clusterPath.contains tNode.decl = true
        · by_cases hplain : fNode.border = 0
          · exact Or.inl (captionPlainMemberClear_proved execution _hcomp hrun hmem hnode hborder
              hfn hne hplain hft hframe)
          · exact captionMemberDescClear_executed hmemdesc hmem hnode hborder hfn hne hft hplain hframe
        · exact captionAncestorClear_executed hself hnest hnode hborder hfn hne htf hframe

/-- Executed `captionRunClear`: the bounded run-level caption clearance for
an executed run. Same short proof as `captionRunClear`, with the executed
local form above; the only seam hypothesis is `ForeignSpansClear`. -/
theorem captionRunClear_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (_hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (hclear : ForeignSpansClear execution.params
      (componentCandidate execution.graph comp candidate) run)
    (hside : CaptionSelfSidesStrict execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hmark : CaptionSameDeclMarkerDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hmemdesc : CaptionMemberDescDisjoint execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp)
    (hnest : CaptionAncestorFrameStrict execution.params
      (componentCandidate execution.graph comp candidate) run) :
    CaptionRunClear execution.params (componentCandidate execution.graph comp candidate) run
      (transportCapSize execution.params o execution.lines comp) := by
  have hlocal :=
     captionLocalClear_executed execution _hwf _hcomp hrun hside hmark hmemdesc hnest
  unfold CaptionRunClear
  intro i stored0 tNode hmem hnode hborder pos g0 hpos hframe
  cases hfn : (componentCandidate execution.graph comp candidate).nodes[pos]? with
  | none =>
    rw [List.getElem?_eq_none_iff] at hfn
    omega
  | some fNode =>
    by_cases hrel : tNode.decl = fNode.decl ∨
        fNode.clusterPath.contains tNode.decl = true ∨
        tNode.clusterPath.contains fNode.decl = true
    · exact hlocal.2 i stored0 tNode hmem hnode hborder pos fNode g0 hfn hrel hframe
    · have hne : tNode.decl ≠ fNode.decl := fun h => hrel (Or.inl h)
      have hpathW : fNode.clusterPath.contains tNode.decl = false := by
        cases hc : fNode.clusterPath.contains tNode.decl with
        | true => exact absurd (Or.inr (Or.inl hc)) hrel
        | false => rfl
      have hpathU : tNode.clusterPath.contains fNode.decl = false := by
        cases hc : tNode.clusterPath.contains fNode.decl with
        | true => exact absurd (Or.inr (Or.inr hc)) hrel
        | false => rfl
      have hdisj := hclear i pos tNode fNode hnode hfn hborder hne hpathW hpathU
      have hself := hlocal.1 i stored0 tNode hmem hnode hborder
      have hcont := strictInside_contained_copy hself
      rw [hframe] at hdisj
      exact Or.inl ((Disjoint.comm _ _).mp (disjoint_of_sub_disjoint hcont hdisj))




