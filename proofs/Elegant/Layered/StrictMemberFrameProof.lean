 import Elegant.Layered.GroupWidthFacts
 import Elegant.Layered.LabelsC8bFacts
 import Elegant.Layered.ForeignBorderSpansProof
 import Elegant.Layered.RouteProxyStart
 import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open CoordsImpl

/-- The checked cluster border width is at least one in every profile, so a
plain member keeps a strict horizontal inset against the side markers that
bracket it. This mirrors `checkedParams_clusterPad_pos`; no kind override
touches `clusterBorderW` (`Params.forKind` overrides spacing, rank spacing,
wrapping, and canvas margin only). -/
theorem checkedParams_clusterBorderW_ge_one {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 1 ≤ P.clusterBorderW := by
  rw [checkedParams_source h]
  change 1 ≤ LayoutConst.cluster_border_w.get profile
  cases profile <;> decide
 /-- Strict horizontal bracket of a plain member by its group's side markers:
 the same binders and witnesses as
 `SceneExecution.component_member_border_interval`, but both interval sides
 are strict. The left side closes from the existing separation context once
 the goal is normalized with the same `titleF` reductions the right side
 already uses; the right side additionally needs `1 ≤ clusterBorderW`
 (both profiles satisfy it), because `fdiv` rounding can otherwise consume
 the unit gap exactly. -/
 theorem SceneExecution.component_member_border_interval_strict {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {index memberIndex : Nat} {node member : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
     (hgroup : node.border = -2)
     (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
     (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
     ∃ (actual : ProperNode) (left right : Nat),
       run.proper.nodes[memberIndex]? = some actual ∧
       actual.node.clusterPath = member.clusterPath ∧
       run.proper.nodes[left]? = some (OrderImpl.borderLeft
         (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
       run.proper.nodes[right]? = some (OrderImpl.borderRight
         (titleF ⟨node, false, none, false⟩, index) execution.params.clusterBorderW) ∧
       (Labels.rectAt run.proper run.xs run.ys left).x <
         (Labels.rectAt run.proper run.xs run.ys memberIndex).x ∧
       (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
           (Labels.rectAt run.proper run.xs run.ys memberIndex).w <
         (Labels.rectAt run.proper run.xs run.ys right).x +
           (Labels.rectAt run.proper run.xs run.ys right).w := by
   obtain ⟨actual, ord, left, right, _, hlayers, hcoordinate, hproper, _, hactualPlain,
     hactualPath, hx, hleft, hright, hbracket⟩ :=
     execution.component_member_bracket hwf hcomp hrun hnode hgroup hmember hplain hinside
   obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
   rw [hlayers] at hli hmi hri
   have hlayer := hbracket.layer_mem
   rw [hlayers] at hlayer
   obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
   obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
   obtain ⟨labeled, hc, hk, _⟩ := componentRun_coordinate_source_alignment hrun
   have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
     (measuredGraph_shape execution.graph_eq) candidate
   have hunique : ∀ (a b : Nat) (na nb : ProperNode),
       run.coordinateProper.nodes[a]? = some na →
       run.coordinateProper.nodes[b]? = some nb →
       na.node.border = 3 → nb.node.border = 3 →
       na.node.clusterPath = nb.node.clusterPath → a = b := by
     intro a b na nb ha hb hba hbb hp
     exact pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb) hba hbb hp
   have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
     li mi left memberIndex _ _ hlt hli hmi hleft hcoordinate
     (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
     (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
   have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
     mi ri memberIndex right _ _ htr hmi hri hcoordinate hright
     (by rw [hactualPlain]; decide) (by rw [hactualPlain]; decide)
     (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
   obtain ⟨hleftFinal, hleftX⟩ := componentRun_border_record hrun hleft (Or.inl rfl)
   obtain ⟨hrightFinal, hrightX⟩ := componentRun_border_record hrun hright (Or.inr rfl)
   have hactualWidth := (sizesNonneg_lookup hsizes memberIndex actual hcoordinate).1
   have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
   have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
   have hactualLoops : 0 ≤ (actual.node.loopExtent : Int) := Int.natCast_nonneg _
   have hgroupLoops : 0 ≤ (node.loopExtent : Int) := Int.natCast_nonneg _
   have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
   have hcbw : 1 ≤ execution.params.clusterBorderW :=
     checkedParams_clusterBorderW_ge_one execution.checked
   change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
   refine ⟨actual, left, right, hproper, hactualPath, hleftFinal, hrightFinal, ?_, ?_⟩
   · simp only [coordSep, CoordsImpl.nodeW, hleft, hcoordinate, OrderImpl.borderLeft] at hleftSep
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
       hleftFinal, hproper, hleftX, hx, OrderImpl.borderLeft,
       titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte]
     simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
     omega
   · simp only [coordSep, CoordsImpl.nodeW, hcoordinate, hright, OrderImpl.borderRight,
       titleF, hgroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
       hproper, hrightFinal, hx, hrightX, OrderImpl.borderRight]
     simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
     omega
 /-- Residual: vertical strictness of a plain member inside its group frame.
 About `frameRect` only, pinned to the executed component run: the member
 frame's top edge lies strictly below the group frame's top edge and its
 bottom edge strictly above the group frame's bottom edge. Strictly simpler
 than `StrictInside` (the two vertical conjuncts); the horizontal conjuncts
 are proved. Tested by `StrictMemberFrame.lean`: every executed
 (group, member) pair has positive top and bottom margins in both profiles. -/
 def MemberFrameStrictVertical (P : Params) (cg : Graph) (run : Run)
     (index memberIndex : Nat) : Prop :=
   (frameRect P cg run index).y < (frameRect P cg run memberIndex).y ∧
     (frameRect P cg run memberIndex).y + (frameRect P cg run memberIndex).h <
       (frameRect P cg run index).y + (frameRect P cg run index).h

 /-- Strict counterpart of `SceneExecution.component_member_contained`: a
 plain member lies strictly inside its group frame. Same binders as the
 non-strict theorem; no extra positivity hypothesis is needed because
 `1 ≤ min nodeGap clusterPad` comes from `crossCoordsClusterWith_spec` and
 `1 ≤ clusterBorderW` is proved above from the checked parameters. The
 vertical sides are the residual `MemberFrameStrictVertical`. -/
 theorem SceneExecution.component_member_strictInside {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {index memberIndex : Nat} {node member : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
     (hgroup : node.border = -2)
     (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
     (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true)
     (hvert : MemberFrameStrictVertical execution.params
       (componentCandidate execution.graph comp candidate) run index memberIndex) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate) run index).StrictInside
       (frameRect execution.params (componentCandidate execution.graph comp candidate) run memberIndex) := by
   let cg := componentCandidate execution.graph comp candidate
   obtain ⟨actual, left, right, hproper, hactualPath, hleft, hright, hleftStrict, hrightStrict⟩ :=
     execution.component_member_border_interval_strict hwf hcomp hrun hnode hgroup hmember hplain hinside
   have hgroupGet : cg.nodes.getD index default = node := by
     simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : (cg.nodes.getD index default).border = -2 := by
     rw [hgroupGet]
     exact hgroup
   obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
   obtain ⟨box, _, hdecl, hpath⟩ := execution.group_node_path_source hgroupSource hgroup
   have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
     simpa only [hdecl] using hpath
   have hleftPath : (OrderImpl.borderLeft (titleF ⟨node, false, none, false⟩, index)
       execution.params.clusterBorderW).node.clusterPath =
         Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := by
     change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
     rw [(titleF_keys _).2.2.1, hgroupGet]
     exact hgroupPath
   have hrightPath : (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
       execution.params.clusterBorderW).node.clusterPath =
         Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := hleftPath
   have hleftContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
     hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
   have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
     hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
   have hmemberGet : cg.nodes.getD memberIndex default = member := by
     simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
   have hmemberFrame : frameRect execution.params cg run memberIndex =
       Labels.rectAt run.proper run.xs run.ys memberIndex := by
     unfold frameRect
     rw [hmemberGet]
     simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
     unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
       RouteImpl.nodeW RouteImpl.nodeH
     simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
   unfold Rect.StrictInside
   unfold MemberFrameStrictVertical at hvert
   rw [hmemberFrame] at hvert
   rw [hmemberFrame]
   have hx1 : (frameRect execution.params cg run index).x <
       (Labels.rectAt run.proper run.xs run.ys memberIndex).x := by
     have h1' : (frameRect execution.params cg run index).x ≤
         (Labels.rectAt run.proper run.xs run.ys left).x := hleftContained.1
     have h2 := hleftStrict
     omega
   have hx2 : (Labels.rectAt run.proper run.xs run.ys memberIndex).x +
         (Labels.rectAt run.proper run.xs run.ys memberIndex).w <
       (frameRect execution.params cg run index).x +
         (frameRect execution.params cg run index).w := by
     have h1 := hrightStrict
     have h2' : (Labels.rectAt run.proper run.xs run.ys right).x +
         (Labels.rectAt run.proper run.xs run.ys right).w ≤
         (frameRect execution.params cg run index).x +
           (frameRect execution.params cg run index).w := hrightContained.2.1
     omega
   exact ⟨hx1, hx2, hvert.1, hvert.2⟩

 /-- Strict horizontal bracket of a child group side marker by its parent
 group's side markers: the same binders and witnesses as
 `SceneExecution.component_child_side_parent_border_interval`, but strict.
 Same proof obligations as the member interval (left needs the `titleF`
 goal normalization, right needs `1 ≤ clusterBorderW`). -/
 theorem SceneExecution.component_child_side_parent_border_interval_strict {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {parentIndex childIndex : Nat} {parent child : Node}
     (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
     (hparentGroup : parent.border = -2)
     (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
     (hchildGroup : child.border = -2)
     {parentBox childBox : ModelBox}
     (hparentBox : inp.boxes[parent.decl]? = some parentBox)
     (hchildBox : inp.boxes[child.decl]? = some childBox)
     (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
     {sideIndex : Nat} {side : ProperNode}
     (hside : run.coordinateProper.nodes[sideIndex]? = some side)
     (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
     (howner : side.node.clusterPath.getLast? = some child.decl) :
     ∃ left right : Nat,
       run.proper.nodes[sideIndex]? = some side ∧
       run.proper.nodes[left]? = some (OrderImpl.borderLeft
         (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
       run.proper.nodes[right]? = some (OrderImpl.borderRight
         (titleF ⟨parent, false, none, false⟩, parentIndex) execution.params.clusterBorderW) ∧
       (Labels.rectAt run.proper run.xs run.ys left).x <
         (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
       (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
           (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
         (Labels.rectAt run.proper run.xs run.ys right).x +
           (Labels.rectAt run.proper run.xs run.ys right).w := by
   obtain ⟨ord, left, right, _, hlayers, _, _, hleft, hright, hbracket⟩ :=
     execution.component_child_side_parent_bracket hwf hcomp hrun hparent hparentGroup
       hchild hchildGroup hparentBox hchildBox hparentRef hne hside hsideBorder howner
   obtain ⟨li, mi, ri, hli, hmi, hri, hlt, htr⟩ := hbracket.positions
   rw [hlayers] at hli hmi hri
   have hlayer := hbracket.layer_mem
   rw [hlayers] at hlayer
   obtain ⟨_, _, _, _, _, _, _, _, hcross, _⟩ := componentRun_spec hrun
   obtain ⟨hng, hcp, _, hsizes, _⟩ := crossCoordsClusterWith_spec hcross
   obtain ⟨labeled, hc, hk, _⟩ := componentRun_coordinate_source_alignment hrun
   have hshape := componentCandidate_shape (components_nodup execution.graph comp hcomp)
     (measuredGraph_shape execution.graph_eq) candidate
   have hunique : ∀ (a b : Nat) (na nb : ProperNode),
       run.coordinateProper.nodes[a]? = some na →
       run.coordinateProper.nodes[b]? = some nb →
       na.node.border = 3 → nb.node.border = 3 →
       na.node.clusterPath = nb.node.clusterPath → a = b := by
     intro a b na nb ha hb hba hbb hp
     exact pc_title_unique hk hshape (by rw [hc]; exact ha) (by rw [hc]; exact hb) hba hbb hp
   have hsideNotTop : side.node.border ≠ -2 := by
     rcases hsideBorder with hb | hb <;> omega
   have hsideNotBottom : side.node.border ≠ 2 := by
     rcases hsideBorder with hb | hb <;> omega
   have hleftSep := cluster_all_pairs_separated hcross hunique _ hlayer
     li mi left sideIndex _ _ hlt hli hmi hleft hside
     (by change (-1 : Int) ≠ -2; decide) (by change (-1 : Int) ≠ 2; decide)
     hsideNotTop hsideNotBottom
   have hrightSep := cluster_all_pairs_separated hcross hunique _ hlayer
     mi ri sideIndex right _ _ htr hmi hri hside hright
     hsideNotTop hsideNotBottom
     (by change (1 : Int) ≠ -2; decide) (by change (1 : Int) ≠ 2; decide)
   obtain ⟨hleftFinal, hleftX⟩ := componentRun_border_record hrun hleft (Or.inl rfl)
   obtain ⟨hrightFinal, hrightX⟩ := componentRun_border_record hrun hright (Or.inr rfl)
   obtain ⟨hsideFinal, hsideX⟩ := componentRun_border_record hrun hside hsideBorder
   have hsideWidth := (sizesNonneg_lookup hsizes sideIndex side hside).1
   have hleftWidth := (sizesNonneg_lookup hsizes left _ hleft).1
   have hrightWidth := (sizesNonneg_lookup hsizes right _ hright).1
   have hsideLoops : 0 ≤ (side.node.loopExtent : Int) := Int.natCast_nonneg _
   have hparentLoops : 0 ≤ (parent.loopExtent : Int) := Int.natCast_nonneg _
   have hgap : 1 ≤ min execution.params.nodeGap execution.params.clusterPad := by omega
   have hcbw : 1 ≤ execution.params.clusterBorderW :=
     checkedParams_clusterBorderW_ge_one execution.checked
   change 0 ≤ execution.params.clusterBorderW at hleftWidth hrightWidth
   refine ⟨left, right, hsideFinal, hleftFinal, hrightFinal, ?_, ?_⟩
   · simp only [coordSep, CoordsImpl.nodeW, hleft, hside, OrderImpl.borderLeft] at hleftSep
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
       hleftFinal, hsideFinal, hleftX, hsideX, OrderImpl.borderLeft,
       titleF, hparentGroup, beq_self_eq_true, Bool.true_or, ↓reduceIte]
     simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hleftSep ⊢
     omega
   · simp only [coordSep, CoordsImpl.nodeW, hside, hright, OrderImpl.borderRight,
       titleF, hparentGroup, beq_self_eq_true, Bool.true_or, ↓reduceIte] at hrightSep
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
       hsideFinal, hrightFinal, hsideX, hrightX, OrderImpl.borderRight]
     simp [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at hrightSep ⊢
     omega

 /-- Fold invariant: a strict lower bound on `minX` survives the hull fold. -/
 private theorem foldl_strict_minX (rects : List Rect) (b : Bounds) (lo : Int)
     (hb : lo < b.minX) (hall : ∀ r ∈ rects, lo < r.x) :
     lo < ((rects.foldl fun b r =>
       ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
         max b.bottom (r.y + r.h)⟩) b).minX := by
   induction rects generalizing b with
   | nil => simpa using hb
   | cons first rest ih =>
     simp only [List.foldl_cons]
     apply ih
     · show lo < min b.minX first.x
       have h1 := hb
       have h2 := hall first (by simp)
       omega
     · intro r hr
       exact hall r (List.mem_cons_of_mem _ hr)
 /-- Strict hull minimum: every element strictly above `lo` puts the hull
 minimum strictly above `lo`. No positivity hypothesis is needed on this
 side because the nonempty fold starts at an element, not at zero. -/
 private theorem strict_minX_of_all_lt (rects : List Rect) (lo : Int)
     (hall : ∀ r ∈ rects, lo < r.x) (hne : rects ≠ []) :
     lo < (boundsOf rects []).minX := by
   cases rects with
   | nil => exact absurd rfl hne
   | cons first rest =>
     unfold boundsOf
     dsimp only
     exact foldl_strict_minX _ _ _ (hall first (by simp)) hall

 /-- Fold invariant: a strict upper bound on `right` survives the hull fold. -/
 private theorem foldl_strict_right (rects : List Rect) (b : Bounds) (hi : Int)
     (hb : b.right < hi) (hall : ∀ r ∈ rects, r.x + r.w < hi) :
     ((rects.foldl fun b r =>
       ⟨min b.minX r.x, min b.minY r.y, max b.right (r.x + r.w),
         max b.bottom (r.y + r.h)⟩) b).right < hi := by
   induction rects generalizing b with
   | nil => simpa using hb
   | cons first rest ih =>
     simp only [List.foldl_cons]
     apply ih
     · show max b.right (first.x + first.w) < hi
       have h1 := hb
       have h2 := hall first (by simp)
       omega
     · intro r hr
       exact hall r (List.mem_cons_of_mem _ hr)
 /-- Strict hull maximum: every element right edge strictly below `hi` puts
 the hull right edge strictly below `hi`, provided the zero base of the
 nonempty fold is also below `hi`. -/
 private theorem strict_right_of_all_lt (rects : List Rect) (hi : Int)
     (hall : ∀ r ∈ rects, r.x + r.w < hi) (hne : rects ≠ [])
     (hpos : 0 < hi) :
     (boundsOf rects []).right < hi := by
   cases rects with
   | nil => exact absurd rfl hne
   | cons first rest =>
     unfold boundsOf
     dsimp only
     exact foldl_strict_right _ _ _ hpos hall

 /-- Residual: vertical strictness of a child group frame inside its parent
 group frame. About `frameRect` only, pinned to the executed component run.
 Strictly simpler than `StrictInside`; the horizontal conjuncts are proved.
 Tested by `StrictMemberFrame.lean`: every executed (parent, child) pair has
 positive top and bottom margins in both profiles. -/
 def ChildFrameStrictVertical (P : Params) (cg : Graph) (run : Run)
     (parentIndex childIndex : Nat) : Prop :=
   (frameRect P cg run parentIndex).y < (frameRect P cg run childIndex).y ∧
     (frameRect P cg run childIndex).y + (frameRect P cg run childIndex).h <
       (frameRect P cg run parentIndex).y + (frameRect P cg run parentIndex).h

 /-- Residual: the parent group frame right edge is positive, discharging the
 zero base of the strict hull-maximum fold. About `frameRect` only, pinned
 to the executed component run. Tested by `StrictMemberFrame.lean`: every
 executed parent frame has a positive right edge in both profiles. -/
 def ParentFrameRightEdgePos (P : Params) (cg : Graph) (run : Run)
     (parentIndex : Nat) : Prop :=
   0 < (frameRect P cg run parentIndex).x + (frameRect P cg run parentIndex).w

 /-- Strict counterpart of
 `SceneExecution.component_child_side_parent_horizontal`: a child side marker
 lies strictly inside its parent frame horizontally. Same binders; proved
 from the strict child-side interval and the parent side-marker
 containments. -/
 theorem SceneExecution.component_child_side_parent_horizontal_strict {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {parentIndex childIndex : Nat} {parent child : Node}
     (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
     (hparentGroup : parent.border = -2)
     (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
     (hchildGroup : child.border = -2)
     {parentBox childBox : ModelBox}
     (hparentBox : inp.boxes[parent.decl]? = some parentBox)
     (hchildBox : inp.boxes[child.decl]? = some childBox)
     (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
     {sideIndex : Nat} {side : ProperNode}
     (hside : run.proper.nodes[sideIndex]? = some side)
     (hsideBorder : side.node.border = -1 ∨ side.node.border = 1)
     (howner : side.node.clusterPath.getLast? = some child.decl) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate)
       run parentIndex).x < (Labels.rectAt run.proper run.xs run.ys sideIndex).x ∧
     (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
         (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
       (frameRect execution.params (componentCandidate execution.graph comp candidate)
         run parentIndex).x +
       (frameRect execution.params (componentCandidate execution.graph comp candidate)
         run parentIndex).w := by
   have hcoordinate := (componentRun_final_border_source hrun hside hsideBorder).1
   obtain ⟨left, right, _, hleft, hright, hlo, hhi⟩ :=
     execution.component_child_side_parent_border_interval_strict hwf hcomp hrun hparent hparentGroup
       hchild hchildGroup hparentBox hchildBox hparentRef hne hcoordinate hsideBorder howner
   let cg := componentCandidate execution.graph comp candidate
   have hparentGet : cg.nodes.getD parentIndex default = parent := by
     simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
   have hframeGroup : (cg.nodes.getD parentIndex default).border = -2 := by
     rw [hparentGet]
     exact hparentGroup
   obtain ⟨_, _, hparentSource⟩ := componentCandidate_nonplain_source hparent (by omega)
   obtain ⟨box, _, hdecl, hpath⟩ := execution.group_node_path_source hparentSource hparentGroup
   have hleftPath : (OrderImpl.borderLeft
       (titleF ⟨parent, false, none, false⟩, parentIndex)
       execution.params.clusterBorderW).node.clusterPath =
         Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
     change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
     rw [(titleF_keys _).2.2.1, hparentGet]
     simpa only [hdecl] using hpath
   have hrightPath : (OrderImpl.borderRight
       (titleF ⟨parent, false, none, false⟩, parentIndex)
       execution.params.clusterBorderW).node.clusterPath =
         Compound.path inp.boxes box ++ [(cg.nodes.getD parentIndex default).decl] := by
     change (titleF ⟨parent, false, none, false⟩).node.clusterPath = _
     exact hleftPath
   have hleftContained := frameRect_side_marker_contained (P := execution.params)
     hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hleft) (Or.inl rfl) hleftPath
   have hrightContained := frameRect_side_marker_contained (P := execution.params)
     hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hright) (Or.inr rfl) hrightPath
   have hx1 : (frameRect execution.params cg run parentIndex).x <
       (Labels.rectAt run.proper run.xs run.ys sideIndex).x := by
     have h1' : (frameRect execution.params cg run parentIndex).x ≤
         (Labels.rectAt run.proper run.xs run.ys left).x := hleftContained.1
     have h2 := hlo
     omega
   have hx2 : (Labels.rectAt run.proper run.xs run.ys sideIndex).x +
         (Labels.rectAt run.proper run.xs run.ys sideIndex).w <
       (frameRect execution.params cg run parentIndex).x +
         (frameRect execution.params cg run parentIndex).w := by
     have h1 := hhi
     have h2' : (Labels.rectAt run.proper run.xs run.ys right).x +
         (Labels.rectAt run.proper run.xs run.ys right).w ≤
         (frameRect execution.params cg run parentIndex).x +
           (frameRect execution.params cg run parentIndex).w := hrightContained.2.1
     omega
   exact ⟨hx1, hx2⟩

 /-- Strict counterpart of `SceneExecution.component_child_frame_contained`:
 a child group frame lies strictly inside its parent group frame. Same
 binders as the non-strict theorem; no extra positivity hypothesis is needed
 (`1 ≤ min nodeGap clusterPad` from `crossCoordsClusterWith_spec`,
 `1 ≤ clusterBorderW` proved above). The vertical sides are the residual
 `ChildFrameStrictVertical` and the strict hull-maximum base is the residual
 `ParentFrameRightEdgePos`. -/
 theorem SceneExecution.component_child_frame_strictInside {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {parentIndex childIndex : Nat} {parent child : Node}
     (hparent : (componentCandidate execution.graph comp candidate).nodes[parentIndex]? = some parent)
     (hparentGroup : parent.border = -2)
     (hchild : (componentCandidate execution.graph comp candidate).nodes[childIndex]? = some child)
     (hchildGroup : child.border = -2)
     {parentBox childBox : ModelBox}
     (hparentBox : inp.boxes[parent.decl]? = some parentBox)
     (hchildBox : inp.boxes[child.decl]? = some childBox)
     (hparentRef : childBox.parent = parentBox.id) (hne : childBox.parent ≠ "")
     (hvert : ChildFrameStrictVertical execution.params
       (componentCandidate execution.graph comp candidate) run parentIndex childIndex)
     (hposR : ParentFrameRightEdgePos execution.params
       (componentCandidate execution.graph comp candidate) run parentIndex) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate)
       run parentIndex).StrictInside
       (frameRect execution.params (componentCandidate execution.graph comp candidate)
         run childIndex) := by
   let cg := componentCandidate execution.graph comp candidate
   let parentFrame := frameRect execution.params cg run parentIndex
   let childFrame := frameRect execution.params cg run childIndex
   let borders := run.proper.nodes.zipIdx.filterMap fun entry =>
     if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
         entry.1.node.clusterPath.getLast? == some child.decl then
       some (Labels.rectAt run.proper run.xs run.ys entry.2)
     else none
   have hparentGet : cg.nodes.getD parentIndex default = parent := by
     simp only [cg, List.getD_eq_getElem?_getD, hparent, Option.getD_some]
   have hchildGet : cg.nodes.getD childIndex default = child := by
     simp only [cg, List.getD_eq_getElem?_getD, hchild, Option.getD_some]
   obtain ⟨sideIndex, side, hside, hsideBorder, howner⟩ :=
     execution.component_group_final_side hcomp hrun hchild hchildGroup
   have hmember : Labels.rectAt run.proper run.xs run.ys sideIndex ∈ borders := by
     apply List.mem_filterMap.mpr
     refine ⟨(side, sideIndex), List.mk_mem_zipIdx_iff_getElem?.mpr hside, ?_⟩
     rcases hsideBorder with hb | hb <;> simp [hb, howner]
   have hnonempty : borders ≠ [] := by
     intro hempty
     rw [hempty] at hmember
     exact List.not_mem_nil hmember
   have hall : ∀ rect ∈ borders,
       parentFrame.x < rect.x ∧ rect.x + rect.w < parentFrame.x + parentFrame.w := by
     intro rect hrect
     obtain ⟨entry, hentry, heq⟩ := List.mem_filterMap.mp hrect
     split at heq
     · rename_i hcondition
       have hconditions := Bool.and_eq_true_iff.mp hcondition
       have hb : entry.1.node.border = -1 ∨ entry.1.node.border = 1 := by
         simpa only [Bool.or_eq_true, beq_iff_eq] using hconditions.1
       have ho : entry.1.node.clusterPath.getLast? = some child.decl :=
         beq_iff_eq.mp hconditions.2
       have hrectEq := Option.some.inj heq
       rw [← hrectEq]
       exact execution.component_child_side_parent_horizontal_strict hwf hcomp hrun
         hparent hparentGroup hchild hchildGroup hparentBox hchildBox hparentRef hne
         (List.mem_zipIdx_iff_getElem?.mp hentry) hb ho
     · cases heq
   have hmin : parentFrame.x < (boundsOf borders []).minX :=
     strict_minX_of_all_lt _ _ (fun r hr => (hall r hr).1) hnonempty
   have hpos' : 0 < parentFrame.x + parentFrame.w := hposR
   have hmax : (boundsOf borders []).right < parentFrame.x + parentFrame.w :=
     strict_right_of_all_lt _ _ (fun r hr => (hall r hr).2) hnonempty hpos'
   have hchildX : childFrame.x = (boundsOf borders []).minX := by
     dsimp only [childFrame]
     simp only [frameRect, hchildGet, hchildGroup,
       show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
     rfl
   have hchildRight : childFrame.x + childFrame.w = (boundsOf borders []).right := by
     dsimp only [childFrame]
     simp only [frameRect, hchildGet, hchildGroup,
       show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
     change (boundsOf borders []).minX +
       ((boundsOf borders []).right - (boundsOf borders []).minX) = _
     omega
   unfold Rect.StrictInside
   change parentFrame.x < childFrame.x ∧
     childFrame.x + childFrame.w < parentFrame.x + parentFrame.w ∧
     parentFrame.y < childFrame.y ∧
     childFrame.y + childFrame.h < parentFrame.y + parentFrame.h
   rw [hchildRight, hchildX]
   exact ⟨hmin, hmax, hvert.1, hvert.2⟩

 /-- Copied from `group_top_coordinate_record` (`GroupTopFacts.lean`): the
 coordinate-graph record of a `-2` graph node. -/
 private theorem proper_top_coordinate_record {P : Params} {cg : Graph} {run : Run}
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

 /-- Copied from `group_top_proper_clusterPath` (`GroupTopFacts.lean`). -/
 private theorem proper_top_proper_clusterPath {P : Params} {cg : Graph} {run : Run}
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

 /-- Copied from `group_top_rank_eq_coordinate` (`GroupTopFacts.lean`): the
 executed `run.proper` rank of every index equals the coordinate rank. -/
 private theorem run_rank_eq_coordinate {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {orderOptions : OrderOptions}
     (hrun : componentRun P cg labels orderOptions = .ok run)
     (i : Nat) :
     rk run.proper.rank i = rk run.coordinateProper.rank i := by
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _, _, _⟩ := componentRun_spec hrun
   rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]

 /-- Copied from `group_top_decl_path` (`GroupTopFacts.lean`). -/
 private theorem proper_top_decl_path {P : Params} {inp : Input} {o : Options}
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

 /-- Copied from `bottom_marker_coordinate_record`
 (`GroupBottomBoundaryProof.lean`). -/
 private theorem proper_bottom_coordinate_record {P : Params} {cg : Graph} {run : Run}
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

 /-- Copied from `bottom_marker_proper_node`
 (`GroupBottomBoundaryProof.lean`). -/
 private theorem proper_bottom_proper_node {P : Params} {cg : Graph} {run : Run}
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

 /-- Copied from `bottom_marker_path` (`GroupBottomBoundaryProof.lean`). -/
 private theorem proper_bottom_decl_path {P : Params} {inp : Input} {o : Options}
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

 /-- Every rank step is at least one when the rank gap is: the label-only
 shrinkage is `fdiv (rankGap + 1) 2 ≥ 1` and slot contributions are
 nonnegative. -/
 private theorem rankStepsFrom_ge_one {rankGap slot : Int} (hg : 1 ≤ rankGap) (hs : 0 ≤ slot) :
     ∀ (flags : List Bool) (ss : List Int), (∀ s ∈ ss, 0 ≤ s) →
       ∀ x ∈ rankStepsFrom rankGap slot flags ss, 1 ≤ x := by
   intro flags ss
   induction ss generalizing flags with
   | nil => intro _ x hx; simp [rankStepsFrom] at hx
   | cons s ss' ih =>
     intro hss x hx
     simp only [rankStepsFrom, List.mem_cons] at hx
     have hs0 : 0 ≤ s := hss s (by simp)
     have hslot : 0 ≤ slot * s := Int.mul_nonneg hs hs0
     rcases hx with rfl | hx
     · have hgap : 1 ≤ (if flags.headD false || flags.tail.headD false then
           Int.fdiv (rankGap + 1) 2 else rankGap) := by
         split
         · rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
           omega
         · omega
       omega
     · exact ih flags.tail (fun s hm => hss s (by simp [hm])) x hx

 /-- Strict band separation: consecutive rank tops are separated by the rank
 step (at least one), so bands at strictly increasing ranks are strictly
 apart. Mirrors `topsFrom_disjoint` with the `+ 1`. -/
 private theorem topsFrom_strict_step :
     ∀ (hs ss : List Int) (t : Int), (∀ h ∈ hs, 0 ≤ h) → (∀ s ∈ ss, 1 ≤ s) →
       ss.length + 1 = hs.length →
       ∀ (r r' : Nat) (a b h : Int), r < r' → (topsFrom 0 1 t hs ss)[r]? = some a →
         (topsFrom 0 1 t hs ss)[r']? = some b → hs[r]? = some h → a + h + 1 ≤ b := by
   intro hs
   induction hs with
   | nil => intro ss t _ _ hl r r' a b h hr ha hb hh; simp at hh
   | cons h0 hs' ih =>
     intro ss t hh hss hl r r' a b h hr ha hb hh'
     cases ss with
     | nil =>
       cases hs' with
       | nil =>
         have e : topsFrom 0 1 t [h0] [] = [t] := rfl
         rw [e] at hb
         cases r' with
         | zero => omega
         | succ r1 => simp at hb
       | cons _ _ => simp at hl
     | cons s ss' =>
       have h0' := hh h0 (by simp)
       have s1 := hss s (by simp)
       have hh1 : ∀ h ∈ hs', 0 ≤ h := fun h hm => hh h (by simp [hm])
       have hss1 : ∀ s ∈ ss', 1 ≤ s := fun s hm => hss s (by simp [hm])
       have hss0 : ∀ s ∈ ss', 0 ≤ s := fun s hm => by have := hss1 s hm; omega
       cases r with
       | zero =>
         cases r' with
         | zero => omega
         | succ r1 =>
           simp only [topsFrom, List.getElem?_cons_zero, Option.some.injEq] at ha
           simp only [topsFrom, List.getElem?_cons_succ] at hb
           simp only [List.getElem?_cons_zero, Option.some.injEq] at hh'
           have hge := topsFrom_ge 0 1 (by decide) (by decide) _ _ _ hh1 hss0 b
             (List.mem_of_getElem? hb)
           omega
       | succ r1 =>
         cases r' with
         | zero => omega
         | succ r2 =>
           simp only [topsFrom, List.getElem?_cons_succ] at ha hb
           simp only [List.getElem?_cons_succ] at hh'
           exact ih ss' (t + h0 + 0 + 1 * s) hh1 hss1 (by simpa using hl) r1 r2 a b h
             (by omega) ha hb hh'

 /-- Strict band tops for executed runs: the top of a lower rank plus its
 layer height plus one fits below the top of any higher rank. -/
 theorem rankAxis_band_top_strict {rankGap slot : Int} {p : Proper} {layers : List (List Nat)}
     {slots y top : List Int} (h : rankCoordsWith rankGap slot p layers slots = .ok (y, top)) :
     ∀ r r' (l l' : List Nat), r < r' → layers[r]? = some l → layers[r']? = some l' →
       top.getD r 0 + CoordsImpl.layerHeight p l + 1 ≤ top.getD r' 0 := by
   intro r r' l l' hr hl hl'
   obtain ⟨hg, hslot, hlen, hnn, _, htop, _⟩ := rankCoordsWith_spec h
   have hlen' : slots.length + 1 = (layers.map (CoordsImpl.layerHeight p)).length := by
     have hr' : r' < layers.length := (List.getElem?_eq_some_iff.mp hl').1
     simp
     omega
   have hh : ∀ x ∈ layers.map (CoordsImpl.layerHeight p), 0 ≤ x := by
     intro x hx
     obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
     exact CoordsImpl.layerHeight_nonneg p m
   have hsteps1 : ∀ x ∈ rankSteps rankGap slot p layers slots, 1 ≤ x :=
     rankStepsFrom_ge_one hg (by omega) _ _ hnn
   have hstepslen : (rankSteps rankGap slot p layers slots).length + 1 =
       (layers.map (CoordsImpl.layerHeight p)).length := by
     simpa [rankSteps_length] using hlen'
   have hL := topsFrom_length 0 1 (layers.map (CoordsImpl.layerHeight p))
     (rankSteps rankGap slot p layers slots) 0 hstepslen
   subst htop
   have hr'len : r' < (topsFrom 0 1 0 (layers.map (CoordsImpl.layerHeight p))
       (rankSteps rankGap slot p layers slots)).length := by
     rw [hL]
     simpa using (List.getElem?_eq_some_iff.mp hl').1
   have hrlen : r < (topsFrom 0 1 0 (layers.map (CoordsImpl.layerHeight p))
       (rankSteps rankGap slot p layers slots)).length := by
     omega
   have ha := List.getElem?_eq_getElem hrlen
   have hb := List.getElem?_eq_getElem hr'len
   have hH : (layers.map (CoordsImpl.layerHeight p))[r]? = some (CoordsImpl.layerHeight p l) := by
     simp [hl]
   have hge := topsFrom_strict_step _ _ _ hh hsteps1 hstepslen r r' _ _ _ hr ha hb hH
   rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ha, hb]
   simpa using hge

 /-- Vertical strictness for an executed plain member, discharged: the member
 frame sits strictly inside its group frame vertically. The rank argument is
 strict on both sides (`ranked_compound_member_interval`), transported from
 the ranking result to the executed ranks; distinct ranks have strictly
 separated y-bands (`rankAxis_band_top_strict`); the top and bottom proxies
 attain their band edges. Discharges `MemberFrameStrictVertical`. -/
 theorem memberFrameStrictVertical_of_executed {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {index memberIndex : Nat} {node member : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
     (hgroup : node.border = -2)
     (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
     (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
     MemberFrameStrictVertical execution.params (componentCandidate execution.graph comp candidate)
       run index memberIndex := by
   let cg := componentCandidate execution.graph comp candidate
   have hlines : execution.lines.length = inp.boxes.length := by
     have h := (mapM_getElem? _ _ _ execution.lines_eq).1
     simpa only [List.length_zipIdx] using h
   obtain ⟨rr, labeled, hrr, hc, hk, hranks, hrecords, hshape⟩ :=
     rankSource_of_componentRun execution.graph_eq hcomp hrun
   obtain ⟨bottom, hbottom⟩ :=
     componentRun_cg_bottom_find execution.graph_eq hlines hcomp hnode hgroup
   have htop : ((node, index) : Node × Nat) ∈ cg.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr hnode
   have hmem : ((member, memberIndex) : Node × Nat) ∈ cg.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr hmember
   have hinterv := ranked_compound_member_interval hrr htop hgroup hbottom hmem hplain hinside
   have hintervTop : rk rr.ranks index + 1 ≤ rk rr.ranks memberIndex := hinterv.1
   have hintervBot : rk rr.ranks memberIndex + 1 ≤ rk rr.ranks bottom.2 := hinterv.2
   have hindexLt : index < cg.nodes.length := (List.getElem?_eq_some_iff.mp hnode).1
   have hmemberLt : memberIndex < cg.nodes.length := (List.getElem?_eq_some_iff.mp hmember).1
   have hbotMem : bottom ∈ cg.nodes.zipIdx := List.mem_of_find?_eq_some hbottom
   have hbotLookup : cg.nodes[bottom.2]? = some bottom.1 :=
     List.mem_zipIdx_iff_getElem?.mp hbotMem
   have hbotLt : bottom.2 < cg.nodes.length := (List.getElem?_eq_some_iff.mp hbotLookup).1
   have eTop : rk run.coordinateProper.rank index = rk rr.ranks index := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hindexLt
     rw [hc] at h2
     exact h2
   have eMember : rk run.coordinateProper.rank memberIndex = rk rr.ranks memberIndex := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hmemberLt
     rw [hc] at h2
     exact h2
   have eBottom : rk run.coordinateProper.rank bottom.2 = rk rr.ranks bottom.2 := by
     have h2 := prepared_coordinate_original_rk (P := execution.params) hrr hranks hbotLt
     rw [hc] at h2
     exact h2
   have rEqT := run_rank_eq_coordinate hrun index
   have rEqM := run_rank_eq_coordinate hrun memberIndex
   have rEqB := run_rank_eq_coordinate hrun bottom.2
   obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, hroute, _, hry, hyseq, _⟩ :=
     componentRun_spec hrun
   have hrankEq : ∀ x, rk run.proper.rank x = rk run.coordinateProper.rank x := by
     intro x
     rw [← hdrop, OrderImpl.dropSynthetic_rank, (proxyWidths_rel hproxy).2.1]
   have hlenEq : run.proper.nodes.length = run.coordinateProper.nodes.length := by
     rw [← hdrop]; exact (proxyWidths_rel hproxy).2.2.1
   have hcov :=
     (RouteImpl.layersOk_spec (RouteImpl.routeWithLanes_geometry hroute).1).2.2.2.1
   have hindexLen : index < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun index hindexLt
   have hmemberLen : memberIndex < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun memberIndex hmemberLt
   have hbotLen : bottom.2 < run.proper.nodes.length :=
     componentRun_original_nodes_covered hrun bottom.2 hbotLt
   obtain ⟨tcoord, htcoord, htb, htd, htpath⟩ :=
     proper_top_coordinate_record hrun hnode hgroup
   obtain ⟨tprop, htprop, htpropP⟩ := proper_top_proper_clusterPath hrun htcoord htb
   have hdeclT : node.clusterPath.contains node.decl = true :=
     (proper_top_decl_path execution.graph_eq hnode hgroup).2
   have htcontains : tprop.node.clusterPath.contains node.decl = true := by
     rw [htpropP, htpath]; exact hdeclT
   have hgroupGet : cg.nodes.getD index default = node := by
     simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : (cg.nodes.getD index default).border = -2 := by
     rw [hgroupGet]; exact hgroup
   have htqmem : (tprop, index) ∈ run.proper.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr htprop
   have htcontains' : (tprop, index).1.node.clusterPath.contains
     (cg.nodes.getD index default).decl = true := by
     rw [hgroupGet]; exact htcontains
   have htopLe : (frameRect execution.params cg run index).y ≤
     (Labels.rectAt run.proper run.xs run.ys index).y :=
     (frameRect_member_vertical (P := execution.params) (cg := cg) (run := run)
       (i := index) (q := (tprop, index)) hframeGroup htqmem htcontains').1
   obtain ⟨ltT, hlyT, _, hnnT⟩ := hcov index hindexLen
   obtain ⟨ltM, hlyM, _, hnnM⟩ := hcov memberIndex hmemberLen
   obtain ⟨ltB, hlyB, _, hnnB⟩ := hcov bottom.2 hbotLen
   rw [rEqT] at hlyT hnnT
   rw [rEqM] at hlyM hnnM
   rw [rEqB] at hlyB hnnB
   have hTopY : (Labels.rectAt run.proper run.xs run.ys index).y = run.ys.getD index 0 := rfl
   have hMemY : (Labels.rectAt run.proper run.xs run.ys memberIndex).y = run.ys.getD memberIndex 0 := rfl
   have hMemBH : (Labels.rectAt run.proper run.xs run.ys memberIndex).y +
       (Labels.rectAt run.proper run.xs run.ys memberIndex).h =
       run.ys.getD memberIndex 0 + RouteImpl.nodeH run.proper memberIndex := rfl
   have hTopBand := (fbs_run_node_band hrun index hindexLen).1
   have hMemBandLo := (fbs_run_node_band hrun memberIndex hmemberLen).1
   have hMemBandHi := (fbs_run_node_band hrun memberIndex hmemberLen).2
   rw [rEqT] at hTopBand
   rw [rEqM] at hMemBandLo hMemBandHi
   have hTopProxy : run.ys.getD index 0 =
       run.top.getD (rk run.coordinateProper.rank index).toNat 0 := by
     have h := componentRun_group_proxy_ys_eq_top hrun hnode hgroup hindexLt
     rw [rEqT] at h
     exact h
   have hltTM : (rk run.coordinateProper.rank index).toNat <
       (rk run.coordinateProper.rank memberIndex).toNat := by
     have h1 := eTop
     have h2 := eMember
     have h3 := hintervTop
     have h4 := hnnT
     have h5 := hnnM
     omega
   have hbandTM := rankAxis_band_top_strict hry _ _ _ _ hltTM hlyT hlyM
   have hHtNonneg : 0 ≤ CoordsImpl.layerHeight run.coordinateProper ltT :=
     CoordsImpl.layerHeight_nonneg _ _
   have hTopStrict : run.ys.getD index 0 < run.ys.getD memberIndex 0 := by
     have h1 := hTopProxy
     have h2 := hbandTM
     have h3 := hMemBandLo
     have h4 := hHtNonneg
     omega
   have hTopDone : (frameRect execution.params cg run index).y <
       (Labels.rectAt run.proper run.xs run.ys memberIndex).y := by
     have h1 := htopLe
     have h2 := hTopY
     have h3 := hTopStrict
     have h4 := hMemY
     omega
   -- bottom side
   have hbotFind := hbottom
   have hbordV : bottom.1.border = 2 := by
     have hcond := List.find?_some hbotFind
     simp only [Bool.and_eq_true, beq_iff_eq] at hcond
     exact hcond.1
   have hdeclV : bottom.1.decl = node.decl := by
     have hcond := List.find?_some hbotFind
     simp only [Bool.and_eq_true, beq_iff_eq] at hcond
     exact hcond.2
   have hnodeB : cg.nodes[bottom.2]? = some bottom.1 := hbotLookup
   obtain ⟨bcoord, hbcoord, hbb, hbd, hbpath, bh0⟩ :=
     proper_bottom_coordinate_record hrun hnodeB hbordV
   obtain ⟨bprop, hbprop, hbpropP, hnodeH⟩ :=
     proper_bottom_proper_node hrun hbcoord hbb bh0
   have hdeclB : bottom.1.clusterPath.contains bottom.1.decl = true :=
     (proper_bottom_decl_path execution.graph_eq hnodeB hbordV).2
   have hbcontains : bprop.node.clusterPath.contains node.decl = true := by
     rw [hbpropP, hbpath, ← hdeclV]; exact hdeclB
   have hbqmem : (bprop, bottom.2) ∈ run.proper.nodes.zipIdx :=
     List.mk_mem_zipIdx_iff_getElem?.mpr hbprop
   have hbmem : Labels.rectAt run.proper run.xs run.ys (bprop, bottom.2).2 ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains node.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := by
     apply List.mem_filterMap.mpr
     refine ⟨(bprop, bottom.2), hbqmem, ?_⟩
     rw [ite_eq_left hbcontains]
   have hbmem' : Labels.rectAt run.proper run.xs run.ys bottom.2 ∈
       (run.proper.nodes.zipIdx.filterMap fun q =>
         if q.1.node.clusterPath.contains node.decl then
           some (Labels.rectAt run.proper run.xs run.ys q.2)
         else none) := hbmem
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
   have hltMB : (rk run.coordinateProper.rank memberIndex).toNat <
       (rk run.coordinateProper.rank bottom.2).toNat := by
     have h1 := eMember
     have h2 := eBottom
     have h3 := hintervBot
     have h4 := hnnM
     have h5 := hnnB
     omega
   have hlyMD : run.layers.getD (rk run.coordinateProper.rank memberIndex).toNat [] = ltM := by
     rw [List.getD_eq_getElem?_getD, hlyM]; rfl
   have hbandMB := rankAxis_band_top_strict hry _ _ _ _ hltMB hlyM hlyB
   have hMemLtBot : run.ys.getD memberIndex 0 + RouteImpl.nodeH run.proper memberIndex <
       run.ys.getD bottom.2 0 := by
     have h1 := hMemBandHi
     have h2 := hbandMB
     have h3 := hYsV
     have hH : 0 ≤ CoordsImpl.layerHeight run.coordinateProper
         (run.layers.getD (rk run.coordinateProper.rank bottom.2).toNat []) :=
       CoordsImpl.layerHeight_nonneg _ _
     rw [hlyMD] at h1
     omega
   have hBotDone : (Labels.rectAt run.proper run.xs run.ys memberIndex).y +
       (Labels.rectAt run.proper run.xs run.ys memberIndex).h <
       (frameRect execution.params cg run index).y +
         (frameRect execution.params cg run index).h := by
     have hle := rect_bottom_le_boundsOf_bottom _ [] _ hbmem'
     have hframeBot : (frameRect execution.params cg run index).y +
         (frameRect execution.params cg run index).h =
         (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
           if q.1.node.clusterPath.contains node.decl then
             some (Labels.rectAt run.proper run.xs run.ys q.2)
           else none) []).bottom := by
       have hg : cg.nodes.getD index default = node := hgroupGet
       simp only [frameRect, hg, hgroup,
         show ((-2 : Int) != -2) = false from rfl, Bool.false_eq_true, ↓reduceIte]
       change (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
           if q.1.node.clusterPath.contains node.decl then
             some (Labels.rectAt run.proper run.xs run.ys q.2)
           else none) []).minY +
         ((boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
           if q.1.node.clusterPath.contains node.decl then
             some (Labels.rectAt run.proper run.xs run.ys q.2)
           else none) []).bottom - (boundsOf (run.proper.nodes.zipIdx.filterMap fun q =>
           if q.1.node.clusterPath.contains node.decl then
             some (Labels.rectAt run.proper run.xs run.ys q.2)
           else none) []).minY) = _
       omega
     have h1 := hMemBH
     have h2 := hMemLtBot
     have h3 := hBotYH
     have h4 := hle
     have h5 := hframeBot
     omega
   have hmemberFrame : frameRect execution.params cg run memberIndex =
       Labels.rectAt run.proper run.xs run.ys memberIndex := by
     obtain ⟨actual, _, _, hproper, _, _, _, _, _⟩ :=
       execution.component_member_border_interval hwf hcomp hrun hnode hgroup
         hmember hplain hinside
     have hmemberGet : cg.nodes.getD memberIndex default = member := by
       simp only [cg, List.getD_eq_getElem?_getD, hmember, Option.getD_some]
     unfold frameRect
     rw [hmemberGet]
     simp only [hplain, show ((0 : Int) != -2) = true from rfl, ↓reduceIte]
     unfold nodeRect Labels.rectAt Labels.labelRect RouteImpl.xAt RouteImpl.yAt
       RouteImpl.nodeW RouteImpl.nodeH
     simp only [List.getD_eq_getElem?_getD, hproper, Option.getD_some]
   unfold MemberFrameStrictVertical
   rw [hmemberFrame]
   exact ⟨hTopDone, hBotDone⟩

 /-- The parent frame right edge is positive, discharged: the frame contains a
 side marker of width `clusterBorderW ≥ 1` at a nonnegative centre, so the
 frame right edge exceeds zero. Discharges `ParentFrameRightEdgePos`. -/
 theorem parentFrameRightEdgePos_of_executed {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {index memberIndex : Nat} {node member : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
     (hgroup : node.border = -2)
     (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
     (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
     ParentFrameRightEdgePos execution.params (componentCandidate execution.graph comp candidate)
       run index := by
   let cg := componentCandidate execution.graph comp candidate
   obtain ⟨_, _, _, right, _, _, _, _, _, _, _, _, _, hright, _⟩ :=
     execution.component_member_bracket hwf hcomp hrun hnode hgroup hmember hplain hinside
   obtain ⟨hrightFinal, hrightX⟩ := componentRun_border_record hrun hright (Or.inr rfl)
   have hgroupGet : cg.nodes.getD index default = node := by
     simp only [cg, List.getD_eq_getElem?_getD, hnode, Option.getD_some]
   have hframeGroup : (cg.nodes.getD index default).border = -2 := by
     rw [hgroupGet]; exact hgroup
   obtain ⟨_, _, hgroupSource⟩ := componentCandidate_nonplain_source hnode (by omega)
   obtain ⟨box, _, hdecl, hpath⟩ := execution.group_node_path_source hgroupSource hgroup
   have hgroupPath : node.clusterPath = Compound.path inp.boxes box ++ [node.decl] := by
     simpa only [hdecl] using hpath
   have hrightPath : (OrderImpl.borderRight (titleF ⟨node, false, none, false⟩, index)
       execution.params.clusterBorderW).node.clusterPath =
         Compound.path inp.boxes box ++ [(cg.nodes.getD index default).decl] := by
     change (titleF ⟨node, false, none, false⟩).node.clusterPath = _
     rw [(titleF_keys _).2.2.1, hgroupGet]
     exact hgroupPath
   have hrightContained := frameRect_side_marker_contained (P := execution.params) (cg := cg)
     hframeGroup (List.mk_mem_zipIdx_iff_getElem?.mpr hrightFinal) (Or.inr rfl) hrightPath
   have hmarker : (Labels.rectAt run.proper run.xs run.ys right).x +
       (Labels.rectAt run.proper run.xs run.ys right).w =
       run.xs.getD right 0 - Int.fdiv execution.params.clusterBorderW 2 +
         execution.params.clusterBorderW := by
     simp only [Labels.rectAt, Labels.labelRect, RouteImpl.xAt, RouteImpl.nodeW,
       hrightFinal, OrderImpl.borderRight]
   have hcbw : 1 ≤ execution.params.clusterBorderW :=
     checkedParams_clusterBorderW_ge_one execution.checked
   have hxsNonneg := fbs_coordinate_centers_nonneg hrun right
   unfold ParentFrameRightEdgePos
   have h1 : (Labels.rectAt run.proper run.xs run.ys right).x +
       (Labels.rectAt run.proper run.xs run.ys right).w ≤
       (frameRect execution.params cg run index).x +
         (frameRect execution.params cg run index).w := hrightContained.2.1
   have h2 : 0 < (Labels.rectAt run.proper run.xs run.ys right).x +
       (Labels.rectAt run.proper run.xs run.ys right).w := by
     have e1 := hmarker
     simp only [Int.fdiv_eq_ediv_of_nonneg _ (show (0 : Int) ≤ 2 by decide)] at e1
     have e2 := hrightX
     omega
   change 0 < (frameRect execution.params cg run index).x +
     (frameRect execution.params cg run index).w
   omega

 /-- Primed member strict theorem: no residual hypotheses. The vertical
 sides are discharged by `memberFrameStrictVertical_of_executed`; no extra
 positivity premise is needed (gap and border-width positivity both follow
 from the executed run). -/
 theorem SceneExecution.component_member_strictInside' {inp : Input} {o : Options}
     {res : FamilyResult} (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o))
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
       execution.measured orderOptions = .ok run)
     {index memberIndex : Nat} {node member : Node}
     (hnode : (componentCandidate execution.graph comp candidate).nodes[index]? = some node)
     (hgroup : node.border = -2)
     (hmember : (componentCandidate execution.graph comp candidate).nodes[memberIndex]? = some member)
     (hplain : member.border = 0) (hinside : member.clusterPath.contains node.decl = true) :
     (frameRect execution.params (componentCandidate execution.graph comp candidate) run index).StrictInside
       (frameRect execution.params (componentCandidate execution.graph comp candidate) run memberIndex) :=
   execution.component_member_strictInside hwf hcomp hrun hnode hgroup hmember hplain hinside
     (memberFrameStrictVertical_of_executed execution hwf hcomp hrun hnode hgroup hmember hplain hinside)

 end Elegant.Layered.PipelineImpl
