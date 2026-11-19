import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.LabelsC8bFacts
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

 end Elegant.Layered.PipelineImpl
