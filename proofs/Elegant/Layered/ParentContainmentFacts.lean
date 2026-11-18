import Elegant.Layered.SceneBounds

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

private theorem member_rect_in_frame_hull {cg : Graph} {run : Run} {i : Nat}
    {q : ProperNode × Nat} (hq : q ∈ run.proper.nodes.zipIdx)
    (hp : q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = true) :
    Labels.rectAt run.proper run.xs run.ys q.2 ∈
      (run.proper.nodes.zipIdx.filterMap fun entry =>
        if entry.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys entry.2)
        else none) := by
  apply List.mem_filterMap.mpr
  refine ⟨q, hq, ?_⟩
  rw [ite_eq_left hp]

private theorem side_rect_in_frame_hull {cg : Graph} {run : Run} {i : Nat}
    {q : ProperNode × Nat} (hq : q ∈ run.proper.nodes.zipIdx)
    (hb : q.1.node.border = -1 ∨ q.1.node.border = 1)
    (hp : q.1.node.clusterPath.getLast? = some (cg.nodes.getD i default).decl) :
    Labels.rectAt run.proper run.xs run.ys q.2 ∈
      (run.proper.nodes.zipIdx.filterMap fun entry =>
        if (entry.1.node.border == -1 || entry.1.node.border == 1) &&
            entry.1.node.clusterPath.getLast? == some (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys entry.2)
        else none) := by
  apply List.mem_filterMap.mpr
  refine ⟨q, hq, ?_⟩
  rcases hb with hb | hb <;> simp [hb, hp]

theorem frameRect_member_vertical {P : Params} {cg : Graph} {run : Run} {i : Nat}
    {q : ProperNode × Nat} (hf : (cg.nodes.getD i default).border = -2)
    (hq : q ∈ run.proper.nodes.zipIdx)
    (hp : q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = true) :
    (frameRect P cg run i).y ≤ (Labels.rectAt run.proper run.xs run.ys q.2).y ∧
      (Labels.rectAt run.proper run.xs run.ys q.2).y +
        (Labels.rectAt run.proper run.xs run.ys q.2).h ≤
          (frameRect P cg run i).y + (frameRect P cg run i).h := by
  have hm := member_rect_in_frame_hull hq hp
  have ht := boundsOf_minY_le_rect_y _ [] _ hm
  have hb := rect_bottom_le_boundsOf_bottom _ [] _ hm
  simp only [frameRect, hf, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  constructor
  · exact ht
  · omega

theorem frameRect_side_marker_contained {P : Params} {cg : Graph} {run : Run} {i : Nat}
    {q : ProperNode × Nat} {ancestors : List Nat}
    (hf : (cg.nodes.getD i default).border = -2)
    (hq : q ∈ run.proper.nodes.zipIdx)
    (hb : q.1.node.border = -1 ∨ q.1.node.border = 1)
    (hp : q.1.node.clusterPath = ancestors ++ [(cg.nodes.getD i default).decl]) :
    (frameRect P cg run i).Contained (Labels.rectAt run.proper run.xs run.ys q.2) := by
  have hmember : q.1.node.clusterPath.contains (cg.nodes.getD i default).decl = true := by
    simp [hp]
  have hlast : q.1.node.clusterPath.getLast? = some (cg.nodes.getD i default).decl := by
    simp [hp]
  have hm := side_rect_in_frame_hull hq hb hlast
  have hl := boundsOf_minX_le_rect_x _ [] _ hm
  have hr := rect_right_le_boundsOf_right _ [] _ hm
  have hv := frameRect_member_vertical (P := P) hf hq hmember
  unfold Rect.Contained
  refine ⟨?_, ?_, hv.1, hv.2⟩ <;>
    simp only [frameRect, hf, show ((-2 : Int) != -2) = false from rfl,
      Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem frameRect_side_marker_display_contained {P : Params} {cg : Graph}
    {run : Run} {i : Nat} {q : ProperNode × Nat} {ancestors : List Nat}
    (hf : (cg.nodes.getD i default).border = -2)
    (hq : q ∈ run.proper.nodes.zipIdx)
    (hb : q.1.node.border = -1 ∨ q.1.node.border = 1)
    (hp : q.1.node.clusterPath = ancestors ++ [(cg.nodes.getD i default).decl])
    (direction : Direction) (height dx dy : Int) :
    (shiftRect dx dy (orientRect direction height (frameRect P cg run i))).Contained
      (shiftRect dx dy
        (orientRect direction height (Labels.rectAt run.proper run.xs run.ys q.2))) := by
  have h := frameRect_side_marker_contained (P := P) hf hq hb hp
  unfold Rect.Contained at h ⊢
  unfold shiftRect orientRect
  cases direction <;> dsimp only at * <;> omega

end Elegant.Layered.PipelineImpl
