import ElegantGeometry.Basic
import Elegant.Model
import Elegant.Scene
import Elegant.Layered.Pipeline
import Elegant.Layered.Pack
import Elegant.Layered.Labels
import Elegant.Layered.PipelineFacts

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Elegant
namespace Layered
namespace PipelineImpl

/-- Same-length pointwise relation; unlike `zip`, neither list can be truncated. -/
inductive SizingRelated {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : SizingRelated r [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      r a b → SizingRelated r as bs → SizingRelated r (a :: as) (b :: bs)

theorem paramsOf_some {profile : Profile} {kind : String} {Q : Params}
    (h : paramsOf profile kind = some Q) :
    ∃ B, baseParams profile = some B ∧ Q = B.forKind profile kind := by
  unfold paramsOf at h
  cases hb : baseParams profile with
  | none => simp [hb] at h
  | some B =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    exact ⟨B, rfl, h.symm⟩

theorem checkedParams_some {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) :
    ∃ B, baseParams profile = some B ∧ P = B.forKind profile kind := by
  unfold checkedParams at h
  cases hp : paramsOf profile kind with
  | none => simp [hp] at h
  | some Q =>
    rw [hp] at h
    by_cases hv : Q.Valid
    · simp only [hv, ↓reduceIte, Except.ok.injEq] at h
      subst P
      exact paramsOf_some hp
    · simp only [hv, ↓reduceIte] at h
      cases h

/-- These signs are facts of the profile constants, not of `Params.Valid`. -/
theorem checkedParams_sizing_nonneg {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) :
    0 ≤ P.lineH ∧ 0 ≤ P.clusterPad ∧ 0 ≤ P.nodePadX ∧
      0 ≤ P.nodePadY ∧ 0 ≤ P.nodeBorder := by
  have table : match baseParams profile with
      | none => True
      | some Q => 0 ≤ Q.lineH ∧ 0 ≤ Q.clusterPad ∧ 0 ≤ Q.nodePadX ∧
          0 ≤ Q.nodePadY ∧ 0 ≤ Q.nodeBorder := by
    letI : Decidable (match baseParams profile with
        | none => True
        | some Q => 0 ≤ Q.lineH ∧ 0 ≤ Q.clusterPad ∧ 0 ≤ Q.nodePadX ∧
            0 ≤ Q.nodePadY ∧ 0 ≤ Q.nodeBorder) := by
      cases baseParams profile <;> infer_instance
    cases profile <;> decide
  obtain ⟨B, hb, rfl⟩ := checkedParams_some h
  simpa only [hb, Params.forKind] using table

theorem checkedParams_lineH_nonneg {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 ≤ P.lineH :=
  (checkedParams_sizing_nonneg h).1

theorem checkedParams_clusterPad_nonneg {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 0 ≤ P.clusterPad :=
  (checkedParams_sizing_nonneg h).2.1

/-- The successful constructor keeps the declaration and fits the measured text.
The dimensions here are before `orientNode` and before fixed-size replacement. -/
theorem sizedNode_text_fit {P : Params} {decl : Nat} {lines : List Measure.Line}
    {n : Node} (hx : 0 ≤ P.nodePadX) (hy : 0 ≤ P.nodePadY)
    (hb : 0 ≤ P.nodeBorder) (h : sizedNode P decl lines = .ok n) :
    n.decl = decl ∧
      lines.foldl (fun w l => max w l.width) 0 ≤ n.w ∧
      (lines.length : Int) * P.lineH ≤ n.h := by
  unfold sizedNode at h
  obtain ⟨size, hs, h⟩ := bind_ok h
  have hn := Except.ok.inj h
  subst n
  unfold nodeSize at hs
  dsimp only at hs
  split at hs
  · simp at hs
  · have heq := Except.ok.inj hs
    subst size
    dsimp only
    have hw := Int.le_max_left
      (lines.foldl (fun w l => max w l.width) 0 + 2 * P.nodePadX + 2 * P.nodeBorder)
      P.nodeMinW
    have hh := Int.le_max_left
      ((lines.length : Int) * P.lineH + 2 * P.nodePadY + 2 * P.nodeBorder)
      P.nodeMinH
    exact ⟨rfl, by omega, by omega⟩

/-- Every result is related to its actual input line list and declaration index;
no statement about arbitrary later accumulators is assumed. -/
theorem sizedNodes_text_fit {P : Params} {lines : List (List Measure.Line)}
    {ns : List Node} (hx : 0 ≤ P.nodePadX) (hy : 0 ≤ P.nodePadY)
    (hb : 0 ≤ P.nodeBorder) (h : sizedNodes P lines = .ok ns) :
    SizingRelated (fun q n =>
      n.decl = q.2 ∧
      q.1.foldl (fun w l => max w l.width) 0 ≤ n.w ∧
      (q.1.length : Int) * P.lineH ≤ n.h) lines.zipIdx ns := by
  have go : ∀ (qs : List (List Measure.Line × Nat)) (out : List Node),
      qs.mapM (fun q => sizedNode P q.2 q.1) = .ok out →
      SizingRelated (fun q n =>
        n.decl = q.2 ∧
        q.1.foldl (fun w l => max w l.width) 0 ≤ n.w ∧
        (q.1.length : Int) * P.lineH ≤ n.h) qs out := by
    intro qs
    induction qs with
    | nil =>
      intro out ho
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at ho
      subst out
      exact .nil
    | cons q qs ih =>
      intro out ho
      rw [List.mapM_cons] at ho
      obtain ⟨n, hn, ho⟩ := bind_ok ho
      obtain ⟨rest, hr, ho⟩ := bind_ok ho
      have heq := Except.ok.inj ho
      subst out
      exact .cons (sizedNode_text_fit hx hy hb hn) (ih rest hr)
  exact go lines.zipIdx ns h

/-- Sizing fit with all padding signs discharged by the selected profile. -/
theorem checkedParams_sizedNodes_text_fit {profile : Profile} {kind : String} {P : Params}
    {lines : List (List Measure.Line)} {ns : List Node}
    (hp : checkedParams profile kind = .ok P) (hn : sizedNodes P lines = .ok ns) :
    SizingRelated (fun q n =>
      n.decl = q.2 ∧
      q.1.foldl (fun w l => max w l.width) 0 ≤ n.w ∧
      (q.1.length : Int) * P.lineH ≤ n.h) lines.zipIdx ns := by
  obtain ⟨_, _, hx, hy, hb⟩ := checkedParams_sizing_nonneg hp
  exact sizedNodes_text_fit hx hy hb hn

/-- Syntactic bridge connecting `stackSize` width to `Labels.stackWidth`. -/
theorem stackSize_width_eq (slot : Int) (labels : List MeasuredLabel) :
    (stackSize slot labels).width = Labels.stackWidth (labels.map fun l => (l.width, l.height)) :=
  by simpa only [stackSize] using
    (Labels.stackWidth_map_pair (fun l : MeasuredLabel => l.width) (fun l => l.height) labels).symm

/-- Syntactic bridge connecting `stackSize` height to `Labels.stackHeight`. -/
theorem stackSize_height_eq (slot : Int) (labels : List MeasuredLabel) :
    (stackSize slot labels).height = Labels.stackHeight slot (labels.map fun l => (l.width, l.height)) :=
  by simpa only [stackSize] using
    (Labels.stackHeight_map_pair slot (fun l : MeasuredLabel => l.width) (fun l => l.height) labels).symm

/-- Rectangle constructor cellBounds equation. -/
theorem cellBounds_rect_eq (canvas : Size) (r : Rect) (paint : Paint) :
    Primitive.cellBounds canvas (.rect r paint) = Size.containsCellRect canvas r := rfl

/-- Rounded rectangle constructor cellBounds equation. -/
theorem cellBounds_roundRect_eq (canvas : Size) (r : Rect) (rad : Int) (paint : Paint) :
    Primitive.cellBounds canvas (.roundRect r rad paint) = Size.containsCellRect canvas r := rfl

/-- Text constructor cellBounds equation. -/
theorem cellBounds_text_eq (canvas : Size) (t : SceneText) :
    Primitive.cellBounds canvas (.text t) = Size.containsCellRect canvas t.rect := rfl

/-- Polyline constructor cellBounds equation. -/
theorem cellBounds_polyline_eq (canvas : Size) (pts : List Point) (corner : Int) (paint : Paint) :
    Primitive.cellBounds canvas (.polyline pts corner paint) = pts.all (Size.containsCell canvas) := rfl

/-- Marker reference constructor cellBounds equation. -/
theorem cellBounds_markerRef_eq (canvas : Size) (name : String) (pos : Point) (axis : MarkerAxis) :
    Primitive.cellBounds canvas (.markerRef name pos axis) = Size.containsCell canvas pos := rfl

/-- Containment preservation from an outer containing rectangle to an inner rectangle. -/
theorem containsCellRect_of_contained {canvas : Size} {outer inner : Rect}
    (h_outer : Size.containsCellRect canvas outer = true)
    (h_cont : outer.Contained inner)
    (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h) :
    Size.containsCellRect canvas inner = true := by
  unfold Size.containsCellRect at h_outer ⊢
  simp only [decide_eq_true_iff] at h_outer ⊢
  unfold Rect.Contained at h_cont
  omega

/-- Truncated division by two for non-negative integers stays non-negative and bounded. -/
theorem tdiv_two_bounds {a : Int} (ha : 0 ≤ a) :
    0 ≤ Int.tdiv a 2 ∧ Int.tdiv a 2 ≤ a := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  show 0 ≤ ((n / 2 : Nat) : Int) ∧ ((n / 2 : Nat) : Int) ≤ (n : Int)
  exact ⟨by omega, by omega⟩

/-- Node text label rectangle containment inside the node bounding box. -/
theorem node_text_rect_containsCellRect (canvas : Size) (r : Rect) (linesCount : Nat) (lineH : Int)
    (hr : Size.containsCellRect canvas r = true)
    (hlh : 0 ≤ lineH)
    (hlines : (linesCount : Int) * lineH ≤ r.h) :
    Size.containsCellRect canvas
      ⟨r.x, r.y + Int.tdiv (r.h - (linesCount : Int) * lineH) 2, r.w, (linesCount : Int) * lineH⟩ = true := by
  unfold Size.containsCellRect at hr ⊢
  simp only [decide_eq_true_iff] at hr ⊢
  have hpos : 0 ≤ (linesCount : Int) * lineH :=
    Int.mul_nonneg (by omega) hlh
  have hdiff : 0 ≤ r.h - (linesCount : Int) * lineH := by omega
  have ⟨htdiv_ge, htdiv_le⟩ := tdiv_two_bounds hdiff
  refine ⟨hr.1, by omega, hr.2.2.1, hpos, hr.2.2.2.2.1, by omega⟩

/-- Cluster title rectangle containment inside the group frame rectangle. The nonnegative
text height comes from the actual parameter derivation (`checkedParams_lineH_nonneg`), not
from the upper height bound: `clusterPad + (max 1 lines.length) * lineH ≤ rect.h` does not
imply `(max 1 lines.length) * lineH ≥ 0` for arbitrary `P.lineH`. -/
theorem title_rect_containsCellRect (canvas : Size) (P : Params) (rect : Rect) (lines : List Measure.Line)
    (hr : Size.containsCellRect canvas rect = true)
    (hlh : 0 ≤ P.lineH)
    (hpad : 0 ≤ P.clusterPad)
    (hpadw : 2 * P.clusterPad ≤ rect.w)
    (hpadh : P.clusterPad + (max 1 lines.length : Int) * P.lineH ≤ rect.h) :
    Size.containsCellRect canvas (titleRect P rect lines) = true := by
  unfold Size.containsCellRect at hr ⊢
  simp only [decide_eq_true_iff] at hr ⊢
  unfold titleRect
  dsimp only
  have hw : max 0 (rect.w - 2 * P.clusterPad) = rect.w - 2 * P.clusterPad := by
    apply Int.max_eq_right
    omega
  rw [hw]
  have hm : (0 : Int) ≤ max 1 (lines.length : Int) :=
    Int.le_trans (by omega) (Int.le_max_left _ _)
  refine ⟨by omega, by omega, by omega, Int.mul_nonneg hm hlh, by omega, by omega⟩

/-- Direct shift and margin expansion preserves rectangle containment in canvas. -/
theorem shiftRect_margin_containsCellRect (W H margin : Int) (r : Rect)
    (hrx : 0 ≤ r.x) (hrw : r.x + r.w ≤ W) (hry : 0 ≤ r.y) (hrh : r.y + r.h ≤ H)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h) (hm : 0 ≤ margin) :
    Size.containsCellRect ⟨W + 2 * margin, H + 2 * margin⟩ (shiftRect margin margin r) = true := by
  unfold Size.containsCellRect shiftRect
  simp only [decide_eq_true_iff]
  omega

/-- Direct shift and margin expansion places points strictly within canvas bounds. -/
theorem shiftPoint_margin_containsCell (W H margin : Int) (p : Point)
    (hpx : 0 ≤ p.x) (hpw : p.x ≤ W) (hpy : 0 ≤ p.y) (hph : p.y ≤ H)
    (hm : 1 ≤ margin) :
    Size.containsCell ⟨W + 2 * margin, H + 2 * margin⟩ (shiftPoint margin margin p) = true := by
  unfold Size.containsCell shiftPoint
  simp only [decide_eq_true_iff]
  omega

/-- Orientation and margin shift preserves rectangle containment across all directions. -/
theorem orient_shiftRect_containsCellRect (d : Direction) (W H margin : Int) (r : Rect)
    (hr : 0 ≤ r.x ∧ r.x + r.w ≤ W ∧ 0 ≤ r.y ∧ r.y + r.h ≤ H ∧ 0 ≤ r.w ∧ 0 ≤ r.h)
    (hm : 0 ≤ margin) :
    Size.containsCellRect (orientCanvas d (W + 2 * margin) (H + 2 * margin))
      (shiftRect margin margin (orientRect d H r)) = true := by
  unfold Size.containsCellRect shiftRect orientRect orientCanvas
  simp only [decide_eq_true_iff]
  cases d <;> dsimp <;> omega

/-- Orientation and margin shift places points strictly within canvas bounds across all directions. -/
theorem orient_shiftPoint_containsCell (d : Direction) (W H margin : Int) (p : Point)
    (hp : 0 ≤ p.x ∧ p.x ≤ W ∧ 0 ≤ p.y ∧ p.y ≤ H)
    (hm : 1 ≤ margin) :
    Size.containsCell (orientCanvas d (W + 2 * margin) (H + 2 * margin))
      (shiftPoint margin margin (orientPoint d H p)) = true := by
  unfold Size.containsCell shiftPoint orientPoint orientCanvas
  simp only [decide_eq_true_iff]
  cases d <;> dsimp <;> omega

/-- Polyline cellBounds holds when all points are within the canvas. -/
theorem polyline_cellBounds_of_points (canvas : Size) (pts : List Point) (corner : Int) (paint : Paint)
    (hp : ∀ p ∈ pts, Size.containsCell canvas p = true) :
    Primitive.cellBounds canvas (.polyline pts corner paint) = true := by
  unfold Primitive.cellBounds
  rw [List.all_eq_true]
  exact hp

/-- Marker reference cellBounds holds when its position is within the canvas. -/
theorem markerRefAt_cellBounds (canvas : Size) (name : String) (pos prev : Point)
    (hp : Size.containsCell canvas pos = true) :
    ∀ item ∈ markerRefAt name pos prev, Primitive.cellBounds canvas item = true := by
  intro item hitem
  unfold markerRefAt at hitem
  split at hitem
  · simp at hitem
  · simp only [List.mem_singleton] at hitem
    subst hitem
    unfold Primitive.cellBounds
    exact hp

/-- Edge items (polyline and boundary markers) satisfy primitive cellBounds. -/
theorem edgeItems_cellBounds (P : Params) (canvas : Size) (pts : List Point) (e : EdgeOptions)
    (hp : ∀ p ∈ pts, Size.containsCell canvas p = true) :
    ∀ item ∈ edgeItems P pts e, Primitive.cellBounds canvas item = true := by
  intro item hitem
  unfold edgeItems at hitem
  split at hitem
  · simp at hitem
  · split at hitem
    · simp only [List.mem_singleton] at hitem
      subst hitem
      exact polyline_cellBounds_of_points canvas pts P.cornerRadius (edgePaint e.stroke) hp
    · rename_i _ hlen
      have hlen2 : 2 ≤ pts.length := by omega
      have h0_mem : pts.getD 0 default ∈ pts := by
        cases pts with
        | nil => contradiction
        | cons x xs => simp [List.getD]
      have hlast_mem : pts.getD (pts.length - 1) default ∈ pts := by
        have hpos : pts.length - 1 < pts.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]
        exact List.getElem_mem hpos
      simp only [List.mem_cons, List.mem_append] at hitem
      rcases hitem with rfl | hm1 | hm2
      · exact polyline_cellBounds_of_points canvas pts P.cornerRadius (edgePaint e.stroke) hp
      · exact markerRefAt_cellBounds canvas e.markerStart (pts.getD 0 default) (pts.getD 1 default) (hp _ h0_mem) item hm1
      · exact markerRefAt_cellBounds canvas e.markerEnd (pts.getD (pts.length - 1) default) (pts.getD (pts.length - 2) default) (hp _ hlast_mem) item hm2

/-- Node items (frame rectangle and centered text label) satisfy primitive cellBounds. -/
theorem nodeItems_cellBounds (P : Params) (canvas : Size) (r : Rect) (lines : List Measure.Line)
    (hr : Size.containsCellRect canvas r = true)
    (hlh : 0 ≤ P.lineH)
    (hlines : (lines.length : Int) * P.lineH ≤ r.h) :
    ∀ item ∈ nodeItems P r lines, Primitive.cellBounds canvas item = true := by
  intro item hitem
  unfold nodeItems at hitem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl
  · unfold Primitive.cellBounds
    exact hr
  · unfold Primitive.cellBounds
    exact node_text_rect_containsCellRect canvas r lines.length P.lineH hr hlh hlines

/-- Group items (frame rectangle and title text label) satisfy primitive cellBounds. -/
theorem groupItems_cellBounds (P : Params) (canvas : Size) (r : Rect) (lines : List Measure.Line)
    (hr : Size.containsCellRect canvas r = true)
    (hlh : 0 ≤ P.lineH)
    (hpad : 0 ≤ P.clusterPad)
    (hpadw : 2 * P.clusterPad ≤ r.w)
    (hpadh : P.clusterPad + (max 1 lines.length : Int) * P.lineH ≤ r.h) :
    ∀ item ∈ groupItems P r lines, Primitive.cellBounds canvas item = true := by
  intro item hitem
  unfold groupItems at hitem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl
  · unfold Primitive.cellBounds
    exact hr
  · unfold Primitive.cellBounds
    exact title_rect_containsCellRect canvas P r lines hr hlh hpad hpadw hpadh

/-- `applyTitles` preserves primitive cellBounds when updated titles satisfy bounds. -/
theorem applyTitles_cellBounds (titles : List (String × Rect)) (canvas : Size)
    (ht : ∀ t ∈ titles, Size.containsCellRect canvas t.2 = true)
    (groups : List Group)
    (hg : ∀ g ∈ groups, ∀ item ∈ g.items, Primitive.cellBounds canvas item = true) :
    ∀ g ∈ applyTitles titles groups, ∀ item ∈ g.items, Primitive.cellBounds canvas item = true := by
  intro g hg_mem item hitem
  unfold applyTitles at hg_mem
  obtain ⟨origG, horigG, rfl⟩ := List.mem_map.mp hg_mem
  split at hitem
  · exact hg origG horigG item hitem
  · rename_i title hfind
    have htitle_mem : title ∈ titles := List.mem_of_find?_eq_some hfind
    have htitle_bound := ht title htitle_mem
    obtain ⟨origItem, horigItem, rfl⟩ := List.mem_map.mp hitem
    split at hitem
    · exact htitle_bound
    · exact hg origG horigG origItem horigItem

/-- Emitted `sceneItems` satisfy primitive cellBounds when boxes, routes, and labels are bounded. -/
theorem sceneItems_cellBounds (P : Params) (canvas : Size) (inp : Input)
    (boxes : List Box) (routes : List Route) (lines : List (List Measure.Line))
    (labels : List SceneLabel)
    (hlh : 0 ≤ P.lineH)
    (hpad : 0 ≤ P.clusterPad)
    (hboxes : ∀ q ∈ boxes.zipIdx,
      Size.containsCellRect canvas q.1.rect = true ∧
      (q.1.role == "node" → ((lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" → 2 * P.clusterPad ≤ q.1.rect.w ∧
        P.clusterPad + (max 1 (lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h))
    (hroutes : ∀ q ∈ routes.zipIdx, ∀ p ∈ q.1.points, Size.containsCell canvas p = true)
    (hlabels : ∀ l ∈ labels, Size.containsCellRect canvas l.rect = true) :
    ∀ g ∈ sceneItems P inp boxes routes lines labels,
      ∀ item ∈ g.items, Primitive.cellBounds canvas item = true := by
  intro g hg item hitem
  unfold sceneItems at hg
  simp only [List.mem_append] at hg
  rcases hg with (hg_grp | hg_edge) | hg_node
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg_grp
    have hq_mem : q ∈ boxes.zipIdx := (List.mem_filter.mp hq).1
    have hrole : q.1.role == "group" := (List.mem_filter.mp hq).2
    have hq_box := hboxes q hq_mem
    rw [hrole] at hq_box
    simp only [true_implies] at hq_box
    exact groupItems_cellBounds P canvas q.1.rect (lines.getD q.2 []) hq_box.1 hlh hpad hq_box.2.2.1 hq_box.2.2.2 item hitem
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg_edge
    simp only [List.mem_append] at hitem
    rcases hitem with h_edge | h_lbl
    · have hpts := hroutes q hq
      exact edgeItems_cellBounds P canvas q.1.points (inp.edges.getD q.2 EdgeOptions.plain) hpts item h_edge
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h_lbl
      have hl_mem : l ∈ labels := (List.mem_filter.mp hl).1
      have hl_rect := hlabels l hl_mem
      unfold Primitive.cellBounds
      exact hl_rect
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg_node
    have hq_mem : q ∈ boxes.zipIdx := (List.mem_filter.mp hq).1
    have hrole : q.1.role == "node" := (List.mem_filter.mp hq).2
    have hq_box := hboxes q hq_mem
    rw [hrole] at hq_box
    simp only [true_implies] at hq_box
    exact nodeItems_cellBounds P canvas q.1.rect (lines.getD q.2 []) hq_box.1 hlh hq_box.2.1 item hitem

/-- Scene primitiveBoundsCheck follows when canvas dimensions and all group items are bounded. -/
theorem scene_primitiveBoundsCheck_of_items (s : Scene)
    (hcw : 0 ≤ s.canvas.w) (hch : 0 ≤ s.canvas.h)
    (hitems : ∀ g ∈ s.items, ∀ item ∈ g.items, Primitive.cellBounds s.canvas item = true) :
    s.PrimitiveBounds := by
  unfold Scene.PrimitiveBounds Scene.primitiveBoundsCheck
  simp only [Bool.and_eq_true_iff, decide_eq_true_iff]
  refine ⟨⟨hcw, hch⟩, ?_⟩
  rw [List.all_eq_true]
  intro g hg
  rw [List.all_eq_true]
  intro item hitem
  exact hitems g hg item hitem

/-- Shifting a part rectangle by packing coordinates preserves nonnegativity and canvas bounds. -/
theorem packed_rect_bounds {r : Rect} {dx dy partW partH canvasW canvasH : Int}
    (hrx : 0 ≤ r.x) (hrw : r.x + r.w ≤ partW)
    (hry : 0 ≤ r.y) (hrh : r.y + r.h ≤ partH)
    (hw : 0 ≤ r.w) (hh : 0 ≤ r.h)
    (hdx : 0 ≤ dx) (hpackX : dx + partW ≤ canvasW)
    (hdy : 0 ≤ dy) (hpackY : dy + partH ≤ canvasH) :
    0 ≤ (shiftRect dx dy r).x ∧
    (shiftRect dx dy r).x + (shiftRect dx dy r).w ≤ canvasW ∧
    0 ≤ (shiftRect dx dy r).y ∧
    (shiftRect dx dy r).y + (shiftRect dx dy r).h ≤ canvasH ∧
    0 ≤ (shiftRect dx dy r).w ∧
    0 ≤ (shiftRect dx dy r).h := by
  unfold shiftRect
  dsimp only
  omega

/-- Shifting a part point by packing coordinates preserves nonnegativity and canvas bounds. -/
theorem packed_point_bounds {p : Point} {dx dy partW partH canvasW canvasH : Int}
    (hpx : 0 ≤ p.x) (hpw : p.x ≤ partW)
    (hpy : 0 ≤ p.y) (hph : p.y ≤ partH)
    (hdx : 0 ≤ dx) (hpackX : dx + partW ≤ canvasW)
    (hdy : 0 ≤ dy) (hpackY : dy + partH ≤ canvasH) :
    0 ≤ (shiftPoint dx dy p).x ∧
    (shiftPoint dx dy p).x ≤ canvasW ∧
    0 ≤ (shiftPoint dx dy p).y ∧
    (shiftPoint dx dy p).y ≤ canvasH := by
  unfold shiftPoint
  dsimp only
  omega

/-- Composite producer: `sceneOf` items all satisfy `cellBounds` when constituents are bounded. -/
theorem sceneOf_items_cellBounds (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hlh : 0 ≤ P.lineH) (hpad : 0 ≤ P.clusterPad)
    (hboxes : ∀ q ∈ (sceneOf P inp o lines acc measured).boxes.zipIdx,
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas q.1.rect = true ∧
      (q.1.role == "node" → ((lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" → 2 * P.clusterPad ≤ q.1.rect.w ∧
        P.clusterPad + (max 1 (lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h))
    (hroutes : ∀ q ∈ (sceneOf P inp o lines acc measured).routes.zipIdx,
      ∀ p ∈ q.1.points, Size.containsCell (sceneOf P inp o lines acc measured).canvas p = true)
    (hlabels : ∀ l ∈ (sceneOf P inp o lines acc measured).labels,
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas l.rect = true)
    (htitles : ∀ t ∈ acc.titles.filterMap fun title => do
        let box ← inp.boxes[title.1]?
        let textLines := lines.getD title.1 []
        let width := textLines.foldl (fun value line => max value line.width) 0
        let height := (max 1 textLines.length : Int) * P.lineH
        let size := match o.direction with
          | .LR | .RL => Size.mk height width
          | .TB | .BT => Size.mk width height
        let rect := { title.2 with w := size.w, h := size.h }
        let margin := P.canvasMargin
        pure (box.id, shiftRect margin margin (orientRect o.direction acc.canvasH rect)),
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas t.2 = true) :
    ∀ g ∈ (sceneOf P inp o lines acc measured).items,
      ∀ item ∈ g.items, Primitive.cellBounds (sceneOf P inp o lines acc measured).canvas item = true := by
  intro g hg item hitem
  unfold sceneOf at hg ⊢
  dsimp only at hg ⊢
  exact applyTitles_cellBounds _ _ htitles _
    (sceneItems_cellBounds P _ inp _ _ lines _ hlh hpad hboxes hroutes hlabels) g hg item hitem

/-- Conditional helper: reduces `sceneOf` primitive bounds to containment of constituent boxes, routes, labels, and titles. -/
theorem sceneOf_primitiveBounds (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hcw : 0 ≤ (sceneOf P inp o lines acc measured).canvas.w)
    (hch : 0 ≤ (sceneOf P inp o lines acc measured).canvas.h)
    (hlh : 0 ≤ P.lineH) (hpad : 0 ≤ P.clusterPad)
    (hboxes : ∀ q ∈ (sceneOf P inp o lines acc measured).boxes.zipIdx,
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas q.1.rect = true ∧
      (q.1.role == "node" → ((lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" → 2 * P.clusterPad ≤ q.1.rect.w ∧
        P.clusterPad + (max 1 (lines.getD q.2 []).length : Int) * P.lineH ≤ q.1.rect.h))
    (hroutes : ∀ q ∈ (sceneOf P inp o lines acc measured).routes.zipIdx,
      ∀ p ∈ q.1.points, Size.containsCell (sceneOf P inp o lines acc measured).canvas p = true)
    (hlabels : ∀ l ∈ (sceneOf P inp o lines acc measured).labels,
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas l.rect = true)
    (htitles : ∀ t ∈ acc.titles.filterMap fun title => do
        let box ← inp.boxes[title.1]?
        let textLines := lines.getD title.1 []
        let width := textLines.foldl (fun value line => max value line.width) 0
        let height := (max 1 textLines.length : Int) * P.lineH
        let size := match o.direction with
          | .LR | .RL => Size.mk height width
          | .TB | .BT => Size.mk width height
        let rect := { title.2 with w := size.w, h := size.h }
        let margin := P.canvasMargin
        pure (box.id, shiftRect margin margin (orientRect o.direction acc.canvasH rect)),
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas t.2 = true) :
    (sceneOf P inp o lines acc measured).PrimitiveBounds :=
  scene_primitiveBoundsCheck_of_items _ hcw hch
    (sceneOf_items_cellBounds P inp o lines acc measured hlh hpad hboxes hroutes hlabels htitles)

theorem canvasMarginOf_ge_one (profile : Profile) (kind : String) :
    1 ≤ canvasMarginOf profile kind := by
  unfold canvasMarginOf kindOverride
  split
  · omega
  · cases profile <;> decide

theorem checkedParams_canvasMargin {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : P.canvasMargin = canvasMarginOf profile kind := by
  obtain ⟨B, _, rfl⟩ := checkedParams_some h
  rfl

theorem checkedParams_canvasMargin_ge_one {profile : Profile} {kind : String} {P : Params}
    (h : checkedParams profile kind = .ok P) : 1 ≤ P.canvasMargin := by
  rw [checkedParams_canvasMargin h]
  exact canvasMarginOf_ge_one profile kind

/-- Boundedness property for a component part produced during layered placement.
Every constituent rectangle, title, route point, and label lies within the part bounding box `[0, width] × [0, height]`. -/
def PartBounded (part : Part) : Prop :=
  0 ≤ part.width ∧ 0 ≤ part.height ∧
  (∀ r ∈ part.rects, 0 ≤ r.x ∧ r.x + r.w ≤ part.width ∧ 0 ≤ r.y ∧ r.y + r.h ≤ part.height ∧ 0 ≤ r.w ∧ 0 ≤ r.h) ∧
  (∀ t ∈ part.titles, 0 ≤ t.2.x ∧ t.2.x + t.2.w ≤ part.width ∧ 0 ≤ t.2.y ∧ t.2.y + t.2.h ≤ part.height ∧ 0 ≤ t.2.w ∧ 0 ≤ t.2.h) ∧
  (∀ route ∈ part.routes, ∀ p ∈ route.2, 0 ≤ p.x ∧ p.x ≤ part.width ∧ 0 ≤ p.y ∧ p.y ≤ part.height) ∧
  (∀ l ∈ part.labels, 0 ≤ l.2.x ∧ l.2.x + l.2.w ≤ part.width ∧ 0 ≤ l.2.y ∧ l.2.y + l.2.h ≤ part.height ∧ 0 ≤ l.2.w ∧ 0 ≤ l.2.h)


/-- Packed accumulator bounds: canvas dimensions are non-negative and all packed items are contained. -/
structure AccBounded (canvasW canvasH : Int) (acc : Acc) : Prop where
  canvas_w_nonneg : 0 ≤ canvasW
  canvas_h_nonneg : 0 ≤ canvasH
  rects_bounded : ∀ (i : Nat) (r : Rect), acc.rects[i]? = some r →
    0 ≤ r.x ∧ r.x + r.w ≤ canvasW ∧ 0 ≤ r.y ∧ r.y + r.h ≤ canvasH ∧ 0 ≤ r.w ∧ 0 ≤ r.h
  titles_bounded : ∀ t ∈ acc.titles,
    0 ≤ t.2.x ∧ t.2.x + t.2.w ≤ canvasW ∧ 0 ≤ t.2.y ∧ t.2.y + t.2.h ≤ canvasH ∧ 0 ≤ t.2.w ∧ 0 ≤ t.2.h
  routes_bounded : ∀ (i : Nat) (pts : List Point), acc.routes[i]? = some pts →
    ∀ p ∈ pts, 0 ≤ p.x ∧ p.x ≤ canvasW ∧ 0 ≤ p.y ∧ p.y ≤ canvasH
  labels_bounded : ∀ (i : Nat) (r : Rect), acc.labels[i]? = some r →
    0 ≤ r.x ∧ r.x + r.w ≤ canvasW ∧ 0 ≤ r.y ∧ r.y + r.h ≤ canvasH ∧ 0 ≤ r.w ∧ 0 ≤ r.h

/-- When the accumulator satisfies packing bounds and margin is valid, all scene boxes are contained in the canvas. -/
theorem sceneOf_boxes_bounded (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hacc : AccBounded acc.canvasW acc.canvasH acc)
    (hmargin : 0 ≤ P.canvasMargin) :
    ∀ q ∈ (sceneOf P inp o lines acc measured).boxes.zipIdx,
      Size.containsCellRect (sceneOf P inp o lines acc measured).canvas q.1.rect = true := by
  intro q hq
  unfold sceneOf at hq ⊢
  dsimp only at hq ⊢
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp hq)
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at heq
  rw [← heq]
  dsimp only
  have hr := hacc.rects_bounded q.2
  have hr' : 0 ≤ (acc.rects.getD q.2 default).x ∧
      (acc.rects.getD q.2 default).x + (acc.rects.getD q.2 default).w ≤ acc.canvasW ∧
      0 ≤ (acc.rects.getD q.2 default).y ∧
      (acc.rects.getD q.2 default).y + (acc.rects.getD q.2 default).h ≤ acc.canvasH ∧
      0 ≤ (acc.rects.getD q.2 default).w ∧
      0 ≤ (acc.rects.getD q.2 default).h := by
    cases hget : acc.rects[q.2]? with
    | none =>
      have hdef : acc.rects.getD q.2 default = default := by
        simp [Array.getD_eq_getD_getElem?, hget]
      rw [hdef]
      change 0 ≤ (0 : Int) ∧ 0 ≤ acc.canvasW ∧ 0 ≤ (0 : Int) ∧
        0 ≤ acc.canvasH ∧ 0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
      exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg, by omega, by omega⟩
    | some r =>
      rw [Array.getD_eq_getD_getElem?, hget]
      exact hr r hget
  exact orient_shiftRect_containsCellRect o.direction acc.canvasW acc.canvasH _ _ hr' hmargin

/-- When the accumulator satisfies packing bounds and margin is at least 1, all route points are contained in the canvas. -/
theorem sceneOf_routes_bounded (P : Params) (inp : Input) (o : Options)
    (lines : List (List Measure.Line)) (acc : Acc) (measured : List MeasuredLabel)
    (hacc : AccBounded acc.canvasW acc.canvasH acc)
    (hmargin : 1 ≤ P.canvasMargin) :
    ∀ q ∈ (sceneOf P inp o lines acc measured).routes.zipIdx,
      ∀ p ∈ q.1.points, Size.containsCell (sceneOf P inp o lines acc measured).canvas p = true := by
  intro q hq p hp
  unfold sceneOf at hq ⊢
  dsimp only at hq ⊢
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp hq)
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add] at heq
  rw [← heq] at hp
  dsimp only at hp
  obtain ⟨origP, horigP, rfl⟩ := List.mem_map.mp hp
  cases hget : acc.routes[q.2]? with
  | none =>
    have : acc.routes.getD q.2 [] = [] := by
      simp [Array.getD_eq_getD_getElem?, hget]
    rw [this] at horigP
    contradiction
  | some pts =>
    rw [Array.getD_eq_getD_getElem?, hget] at horigP
    have hp_bound := hacc.routes_bounded q.2 pts hget origP horigP
    exact orient_shiftPoint_containsCell o.direction acc.canvasW acc.canvasH _ origP hp_bound hmargin

/-- All fields are equations from one successful execution. No field asserts a
geometric bound, text fit, or validator result. -/
structure SceneExecution (inp : Input) (o : Options) (res : FamilyResult) where
  params : Params
  metric : Measure.Metric
  lines : List (List Measure.Line)
  measured : List MeasuredLabel
  graph : Graph
  componentsAcc : Acc
  packedAcc : Acc
  checked : checkedParams o.profile inp.kind = .ok params
  metric_eq : metricOf o.profile o.fontFamily = .ok metric
  lines_eq : boxLines metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp = .ok lines
  measured_eq : measureLabels params metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    inp o.direction = .ok measured
  graph_eq : measuredGraph params inp o lines = .ok graph
  components_eq : (components graph).foldlM
    (fun acc comp => layoutComponent params inp o graph acc comp measured)
    ⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ = .ok componentsAcc
  packed_eq : packAcc params o componentsAcc = .ok packedAcc
  scene_eq : res.scene = sceneOf params inp o lines packedAcc measured

/-- Extract the exact measured graph, selected-component fold, and packed
accumulator that `layout` used; no `toOption.getD` reconstruction is involved. -/
theorem layout_sceneExecution {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) : Nonempty (SceneExecution inp o res) := by
  obtain ⟨P, metric, lines, measured, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg, hc, hp, hs, _, _⟩ := Layered.layout_success_phases h
  exact ⟨⟨P, metric, lines, measured, graph, componentsAcc, packedAcc,
    hP, hm, hl, hmeasured, hg, hc, hp, hs⟩⟩

theorem SceneExecution.parameter_signs {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    0 ≤ execution.params.lineH ∧ 0 ≤ execution.params.clusterPad ∧
      0 ≤ execution.params.nodePadX ∧ 0 ≤ execution.params.nodePadY ∧
      0 ≤ execution.params.nodeBorder :=
  checkedParams_sizing_nonneg execution.checked

/-- The recursive producer reserves the measured title in both axes, including
the side-caption branches. This is a fact of `childFrameSize`, not an assumption
that an arbitrary `Input.fixedSizes` entry fits its text. -/
theorem childFrameSize_title_fit (direction : String) (pad width height : Int)
    (content : Size) (hcw : 0 ≤ content.w) (hch : 0 ≤ content.h) :
    width + 2 * pad ≤ (childFrameSize direction pad width height content).w ∧
      height + 2 * pad ≤ (childFrameSize direction pad width height content).h := by
  unfold childFrameSize
  split <;> dsimp only <;> omega

/-- A fixed frame made by the recursive constructor has the vertical room used
by the unexpanded parent's fallback caption, regardless of the child's direction. -/
theorem childFrameSize_fallback_fit (direction : String) (pad width height : Int)
    (content : Size) (hcw : 0 ≤ content.w) (hch : 0 ≤ content.h)
    (hp : 0 ≤ pad) (hw : 0 ≤ width) :
    2 * pad ≤ (childFrameSize direction pad width height content).w ∧
      pad + height ≤ (childFrameSize direction pad width height content).h := by
  have hf := childFrameSize_title_fit direction pad width height content hcw hch
  omega

/-- `componentTitles` records the actual title-node dimensions. In particular,
the caption rectangle is not the frame rectangle or the border-3 reservation. -/
theorem componentTitles_dimension_source (P : Params) (cg : Graph) (run : Run)
    {title : Nat × Rect} (ht : title ∈ componentTitles P cg run) :
    ∃ top ∈ cg.nodes.zipIdx,
      top.1.border = -2 ∧ title.1 = top.2 ∧
        title.2.w = top.1.w ∧ title.2.h = top.1.h - P.clusterPad := by
  unfold componentTitles at ht
  obtain ⟨top, htop, ht⟩ := List.mem_filterMap.mp ht
  dsimp only at ht
  split at ht
  · contradiction
  · rename_i hborder
    cases hfind : run.proper.nodes.zipIdx.find? (fun q =>
        q.1.node.border == 3 && q.1.node.clusterPath == top.1.clusterPath) with
    | none => simp [hfind] at ht
    | some reservation =>
      simp [hfind] at ht
      subst title
      refine ⟨top, htop, ?_, rfl, rfl, rfl⟩
      simpa using hborder

/-- Packing starts with zero dimensions and only takes maxima, independently of
the contents of the rectangles that will later be copied into the accumulator. -/
theorem pack_canvas_nonneg {maxWidth : Nat} {gap margin aspectNum aspectDen : Int}
    {items : List Pack.Item} {out : Pack.State}
    (h : Pack.pack maxWidth gap margin aspectNum aspectDen items = .ok out) :
    0 ≤ out.width ∧ 0 ≤ out.height := by
  unfold Pack.pack at h
  split at h
  · change Except.error LayoutError.domain = Except.ok out at h
    cases h
  · rename_i signs
    obtain ⟨target, _, h⟩ := bind_ok h
    obtain ⟨result, hr, h⟩ := bind_ok h
    have hi : Pack.Inv ({} : Pack.State) := by
      simp [Pack.Inv]
    have hg : 0 ≤ gap := by omega
    have hm : 0 ≤ margin := by omega
    have bounds := Pack.fold_inv hg items hi hr
    dsimp only at h
    split at h
    · change Except.error LayoutError.overflow = Except.ok out at h
      cases h
    · have he := Except.ok.inj h
      subst out
      dsimp only
      exact ⟨by have := bounds.2.2.2.1; omega,
        by have := bounds.2.2.2.2.1; omega⟩

theorem packAcc_canvas_nonneg {P : Params} {o : Options} {acc out : Acc}
    (h : packAcc P o acc = .ok out) :
    0 ≤ out.canvasW ∧ 0 ≤ out.canvasH := by
  unfold packAcc at h
  obtain ⟨packed, hp, h⟩ := bind_ok h
  have hb := pack_canvas_nonneg hp
  have preserve : ∀ (qs : List ((List Nat × Part) × Rect)) (a : Acc),
      0 ≤ a.canvasW ∧ 0 ≤ a.canvasH →
      0 ≤ (qs.foldl (fun out q =>
        { out with
          rects := (q.1.1.zip q.1.2.rects).foldl
            (fun a r => if r.1 < a.size then
              a.set! r.1 (shiftRect q.2.x q.2.y r.2) else a) out.rects
          routes := q.1.2.routes.foldl
            (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) out.routes
          labels := q.1.2.labels.foldl
            (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) out.labels
          titles := out.titles ++ q.1.2.titles.map
            (fun r => (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2)) }) a).canvasW ∧
      0 ≤ (qs.foldl (fun out q =>
        { out with
          rects := (q.1.1.zip q.1.2.rects).foldl
            (fun a r => if r.1 < a.size then
              a.set! r.1 (shiftRect q.2.x q.2.y r.2) else a) out.rects
          routes := q.1.2.routes.foldl
            (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) out.routes
          labels := q.1.2.labels.foldl
            (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) out.labels
          titles := out.titles ++ q.1.2.titles.map
            (fun r => (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2)) }) a).canvasH := by
    intro qs
    induction qs with
    | nil => intro a ha; exact ha
    | cons q qs ih => intro a ha; exact ih _ ha
  have he := Except.ok.inj h
  subst out
  exact preserve _ _ hb

/-- Even an empty leaf has both margins. This does not require primitive bounds. -/
theorem layout_canvas_margins {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.w ∧
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.h := by
  obtain ⟨execution⟩ := layout_sceneExecution h
  have hb := packAcc_canvas_nonneg execution.packed_eq
  rw [← checkedParams_canvasMargin execution.checked]
  rw [execution.scene_eq]
  change _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).w ∧
    _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).h
  cases o.direction <;> simp only [orientCanvas] <;> omega

/-- Expansion keeps the parent canvas verbatim. -/
theorem expandChild_canvas {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {height : Int} {parent child out : FamilyResult}
    (h : expandChild P inp o group height parent child = .ok out) :
    out.scene.canvas = parent.scene.canvas := by
  unfold expandChild at h
  cases hf : parent.scene.boxes.find? (fun box => box.id == group.id) with
  | none =>
    simp only [hf, bind, Except.bind] at h
    cases h
  | some frame =>
    simp only [hf, bind, Except.bind] at h
    obtain ⟨metric, _, h⟩ := bind_ok h
    obtain ⟨titleLines, _, h⟩ := bind_ok h
    obtain ⟨metric', _, h⟩ := bind_ok h
    obtain ⟨lines, _, h⟩ := bind_ok h
    have he := Except.ok.inj h
    subst out
    rfl

/-- Recursive calls inherit the canvas lower bound from their actual parent
leaf, through expansion, not from a text-fit invariant. -/
theorem layoutRecursive_canvas_margins (fuel : Nat) {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutRecursive fuel inp o = .ok res) :
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.w ∧
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.h := by
  induction fuel generalizing inp o res with
  | zero => exact layout_canvas_margins h
  | succ fuel ih =>
    simp only [layoutRecursive] at h
    split at h
    · exact layout_canvas_margins h
    · obtain ⟨P, _, h⟩ := bind_ok h
      obtain ⟨metric, _, h⟩ := bind_ok h
      obtain ⟨child, _, h⟩ := bind_ok h
      obtain ⟨titleLines, _, h⟩ := bind_ok h
      obtain ⟨parent, hp, h⟩ := bind_ok h
      have hc := expandChild_canvas h
      rw [hc]
      have key := ih hp
      exact key

/-- A frame origin retains the producing input and its indexed caption. It
does not claim that its id occurs in every later selected input. -/
structure FrameOrigin (o : Options) (id : String) (size : Size) where
  source : Input
  group : ModelBox
  fuel : Nat
  params : Params
  metric : Measure.Metric
  child : FamilyResult
  titleLines : List Measure.Line
  group_found : source.boxes.find? (fun box =>
    Compound.independent source.boxes source.routes box &&
      !source.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group
  id_eq : id = group.id
  checked : checkedParams o.profile source.kind = .ok params
  metric_eq : metricOf o.profile o.fontFamily = .ok metric
  child_eq : layoutRecursive fuel
    (selectInput source (fun box => Compound.inside source.boxes group.id box.id) group.id)
    { o with direction := directionOf group.direction } = .ok child
  title_eq : StyledMeasure.wrap metric
    (Measure.wrapTarget metric.profile params.wrapWidth (if o.profile == .cell then o.maxWidth else 0))
    (source.texts.getD
      ((source.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
      .ok titleLines
  size_eq : size = childFrameSize group.direction params.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * params.lineH)
    ⟨child.scene.canvas.w - 2 * canvasMarginOf o.profile source.kind,
      child.scene.canvas.h - 2 * canvasMarginOf o.profile source.kind⟩

theorem FrameOrigin.content_nonneg {o : Options} {id : String} {size : Size}
    (origin : FrameOrigin o id size) :
    0 ≤ origin.child.scene.canvas.w - 2 * canvasMarginOf o.profile origin.source.kind ∧
    0 ≤ origin.child.scene.canvas.h - 2 * canvasMarginOf o.profile origin.source.kind := by
  have hb := layoutRecursive_canvas_margins origin.fuel origin.child_eq
  change
    2 * canvasMarginOf o.profile origin.source.kind ≤ origin.child.scene.canvas.w ∧
    2 * canvasMarginOf o.profile origin.source.kind ≤ origin.child.scene.canvas.h at hb
  exact ⟨by omega, by omega⟩

theorem FrameOrigin.fallback_fit {o : Options} {id : String} {size : Size}
    (origin : FrameOrigin o id size) :
    2 * origin.params.clusterPad ≤ size.w ∧
    origin.params.clusterPad +
      (max 1 origin.titleLines.length : Int) * origin.params.lineH ≤ size.h := by
  have width_nonneg : ∀ (lines : List Measure.Line) (start : Int),
      0 ≤ start → 0 ≤ lines.foldl (fun width line => max width line.width) start := by
    intro lines
    induction lines with
    | nil => intro start hs; exact hs
    | cons line lines ih =>
      intro start hs
      exact ih _ (Int.le_trans hs (Int.le_max_left _ _))
  have hb := origin.content_nonneg
  have hw := congrArg Size.w origin.size_eq
  have hh := congrArg Size.h origin.size_eq
  have fit := childFrameSize_fallback_fit origin.group.direction origin.params.clusterPad
    (origin.titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 origin.titleLines.length : Int) * origin.params.lineH) ⟨_, _⟩ hb.1 hb.2
    (checkedParams_clusterPad_nonneg origin.checked)
    (width_nonneg origin.titleLines 0 (by omega))
  exact ⟨hw.symm ▸ fit.1, hh.symm ▸ fit.2⟩

def GenuineFrames (o : Options) (entries : List (String × Size)) : Prop :=
  ∀ entry ∈ entries, Nonempty (FrameOrigin o entry.1 entry.2)

theorem genuineFrames_selectInput {o : Options} {inp : Input}
    (keep : ModelBox → Bool) (root : String)
    (h : GenuineFrames o inp.fixedSizes) :
    GenuineFrames o (selectInput inp keep root).fixedSizes := h

theorem genuineFrames_append {o : Options} {entries : List (String × Size)}
    {id : String} {size : Size} (h : GenuineFrames o entries)
    (origin : FrameOrigin o id size) :
    GenuineFrames o (entries ++ [(id, size)]) := by
  intro entry he
  rcases List.mem_append.mp he with he | he
  · exact h entry he
  · have heq := List.mem_singleton.mp he
    subst entry
    exact ⟨origin⟩

/-- A leaf's actual first-match lookup recovers its producing execution. Carried
entries whose ids are absent from the leaf need not satisfy a membership claim. -/
theorem genuineFrames_used {o : Options} {inp : Input} {id : String}
    {entry : String × Size} (h : GenuineFrames o inp.fixedSizes)
    (used : inp.fixedSizes.find? (fun fixed => fixed.1 == id) = some entry) :
    Nonempty (FrameOrigin o entry.1 entry.2) :=
  h entry (List.mem_of_find?_eq_some used)

/-- Every successful recursive group branch produces a genuine frame with the
same child execution and caption measurement used by the runtime constructor. -/
theorem layoutRecursive_frame_origin {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult} {group : ModelBox}
    (hg : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (h : layoutRecursive (fuel + 1) inp o = .ok res) :
    ∃ size : Size, Nonempty (FrameOrigin o group.id size) := by
  simp only [layoutRecursive, hg] at h
  obtain ⟨P, hP, h⟩ := bind_ok h
  obtain ⟨metric, hm, h⟩ := bind_ok h
  obtain ⟨child, hc, h⟩ := bind_ok h
  obtain ⟨titleLines, ht, h⟩ := bind_ok h
  refine ⟨childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * canvasMarginOf o.profile inp.kind,
      child.scene.canvas.h - 2 * canvasMarginOf o.profile inp.kind⟩,
    ⟨⟨inp, group, fuel, P, metric, child, titleLines,
      hg, rfl, hP, hm, hc, ht, rfl⟩⟩⟩

/-- Indexed selection transports the original caption, including its original
id fallback; no equality search on caption strings is involved. -/
theorem selectInput_caption_at (inp : Input) (keep : ModelBox → Bool)
    (root : String) (i : Nat) (q : ModelBox × Nat)
    (hq : (inp.boxes.zipIdx.filter fun q => keep q.1)[i]? = some q) :
    (selectInput inp keep root).texts[i]? = some (inp.texts.getD q.2 q.1.id) := by
  simp only [selectInput, List.getElem?_map, hq, Option.map_some]

/-! ### Part-level boundedness, derived from the placement functions

`PartBounded` for a placed component part follows from `boundsOf` containment,
nonnegative proper-node dimensions, the measured label dimensions, and the label
envelope facts. No property of an arbitrary accumulator is assumed. -/

/-- Every node of a proper has nonnegative width and height. -/
def ProperDimsNonneg (p : Proper) : Prop :=
  ∀ (v : Nat) (nd : ProperNode), p.nodes[v]? = some nd → 0 ≤ nd.node.w ∧ 0 ≤ nd.node.h

/-- `sizesNonneg` is the executable form of `ProperDimsNonneg`. -/
theorem sizesNonneg_lookup {p : Proper} (h : CoordsImpl.sizesNonneg p = true) :
    ProperDimsNonneg p := by
  intro v nd hv
  have hm : nd ∈ p.nodes := List.mem_of_getElem? hv
  unfold CoordsImpl.sizesNonneg at h
  rw [List.all_eq_true] at h
  simpa using h nd hm

/-- Proxy materialization retains nonnegative heights and checks every replacement
width before emitting it. The premise describes the executed coordinate phase. -/
theorem proxyWidths_dims_nonneg {p q : Proper} {xs ys : List Int}
    (hd : ProperDimsNonneg p)
    (h : proxyWidths p xs = .ok (q, ys)) :
    ProperDimsNonneg q := by
  unfold proxyWidths at h
  obtain ⟨updated, hu, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hq : q = { p with nodes := updated.map (·.1) } :=
    (Prod.mk.inj he).1.symm
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ hu
  subst q
  intro v nd hv
  have hvlt : v < updated.length := by
    have := List.getElem?_eq_some_iff.mp hv
    simpa using this.1
  have hlength : updated.length = p.nodes.length := by
    simpa only [List.length_zipIdx] using hlen
  have hvp : v < p.nodes.length := hlength ▸ hvlt
  let old := p.nodes[v]
  have hold : p.nodes[v]? = some old := List.getElem?_eq_some_iff.mpr ⟨hvp, rfl⟩
  obtain ⟨b, hb, hget⟩ := hidx v (old, v)
    (by simp [List.getElem?_zipIdx, hold])
  have hnd : b.1 = nd := by
    simpa only [List.getElem?_map, hget, Option.map_some, Option.some.injEq] using hv
  rw [← hnd]
  dsimp only at hb
  split at hb
  · cases hl : old.node.clusterPath.getLast? with
    | none => simp [hl] at hb
    | some owner =>
      simp only [hl] at hb
      obtain ⟨span, _, hb⟩ := bind_ok hb
      obtain ⟨width, _, hb⟩ := bind_ok hb
      split at hb
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hb
      · rename_i hw
        obtain ⟨center, _, hb⟩ := bind_ok hb
        have he := Except.ok.inj hb
        rw [← he]
        change 0 ≤ width ∧ 0 ≤ old.node.h
        exact ⟨by omega, (hd v old hold).2⟩
  · have he := Except.ok.inj hb
    rw [← he]
    exact hd v old hold

/-- A successful run's coordinate-size check also bounds the final routing
proper: proxy widths are checked and dropping synthetic edges changes no node. -/
theorem componentRun_dims_nonneg {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRun P cg labels orderOptions = .ok run) :
    ProperDimsNonneg run.proper := by
  obtain ⟨_, _, _, q, _, _, _, _, _, hproxy, hdrop, _, _, hy, _, _⟩ :=
    componentRun_spec h
  obtain ⟨_, _, _, _, hsize, _, _⟩ := CoordsImpl.rankCoordsWith_spec hy
  have hd := proxyWidths_dims_nonneg (sizesNonneg_lookup hsize) hproxy
  rw [← hdrop]
  exact hd

/-- Label measurement constructs nonnegative dimensions even when orientation
swaps the two axes. No condition on the source text is required. -/
theorem measureLabels_nonneg {P : Params} {m : Measure.Metric} {target : Int}
    {inp : Input} {direction : Direction} {labels : List MeasuredLabel}
    (hline : 0 ≤ P.lineH) (hslot : 0 ≤ P.slot)
    (h : measureLabels P m target inp direction = .ok labels) :
    ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter := by
  unfold measureLabels at h
  obtain ⟨options, ho, h⟩ := bind_ok h
  have he := Except.ok.inj h
  subst labels
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ ho
  intro l hl
  obtain ⟨opt, hopt, hl⟩ := List.mem_filterMap.mp hl
  have hopt : some l ∈ options := by
    have he : opt = some l := by simpa using hl
    exact he ▸ hopt
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hopt
  have hil : i < options.length := (List.getElem?_eq_some_iff.mp hi).1
  have his : i < inp.labels.zipIdx.length := hlen ▸ hil
  let source := inp.labels.zipIdx[i]
  obtain ⟨result, hr, hresult⟩ := hidx i source
    (List.getElem?_eq_some_iff.mpr ⟨his, rfl⟩)
  have hresult : result = some l := by
    rw [hi] at hresult
    exact (Option.some.inj hresult).symm
  subst result
  dsimp only at hr
  split at hr
  · change Except.ok none = Except.ok (some l) at hr
    cases hr
  · obtain ⟨lines, _, hr⟩ := bind_ok hr
    have width_nonneg : ∀ (ls : List Measure.Line) (start : Int),
        0 ≤ start → 0 ≤ ls.foldl (fun w line => max w line.width) start := by
      intro ls
      induction ls with
      | nil => intro start hs; exact hs
      | cons line ls ih =>
        intro start hs
        exact ih _ (Int.le_trans hs (Int.le_max_left _ _))
    have hw := width_nonneg lines 0 (by omega)
    have hh : 0 ≤ (lines.length : Int) * P.lineH :=
      Int.mul_nonneg (by omega) hline
    have hg : 0 ≤ (if m.profile == .cell then P.slot else 0) := by
      split <;> omega
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * P.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if m.profile == .cell then P.slot else 0) ∨
        I32_MAX < (lines.length : Int) * P.lineH +
          (if m.profile == .cell then P.slot else 0)
    · simp only [hover, ↓reduceIte] at hr
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hr
    · simp only [hover, ↓reduceIte] at hr
      cases direction <;>
        dsimp only at hr <;>
        have he := Option.some.inj (Except.ok.inj hr) <;>
        subst l <;> exact ⟨by assumption, by assumption, hg⟩

/-- The public leaf's measured-label signs come from its actual measurement
phase and checked constants, rather than a hypothesis on arbitrary labels. -/
theorem SceneExecution.measured_nonneg {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ l ∈ execution.measured, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter := by
  have hs := (checkedParams_valid execution.checked).2.2.1
  exact measureLabels_nonneg execution.parameter_signs.1 (by omega) execution.measured_eq

/-- Recover all non-envelope sizing premises from the component execution that
actually emitted the part. In particular no unsuccessful portfolio run is
quantified over. The area update does not change any placed geometry. -/
theorem SceneExecution.actual_component_sizing
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ index run loops area,
      componentRun execution.params
        (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      componentLoops execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured = .ok loops ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } ∧
      ProperDimsNonneg run.proper ∧
      (∀ i, i < (componentCandidate execution.graph part.1 index).nodes.length →
        i < run.proper.nodes.length) ∧
      (∀ (i : Nat) (top : Node),
        (componentCandidate execution.graph part.1 index).nodes[i]? = some top →
        top.border = -2 → 0 ≤ top.w ∧ execution.params.clusterPad ≤ top.h) ∧
      0 ≤ (componentCandidate execution.graph part.1 index).slot := by
  obtain ⟨_, hall⟩ := actual_components_parts_geometry (by rfl) execution.components_eq
  obtain ⟨index, _, run, loops, area, _, _, _, hrun, hloops, heq⟩ := hall part hpart
  refine ⟨index, run, loops, area, hrun, hloops, heq,
    componentRun_dims_nonneg hrun, componentRun_original_nodes_covered hrun, ?_,
    componentRun_slot_nonneg hrun⟩
  intro i top htop hb
  exact actual_title_dims_nonneg execution.graph_eq execution.parameter_signs.1 htop hb

theorem SceneExecution.component_plain_node_dims
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ index run loops area,
      componentRun execution.params
        (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } ∧
      ∀ (i : Nat) (node : ProperNode),
        run.coordinateProper.nodes[i]? = some node →
        node.node.border = 0 → run.proper.nodes[i]? = some node := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  refine ⟨index, run, loops, area, hrun, hplace, ?_⟩
  intro i node hnode hborder
  exact componentRun_plain_node_dims hrun hnode hborder

/-- Node-anchored rectangles have the nonnegative dimensions of their node. -/
theorem rectAt_dims {p : Proper} (hd : ProperDimsNonneg p) (xs ys : List Int) (v : Nat) :
    0 ≤ (Labels.rectAt p xs ys v).w ∧ 0 ≤ (Labels.rectAt p xs ys v).h := by
  rw [rectAt_eq_box]
  cases hv : p.nodes[v]? with
  | none =>
    simp only [hv, RouteImpl.nodeW, RouteImpl.nodeH]
    exact ⟨by omega, by omega⟩
  | some nd =>
    have h := hd v nd hv
    have hw : RouteImpl.nodeW p v = nd.node.w := by simp [RouteImpl.nodeW, hv]
    have hh : RouteImpl.nodeH p v = nd.node.h := by simp [RouteImpl.nodeH, hv]
    rw [hw, hh]
    exact h

/-- The frame rectangle of every component-graph node has nonnegative dimensions. -/
theorem frameRect_dims_nonneg (P : Params) (cg : Graph) (run : Run) (i : Nat)
    (hd : ProperDimsNonneg run.proper) (hi : i < run.proper.nodes.length) :
    0 ≤ (frameRect P cg run i).w ∧ 0 ≤ (frameRect P cg run i).h := by
  have cons_width : ∀ (l : List Rect), l ≠ [] → (∀ r ∈ l, 0 ≤ r.w) →
      0 ≤ (boundsOf l []).right - (boundsOf l []).minX := by
    intro l hne hall
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact boundsOf_width_nonneg_of_rect List.mem_cons_self (hall b List.mem_cons_self)
  have cons_height : ∀ (l : List Rect), l ≠ [] → (∀ r ∈ l, 0 ≤ r.h) →
      0 ≤ (boundsOf l []).bottom - (boundsOf l []).minY := by
    intro l hne hall
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hne
    exact boundsOf_height_nonneg_of_rect List.mem_cons_self (hall b List.mem_cons_self)
  have filter_dims : ∀ (cond : ProperNode × Nat → Bool),
      ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if cond q then some (Labels.rectAt run.proper run.xs run.ys q.2) else none),
        0 ≤ r.w ∧ 0 ≤ r.h := by
    intro cond r hr
    rw [List.mem_filterMap] at hr
    obtain ⟨q, hq, hqr⟩ := hr
    split at hqr
    · injection hqr with he
      rw [← he]
      exact rectAt_dims hd run.xs run.ys q.2
    · exact absurd hqr (by simp)
  unfold frameRect
  dsimp only
  split
  · dsimp only [nodeRect]
    obtain ⟨nd, hnd⟩ : ∃ nd, run.proper.nodes[i]? = some nd :=
      ⟨run.proper.nodes[i]'hi, List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩⟩
    have hget : run.proper.nodes.getD i default = nd := by
      simp [List.getD_eq_getElem?_getD, hnd]
    rw [hget]
    exact hd i nd hnd
  · rename_i hborder
    have hborders : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if (q.1.node.border == -1 || q.1.node.border == 1) &&
            q.1.node.clusterPath.getLast? == some (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2) else none),
        0 ≤ r.w ∧ 0 ≤ r.h :=
      filter_dims (fun q => (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some (cg.nodes.getD i default).decl)
    have hrects : ∀ r ∈ (run.proper.nodes.zipIdx.filterMap fun q =>
        if q.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
          some (Labels.rectAt run.proper run.xs run.ys q.2) else none),
        0 ≤ r.w ∧ 0 ≤ r.h :=
      filter_dims (fun q => q.1.node.clusterPath.contains (cg.nodes.getD i default).decl)
    refine ⟨?_, ?_⟩
    · by_cases hbl :
        (run.proper.nodes.zipIdx.filterMap fun q =>
          if (q.1.node.border == -1 || q.1.node.border == 1) &&
              q.1.node.clusterPath.getLast? == some (cg.nodes.getD i default).decl then
            some (Labels.rectAt run.proper run.xs run.ys q.2) else none) = []
      · rw [hbl]; exact boundsOf_width_nonneg_of_empty
      · exact cons_width _ hbl (fun r hr => (hborders r hr).1)
    · by_cases hrl :
        (run.proper.nodes.zipIdx.filterMap fun q =>
          if q.1.node.clusterPath.contains (cg.nodes.getD i default).decl then
            some (Labels.rectAt run.proper run.xs run.ys q.2) else none) = []
      · rw [hrl]; exact boundsOf_height_nonneg_of_empty
      · exact cons_height _ hrl (fun r hr => (hrects r hr).2)

/-- Title rectangles of a component graph have nonnegative dimensions when every
title anchor of the graph does. -/
theorem componentTitles_dims_nonneg (P : Params) (cg : Graph) (run : Run)
    (ht : ∀ (i : Nat) (top : Node), cg.nodes[i]? = some top → top.border = -2 →
      0 ≤ top.w ∧ P.clusterPad ≤ top.h) :
    ∀ t ∈ componentTitles P cg run, 0 ≤ t.2.w ∧ 0 ≤ t.2.h := by
  intro t htm
  obtain ⟨top, htop, hborder, _, hw, hh⟩ := componentTitles_dimension_source P cg run htm
  have heq : cg.nodes[top.2]? = some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htop
  have hnd := ht top.2 top.1 heq hborder
  rw [hw, hh]
  exact ⟨hnd.1, by omega⟩

/-- What `placedLabels` needs from each label envelope: the envelope itself has
nonnegative dimensions, and the stack of the edge's labels fits, in both axes,
into some entry of `labelBounds` whose origin does not exceed the envelope's. -/
def EnvelopeFits (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (k : Nat) (e : Edge) (env : Rect),
    cg.edges[k]? = some e →
    labelEnvelope P cg run labels k e = some env →
    0 ≤ env.w ∧ 0 ≤ env.h ∧
    ∃ entry, entry ∈ labelBounds P cg run labels ∧
      entry.x ≤ env.x ∧ entry.y ≤ env.y ∧
      env.x + Labels.stackWidth
          ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
        entry.x + entry.w ∧
      env.y + Labels.stackHeight cg.slot
          ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
        entry.y + entry.h

/-- Loop placement uses exactly the measured stack dimensions in both its
ordinary and exact-port branches. This is independent of route coordinates. -/
theorem labelEnvelope_loop_size {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail = e.head)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env.w = (stackSize cg.slot (routeLabels labels e.decl)).width ∧
      env.h = (stackSize cg.slot (routeLabels labels e.decl)).height := by
  unfold labelEnvelope at henv
  obtain ⟨first, _, henv⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = true := by simp [hloop]
  simp only [hb, ↓reduceIte] at henv
  split at henv <;>
    have he := Option.some.inj henv <;>
    rw [← he] <;> exact ⟨rfl, rfl⟩

/-- A self-loop's own label-bound entry contains its complete measured stack;
there is no appeal to a scene-validity assumption. -/
theorem labelEnvelope_loop_fits {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv : labelEnvelope P cg run labels k e = some env)
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter) :
    0 ≤ env.w ∧ 0 ≤ env.h ∧
      ∃ entry, entry ∈ labelBounds P cg run labels ∧
        entry.x ≤ env.x ∧ entry.y ≤ env.y ∧
        env.x + Labels.stackWidth
            ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
          entry.x + entry.w ∧
        env.y + Labels.stackHeight cg.slot
            ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
          entry.y + entry.h := by
  obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop henv
  have hw' : env.w = Labels.stackWidth
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) :=
    hw.trans (stackSize_width_eq _ _)
  have hh' : env.h = Labels.stackHeight cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) :=
    hh.trans (stackSize_height_eq _ _)
  have hh0 : 0 ≤ env.h := by
    rw [hh']
    apply Labels.stackHeight_nonneg _ hslot
    intro size hs
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
    exact (hlab l (List.mem_filter.mp hl).1).2.1
  refine ⟨?_, hh0, env, ?_, by omega, by omega, by omega, by omega⟩
  · rw [hw']
    exact Labels.stackWidth_nonneg _
  · unfold labelBounds
    apply List.mem_filterMap.mpr
    refine ⟨(e, k), List.mem_zipIdx_iff_getElem?.mpr hk, ?_⟩
    simp only [henv]
    simp [hloop]

/-- Reversed lanes reserve the complete measured stack directly; lane position
and rank coordinates affect only its origin. -/
theorem labelEnvelope_reversed_size {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hloop : e.tail ≠ e.head) (hrev : e.reversed = true)
    (henv : labelEnvelope P cg run labels k e = some env) :
    env.w = (stackSize cg.slot (routeLabels labels e.decl)).width ∧
      env.h = (stackSize cg.slot (routeLabels labels e.decl)).height := by
  unfold labelEnvelope at henv
  obtain ⟨first, _, henv⟩ := Option.bind_eq_some_iff.mp henv
  have hb : (e.tail == e.head) = false := by simp [hloop]
  simp only [hb, hrev, ↓reduceIte, Bool.false_eq_true] at henv
  obtain ⟨lane, _, henv⟩ := Option.bind_eq_some_iff.mp henv
  have he := Option.some.inj henv
  rw [← he]
  exact ⟨rfl, rfl⟩

/-- The non-loop bound expands to the left by the measured gutter, so any
envelope that reserves its stack yields the exact entry needed by placement. -/
theorem labelEnvelope_nonloop_fits {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {k : Nat} {e : Edge} {env : Rect}
    (hk : cg.edges[k]? = some e) (hloop : e.tail ≠ e.head)
    (henv : labelEnvelope P cg run labels k e = some env)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hslot : 0 ≤ cg.slot)
    (hw : Labels.stackWidth
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤ env.w)
    (hh : Labels.stackHeight cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤ env.h) :
    0 ≤ env.w ∧ 0 ≤ env.h ∧
      ∃ entry, entry ∈ labelBounds P cg run labels ∧
        entry.x ≤ env.x ∧ entry.y ≤ env.y ∧
        env.x + Labels.stackWidth
            ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
          entry.x + entry.w ∧
        env.y + Labels.stackHeight cg.slot
            ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤
          entry.y + entry.h := by
  have hfirst : ∃ first, (routeLabels labels e.decl).head? = some first := by
    unfold labelEnvelope at henv
    obtain ⟨first, hf, _⟩ := Option.bind_eq_some_iff.mp henv
    exact ⟨first, hf⟩
  obtain ⟨first, hf⟩ := hfirst
  have hmem : first ∈ routeLabels labels e.decl :=
    List.mem_of_mem_head? (by rw [hf]; simp)
  have hg := (hlab first (List.mem_filter.mp hmem).1).2.2
  have hw0 := Labels.stackWidth_nonneg
    ((routeLabels labels e.decl).map fun l => (l.width, l.height))
  have hh0 : 0 ≤ Labels.stackHeight cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) := by
    apply Labels.stackHeight_nonneg _ hslot
    intro size hs
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hs
    exact (hlab l (List.mem_filter.mp hl).1).2.1
  let entry : Rect := { env with x := env.x - first.gutter, w := env.w + first.gutter }
  refine ⟨by omega, by omega, entry, ?_, ?_, ?_, ?_, ?_⟩
  · unfold labelBounds
    apply List.mem_filterMap.mpr
    refine ⟨(e, k), List.mem_zipIdx_iff_getElem?.mpr hk, ?_⟩
    simp [henv, hloop, hf, entry]
  · dsimp only [entry]; omega
  · exact Int.le_refl _
  · dsimp only [entry]; omega
  · dsimp only [entry]; omega

/-- Every envelope produced by the successful component pipeline reserves its
measured label stack. Forward anchors use the executed sizing/coordinate
transport, while loops and reversed lanes reserve stack dimensions directly. -/
theorem componentRun_envelopeFits {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (hrun : componentRun P cg labels orderOptions = .ok run)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter) :
    EnvelopeFits P cg run labels := by
  intro k edge env hk henv
  have hslot := componentRun_slot_nonneg hrun
  by_cases hloop : edge.tail = edge.head
  · exact labelEnvelope_loop_fits hk hloop henv hslot hlab
  · have hreserved :
        Labels.stackWidth ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ env.w ∧
        Labels.stackHeight cg.slot
          ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ env.h := by
      by_cases hrev : edge.reversed = true
      · obtain ⟨hw, hh⟩ := labelEnvelope_reversed_size hloop hrev henv
        rw [hw, hh, stackSize_width_eq, stackSize_height_eq]
        exact ⟨Int.le_refl _, Int.le_refl _⟩
      · have hfalse : edge.reversed = false := by
          cases he : edge.reversed with
          | false => rfl
          | true => exact False.elim (hrev he)
        have hforward := henv
        unfold labelEnvelope at hforward
        obtain ⟨first, hfirst, hforward⟩ := Option.bind_eq_some_iff.mp hforward
        have hb : (edge.tail == edge.head) = false := by simp [hloop]
        simp only [hb, hfalse, ↓reduceIte, Bool.false_eq_true] at hforward
        obtain ⟨found, hfound, hforward⟩ := Option.bind_eq_some_iff.mp hforward
        obtain ⟨index, nd, hi, hnode, hw, hh⟩ :=
          componentRun_forward_anchor_size hrun hk hloop hfirst
        rw [labelAnchorIndex_eq] at hi
        have hindex : found.2 = index := by
          simpa only [hfound, Option.map_some, Option.some.injEq] using hi
        have hrect : env = Labels.textRectAt run.proper run.xs run.ys found.2 first.gutter :=
          (Option.some.inj hforward).symm
        rw [hrect, hindex]
        rw [stackSize_width_eq] at hw
        rw [stackSize_height_eq] at hh
        have hbound :
            Labels.stackWidth
                ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤
              nd.node.w - first.gutter ∧
            Labels.stackHeight cg.slot
                ((routeLabels labels edge.decl).map fun l => (l.width, l.height)) ≤ nd.node.h :=
          ⟨by omega, by omega⟩
        simpa [Labels.textRectAt, Labels.rectAt, Labels.labelRect,
          RouteImpl.nodeW, RouteImpl.nodeH, hnode] using hbound
    exact labelEnvelope_nonloop_fits hk hloop henv hlab hslot hreserved.1 hreserved.2

/-- Every placed label rectangle of a component lies inside the bounds of any
rectangle and point list that contains `labelBounds`. -/
theorem placedLabels_within (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel)
    (fullRects : List Rect) (fullPts : List Point)
    (hsub : ∀ r ∈ labelBounds P cg run labels, r ∈ fullRects)
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hfit : EnvelopeFits P cg run labels) :
    ∀ q ∈ placedLabels P cg run labels,
      (boundsOf fullRects fullPts).minX ≤ q.2.x ∧
      q.2.x + q.2.w ≤ (boundsOf fullRects fullPts).right ∧
      (boundsOf fullRects fullPts).minY ≤ q.2.y ∧
      q.2.y + q.2.h ≤ (boundsOf fullRects fullPts).bottom ∧
      0 ≤ q.2.w ∧ 0 ≤ q.2.h := by
  have stack_contained : ∀ (k : Nat) (e : Edge) (env : Rect) (r : Rect),
      cg.edges[k]? = some e →
      labelEnvelope P cg run labels k e = some env →
      r ∈ Labels.stackRects env.x env.y cg.slot
          ((routeLabels labels e.decl).map fun l => (l.width, l.height)) →
      ∃ entry, entry ∈ labelBounds P cg run labels ∧
        0 ≤ r.w ∧ 0 ≤ r.h ∧
        (boundsOf fullRects fullPts).minX ≤ r.x ∧
        r.x + r.w ≤ (boundsOf fullRects fullPts).right ∧
        (boundsOf fullRects fullPts).minY ≤ r.y ∧
        r.y + r.h ≤ (boundsOf fullRects fullPts).bottom := by
    intro k e env r hk henv hr
    obtain ⟨hew, heh, entry, hentry, hex, hey, hxw, hyh⟩ := hfit k e env hk henv
    have hdims : ∀ s ∈ (routeLabels labels e.decl).map fun l => (l.width, l.height),
        0 ≤ s.1 ∧ 0 ≤ s.2 := by
      intro s hs
      rw [List.mem_map] at hs
      obtain ⟨l, hl, rfl⟩ := hs
      exact ⟨(hlab l (List.mem_filter.mp hl).1).1, (hlab l (List.mem_filter.mp hl).1).2.1⟩
    have hcon := Labels.stackRects_contained_at (x := env.x) (y := env.y) (gap := cg.slot)
      entry hslot hdims hex hxw hey hyh r hr
    have hentry' := boundsOf_contains_rect fullRects fullPts entry (hsub entry hentry)
    exact ⟨entry, hentry, hcon.1, hcon.2.1,
      Int.le_trans hentry'.1 hcon.2.2.1,
      Int.le_trans hcon.2.2.2.1 hentry'.2.1,
      Int.le_trans hentry'.2.2.1 hcon.2.2.2.2.1,
      Int.le_trans hcon.2.2.2.2.2 hentry'.2.2.2⟩
  intro q hq
  unfold placedLabels at hq
  dsimp only at hq
  rw [List.mem_filterMap] at hq
  obtain ⟨l, hl, hq2⟩ := hq
  obtain ⟨edge, hedge, hq2⟩ := Option.bind_eq_some_iff.mp hq2
  obtain ⟨e, he, hq2⟩ := Option.bind_eq_some_iff.mp hq2
  obtain ⟨env, henv, hq2⟩ := Option.bind_eq_some_iff.mp hq2
  have hq2' : (Option.bind
      (List.find? (fun w : MeasuredLabel × Rect => w.1.index == l.index)
        ((routeLabels labels e.decl).zip
          (Labels.stackRects env.x env.y cg.slot
            ((routeLabels labels e.decl).map fun m : MeasuredLabel => (m.width, m.height)))))
      (fun placed : MeasuredLabel × Rect => Option.some (l.index, placed.2))) = some q := hq2
  obtain ⟨placed, hplaced, hq3⟩ := Option.bind_eq_some_iff.mp hq2'
  have hq4 : (l.index, placed.2) = q := Option.some.inj (by simpa using hq3)
  subst hq4
  have hr : placed.2 ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) :=
    Labels.mem_zip_snd (List.mem_of_find?_eq_some hplaced)
  obtain ⟨entry, hentry, hw, hh, hx, hxw, hy, hyh⟩ :=
    stack_contained edge e env placed.2 he henv hr
  exact ⟨hx, hxw, hy, hyh, hw, hh⟩

/-- Every `labelBounds` entry has nonnegative dimensions when every label
envelope does. -/
theorem labelBounds_dims (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hfit : EnvelopeFits P cg run labels) :
    ∀ r ∈ labelBounds P cg run labels, 0 ≤ r.w ∧ 0 ≤ r.h := by
  intro r hr
  unfold labelBounds at hr
  rw [List.mem_filterMap] at hr
  obtain ⟨q, hq, hr2⟩ := hr
  have hzip : cg.edges[q.2]? = some q.1 :=
    List.mem_zipIdx_iff_getElem?.mp hq
  obtain ⟨env, henv, hr3⟩ := Option.bind_eq_some_iff.mp hr2
  obtain ⟨hew, heh, _, _, _, _, _, _⟩ := hfit q.2 q.1 env hzip henv
  split at hr3
  · injection hr3 with he
    rw [← he]
    exact ⟨hew, heh⟩
  · obtain ⟨first, hf, hr4⟩ := Option.bind_eq_some_iff.mp hr3
    injection hr4 with he
    rw [← he]
    dsimp only
    have hin : first ∈ routeLabels labels q.1.decl :=
      List.mem_of_mem_head? (by rw [hf]; simp)
    have hg : 0 ≤ first.gutter := (hlab first (List.mem_filter.mp hin).1).2.2
    constructor
    · omega
    · exact heh

/-- A placed component part is bounded when its proper nodes have nonnegative
dimensions, its title anchors do, its measured labels do, and the label
envelopes fit their stacks. This replaces every accumulator-shaped assumption. -/
theorem placeComponent_partBounded (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
    (hdims : ProperDimsNonneg run.proper)
    (hprop : ∀ i, i < cg.nodes.length → i < run.proper.nodes.length)
    (htitles : ∀ (i : Nat) (top : Node), cg.nodes[i]? = some top → top.border = -2 →
      0 ≤ top.w ∧ P.clusterPad ≤ top.h)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hslot : 0 ≤ cg.slot)
    (hfit : EnvelopeFits P cg run labels) :
    PartBounded (placeComponent P cg run 0 labels loops) := by
  have lb_dims := labelBounds_dims P cg run labels hlab hfit
  have ct_dims := componentTitles_dims_nonneg P cg run htitles
  have width_nonneg : 0 ≤ (placeComponent P cg run 0 labels loops).width := by
    unfold placeComponent
    refine boundsOf_width_nonneg ?_
    by_cases hp : (run.routes.flatMap (·.points) ++ loops.flatMap fun q => q.2.points) = []
    · by_cases hr1 : (List.range cg.nodes.length).map (frameRect P cg run) = []
      · by_cases hr2 :
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx = []
        · by_cases hr3 : labelBounds P cg run labels = []
          · by_cases hr4 : (componentTitles P cg run).map (·.2) = []
            · refine Or.inr (Or.inr ⟨?_, hp⟩)
              rw [hr2, hr1, hr3, hr4]
              simp
            · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hr4
              obtain ⟨t0, ht0, ht1⟩ := List.mem_map.mp ht
              subst ht1
              refine Or.inl ⟨t0.2, ?_, (ct_dims t0 ht0).1⟩
              rw [hr2, hr1, hr3]
              exact List.mem_append.mpr (Or.inr ht)
          · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hr3
            refine Or.inl ⟨r, ?_, (lb_dims r hr).1⟩
            rw [hr2, hr1]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))
        · exfalso
          have hp0 : 0 <
              ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.length :=
            List.length_pos_iff.mpr hr2
          rw [List.length_zipIdx] at hp0
          rw [hr1] at hp0
          simp at hp0
      · obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr1
        obtain ⟨i0, hi0mem, hr0e⟩ := List.mem_map.mp hr0
        subst hr0e
        have hi0 : i0 < cg.nodes.length := List.mem_range.mp hi0mem
        have hd := frameRect_dims_nonneg P cg run i0 hdims (hprop i0 hi0)
        refine Or.inl ⟨frameRect P cg run i0, ?_, hd.1⟩
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i0, hi0mem, rfl⟩))))))
    · exact Or.inr (Or.inl hp)
  have height_nonneg : 0 ≤ (placeComponent P cg run 0 labels loops).height := by
    unfold placeComponent
    refine boundsOf_height_nonneg ?_
    by_cases hp : (run.routes.flatMap (·.points) ++ loops.flatMap fun q => q.2.points) = []
    · by_cases hr1 : (List.range cg.nodes.length).map (frameRect P cg run) = []
      · by_cases hr2 :
          ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx = []
        · by_cases hr3 : labelBounds P cg run labels = []
          · by_cases hr4 : (componentTitles P cg run).map (·.2) = []
            · refine Or.inr (Or.inr ⟨?_, hp⟩)
              rw [hr2, hr1, hr3, hr4]
              simp
            · obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hr4
              obtain ⟨t0, ht0, ht1⟩ := List.mem_map.mp ht
              subst ht1
              refine Or.inl ⟨t0.2, ?_, (ct_dims t0 ht0).2⟩
              rw [hr2, hr1, hr3]
              exact List.mem_append.mpr (Or.inr ht)
          · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hr3
            refine Or.inl ⟨r, ?_, (lb_dims r hr).2⟩
            rw [hr2, hr1]
            exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))
        · exfalso
          have hp0 : 0 <
              ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.length :=
            List.length_pos_iff.mpr hr2
          rw [List.length_zipIdx] at hp0
          rw [hr1] at hp0
          simp at hp0
      · obtain ⟨r0, hr0⟩ := List.exists_mem_of_ne_nil _ hr1
        obtain ⟨i0, hi0mem, hr0e⟩ := List.mem_map.mp hr0
        subst hr0e
        have hi0 : i0 < cg.nodes.length := List.mem_range.mp hi0mem
        have hd := frameRect_dims_nonneg P cg run i0 hdims (hprop i0 hi0)
        refine Or.inl ⟨frameRect P cg run i0, ?_, hd.2⟩
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
          (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i0, hi0mem, rfl⟩))))))
    · exact Or.inr (Or.inl hp)
  refine ⟨width_nonneg, height_nonneg, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hb := placeComponent_rects_bounds_zero P cg run labels loops r hr
    have hdims : 0 ≤ r.w ∧ 0 ≤ r.h := by
      obtain ⟨r0, hr0, hr1⟩ := List.mem_map.mp hr
      subst hr1
      obtain ⟨i0, hi0mem, hr2⟩ := List.mem_map.mp hr0
      subst hr2
      exact frameRect_dims_nonneg P cg run i0 hdims
        (hprop i0 (List.mem_range.mp hi0mem))
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hdims.1, hdims.2⟩
  · intro t ht'
    have hb := placeComponent_titles_bounds_zero P cg run labels loops t ht'
    obtain ⟨q0, hq0m, rfl⟩ := List.mem_map.mp ht'
    have hdim := ct_dims q0 hq0m
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hdim.1, hdim.2⟩
  · intro route hroute p hp
    have hb : 0 ≤ p.x ∧ p.x ≤ (placeComponent P cg run 0 labels loops).width ∧
        0 ≤ p.y ∧ p.y ≤ (placeComponent P cg run 0 labels loops).height := by
      obtain ⟨q, hqmem, hr1⟩ := List.mem_map.mp hroute
      subst hr1
      dsimp only at hp ⊢
      obtain ⟨origP, horigP, hr2⟩ := List.mem_map.mp hp
      rw [← hr2]
      cases hloop : loops.find? (fun l => l.1 == q.1.decl) with
      | some loopPt =>
        simp only [hloop, Option.map_some, Option.getD_some] at horigP
        have hpt_in : origP ∈ loops.flatMap (fun q => q.2.points) := by
          rw [List.mem_flatMap]
          exact ⟨loopPt, List.mem_of_find?_eq_some hloop, horigP⟩
        have hpt_all : origP ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points) :=
          List.mem_append_right _ hpt_in
        exact placeComponent_shifted_point_bounds_zero P cg run labels loops origP hpt_all
      | none =>
        simp only [hloop, Option.map_none, Option.getD_none, edgePoints] at horigP
        have hpt_in : origP ∈ run.routes.flatMap (·.points) := by
          rw [List.mem_flatMap]
          cases hrun : run.routes[q.2]? with
          | none =>
            simp only [List.getD_eq_getElem?_getD, hrun, Option.getD_none] at horigP
            change origP ∈ ([] : List Point) at horigP
            contradiction
          | some rt =>
            simp only [List.getD_eq_getElem?_getD, hrun, Option.getD_some] at horigP
            exact ⟨rt, List.mem_of_getElem? hrun, horigP⟩
        have hpt_all : origP ∈ run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points) :=
          List.mem_append_left _ hpt_in
        exact placeComponent_shifted_point_bounds_zero P cg run labels loops origP hpt_all
    exact hb
  · intro l hl
    obtain ⟨q0, hq0m, hl1⟩ := List.mem_map.mp hl
    have hpm : q0 ∈ placedLabels P cg run labels := hq0m
    have hb := placedLabels_within P cg run labels
      ((List.range cg.nodes.length).map (frameRect P cg run) ++
        ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx.map (fun q =>
          ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
            q.1.h⟩) ++
        labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
      (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))
      (fun r hr' => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr'))))
      hslot hlab hfit q0 hpm
    rw [← hl1]
    dsimp only [shiftRect]
    obtain ⟨hx, hxw, hy, hyh, hw, hh⟩ := hb
    have hwidth : (placeComponent P cg run 0 labels loops).width =
        (boundsOf
          (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                List.map
                  (fun q =>
                    ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
                      q.1.h⟩)
                  ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
              labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
          (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).right -
      (boundsOf
          (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                List.map
                  (fun q =>
                    ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
                      q.1.h⟩)
                  ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
              labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
          (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minX := rfl
    have hheight : (placeComponent P cg run 0 labels loops).height =
        (boundsOf
          (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                List.map
                  (fun q =>
                    ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
                      q.1.h⟩)
                  ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
              labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
          (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).bottom -
      (boundsOf
          (List.map (frameRect P cg run) (List.range cg.nodes.length) ++
                List.map
                  (fun q =>
                    ⟨q.1.x + q.1.w, q.1.y, Loops.extent cg.slot (loopSizes cg.edges labels q.2 cg.slot),
                      q.1.h⟩)
                  ((List.range cg.nodes.length).map (frameRect P cg run)).zipIdx ++
              labelBounds P cg run labels ++ (componentTitles P cg run).map (·.2))
          (run.routes.flatMap (·.points) ++ loops.flatMap (fun q => q.2.points))).minY := rfl
    rw [hwidth, hheight]
    refine ⟨?_, ?_, ?_, ?_, hw, hh⟩
    · omega
    · omega
    · omega
    · omega

/-- Every emitted part is bounded by the component execution that produced it.
All sizing, slot, measurement, and envelope obligations are discharged here;
the only retained input is the actual successful leaf execution. -/
theorem SceneExecution.components_parts_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ part ∈ execution.componentsAcc.parts, PartBounded part.2 := by
  intro part hpart
  obtain ⟨index, run, loops, area, hrun, _, heq, hdims, hcoverage, htitles, hslot⟩ :=
    execution.actual_component_sizing hpart
  have hbound := placeComponent_partBounded execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured loops
    hdims hcoverage htitles execution.measured_nonneg hslot
    (componentRun_envelopeFits hrun execution.measured_nonneg)
  rw [heq]
  exact hbound

theorem SceneExecution.component_title_caption_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {title : Nat × Rect} (htitle : title ∈ part.2.titles) :
    let lines := execution.lines.getD (part.1.getD title.1 0) []
    let width := lines.foldl (fun value line => max value line.width) 0
    let height := (max 1 lines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h := by
  obtain ⟨index, run, loops, area, _, _, heq, _⟩ :=
    execution.actual_component_sizing hpart
  rw [heq] at htitle
  change title ∈ (componentTitles execution.params
    (componentCandidate execution.graph part.1 index) run).map (fun q =>
      (q.1, shiftRect
        (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index)
          run execution.measured loops).minX)
        (0 - (placeBounds execution.params (componentCandidate execution.graph part.1 index)
          run execution.measured loops).minY) q.2)) at htitle
  obtain ⟨raw, hraw, heTitle⟩ := List.mem_map.mp htitle
  subst title
  obtain ⟨top, htop, hborder, hindex, hw, hh⟩ :=
    componentTitles_dimension_source execution.params
      (componentCandidate execution.graph part.1 index) run hraw
  have hfit := actual_title_caption_fit execution.graph_eq
    (List.mem_zipIdx_iff_getElem?.mp htop) hborder
  have width_nonneg : ∀ (lines : List Measure.Line) (start : Int),
      0 ≤ start → 0 ≤ lines.foldl (fun width line => max width line.width) start := by
    intro lines
    induction lines with
    | nil => intro start hs; exact hs
    | cons line lines ih =>
      intro start hs
      exact ih _ (Int.le_trans hs (Int.le_max_left _ _))
  have hw0 := width_nonneg
    (execution.lines.getD (part.1.getD top.2 0) []) 0 (by omega)
  have hh0 : 0 ≤
      (max 1 (execution.lines.getD (part.1.getD top.2 0) []).length : Int) *
        execution.params.lineH :=
    Int.mul_nonneg (by omega) execution.parameter_signs.1
  dsimp only [shiftRect]
  rw [hindex, hw, hh]
  cases hd : o.direction <;> simp only [hd] at hfit ⊢ <;>
    exact ⟨by omega, by omega, by omega, by omega⟩



/-- A rectangle inside the packed canvas. -/
def RectOK (W H : Int) (r : Rect) : Prop :=
  0 ≤ r.x ∧ r.x + r.w ≤ W ∧ 0 ≤ r.y ∧ r.y + r.h ≤ H ∧ 0 ≤ r.w ∧ 0 ≤ r.h

/-- A point inside the packed canvas. -/
def PtOK (W H : Int) (p : Point) : Prop :=
  0 ≤ p.x ∧ p.x ≤ W ∧ 0 ≤ p.y ∧ p.y ≤ H

/-- Rectangular coverage: index `i` is written by the rectangles of a part when
it appears in `comp` within the length of `part.rects`. -/
def RectCovered (comp : List Nat) (rectsLength : Nat) (i : Nat) : Prop :=
  ∃ k, comp[k]? = some i ∧ k < rectsLength

/-- Route coverage: index `i` is written by the routes of a part when it equals
some route key. -/
def RouteCovered (routes : List (Nat × List Point)) (i : Nat) : Prop :=
  ∃ r ∈ routes, r.1 = i

/-- Label coverage: index `i` is written by the labels of a part when it equals
some label key. -/
def LabelCovered (labels : List (Nat × Rect)) (i : Nat) : Prop :=
  ∃ r ∈ labels, r.1 = i

/-- Array writes through `set!` are visible at the written index. -/
theorem getElem?_set!_self {α : Type} {a : Array α} {i : Nat} (hi : i < a.size) (v : α) :
    (a.set! i v)[i]? = some v := by
  rw [Array.set!_eq_setIfInBounds]
  exact Array.getElem?_setIfInBounds_self_of_lt hi

/-- Array writes through `set!` do not change other indices. -/
theorem getElem?_set!_ne {α : Type} {a : Array α} {i j : Nat} (hne : i ≠ j) (v : α) :
    (a.set! i v)[j]? = a[j]? := by
  rw [Array.set!_eq_setIfInBounds]
  exact Array.getElem?_setIfInBounds_ne hne

/-- `Array.set!` preserves the array size. -/
theorem size_set!_eq {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds]
  exact Array.size_setIfInBounds

/-- The guarded rectangle fold preserves the array size. -/
theorem size_zipFold_eq (g : Rect → Rect) (vals : List Rect) :
    ∀ (comp : List Nat) (a : Array Rect),
      ((comp.zip vals).foldl
          (fun a q => if q.1 < a.size then a.set! q.1 (g q.2) else a) a).size = a.size := by
  induction vals with
  | nil => intro comp a; rw [List.zip_nil_right, List.foldl_nil]
  | cons v vs ih =>
    intro comp a
    cases comp with
    | nil => rw [List.zip_nil_left, List.foldl_nil]
    | cons c0 crest =>
      rw [List.zip_cons_cons, List.foldl_cons, ih crest
        (if c0 < a.size then a.set! c0 (g v) else a)]
      split
      · rw [size_set!_eq]
      · rfl

/-- The key-indexed rectangle fold preserves the array size. -/
theorem size_keyFold_rects_eq (g : Rect → Rect) (vals : List (Nat × Rect)) (a : Array Rect) :
    (vals.foldl (fun a q => a.set! q.1 (g q.2)) a).size = a.size := by
  induction vals generalizing a with
  | nil => rw [List.foldl_nil]
  | cons v vs ih => rw [List.foldl_cons, ih, size_set!_eq]

/-- The key-indexed point-list fold preserves the array size. -/
theorem size_keyFold_pts_eq (g : List Point → List Point) (vals : List (Nat × List Point))
    (a : Array (List Point)) :
    (vals.foldl (fun a r => a.set! r.1 (g r.2)) a).size = a.size := by
  induction vals generalizing a with
  | nil => rw [List.foldl_nil]
  | cons v vs ih => rw [List.foldl_cons, ih, size_set!_eq]

/-- The guarded `comp`-keyed rectangle fold keeps the index covered below the
array size, or the previous value. -/
theorem zipCover_rects (g : Rect → Rect) (vals : List Rect) :
    ∀ (comp : List Nat) (a : Array Rect) (i : Nat) (r : Rect),
      ((comp.zip vals).foldl
          (fun a q => if q.1 < a.size then a.set! q.1 (g q.2) else a) a)[i]? = some r →
      (∃ k, comp[k]? = some i ∧ k < vals.length ∧ i < a.size) ∨ a[i]? = some r := by
  induction vals with
  | nil =>
    intro comp a i r hi
    rw [List.zip_nil_right, List.foldl_nil] at hi
    exact Or.inr hi
  | cons v vs ih =>
    intro comp a i r hi
    cases comp with
    | nil =>
      rw [List.zip_nil_left, List.foldl_nil] at hi
      exact Or.inr hi
    | cons c0 crest =>
      rw [List.zip_cons_cons, List.foldl_cons] at hi
      split at hi
      · rename_i hc0
        rcases ih crest (a.set! c0 (g v)) i r hi with ⟨k, hk, hkl, hil⟩ | h
        · rw [size_set!_eq] at hil
          refine Or.inl ⟨k + 1, ?_, by rw [List.length_cons]; omega, hil⟩
          show (c0 :: crest)[k + 1]? = some i
          rw [List.getElem?_cons_succ]
          exact hk
        · by_cases hci : c0 = i
          · refine Or.inl ⟨0, ?_, by simp, by rw [hci] at hc0; exact hc0⟩
            show (c0 :: crest)[0]? = some i
            rw [hci]
            exact List.getElem?_cons_zero
          · rw [getElem?_set!_ne hci] at h
            exact Or.inr h
      · rename_i hc0
        rcases ih crest a i r hi with ⟨k, hk, hkl, hil⟩ | h
        · refine Or.inl ⟨k + 1, ?_, by rw [List.length_cons]; omega, hil⟩
          show (c0 :: crest)[k + 1]? = some i
          rw [List.getElem?_cons_succ]
          exact hk
        · exact Or.inr h

/-- The key-indexed point-list fold keeps the key covered below the array
size, or the previous value. -/
theorem keyCover_pts (g : List Point → List Point) (vals : List (Nat × List Point)) :
    ∀ (a : Array (List Point)) (i : Nat) (pts : List Point),
      (vals.foldl (fun a r => a.set! r.1 (g r.2)) a)[i]? = some pts →
      (∃ r ∈ vals, r.1 = i ∧ i < a.size) ∨ a[i]? = some pts := by
  induction vals with
  | nil =>
    intro a i pts hi
    rw [List.foldl_nil] at hi
    exact Or.inr hi
  | cons v vs ih =>
    intro a i pts hi
    rw [List.foldl_cons] at hi
    rcases ih (a.set! v.1 (g v.2)) i pts hi with ⟨r, hr, hke, hil⟩ | h
    · rw [size_set!_eq a v.1 (g v.2)] at hil
      exact Or.inl ⟨r, List.mem_cons_of_mem _ hr, hke, hil⟩
    · by_cases he : i = v.1
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, he] at h
        split at h
        · split at h
          · rename_i hisz
            exact Or.inl ⟨v, List.mem_cons_self, he.symm, by rw [he]; exact hisz⟩
          · exact absurd h (by simp)
        · rename_i himp
          exact (himp rfl).elim
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
        simp only [Ne.symm he, reduceIte] at h
        exact Or.inr h

/-- The key-indexed rectangle fold keeps the key covered below the array size,
or the previous value. -/
theorem keyCover_rects (g : Rect → Rect) (vals : List (Nat × Rect)) :
    ∀ (a : Array Rect) (i : Nat) (r : Rect),
      (vals.foldl (fun a q => a.set! q.1 (g q.2)) a)[i]? = some r →
      (∃ q ∈ vals, q.1 = i ∧ i < a.size) ∨ a[i]? = some r := by
  induction vals with
  | nil =>
    intro a i r hi
    rw [List.foldl_nil] at hi
    exact Or.inr hi
  | cons v vs ih =>
    intro a i r hi
    rw [List.foldl_cons] at hi
    rcases ih (a.set! v.1 (g v.2)) i r hi with ⟨q, hq, hke, hil⟩ | h
    · rw [size_set!_eq a v.1 (g v.2)] at hil
      exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, hke, hil⟩
    · by_cases he : i = v.1
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, he] at h
        split at h
        · split at h
          · rename_i hisz
            exact Or.inl ⟨v, List.mem_cons_self, he.symm, by rw [he]; exact hisz⟩
          · exact absurd h (by simp)
        · rename_i himp
          exact (himp rfl).elim
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
        simp only [Ne.symm he, reduceIte] at h
        exact Or.inr h

/-- Setting the bookkeeping area of a part does not change its rectangles. -/
theorem withArea_rects (p : Part) (a : Int) : ({ p with area := a } : Part).rects = p.rects := rfl

/-- Rectangle writes of `layoutComponent` land at indices covered by the
appended part below the array size, or the value is inherited. -/
theorem layoutComponent_rects_cover {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.rects[i]? = some r →
      (∃ part ∈ acc'.parts, RectCovered part.1 part.2.rects.length i ∧ i < acc.rects.size) ∨
      acc.rects[i]? = some r := by
  unfold layoutComponent at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.rects he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hrects0⟩ :
        ∃ p : Part, result.parts = acc.parts ++ [(comp, p)] ∧
          p.rects = (placeComponent P chosen.value.fst chosen.value.snd 0 measured loops).rects := by
      apply Exists.intro
      refine ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases zipCover_rects id _ comp acc.rects i r hi with hz | h
    · obtain ⟨k, hk, hkl, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.rects = part0.rects := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hrects0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hrects0]
        exact ⟨k, hk, hkl⟩
    · exact Or.inr h

/-- Route writes of `layoutComponent` land at keys of the appended part below
the array size, or the value is inherited. -/
theorem layoutComponent_routes_cover {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    ∀ i (pts : List Point), acc'.routes[i]? = some pts →
      (∃ part ∈ acc'.parts, RouteCovered part.2.routes i ∧ i < acc.routes.size) ∨
      acc.routes[i]? = some pts := by
  unfold layoutComponent at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i pts hi
  rw [← congrArg Acc.routes he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hroutes0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.routes = (placeComponent P chosen.value.fst chosen.value.snd 0 measured loops).routes := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_pts id _ acc.routes i pts hi with hz | h
    · obtain ⟨r, hr, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.routes = part0.routes := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hroutes0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hroutes0]
        exact ⟨r, hr, hke⟩
    · exact Or.inr h

/-- Label writes of `layoutComponent` land at keys of the appended part below
the array size, or the value is inherited. -/
theorem layoutComponent_labels_cover {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    ∀ i (r : Rect), acc'.labels[i]? = some r →
      (∃ part ∈ acc'.parts, LabelCovered part.2.labels i ∧ i < acc.labels.size) ∨
      acc.labels[i]? = some r := by
  unfold layoutComponent at h
  obtain ⟨chosen, hchosen, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  intro i r hi
  rw [← congrArg Acc.labels he] at hi
  dsimp only at hi
  unfold placePart at hresult
  obtain ⟨loops, hloops, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · obtain ⟨part0, _hPl, hlabels0⟩ : ∃ p : Part,
        result.parts = acc.parts ++ [(comp, p)] ∧
          p.labels = (placeComponent P chosen.value.fst chosen.value.snd 0 measured loops).labels := by
      apply Exists.intro
      exact ⟨Eq.symm (congrArg Acc.parts (Except.ok.inj hres)), rfl⟩
    have heq := Except.ok.inj hres
    subst heq
    dsimp only at hi
    rcases keyCover_rects id _ acc.labels i r hi with hz | h
    · obtain ⟨q, hq, hke, hil⟩ := hz
      obtain ⟨partApp, hmem0, hpartsEq⟩ : ∃ p : Part,
          acc'.parts = acc.parts ++ [(comp, p)] ∧ p.labels = part0.labels := by
        rw [← congrArg Acc.parts he]
        apply Exists.intro
        · refine ⟨?_, ?_⟩
          · simp only [List.drop_append, List.drop_length, Nat.sub_self, List.drop_zero,
              List.map_cons, List.map_nil, List.nil_append]
            try rfl
          · exact hlabels0.symm
      refine Or.inl ⟨(comp, partApp), ?_, ?_, hil⟩
      · rw [hmem0]
        exact List.mem_append.mpr (Or.inr (by simp))
      · rw [hpartsEq, hlabels0]
        exact ⟨q, hq, hke⟩
    · exact Or.inr h

/-- `layoutComponent` preserves the three array sizes. -/
theorem layoutComponent_sizes {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    acc.rects.size = acc'.rects.size ∧ acc.routes.size = acc'.routes.size ∧
      acc.labels.size = acc'.labels.size := by
  unfold layoutComponent at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hr := congrArg Acc.rects he
  have ho := congrArg Acc.routes he
  have hl := congrArg Acc.labels he
  unfold placePart at hresult
  obtain ⟨_, _, hres⟩ := bind_ok hresult
  dsimp only at hres
  split at hres
  · simp at hres
  · have heq := Except.ok.inj hres
    subst heq
    dsimp only at hr ho hl
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr]; exact (size_zipFold_eq id _ _ _).symm
    · rw [← ho]; exact (size_keyFold_pts_eq id _ _).symm
    · rw [← hl]; exact (size_keyFold_rects_eq id _ _).symm

/-- `layoutComponent` keeps every incoming part. -/
theorem layoutComponent_parts_mono {P : Params} {inp : Input} {o : Options} {g : Graph}
    {acc acc' : Acc} {comp : List Nat} {measured : List MeasuredLabel}
    (h : layoutComponent P inp o g acc comp measured = .ok acc') :
    ∀ q ∈ acc.parts, q ∈ acc'.parts := by
  unfold layoutComponent at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨result, hresult, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have he := Except.ok.inj h
  have hp := congrArg Acc.parts he
  intro q hq
  rw [← hp]
  exact List.mem_append.mpr (Or.inl hq)

/-- The component fold never removes parts. -/
theorem foldlM_parts_mono (f : Acc → List Nat → Except LayoutError Acc)
    (hmono : ∀ start comp acc', f start comp = .ok acc' →
      ∀ q ∈ start.parts, q ∈ acc'.parts) :
    ∀ (comps : List (List Nat)) (start : Acc) (acc : Acc),
      comps.foldlM f start = .ok acc → ∀ q ∈ start.parts, q ∈ acc.parts := by
  intro comps
  induction comps with
  | nil =>
    intro start acc h q hq
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    exact hq
  | cons c cs ih =>
    intro start acc h q hq
    simp only [List.foldlM_cons] at h
    cases hc : f start c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      exact ih next acc h q (hmono start c next hc q hq)

/-- The component fold keeps the start rectangle at indices its parts never
cover. -/
theorem foldlM_rects_uncovered (f : Acc → List Nat → Except LayoutError Acc)
    (cover : ∀ start comp acc', f start comp = .ok acc' →
      ∀ i (r : Rect), acc'.rects[i]? = some r →
        (∃ part ∈ acc'.parts, RectCovered part.1 part.2.rects.length i ∧ i < start.rects.size) ∨
        start.rects[i]? = some r)
    (hmono : ∀ start comp acc', f start comp = .ok acc' →
      ∀ q ∈ start.parts, q ∈ acc'.parts) :
    ∀ (comps : List (List Nat)) (start : Acc) (acc : Acc),
      comps.foldlM f start = .ok acc →
      (∀ (i : Nat) (r : Rect), start.rects[i]? = some r →
        ((∀ q ∈ start.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨ i ≥ start.rects.size) →
        r = default) →
      ∀ (i : Nat) (r : Rect), acc.rects[i]? = some r →
        ((∀ q ∈ acc.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨ i ≥ acc.rects.size) →
        r = default := by
  intro comps
  induction comps with
  | nil =>
    intro start acc h hbase
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    exact hbase
  | cons c cs ih =>
    intro start acc h hbase
    simp only [List.foldlM_cons] at h
    cases hc : f start c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      have hbase' : ∀ (i : Nat) (r : Rect), next.rects[i]? = some r →
          ((∀ q ∈ next.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨ i ≥ next.rects.size) →
          r = default := by
        intro i r hi hun
        rcases hun with hun | hge
        · rcases cover start c next hc i r hi with ⟨part, hpm, hcn, -⟩ | hinstart
          · exact absurd hcn (hun part hpm)
          · exact hbase i r hinstart
              (Or.inl (fun q hq hcvq => hun q (hmono start c next hc q hq) hcvq))
        · rw [Array.getElem?_eq_none hge] at hi
          exact absurd hi (by simp)
      exact ih next acc h hbase'

/-- The component fold keeps the start route at indices its parts never
cover. -/
theorem foldlM_routes_uncovered (f : Acc → List Nat → Except LayoutError Acc)
    (cover : ∀ start comp acc', f start comp = .ok acc' →
      ∀ i (pts : List Point), acc'.routes[i]? = some pts →
        (∃ part ∈ acc'.parts, RouteCovered part.2.routes i ∧ i < start.routes.size) ∨
        start.routes[i]? = some pts)
    (hmono : ∀ start comp acc', f start comp = .ok acc' →
      ∀ q ∈ start.parts, q ∈ acc'.parts) :
    ∀ (comps : List (List Nat)) (start : Acc) (acc : Acc),
      comps.foldlM f start = .ok acc →
      (∀ (i : Nat) (pts : List Point), start.routes[i]? = some pts →
        ((∀ q ∈ start.parts, ¬ RouteCovered q.2.routes i) ∨ i ≥ start.routes.size) →
        pts = []) →
      ∀ (i : Nat) (pts : List Point), acc.routes[i]? = some pts →
        ((∀ q ∈ acc.parts, ¬ RouteCovered q.2.routes i) ∨ i ≥ acc.routes.size) →
        pts = [] := by
  intro comps
  induction comps with
  | nil =>
    intro start acc h hbase
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    exact hbase
  | cons c cs ih =>
    intro start acc h hbase
    simp only [List.foldlM_cons] at h
    cases hc : f start c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      have hbase' : ∀ (i : Nat) (pts : List Point), next.routes[i]? = some pts →
          ((∀ q ∈ next.parts, ¬ RouteCovered q.2.routes i) ∨ i ≥ next.routes.size) →
          pts = [] := by
        intro i pts hi hun
        rcases hun with hun | hge
        · rcases cover start c next hc i pts hi with ⟨part, hpm, hcn, -⟩ | hinstart
          · exact absurd hcn (hun part hpm)
          · exact hbase i pts hinstart
              (Or.inl (fun q hq hcvq => hun q (hmono start c next hc q hq) hcvq))
        · rw [Array.getElem?_eq_none hge] at hi
          exact absurd hi (by simp)
      exact ih next acc h hbase'

/-- The component fold keeps the start label at indices its parts never
cover. -/
theorem foldlM_labels_uncovered (f : Acc → List Nat → Except LayoutError Acc)
    (cover : ∀ start comp acc', f start comp = .ok acc' →
      ∀ i (r : Rect), acc'.labels[i]? = some r →
        (∃ part ∈ acc'.parts, LabelCovered part.2.labels i ∧ i < start.labels.size) ∨
        start.labels[i]? = some r)
    (hmono : ∀ start comp acc', f start comp = .ok acc' →
      ∀ q ∈ start.parts, q ∈ acc'.parts) :
    ∀ (comps : List (List Nat)) (start : Acc) (acc : Acc),
      comps.foldlM f start = .ok acc →
      (∀ (i : Nat) (r : Rect), start.labels[i]? = some r →
        ((∀ q ∈ start.parts, ¬ LabelCovered q.2.labels i) ∨ i ≥ start.labels.size) →
        r = default) →
      ∀ (i : Nat) (r : Rect), acc.labels[i]? = some r →
        ((∀ q ∈ acc.parts, ¬ LabelCovered q.2.labels i) ∨ i ≥ acc.labels.size) →
        r = default := by
  intro comps
  induction comps with
  | nil =>
    intro start acc h hbase
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    exact hbase
  | cons c cs ih =>
    intro start acc h hbase
    simp only [List.foldlM_cons] at h
    cases hc : f start c with
    | error e => simp [hc, bind, Except.bind] at h
    | ok next =>
      simp only [hc, bind, Except.bind] at h
      have hbase' : ∀ (i : Nat) (r : Rect), next.labels[i]? = some r →
          ((∀ q ∈ next.parts, ¬ LabelCovered q.2.labels i) ∨ i ≥ next.labels.size) →
          r = default := by
        intro i r hi hun
        rcases hun with hun | hge
        · rcases cover start c next hc i r hi with ⟨part, hpm, hcn, -⟩ | hinstart
          · exact absurd hcn (hun part hpm)
          · exact hbase i r hinstart
              (Or.inl (fun q hq hcvq => hun q (hmono start c next hc q hq) hcvq))
        · rw [Array.getElem?_eq_none hge] at hi
          exact absurd hi (by simp)
      exact ih next acc h hbase'

/-- The guarded `comp`-keyed rectangle fold writes only bounded shifts; values
it does not touch keep the incoming invariant. -/
theorem zipFold_untouched (g : Rect → Rect) (vals : List Rect) :
    ∀ (comp : List Nat) (a : Array Rect) (i : Nat),
      (¬ RectCovered comp vals.length i ∨ ¬ (i < a.size)) →
      ((comp.zip vals).foldl
          (fun a q => if q.1 < a.size then a.set! q.1 (g q.2) else a) a)[i]? = a[i]? := by
  induction vals with
  | nil => intro comp a i _; rw [List.zip_nil_right, List.foldl_nil]
  | cons v vs ih =>
    intro comp a i h
    cases comp with
    | nil => rw [List.zip_nil_left, List.foldl_nil]
    | cons c0 crest =>
      rw [List.zip_cons_cons, List.foldl_cons]
      rcases h with hnc | hsz
      · by_cases hci : c0 = i
        · rw [hci] at hnc
          exact absurd ⟨0, rfl, by simp⟩ hnc
        · have htail : ¬ RectCovered crest vs.length i := by
            intro hcv
            obtain ⟨k, hk, hkl⟩ := hcv
            exact hnc ⟨k + 1, by rw [List.getElem?_cons_succ]; exact hk,
              by rw [List.length_cons]; omega⟩
          rw [ih crest (if c0 < a.size then a.set! c0 (g v) else a) i (Or.inl htail),
            Array.set!_eq_setIfInBounds]
          split
          · rw [Array.getElem?_setIfInBounds_ne hci]
          · rfl
      · by_cases hci : c0 = i
        · rw [hci]
          rw [ite_eq_right hsz]
          exact ih crest a i (Or.inr hsz)
        · split
          · rename_i hlt
            rw [ih crest (a.set! c0 (g v)) i
              (Or.inr (by rw [size_set!_eq]; exact hsz)),
              Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
            simp only [show ¬ (c0 = i) from hci, reduceIte]
          · exact ih crest a i (Or.inr hsz)

/-- The guarded `comp`-keyed rectangle fold writes a bounded shift at every
covered index below the array size, and the last writer wins. -/
theorem zipFold_val_shifted (g : Rect → Rect) (vals : List Rect) :
    ∀ (comp : List Nat) (a : Array Rect) (i : Nat),
      RectCovered comp vals.length i → i < a.size →
      ∃ v ∈ vals, ((comp.zip vals).foldl
          (fun a q => if q.1 < a.size then a.set! q.1 (g q.2) else a) a)[i]? = some (g v) := by
  induction vals with
  | nil =>
    intro comp a i hcov _
    obtain ⟨k, _, hkl⟩ := hcov
    exact absurd hkl (by simp)
  | cons v vs ih =>
    intro comp a i hcov hisz
    obtain ⟨k, hk, hkl⟩ := hcov
    cases comp with
    | nil => exact absurd hk (by simp)
    | cons c0 crest =>
      rw [List.zip_cons_cons, List.foldl_cons]
      split
      · rename_i hlt
        by_cases htail : RectCovered crest vs.length i
        · obtain ⟨v', hv', hv'l⟩ :=
            ih crest (a.set! c0 (g v)) i htail (by rw [size_set!_eq]; exact hisz)
          exact ⟨v', List.mem_cons_of_mem _ hv', hv'l⟩
        · cases k with
          | zero =>
            rw [List.getElem?_cons_zero, Option.some.injEq] at hk
            rw [hk]
            dsimp only
            rw [zipFold_untouched g vs crest (a.set! i (g v)) i (Or.inl htail),
              getElem?_set!_self hisz]
            exact ⟨v, List.mem_cons_self, rfl⟩
          | succ k' =>
            rw [List.getElem?_cons_succ] at hk
            rw [List.length_cons] at hkl
            exact absurd ⟨k', hk, by omega⟩ htail
      · rename_i hlt
        cases k with
        | zero =>
          rw [List.getElem?_cons_zero, Option.some.injEq] at hk
          rw [hk] at hlt
          exact absurd hisz hlt
        | succ k' =>
          rw [List.getElem?_cons_succ] at hk
          rw [List.length_cons] at hkl
          obtain ⟨v', hv', hv'l⟩ := ih crest a i ⟨k', hk, by omega⟩ hisz
          exact ⟨v', List.mem_cons_of_mem _ hv', hv'l⟩

/-- The key-indexed point-list fold does not touch an index that no write
reaches, and it keeps the previous value there. -/
theorem keyFold_untouched_pts (g : List Point → List Point)
    (vals : List (Nat × List Point)) :
    ∀ (a : Array (List Point)) (i : Nat),
      (¬ (∃ r ∈ vals, r.1 = i) ∨ ¬ (i < a.size)) →
      (vals.foldl (fun a q => a.set! q.1 (g q.2)) a)[i]? = a[i]? := by
  induction vals with
  | nil => intro a i _; rw [List.foldl_nil]
  | cons v vs ih =>
    intro a i h
    rw [List.foldl_cons]
    rcases h with hnc | hsz
    · by_cases hei : i = v.1
      · subst hei
        exact absurd ⟨v, List.mem_cons_self, rfl⟩ hnc
      · rw [ih (a.set! v.1 (g v.2)) i
            (Or.inl (fun ⟨r', hr', hke'⟩ => hnc ⟨r', List.mem_cons_of_mem _ hr', hke'⟩)),
          Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [show ¬ (v.1 = i) from fun h' => hei h'.symm, reduceIte]
    · by_cases hei : i = v.1
      · subst hei
        have hsz' : ¬ (v.1 < (a.set! v.1 (g v.2)).size) := by
          rw [size_set!_eq]
          exact hsz
        rw [ih (a.set! v.1 (g v.2)) v.1 (Or.inr hsz')]
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        rw [size_set!_eq] at hsz'
        simp only [reduceIte]
        rw [ite_eq_right hsz']
        exact (Array.getElem?_eq_none (Nat.not_lt.mp hsz')).symm
      · rw [ih (a.set! v.1 (g v.2)) i
            (Or.inr (by rw [size_set!_eq a v.1 (g v.2)]; exact hsz)),
          Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [show ¬ (v.1 = i) from fun h' => hei h'.symm, reduceIte]

/-- The key-indexed point-list fold writes a bounded shift at its covered
keys below the array size, and the last writer wins. -/
theorem keyFold_val_pts (g : List Point → List Point) (vals : List (Nat × List Point)) :
    ∀ (a : Array (List Point)) (i : Nat), (∃ r ∈ vals, r.1 = i) → i < a.size →
      ∃ r ∈ vals, (vals.foldl (fun a q => a.set! q.1 (g q.2)) a)[i]? = some (g r.2) := by
  induction vals with
  | nil =>
    intro a i hcov _
    obtain ⟨r, hr, _⟩ := hcov
    exact absurd hr (by simp)
  | cons v vs ih =>
    intro a i hcov hisz
    obtain ⟨r, hr, hke⟩ := hcov
    rcases List.mem_cons.mp hr with hr'' | hr'
    · by_cases htail : ∃ r' ∈ vs, r'.1 = i
      · obtain ⟨r'', hr2, hke2⟩ := htail
        obtain ⟨w, hw, hw'l⟩ := ih (a.set! v.1 (g v.2)) i ⟨r'', hr2, hke2⟩
          (by rw [size_set!_eq a v.1 (g v.2)]; exact hisz)
        exact ⟨w, List.mem_cons_of_mem _ hw, hw'l⟩
      · have hvi : v.1 = i := by rw [← hr'']; exact hke
        rw [List.foldl_cons, hvi,
          keyFold_untouched_pts g vs (a.set! i (g v.2)) i (Or.inl htail),
          getElem?_set!_self hisz]
        exact ⟨v, List.mem_cons_self, rfl⟩
    · obtain ⟨w, hw, hw'l⟩ := ih (a.set! v.1 (g v.2)) i ⟨r, hr', hke⟩
        (by rw [size_set!_eq a v.1 (g v.2)]; exact hisz)
      exact ⟨w, List.mem_cons_of_mem _ hw, hw'l⟩

/-- The key-indexed rectangle fold does not touch an index that no write
reaches, and it keeps the previous value there. -/
theorem keyFold_untouched_rects (g : Rect → Rect) (vals : List (Nat × Rect)) :
    ∀ (a : Array Rect) (i : Nat),
      (¬ (∃ r ∈ vals, r.1 = i) ∨ ¬ (i < a.size)) →
      (vals.foldl (fun a q => a.set! q.1 (g q.2)) a)[i]? = a[i]? := by
  induction vals with
  | nil => intro a i _; rw [List.foldl_nil]
  | cons v vs ih =>
    intro a i h
    rw [List.foldl_cons]
    rcases h with hnc | hsz
    · by_cases hei : i = v.1
      · subst hei
        exact absurd ⟨v, List.mem_cons_self, rfl⟩ hnc
      · rw [ih (a.set! v.1 (g v.2)) i
            (Or.inl (fun ⟨r', hr', hke'⟩ => hnc ⟨r', List.mem_cons_of_mem _ hr', hke'⟩)),
          Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [show ¬ (v.1 = i) from fun h' => hei h'.symm, reduceIte]
    · by_cases hei : i = v.1
      · subst hei
        have hsz' : ¬ (v.1 < (a.set! v.1 (g v.2)).size) := by
          rw [size_set!_eq]
          exact hsz
        rw [ih (a.set! v.1 (g v.2)) v.1 (Or.inr hsz')]
        rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        rw [size_set!_eq] at hsz'
        simp only [reduceIte]
        rw [ite_eq_right hsz']
        exact (Array.getElem?_eq_none (Nat.not_lt.mp hsz')).symm
      · rw [ih (a.set! v.1 (g v.2)) i
            (Or.inr (by rw [size_set!_eq a v.1 (g v.2)]; exact hsz)),
          Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp only [show ¬ (v.1 = i) from fun h' => hei h'.symm, reduceIte]

/-- The key-indexed rectangle fold writes a bounded shift at its covered keys
below the array size, and the last writer wins. -/
theorem keyFold_val_rects (g : Rect → Rect) (vals : List (Nat × Rect)) :
    ∀ (a : Array Rect) (i : Nat), (∃ r ∈ vals, r.1 = i) → i < a.size →
      ∃ r ∈ vals, (vals.foldl (fun a q => a.set! q.1 (g q.2)) a)[i]? = some (g r.2) := by
  induction vals with
  | nil =>
    intro a i hcov _
    obtain ⟨r, hr, _⟩ := hcov
    exact absurd hr (by simp)
  | cons v vs ih =>
    intro a i hcov hisz
    obtain ⟨r, hr, hke⟩ := hcov
    rcases List.mem_cons.mp hr with hr'' | hr'
    · by_cases htail : ∃ r' ∈ vs, r'.1 = i
      · obtain ⟨r'', hr2, hke2⟩ := htail
        obtain ⟨w, hw, hw'l⟩ := ih (a.set! v.1 (g v.2)) i ⟨r'', hr2, hke2⟩
          (by rw [size_set!_eq a v.1 (g v.2)]; exact hisz)
        exact ⟨w, List.mem_cons_of_mem _ hw, hw'l⟩
      · have hvi : v.1 = i := by rw [← hr'']; exact hke
        rw [List.foldl_cons, hvi,
          keyFold_untouched_rects g vs (a.set! i (g v.2)) i (Or.inl htail),
          getElem?_set!_self hisz]
        exact ⟨v, List.mem_cons_self, rfl⟩
    · obtain ⟨w, hw, hw'l⟩ := ih (a.set! v.1 (g v.2)) i ⟨r, hr', hke⟩
        (by rw [size_set!_eq a v.1 (g v.2)]; exact hisz)
      exact ⟨w, List.mem_cons_of_mem _ hw, hw'l⟩

/-- The guarded `comp`-keyed rectangle fold writes only bounded shifts; values
it does not touch keep the incoming invariant. -/
theorem rectsInner_bounded (W H : Int) (_hcw : 0 ≤ W) (_hch : 0 ≤ H)
    (dx dy : Int) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) (pw ph : Int)
    (hX : dx + pw ≤ W) (hY : dy + ph ≤ H)
    (vals : List Rect)
    (hrb : ∀ r ∈ vals, 0 ≤ r.x ∧ r.x + r.w ≤ pw ∧ 0 ≤ r.y ∧ r.y + r.h ≤ ph ∧ 0 ≤ r.w ∧ 0 ≤ r.h)
    (comp : List Nat) (a : Array Rect)
    (Cov : Nat → Prop)
    (ha : ∀ i (r : Rect), a[i]? = some r →
      (¬ RectCovered comp vals.length i ∨ ¬ (i < a.size)) →
      RectOK W H r ∨ r = default ∨ (Cov i ∧ i < a.size)) :
    ∀ i (r : Rect), ((comp.zip vals).foldl
        (fun a q => if q.1 < a.size then a.set! q.1 (shiftRect dx dy q.2) else a) a)[i]? = some r →
      RectOK W H r ∨ r = default ∨ (Cov i ∧ i < a.size) := by
  intro i r hi
  have hisz : i < a.size := by
    by_cases hb : i < a.size
    · exact hb
    · exfalso
      have hnone : a[i]? = none := Array.getElem?_eq_none (Nat.not_lt.mp hb)
      rw [zipFold_untouched (shiftRect dx dy) vals comp a i (Or.inr hb)] at hi
      rw [hnone] at hi
      exact absurd hi (by simp)
  by_cases hcv : RectCovered comp vals.length i
  · obtain ⟨v, hv, hv'l⟩ := zipFold_val_shifted (shiftRect dx dy) vals comp a i hcv hisz
    have hreq : r = shiftRect dx dy v := Option.some.inj (hi.symm.trans hv'l)
    refine Or.inl ?_
    rw [hreq]
    exact packed_rect_bounds (hrb v hv).1 (hrb v hv).2.1 (hrb v hv).2.2.1
      (hrb v hv).2.2.2.1 (hrb v hv).2.2.2.2.1 (hrb v hv).2.2.2.2.2 hdx hX hdy hY
  · rw [zipFold_untouched (shiftRect dx dy) vals comp a i (Or.inl hcv)] at hi
    exact ha i r hi (Or.inl hcv)

/-- The key-indexed point-list fold writes only bounded shifts; untouched
values keep the incoming invariant. -/
theorem keyPtsInner_bounded (W H : Int) (_hcw : 0 ≤ W) (_hch : 0 ≤ H)
    (dx dy : Int) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) (pw ph : Int)
    (hX : dx + pw ≤ W) (hY : dy + ph ≤ H)
    (vals : List (Nat × List Point))
    (hrb : ∀ r ∈ vals, ∀ p ∈ r.2, 0 ≤ p.x ∧ p.x ≤ pw ∧ 0 ≤ p.y ∧ p.y ≤ ph)
    (a : Array (List Point))
    (Cov : Nat → Prop)
    (ha : ∀ i (pts : List Point), a[i]? = some pts →
      (¬ RouteCovered vals i ∨ ¬ (i < a.size)) →
      (∀ p ∈ pts, PtOK W H p) ∨ pts = [] ∨ (Cov i ∧ i < a.size)) :
    ∀ i (pts : List Point),
      (vals.foldl (fun a r => a.set! r.1 (r.2.map (shiftPoint dx dy))) a)[i]? = some pts →
      (∀ p ∈ pts, PtOK W H p) ∨ pts = [] ∨ (Cov i ∧ i < a.size) := by
  intro i pts hi
  have hisz : i < a.size := by
    by_cases hb : i < a.size
    · exact hb
    · exfalso
      have hnone : a[i]? = none := Array.getElem?_eq_none (Nat.not_lt.mp hb)
      rw [keyFold_untouched_pts (fun l => l.map (shiftPoint dx dy)) vals a i (Or.inr hb)] at hi
      rw [hnone] at hi
      exact absurd hi (by simp)
  by_cases hcv : RouteCovered vals i
  · obtain ⟨r, hr, hke⟩ := hcv
    obtain ⟨w, hw, hw'l⟩ :=
      keyFold_val_pts (fun l => l.map (shiftPoint dx dy)) vals a i ⟨r, hr, hke⟩ hisz
    have hpts : pts = w.2.map (shiftPoint dx dy) := Option.some.inj (hi.symm.trans hw'l)
    refine Or.inl (fun p hp => ?_)
    rw [hpts, List.mem_map] at hp
    obtain ⟨p0, hp0m, rfl⟩ := hp
    have h4 := hrb w hw p0 hp0m
    exact packed_point_bounds h4.1 h4.2.1 h4.2.2.1 h4.2.2.2 hdx hX hdy hY
  · rw [keyFold_untouched_pts (fun l => l.map (shiftPoint dx dy)) vals a i (Or.inl hcv)] at hi
    exact ha i pts hi (Or.inl hcv)

/-- The key-indexed rectangle fold writes only bounded shifts; untouched
values keep the incoming invariant. -/
theorem keyRectsInner_bounded (W H : Int) (_hcw : 0 ≤ W) (_hch : 0 ≤ H)
    (dx dy : Int) (hdx : 0 ≤ dx) (hdy : 0 ≤ dy) (pw ph : Int)
    (hX : dx + pw ≤ W) (hY : dy + ph ≤ H)
    (vals : List (Nat × Rect))
    (hrb : ∀ r ∈ vals, 0 ≤ r.2.x ∧ r.2.x + r.2.w ≤ pw ∧ 0 ≤ r.2.y ∧ r.2.y + r.2.h ≤ ph ∧
      0 ≤ r.2.w ∧ 0 ≤ r.2.h)
    (a : Array Rect)
    (Cov : Nat → Prop)
    (ha : ∀ i (r : Rect), a[i]? = some r →
      (¬ LabelCovered vals i ∨ ¬ (i < a.size)) →
      RectOK W H r ∨ r = default ∨ (Cov i ∧ i < a.size)) :
    ∀ i (r : Rect),
      (vals.foldl (fun a q => a.set! q.1 (shiftRect dx dy q.2)) a)[i]? = some r →
      RectOK W H r ∨ r = default ∨ (Cov i ∧ i < a.size) := by
  intro i r hi
  have hisz : i < a.size := by
    by_cases hb : i < a.size
    · exact hb
    · exfalso
      have hnone : a[i]? = none := Array.getElem?_eq_none (Nat.not_lt.mp hb)
      rw [keyFold_untouched_rects (shiftRect dx dy) vals a i (Or.inr hb)] at hi
      rw [hnone] at hi
      exact absurd hi (by simp)
  by_cases hcv : LabelCovered vals i
  · obtain ⟨r0, hr0, hke⟩ := hcv
    obtain ⟨w, hw, hw'l⟩ := keyFold_val_rects (shiftRect dx dy) vals a i ⟨r0, hr0, hke⟩ hisz
    have hreq : r = shiftRect dx dy w.2 := Option.some.inj (hi.symm.trans hw'l)
    refine Or.inl ?_
    rw [hreq]
    exact packed_rect_bounds (hrb w hw).1 (hrb w hw).2.1 (hrb w hw).2.2.1
      (hrb w hw).2.2.2.1 (hrb w hw).2.2.2.2.1 (hrb w hw).2.2.2.2.2 hdx hX hdy hY
  · rw [keyFold_untouched_rects (shiftRect dx dy) vals a i (Or.inl hcv)] at hi
    exact ha i r hi (Or.inl hcv)

/-- One packing step. -/
def packStep (out : Acc) (q : (List Nat × Part) × Rect) : Acc :=
  { out with
    rects := (q.1.1.zip q.1.2.rects).foldl
      (fun a r => if r.1 < a.size then a.set! r.1 (shiftRect q.2.x q.2.y r.2) else a) out.rects
    routes := q.1.2.routes.foldl
      (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) out.routes
    labels := q.1.2.labels.foldl
      (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) out.labels
    titles := out.titles ++ q.1.2.titles.map
      (fun r => (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2)) }

/-- The packing invariant: stored values are bounded, defaults, or still
pending coverage by a remaining part; titles are bounded. -/
def PackInv (W H : Int) (qs : List ((List Nat × Part) × Rect)) (out : Acc) : Prop :=
  (∀ i (r : Rect), out.rects[i]? = some r →
    RectOK W H r ∨ r = default ∨
      (∃ q ∈ qs, RectCovered q.1.1 q.1.2.rects.length i ∧ i < out.rects.size)) ∧
  (∀ i (pts : List Point), out.routes[i]? = some pts →
    (∀ p ∈ pts, PtOK W H p) ∨ pts = [] ∨
      (∃ q ∈ qs, RouteCovered q.1.2.routes i ∧ i < out.routes.size)) ∧
  (∀ i (r : Rect), out.labels[i]? = some r →
    RectOK W H r ∨ r = default ∨
      (∃ q ∈ qs, LabelCovered q.1.2.labels i ∧ i < out.labels.size)) ∧
  (∀ t ∈ out.titles, RectOK W H t.2)

/-- One packing step preserves the array sizes. -/
theorem packStep_sizes (start : Acc) (q : (List Nat × Part) × Rect) :
    (packStep start q).rects.size = start.rects.size ∧
      (packStep start q).routes.size = start.routes.size ∧
      (packStep start q).labels.size = start.labels.size := by
  unfold packStep
  refine ⟨?_, ?_, ?_⟩
  · exact size_zipFold_eq (shiftRect q.2.x q.2.y) q.1.2.rects q.1.1 start.rects
  · exact size_keyFold_pts_eq (fun l => l.map (shiftPoint q.2.x q.2.y)) q.1.2.routes
      start.routes
  · exact size_keyFold_rects_eq (shiftRect q.2.x q.2.y) q.1.2.labels start.labels

/-- The packing fold preserves the canvas dimensions. -/
theorem foldl_packStep_canvas (qs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (qs.foldl packStep start).canvasW = start.canvasW ∧
      (qs.foldl packStep start).canvasH = start.canvasH := by
  induction qs generalizing start with
  | nil => exact ⟨rfl, rfl⟩
  | cons q rest ih =>
    rw [List.foldl_cons, (ih (packStep start q)).1, (ih (packStep start q)).2]
    exact ⟨rfl, rfl⟩

/-- One packing step maintains the packing invariant. -/
theorem packStep_inv (W H : Int) (hcw : 0 ≤ W) (hch : 0 ≤ H)
    (qs : List ((List Nat × Part) × Rect)) (q : (List Nat × Part) × Rect)
    (hbox : ∀ z ∈ q :: qs, 0 ≤ z.2.x ∧ z.2.x + z.1.2.width ≤ W ∧
      0 ≤ z.2.y ∧ z.2.y + z.1.2.height ≤ H)
    (hpart : ∀ z ∈ q :: qs, PartBounded z.1.2)
    (start : Acc)
    (hinv : PackInv W H (q :: qs) start) :
    PackInv W H qs (packStep start q) := by
  obtain ⟨hinv1, hinv2, hinv3, hinv4⟩ := hinv
  have hqmem : q ∈ q :: qs := List.mem_cons_self
  have hqbox := hbox q hqmem
  have hqpart := hpart q hqmem
  have hsizes := packStep_sizes start q
  have hrects : ∀ (i' : Nat) (r' : Rect), start.rects[i']? = some r' →
      (¬ RectCovered q.1.1 q.1.2.rects.length i' ∨ ¬ i' < start.rects.size) →
      RectOK W H r' ∨ r' = default ∨
        ((∃ q' ∈ qs, RectCovered q'.1.1 q'.1.2.rects.length i') ∧ i' < start.rects.size) := by
    intro i' r' hi' hunc
    rcases hinv1 i' r' hi' with h' | h' | ⟨q', hq', hcv, hsz⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr ⟨?_, hsz⟩)
      rcases List.mem_cons.mp hq' with heq | hmem
      · exfalso
        rw [heq] at hcv
        rcases hunc with h1 | h2
        · exact h1 hcv
        · exact h2 hsz
      · exact ⟨q', hmem, hcv⟩
  have hroutes : ∀ (i' : Nat) (pts' : List Point), start.routes[i']? = some pts' →
      (¬ RouteCovered q.1.2.routes i' ∨ ¬ i' < start.routes.size) →
      (∀ p ∈ pts', PtOK W H p) ∨ pts' = [] ∨
        ((∃ q' ∈ qs, RouteCovered q'.1.2.routes i') ∧ i' < start.routes.size) := by
    intro i' pts' hi' hunc
    rcases hinv2 i' pts' hi' with h' | h' | ⟨q', hq', hcv, hsz⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr ⟨?_, hsz⟩)
      rcases List.mem_cons.mp hq' with heq | hmem
      · exfalso
        rw [heq] at hcv
        rcases hunc with h1 | h2
        · exact h1 hcv
        · exact h2 hsz
      · exact ⟨q', hmem, hcv⟩
  have hlabels : ∀ (i' : Nat) (r' : Rect), start.labels[i']? = some r' →
      (¬ LabelCovered q.1.2.labels i' ∨ ¬ i' < start.labels.size) →
      RectOK W H r' ∨ r' = default ∨
        ((∃ q' ∈ qs, LabelCovered q'.1.2.labels i') ∧ i' < start.labels.size) := by
    intro i' r' hi' hunc
    rcases hinv3 i' r' hi' with h' | h' | ⟨q', hq', hcv, hsz⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · refine Or.inr (Or.inr ⟨?_, hsz⟩)
      rcases List.mem_cons.mp hq' with heq | hmem
      · exfalso
        rw [heq] at hcv
        rcases hunc with h1 | h2
        · exact h1 hcv
        · exact h2 hsz
      · exact ⟨q', hmem, hcv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i r hi
    have h := rectsInner_bounded W H hcw hch q.2.x q.2.y hqbox.1 hqbox.2.2.1
      q.1.2.width q.1.2.height hqbox.2.1 hqbox.2.2.2 q.1.2.rects
      (fun r hr => hqpart.2.2.1 r hr) q.1.1 start.rects
      (fun j => ∃ q' ∈ qs, RectCovered q'.1.1 q'.1.2.rects.length j)
      hrects i r hi
    rcases h with h | h | ⟨hcov0, hsz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨q', hq', hcv⟩ := hcov0
      exact Or.inr (Or.inr ⟨q', hq', hcv, by rw [hsizes.1]; exact hsz⟩)
  · intro i pts hi
    have h := keyPtsInner_bounded W H hcw hch q.2.x q.2.y hqbox.1 hqbox.2.2.1
      q.1.2.width q.1.2.height hqbox.2.1 hqbox.2.2.2 q.1.2.routes
      (fun r hr p hp => hqpart.2.2.2.2.1 r hr p hp) start.routes
      (fun j => ∃ q' ∈ qs, RouteCovered q'.1.2.routes j)
      hroutes i pts hi
    rcases h with h | h | ⟨hcov0, hsz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨q', hq', hcv⟩ := hcov0
      exact Or.inr (Or.inr ⟨q', hq', hcv, by rw [hsizes.2.1]; exact hsz⟩)
  · intro i r hi
    have h := keyRectsInner_bounded W H hcw hch q.2.x q.2.y hqbox.1 hqbox.2.2.1
      q.1.2.width q.1.2.height hqbox.2.1 hqbox.2.2.2 q.1.2.labels
      (fun r hr => hqpart.2.2.2.2.2 r hr) start.labels
      (fun j => ∃ q' ∈ qs, LabelCovered q'.1.2.labels j)
      hlabels i r hi
    rcases h with h | h | ⟨hcov0, hsz⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨q', hq', hcv⟩ := hcov0
      exact Or.inr (Or.inr ⟨q', hq', hcv, by rw [hsizes.2.2]; exact hsz⟩)
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hinv4 t h
    · rw [List.mem_map] at h
      obtain ⟨r0, hr0, rfl⟩ := h
      dsimp only
      exact packed_rect_bounds (hqpart.2.2.2.1 r0 hr0).1 (hqpart.2.2.2.1 r0 hr0).2.1
        (hqpart.2.2.2.1 r0 hr0).2.2.1 (hqpart.2.2.2.1 r0 hr0).2.2.2.1
        (hqpart.2.2.2.1 r0 hr0).2.2.2.2.1 (hqpart.2.2.2.1 r0 hr0).2.2.2.2.2
        hqbox.1 hqbox.2.1 hqbox.2.2.1 hqbox.2.2.2


/-- The packing fold keeps stored values bounded or defaulted, and titles
bounded. -/
theorem packFold_bounded (W H : Int) (hcw : 0 ≤ W) (hch : 0 ≤ H)
    (qs : List ((List Nat × Part) × Rect)) :
    ∀ (start : Acc),
      (∀ q ∈ qs, 0 ≤ q.2.x ∧ q.2.x + q.1.2.width ≤ W ∧
        0 ≤ q.2.y ∧ q.2.y + q.1.2.height ≤ H) →
      (∀ q ∈ qs, PartBounded q.1.2) →
      PackInv W H qs start →
      (∀ (i : Nat) (r : Rect), (qs.foldl packStep start).rects[i]? = some r →
          RectOK W H r ∨ r = default) ∧
      (∀ (i : Nat) (pts : List Point), (qs.foldl packStep start).routes[i]? = some pts →
          (∀ p ∈ pts, PtOK W H p) ∨ pts = []) ∧
      (∀ (i : Nat) (r : Rect), (qs.foldl packStep start).labels[i]? = some r →
          RectOK W H r ∨ r = default) ∧
      (∀ t ∈ (qs.foldl packStep start).titles, RectOK W H t.2) := by
  induction qs with
  | nil =>
    intro start _ _ hinv
    obtain ⟨hinv1, hinv2, hinv3, hinv4⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i r hi
      rcases hinv1 i r hi with h | h | ⟨q', hq', _, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hq' (by simp)
    · intro i pts hi
      rcases hinv2 i pts hi with h | h | ⟨q', hq', _, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hq' (by simp)
    · intro i r hi
      rcases hinv3 i r hi with h | h | ⟨q', hq', _, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hq' (by simp)
    · intro t ht
      exact hinv4 t ht
  | cons q rest ih =>
    intro start hbox hpart hinv
    have hstep := packStep_inv W H hcw hch rest q hbox hpart start hinv
    simp only [List.foldl_cons]
    exact ih (packStep start q)
      (fun z hz => hbox z (List.mem_cons_of_mem _ hz))
      (fun z hz => hpart z (List.mem_cons_of_mem _ hz)) hstep

/-- Position-paired extraction from a zip of equal-length lists. -/
theorem mem_zip_pairing {α β : Type} {l₁ : List α} {l₂ : List β}
    (hlen : l₁.length = l₂.length)
    (q : α × β) (hq : q ∈ l₁.zip l₂) :
    ∃ k : Nat, l₁[k]? = some q.1 ∧ l₂[k]? = some q.2 := by
  revert l₂
  induction l₁ with
  | nil =>
    intro l₂ hlen hq
    cases l₂ with
    | nil => cases hq
    | cons b bs => rw [List.zip_nil_left] at hq; cases hq
  | cons a as ih =>
    intro l₂ hlen hq
    cases l₂ with
    | nil => rw [List.zip_nil_right] at hq; cases hq
    | cons b bs =>
      rw [List.zip_cons_cons] at hq
      rcases List.mem_cons.mp hq with heq | htail
      · subst heq
        exact ⟨0, by simp, by simp⟩
      · have hl : as.length = bs.length := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨k, hk1, hk2⟩ := ih hl htail
        exact ⟨k + 1, by rw [List.getElem?_cons_succ]; exact hk1,
          by rw [List.getElem?_cons_succ]; exact hk2⟩

/-- Paired lookups at one index give zip membership. -/
theorem zip_mem_of_getElem? {α β : Type} {l₁ : List α} {l₂ : List β} :
    ∀ {k : Nat} {x : α} {y : β}, l₁[k]? = some x → l₂[k]? = some y →
      (x, y) ∈ l₁.zip l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    intro k x y h1 _
    exact absurd h1 (by simp)
  | cons _ as ih =>
    rename_i l₂
    intro k x y h1 h2
    cases l₂ with
    | nil => exact absurd h2 (by simp)
    | cons _ bs =>
      rw [List.zip_cons_cons]
      cases k with
      | zero =>
        rw [List.getElem?_cons_zero] at h1 h2
        rw [Option.some.injEq] at h1 h2
        subst h1
        subst h2
        exact List.mem_cons.mpr (Or.inl rfl)
      | succ k' =>
        rw [List.getElem?_cons_succ] at h1 h2
        exact List.mem_cons_of_mem _ (ih h1 h2)

/-- Packing turns bounded parts into a bounded accumulator. -/
theorem inlineFold_eq_packStep (qs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (qs.foldl (fun out q => { out with
      rects := (q.1.1.zip q.1.2.rects).foldl
        (fun a r => if r.1 < a.size then a.set! r.1 (shiftRect q.2.x q.2.y r.2) else a) out.rects
      routes := q.1.2.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) out.routes
      labels := q.1.2.labels.foldl
        (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) out.labels
      titles := out.titles ++ q.1.2.titles.map
        (fun r => (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2)) }) start) =
      (qs.foldl packStep start) := by
  induction qs generalizing start with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    exact ih { start with
      rects := (q.1.1.zip q.1.2.rects).foldl
        (fun a r => if r.1 < a.size then a.set! r.1 (shiftRect q.2.x q.2.y r.2) else a) start.rects
      routes := q.1.2.routes.foldl
        (fun a r => a.set! r.1 (r.2.map (shiftPoint q.2.x q.2.y))) start.routes
      labels := q.1.2.labels.foldl
        (fun a r => a.set! r.1 (shiftRect q.2.x q.2.y r.2)) start.labels
      titles := start.titles ++ q.1.2.titles.map
        (fun r => (q.1.1.getD r.1 0, shiftRect q.2.x q.2.y r.2)) }

theorem packAcc_bounded {P : Params} {o : Options} {acc out : Acc}
    (hparts : ∀ q ∈ acc.parts, PartBounded q.2)
    (hstart_rects : ∀ (i : Nat) (r : Rect), acc.rects[i]? = some r →
      ((∀ q ∈ acc.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨ i ≥ acc.rects.size) →
      r = default)
    (hstart_routes : ∀ (i : Nat) (pts : List Point), acc.routes[i]? = some pts →
      ((∀ q ∈ acc.parts, ¬ RouteCovered q.2.routes i) ∨ i ≥ acc.routes.size) → pts = [])
    (hstart_labels : ∀ (i : Nat) (r : Rect), acc.labels[i]? = some r →
      ((∀ q ∈ acc.parts, ¬ LabelCovered q.2.labels i) ∨ i ≥ acc.labels.size) → r = default)
    (h : packAcc P o acc = .ok out) :
    AccBounded out.canvasW out.canvasH out := by
  have hcn := packAcc_canvas_nonneg h
  obtain ⟨hcnw, hcnh⟩ := hcn
  unfold packAcc at h
  obtain ⟨packed, hpk, h⟩ := bind_ok h
  rw [inlineFold_eq_packStep] at h
  have he := Except.ok.inj h
  have hcanvas : packed.width = out.canvasW ∧ packed.height = out.canvasH := by
    rw [← he]
    have hfc := foldl_packStep_canvas (acc.parts.zip packed.boxes)
      ({ acc with canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc)
    rw [hfc.1, hfc.2]
    exact ⟨rfl, rfl⟩
  have hcw : 0 ≤ packed.width := by rw [hcanvas.1]; exact hcnw
  have hch : 0 ≤ packed.height := by rw [hcanvas.2]; exact hcnh
  have hcount := Pack.pack_count hpk
  have hlen : acc.parts.length = packed.boxes.length := by
    rw [hcount]
    simp
  have hbound := Pack.pack_bounds hpk
  have hbox : ∀ q ∈ acc.parts.zip packed.boxes,
      0 ≤ q.2.x ∧ q.2.x + q.1.2.width ≤ packed.width ∧
      0 ≤ q.2.y ∧ q.2.y + q.1.2.height ≤ packed.height := by
    intro q hq
    obtain ⟨k, hk1, hk2⟩ := mem_zip_pairing hlen q hq
    have hbk : packed.boxes[k]? = some q.2 := hk2
    have hmem : q.2 ∈ packed.boxes := List.mem_of_getElem? hbk
    have hbf := hbound.2 q.2 hmem
    have hwh : q.2.w = q.1.2.width ∧ q.2.h = q.1.2.height := by
      have hdim' := Pack.pack_dimensions hpk
      simp only [Pack.dimensions, List.map_map, Function.comp_def] at hdim'
      have h1 := congrArg (fun l : List (Int × Int) => l[k]?) hdim'
      rw [List.getElem?_map, hbk, List.getElem?_map, hk1] at h1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
      exact h1
    obtain ⟨hw, hh⟩ := hwh
    exact ⟨hbf.1, by omega, hbf.2.1, by omega⟩
  have hpair : ∀ q' ∈ acc.parts, ∃ bx : Rect, (q', bx) ∈ acc.parts.zip packed.boxes := by
    intro q' hq'
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hq'
    have hkl : k < acc.parts.length := (List.getElem?_eq_some_iff.mp hk).1
    have hbk : k < packed.boxes.length := by omega
    have hbx : packed.boxes[k]? = some packed.boxes[k] :=
      List.getElem?_eq_some_iff.mpr ⟨hbk, rfl⟩
    exact ⟨packed.boxes[k], zip_mem_of_getElem? hk hbx⟩
  have hpart' : ∀ q ∈ acc.parts.zip packed.boxes, PartBounded q.1.2 := by
    intro q hq
    obtain ⟨k, hk1, _⟩ := mem_zip_pairing hlen q hq
    exact hparts q.1 (List.mem_of_getElem? hk1)
  have hstart : PackInv packed.width packed.height (acc.parts.zip packed.boxes)
      { acc with canvasW := packed.width, canvasH := packed.height, titles := [] } :=
    ⟨fun i r hi => by
      by_cases hpend : ∃ q ∈ acc.parts.zip packed.boxes,
        RectCovered q.1.1 q.1.2.rects.length i
      · obtain ⟨z, hzm, hzc⟩ := hpend
        exact Or.inr (Or.inr ⟨z, hzm, hzc, (Array.getElem?_eq_some_iff.mp hi).1⟩)
      · refine Or.inr (Or.inl (hstart_rects i r hi (Or.inl ?_)))
        intro q' hq' hcv
        obtain ⟨bx, hbx⟩ := hpair q' hq'
        exact hpend ⟨(q', bx), hbx, hcv⟩,
     fun i pts hi => by
      by_cases hpend : ∃ q ∈ acc.parts.zip packed.boxes,
        RouteCovered q.1.2.routes i
      · obtain ⟨z, hzm, hzc⟩ := hpend
        exact Or.inr (Or.inr ⟨z, hzm, hzc, (Array.getElem?_eq_some_iff.mp hi).1⟩)
      · refine Or.inr (Or.inl (hstart_routes i pts hi (Or.inl ?_)))
        intro q' hq' hcov
        obtain ⟨bx, hbx⟩ := hpair q' hq'
        exact hpend ⟨(q', bx), hbx, hcov⟩,
     fun i r hi => by
      by_cases hpend : ∃ q ∈ acc.parts.zip packed.boxes,
        LabelCovered q.1.2.labels i
      · obtain ⟨z, hzm, hzc⟩ := hpend
        exact Or.inr (Or.inr ⟨z, hzm, hzc, (Array.getElem?_eq_some_iff.mp hi).1⟩)
      · refine Or.inr (Or.inl (hstart_labels i r hi (Or.inl ?_)))
        intro q' hq' hcov
        obtain ⟨bx, hbx⟩ := hpair q' hq'
        exact hpend ⟨(q', bx), hbx, hcov⟩,
     fun t ht => absurd ht (by simp)⟩
  have hs_rects_zip : ∀ (i : Nat) (r : Rect),
      ({ acc with canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc).rects[i]? = some r →
      ((∀ z ∈ acc.parts.zip packed.boxes, ¬ RectCovered z.1.1 z.1.2.rects.length i) ∨
        i ≥ acc.rects.size) → r = default := by
    intro i r hi hcov
    rcases hcov with hun | hge
    · refine hstart_rects i r hi (Or.inl (fun q' hq' hcv => ?_))
      obtain ⟨bx, hbx⟩ := hpair q' hq'
      exact hun (q', bx) hbx hcv
    · exact hstart_rects i r hi (Or.inr hge)
  have hs_routes_zip : ∀ (i : Nat) (pts : List Point),
      ({ acc with canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc).routes[i]? = some pts →
      ((∀ z ∈ acc.parts.zip packed.boxes, ¬ RouteCovered z.1.2.routes i) ∨
        i ≥ acc.routes.size) → pts = [] := by
    intro i pts hi hcov
    rcases hcov with hun | hge
    · refine hstart_routes i pts hi (Or.inl (fun q' hq' hcv => ?_))
      obtain ⟨bx, hbx⟩ := hpair q' hq'
      exact hun (q', bx) hbx hcv
    · exact hstart_routes i pts hi (Or.inr hge)
  have hs_labels_zip : ∀ (i : Nat) (r : Rect),
      ({ acc with canvasW := packed.width, canvasH := packed.height, titles := [] } : Acc).labels[i]? = some r →
      ((∀ z ∈ acc.parts.zip packed.boxes, ¬ LabelCovered z.1.2.labels i) ∨
        i ≥ acc.labels.size) → r = default := by
    intro i r hi hcov
    rcases hcov with hun | hge
    · refine hstart_labels i r hi (Or.inl (fun q' hq' hcv => ?_))
      obtain ⟨bx, hbx⟩ := hpair q' hq'
      exact hun (q', bx) hbx hcv
    · exact hstart_labels i r hi (Or.inr hge)
  obtain ⟨c1, c2, c3, c4⟩ :=
    packFold_bounded packed.width packed.height hcw hch (acc.parts.zip packed.boxes)
      { acc with canvasW := packed.width, canvasH := packed.height, titles := [] }
      hbox hpart' hstart
  have hdef : ∀ (W H : Int), 0 ≤ W → 0 ≤ H → RectOK W H (default : Rect) := by
    intro W H _ _
    have e1 : (default : Rect).x = 0 := rfl
    have e2 : (default : Rect).y = 0 := rfl
    have e3 : (default : Rect).w = 0 := rfl
    have e4 : (default : Rect).h = 0 := rfl
    constructor <;> omega
  refine ⟨hcnw, hcnh, ?_, ?_, ?_, ?_⟩
  · intro i r hi
    rw [← he] at hi
    rcases c1 i r hi with h | h
    · rw [hcanvas.1, hcanvas.2] at h
      exact h
    · rw [h]
      exact hdef out.canvasW out.canvasH hcnw hcnh
  · rw [he] at c4
    rw [hcanvas.1, hcanvas.2] at c4
    exact c4
  · intro i pts hi
    rw [← he] at hi
    rcases c2 i pts hi with h | h
    · rw [hcanvas.1, hcanvas.2] at h
      exact h
    · rw [h]
      simp
  · intro i r hi
    rw [← he] at hi
    rcases c3 i r hi with h | h
    · rw [hcanvas.1, hcanvas.2] at h
      exact h
    · rw [h]
      exact hdef out.canvasW out.canvasH hcnw hcnh

/-- The fold's starting arrays hold only the defaults written at construction. -/
theorem layout_startAcc_defaults (inp : Input) :
    (∀ (i : Nat) (r : Rect), (Array.replicate inp.boxes.length default)[i]? = some r → r = default) ∧
    (∀ (i : Nat) (pts : List Point), (Array.replicate inp.routes.length ([] : List Point))[i]? = some pts → pts = []) ∧
    (∀ (i : Nat) (r : Rect), (Array.replicate inp.labels.length default)[i]? = some r → r = default) := by
  constructor
  · intro i r hi
    rw [Array.getElem?_replicate] at hi
    split at hi
    · exact (Option.some.inj hi).symm
    · exact absurd hi (by simp)
  · constructor
    · intro i pts hi
      rw [Array.getElem?_replicate] at hi
      split at hi
      · exact (Option.some.inj hi).symm
      · exact absurd hi (by simp)
    · intro i r hi
      rw [Array.getElem?_replicate] at hi
      split at hi
      · exact (Option.some.inj hi).symm
      · exact absurd hi (by simp)

/-- The start accumulator of `layout` and every parts hypothesis instance are
one execution's actual fold data. -/
theorem SceneExecution.packedAcc_bounded {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hparts : ∀ q ∈ execution.componentsAcc.parts, PartBounded q.2) :
    AccBounded execution.packedAcc.canvasW execution.packedAcc.canvasH execution.packedAcc := by
  have hstart_rects : ∀ (i : Nat) (r : Rect),
      execution.componentsAcc.rects[i]? = some r →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ RectCovered q.1 q.2.rects.length i) ∨
        i ≥ execution.componentsAcc.rects.size) → r = default := by
    refine foldlM_rects_uncovered
      (fun a c => layoutComponent execution.params inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponent_rects_cover hc)
      (fun start comp acc' hc => layoutComponent_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).1 i r hi
  have hstart_routes : ∀ (i : Nat) (pts : List Point),
      execution.componentsAcc.routes[i]? = some pts →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ RouteCovered q.2.routes i) ∨
        i ≥ execution.componentsAcc.routes.size) → pts = [] := by
    refine foldlM_routes_uncovered
      (fun a c => layoutComponent execution.params inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponent_routes_cover hc)
      (fun start comp acc' hc => layoutComponent_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i pts hi _ => (layout_startAcc_defaults inp).2.1 i pts hi
  have hstart_labels : ∀ (i : Nat) (r : Rect),
      execution.componentsAcc.labels[i]? = some r →
      ((∀ q ∈ execution.componentsAcc.parts, ¬ LabelCovered q.2.labels i) ∨
        i ≥ execution.componentsAcc.labels.size) → r = default := by
    refine foldlM_labels_uncovered
      (fun a c => layoutComponent execution.params inp o
        execution.graph a c execution.measured)
      (fun start comp acc' hc => layoutComponent_labels_cover hc)
      (fun start comp acc' hc => layoutComponent_parts_mono hc)
      (components execution.graph)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩
      execution.componentsAcc execution.components_eq ?_
    exact fun i r hi _ => (layout_startAcc_defaults inp).2.2 i r hi
  exact packAcc_bounded hparts hstart_rects hstart_routes hstart_labels execution.packed_eq

/-- Boxes, routes, and canvas dimensions of a successful leaf execution are
contained in the canvas whenever every placed component part is bounded. -/
theorem layout_scene_box_route_bounded {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res)
    (hparts : ∀ q ∈ (Classical.choice (layout_sceneExecution h)).componentsAcc.parts,
      PartBounded q.2) :
    0 ≤ res.scene.canvas.w ∧ 0 ≤ res.scene.canvas.h ∧
      (∀ q ∈ res.scene.boxes.zipIdx,
        Size.containsCellRect res.scene.canvas q.1.rect = true) ∧
      (∀ q ∈ res.scene.routes.zipIdx, ∀ p ∈ q.1.points,
        Size.containsCell res.scene.canvas p = true) := by
  let execution := Classical.choice (layout_sceneExecution h)
  have hacc := execution.packedAcc_bounded hparts
  have _hm := layout_canvas_margins h
  have hm1 := checkedParams_canvasMargin_ge_one execution.checked
  have hm0 := canvasMarginOf_ge_one o.profile inp.kind
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [execution.scene_eq]
    exact sceneOf_boxes_bounded execution.params inp o execution.lines
      execution.packedAcc execution.measured hacc (by omega)
  · rw [execution.scene_eq]
    exact sceneOf_routes_bounded execution.params inp o execution.lines
      execution.packedAcc execution.measured hacc hm1

theorem layout_scene_box_route_bounded_of_success
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    0 ≤ res.scene.canvas.w ∧ 0 ≤ res.scene.canvas.h ∧
      (∀ q ∈ res.scene.boxes.zipIdx,
        Size.containsCellRect res.scene.canvas q.1.rect = true) ∧
      (∀ q ∈ res.scene.routes.zipIdx, ∀ p ∈ q.1.points,
        Size.containsCell res.scene.canvas p = true) := by
  let execution := Classical.choice (layout_sceneExecution h)
  exact layout_scene_box_route_bounded h execution.components_parts_bounded

theorem SceneExecution.measured_rect_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (index : Nat) :
    Size.containsCellRect res.scene.canvas
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.labels.getD index default))) = true := by
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hrect :
      let rect := execution.packedAcc.labels.getD index default
      0 ≤ rect.x ∧ rect.x + rect.w ≤ execution.packedAcc.canvasW ∧
      0 ≤ rect.y ∧ rect.y + rect.h ≤ execution.packedAcc.canvasH ∧
      0 ≤ rect.w ∧ 0 ≤ rect.h := by
    cases hget : execution.packedAcc.labels[index]? with
    | none =>
      rw [Array.getD_eq_getD_getElem?, hget]
      change 0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasW ∧
        0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasH ∧
        0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
      exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg,
        by omega, by omega⟩
    | some stored =>
      rw [Array.getD_eq_getD_getElem?, hget]
      exact hacc.labels_bounded index stored hget
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  rw [execution.scene_eq]
  exact orient_shiftRect_containsCellRect o.direction execution.packedAcc.canvasW
    execution.packedAcc.canvasH execution.params.canvasMargin _ hrect (by omega)

theorem SceneExecution.measured_label_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index : Nat} {source : ModelLabel} {measured : MeasuredLabel}
    (hsource : inp.labels[index]? = some source)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = some measured)
    (hexclusive : inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false) :
    ∃ placed ∈ res.scene.labels, placed.id = source.id ∧ placed.owner = source.owner ∧
      Size.containsCellRect res.scene.canvas placed.rect = true := by
  let rect := execution.packedAcc.labels.getD measured.index default
  let placed : SceneLabel := {
    id := source.id, owner := source.owner, text := source.text
    rect := shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH rect)
    lines := measured.lines.map fun line => String.ofList line.text }
  have hemitted : placed ∈
      (sceneOf execution.params inp o execution.lines execution.packedAcc execution.measured).labels := by
    unfold sceneOf
    apply List.mem_filterMap.mpr
    refine ⟨(source, index), List.mem_zipIdx_iff_getElem?.mpr hsource, ?_⟩
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte, hmeasured]
    rfl
  have hcontained := execution.measured_rect_bounded measured.index
  rw [execution.scene_eq] at hcontained ⊢
  exact ⟨placed, hemitted, rfl, rfl, hcontained⟩

theorem SceneExecution.packed_title_caption_fit
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ title ∈ execution.packedAcc.titles,
      let lines := execution.lines.getD title.1 []
      let width := lines.foldl (fun value line => max value line.width) 0
      let height := (max 1 lines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h := by
  let fits : Nat × Rect → Prop := fun title =>
    let lines := execution.lines.getD title.1 []
    let width := lines.foldl (fun value line => max value line.width) 0
    let height := (max 1 lines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h
  have fold : ∀ (pairs : List ((List Nat × Part) × Rect)) (start : Acc),
      (∀ pair ∈ pairs, ∀ title ∈ pair.1.2.titles,
        fits (pair.1.1.getD title.1 0, shiftRect pair.2.x pair.2.y title.2)) →
      (∀ title ∈ start.titles, fits title) →
      ∀ title ∈ (pairs.foldl packStep start).titles, fits title := by
    intro pairs
    induction pairs with
    | nil => intro start _ hstart; exact hstart
    | cons pair pairs ih =>
      intro start hpairs hstart
      rw [List.foldl_cons]
      apply ih _ (fun p hp => hpairs p (List.mem_cons_of_mem _ hp))
      intro title htitle
      change title ∈ start.titles ++ pair.1.2.titles.map
        (fun raw => (pair.1.1.getD raw.1 0, shiftRect pair.2.x pair.2.y raw.2)) at htitle
      rcases List.mem_append.mp htitle with hold | hnew
      · exact hstart title hold
      · obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hnew
        exact hpairs pair List.mem_cons_self raw hraw
  change ∀ title ∈ execution.packedAcc.titles, fits title
  have hpack := execution.packed_eq
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  rw [inlineFold_eq_packStep] at hpack
  have he := Except.ok.inj hpack
  rw [← he]
  apply fold
  · intro pair hpair title htitle
    have hfit := execution.component_title_caption_fit (List.of_mem_zip hpair).1 htitle
    exact hfit
  · intro title htitle
    simp at htitle

theorem SceneExecution.title_rect_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ title ∈ execution.packedAcc.titles,
      let lines := execution.lines.getD title.1 []
      let width := lines.foldl (fun value line => max value line.width) 0
      let height := (max 1 lines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      Size.containsCellRect res.scene.canvas
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            { title.2 with w := size.w, h := size.h })) = true := by
  intro title htitle
  let lines := execution.lines.getD title.1 []
  let width := lines.foldl (fun value line => max value line.width) 0
  let height := (max 1 lines.length : Int) * execution.params.lineH
  let size := match o.direction with
    | .LR | .RL => Size.mk height width
    | .TB | .BT => Size.mk width height
  have hfit := execution.packed_title_caption_fit title htitle
  change 0 ≤ size.w ∧ 0 ≤ size.h ∧ size.w ≤ title.2.w ∧ size.h ≤ title.2.h at hfit
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hstored := hacc.titles_bounded title htitle
  have hrect :
      0 ≤ title.2.x ∧ title.2.x + size.w ≤ execution.packedAcc.canvasW ∧
      0 ≤ title.2.y ∧ title.2.y + size.h ≤ execution.packedAcc.canvasH ∧
      0 ≤ size.w ∧ 0 ≤ size.h :=
    ⟨hstored.1, by omega, hstored.2.2.1, by omega, hfit.1, hfit.2.1⟩
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  rw [execution.scene_eq]
  exact orient_shiftRect_containsCellRect o.direction execution.packedAcc.canvasW
    execution.packedAcc.canvasH execution.params.canvasMargin
    { title.2 with w := size.w, h := size.h } hrect (by omega)

theorem SceneExecution.scene_titles_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    ∀ title ∈ execution.packedAcc.titles.filterMap (fun stored => do
      let box ← inp.boxes[stored.1]?
      let lines := execution.lines.getD stored.1 []
      let width := lines.foldl (fun value line => max value line.width) 0
      let height := (max 1 lines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          { stored.2 with w := size.w, h := size.h }))),
      Size.containsCellRect res.scene.canvas title.2 = true := by
  intro title htitle
  obtain ⟨stored, hstored, hproduced⟩ := List.mem_filterMap.mp htitle
  obtain ⟨box, _, hproduced⟩ := Option.bind_eq_some_iff.mp hproduced
  have he := Option.some.inj hproduced
  subst title
  exact execution.title_rect_bounded stored hstored

theorem SceneExecution.unmeasured_title_label_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index ownerIndex : Nat} {source : ModelLabel} {title : String × Rect}
    (hsource : inp.labels[index]? = some source)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = none)
    (hexclusive : inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false)
    (howner : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) =
      some ownerIndex)
    (htitle : ((execution.packedAcc.titles.filterMap (fun stored => do
      let box ← inp.boxes[stored.1]?
      let lines := execution.lines.getD stored.1 []
      let width := lines.foldl (fun value line => max value line.width) 0
      let height := (max 1 lines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      let rect := { stored.2 with w := size.w, h := size.h }
      pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH rect)))).find?
        (fun candidate => candidate.1 == source.owner)) = some title) :
    ∃ placed ∈ res.scene.labels, placed.id = source.id ∧ placed.owner = source.owner ∧
      Size.containsCellRect res.scene.canvas placed.rect = true := by
  have hbound := execution.scene_titles_bounded title (List.mem_of_find?_eq_some htitle)
  let placed : SceneLabel := {
    id := source.id, owner := source.owner, text := source.text, rect := title.2
    lines := (execution.lines.getD ownerIndex []).map fun line => String.ofList line.text }
  have hemitted : placed ∈
      (sceneOf execution.params inp o execution.lines execution.packedAcc execution.measured).labels := by
    unfold sceneOf
    apply List.mem_filterMap.mpr
    refine ⟨(source, index), List.mem_zipIdx_iff_getElem?.mpr hsource, ?_⟩
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte, hmeasured, howner]
    cases hd : o.direction <;>
      simp only [hd, Option.bind_eq_bind, Pure.pure] at htitle ⊢ <;>
      simp only [htitle, Option.map_some, Option.getD_some] <;>
      rfl
  rw [execution.scene_eq] at hbound ⊢
  exact ⟨placed, hemitted, rfl, rfl, hbound⟩

theorem ownedTextRect_containsCellRect (P : Params) (canvas : Size)
    (box : Box) (lines : List Measure.Line)
    (hr : Size.containsCellRect canvas box.rect = true)
    (hlh : 0 ≤ P.lineH)
    (hnode : (lines.length : Int) * P.lineH ≤ box.rect.h)
    (hgroup : box.role = "group" →
      0 ≤ P.clusterPad ∧ 2 * P.clusterPad ≤ box.rect.w ∧
        P.clusterPad + (max 1 lines.length : Int) * P.lineH ≤ box.rect.h) :
    Size.containsCellRect canvas (ownedTextRect P box lines) = true := by
  unfold ownedTextRect
  split
  · rename_i hg
    have hp := hgroup (by simpa using hg)
    exact title_rect_containsCellRect canvas P box.rect lines hr hlh hp.1 hp.2.1 hp.2.2
  · have hdiff : 0 ≤ box.rect.h - (lines.length : Int) * P.lineH := by omega
    have hdivision :
        Int.fdiv (box.rect.h - (lines.length : Int) * P.lineH) 2 =
          Int.tdiv (box.rect.h - (lines.length : Int) * P.lineH) 2 := by
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hdiff
      rw [hn]
      rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2),
        Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg n)]
    dsimp only
    rw [hdivision]
    exact node_text_rect_containsCellRect canvas box.rect lines.length P.lineH hr hlh hnode

theorem SceneExecution.unmeasured_fallback_label_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {index ownerIndex : Nat} {source : ModelLabel}
    (hsource : inp.labels[index]? = some source)
    (hmeasured : execution.measured.find? (fun label => label.index == index) = none)
    (hexclusive : inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false)
    (howner : inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) =
      some ownerIndex)
    (htitle : ((execution.packedAcc.titles.filterMap fun title => do
      let box ← inp.boxes[title.1]?
      let textLines := execution.lines.getD title.1 []
      let width := textLines.foldl (fun value line => max value line.width) 0
      let height := (max 1 textLines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      let rect := { title.2 with w := size.w, h := size.h }
      pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH rect))).find?
          (fun title => title.1 == source.owner)) = none)
    (hfallback : Size.containsCellRect res.scene.canvas
      (ownedTextRect execution.params
        ((inp.boxes.zipIdx.map fun q =>
          Box.mk q.1.id q.1.role.id
            (shiftRect execution.params.canvasMargin execution.params.canvasMargin
              (orientRect o.direction execution.packedAcc.canvasH
                (execution.packedAcc.rects.getD q.2 default)))
            q.1.parent q.1.exclusive).getD ownerIndex ⟨"", "", default, "", false⟩)
        (execution.lines.getD ownerIndex [])) = true) :
    ∃ placed ∈ res.scene.labels, placed.id = source.id ∧ placed.owner = source.owner ∧
      Size.containsCellRect res.scene.canvas placed.rect = true := by
  let placed : SceneLabel := {
    id := source.id, owner := source.owner, text := source.text
    rect := ownedTextRect execution.params
      ((inp.boxes.zipIdx.map fun q =>
        Box.mk q.1.id q.1.role.id
          (shiftRect execution.params.canvasMargin execution.params.canvasMargin
            (orientRect o.direction execution.packedAcc.canvasH
              (execution.packedAcc.rects.getD q.2 default)))
          q.1.parent q.1.exclusive).getD ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex [])
    lines := (execution.lines.getD ownerIndex []).map fun line => String.ofList line.text }
  have hemitted : placed ∈
      (sceneOf execution.params inp o execution.lines execution.packedAcc execution.measured).labels := by
    unfold sceneOf
    apply List.mem_filterMap.mpr
    refine ⟨(source, index), List.mem_zipIdx_iff_getElem?.mpr hsource, ?_⟩
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte, hmeasured, howner]
    cases hd : o.direction <;>
      simp only [hd, Option.bind_eq_bind, Pure.pure] at htitle ⊢ <;>
      simp only [htitle, Option.map_none, Option.getD_none, placed, hd]
  rw [execution.scene_eq] at hfallback ⊢
  exact ⟨placed, hemitted, rfl, rfl, hfallback⟩

theorem FrameOrigin.caption_cellBounds {o : Options} {id : String} {size : Size}
    (origin : FrameOrigin o id size) (canvas : Size) (rect : Rect)
    (hr : Size.containsCellRect canvas rect = true)
    (hw : rect.w = size.w) (hh : rect.h = size.h) :
    Size.containsCellRect canvas
      (ownedTextRect origin.params
        ⟨id, "group", rect, "", false⟩ origin.titleLines) = true := by
  have fit := origin.fallback_fit
  have signs := checkedParams_sizing_nonneg origin.checked
  have hheight :
      (origin.titleLines.length : Int) * origin.params.lineH ≤
        (max 1 origin.titleLines.length : Int) * origin.params.lineH :=
    Int.mul_le_mul_of_nonneg_right (by omega) signs.1
  apply ownedTextRect_containsCellRect origin.params canvas _ origin.titleLines hr signs.1
  · dsimp only
    rw [hh]
    omega
  · intro _
    dsimp only
    exact ⟨signs.2.1, hw.symm ▸ fit.1, hh.symm ▸ fit.2⟩

theorem SceneExecution.owner_rect_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (index : Nat) :
    Size.containsCellRect res.scene.canvas
      (shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (execution.packedAcc.rects.getD index default))) = true := by
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hrect :
      let rect := execution.packedAcc.rects.getD index default
      0 ≤ rect.x ∧ rect.x + rect.w ≤ execution.packedAcc.canvasW ∧
      0 ≤ rect.y ∧ rect.y + rect.h ≤ execution.packedAcc.canvasH ∧
      0 ≤ rect.w ∧ 0 ≤ rect.h := by
    cases hget : execution.packedAcc.rects[index]? with
    | none =>
      rw [Array.getD_eq_getD_getElem?, hget]
      change 0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasW ∧
        0 ≤ (0 : Int) ∧ 0 ≤ execution.packedAcc.canvasH ∧
        0 ≤ (0 : Int) ∧ 0 ≤ (0 : Int)
      exact ⟨by omega, hacc.canvas_w_nonneg, by omega, hacc.canvas_h_nonneg,
        by omega, by omega⟩
    | some stored =>
      rw [Array.getD_eq_getD_getElem?, hget]
      exact hacc.rects_bounded index stored hget
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  rw [execution.scene_eq]
  exact orient_shiftRect_containsCellRect o.direction execution.packedAcc.canvasW
    execution.packedAcc.canvasH execution.params.canvasMargin _ hrect (by omega)

theorem FrameOrigin.box_caption_cellBounds {o : Options} {id : String} {size : Size}
    (origin : FrameOrigin o id size) (canvas : Size) (box : Box)
    (hr : Size.containsCellRect canvas box.rect = true)
    (hrole : box.role = "group") (hw : box.rect.w = size.w)
    (hh : box.rect.h = size.h) :
    Size.containsCellRect canvas
      (ownedTextRect origin.params box origin.titleLines) = true := by
  have hbound := origin.caption_cellBounds canvas box.rect hr hw hh
  simpa only [ownedTextRect, hrole, beq_self_eq_true, ↓reduceIte] using hbound

theorem SceneExecution.unmeasured_rect_bounded
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) (owner : String) (fallback : Rect)
    (hfallback : Size.containsCellRect res.scene.canvas fallback = true) :
    let titles := execution.packedAcc.titles.filterMap fun stored => do
      let box ← inp.boxes[stored.1]?
      let textLines := execution.lines.getD stored.1 []
      let width := textLines.foldl (fun value line => max value line.width) 0
      let height := (max 1 textLines.length : Int) * execution.params.lineH
      let size := match o.direction with
        | .LR | .RL => Size.mk height width
        | .TB | .BT => Size.mk width height
      let rect := { stored.2 with w := size.w, h := size.h }
      pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH rect))
    Size.containsCellRect res.scene.canvas
      (((titles.find? (fun title => title.1 == owner)).map (·.2)).getD fallback) = true := by
  let titles := execution.packedAcc.titles.filterMap fun stored => do
    let box ← inp.boxes[stored.1]?
    let textLines := execution.lines.getD stored.1 []
    let width := textLines.foldl (fun value line => max value line.width) 0
    let height := (max 1 textLines.length : Int) * execution.params.lineH
    let size := match o.direction with
      | .LR | .RL => Size.mk height width
      | .TB | .BT => Size.mk width height
    let rect := { stored.2 with w := size.w, h := size.h }
    pure (box.id, shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH rect))
  change Size.containsCellRect res.scene.canvas
    (((titles.find? (fun title => title.1 == owner)).map (·.2)).getD fallback) = true
  cases hfind : titles.find? (fun title => title.1 == owner) with
  | none => exact hfallback
  | some title =>
    exact execution.scene_titles_bounded title (List.mem_of_find?_eq_some hfind)

theorem SceneExecution.canvas_nonneg
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    0 ≤ res.scene.canvas.w ∧ 0 ≤ res.scene.canvas.h := by
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  have hw := hacc.canvas_w_nonneg
  have hh := hacc.canvas_h_nonneg
  rw [execution.scene_eq]
  unfold sceneOf orientCanvas
  dsimp only
  cases o.direction <;> dsimp only <;> constructor <;> omega

theorem SceneExecution.primitiveBounds_of_box_sizing_labels
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hsizing : ∀ q ∈ res.scene.boxes.zipIdx,
      (q.1.role == "node" →
        ((execution.lines.getD q.2 []).length : Int) * execution.params.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" →
        2 * execution.params.clusterPad ≤ q.1.rect.w ∧
        execution.params.clusterPad +
          (max 1 (execution.lines.getD q.2 []).length : Int) *
            execution.params.lineH ≤ q.1.rect.h))
    (hlabels : ∀ label ∈ res.scene.labels,
      Size.containsCellRect res.scene.canvas label.rect = true) :
    res.scene.PrimitiveBounds := by
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  have signs := execution.parameter_signs
  have hboxes := sceneOf_boxes_bounded execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)
  have hroutes := sceneOf_routes_bounded execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc hmargin
  have htitles := execution.scene_titles_bounded
  rw [execution.scene_eq] at hsizing hlabels htitles ⊢
  apply sceneOf_primitiveBounds
  · exact (execution.scene_eq ▸ execution.canvas_nonneg).1
  · exact (execution.scene_eq ▸ execution.canvas_nonneg).2
  · exact signs.1
  · exact signs.2.1
  · intro q hq
    exact ⟨hboxes q hq, (hsizing q hq).1, (hsizing q hq).2⟩
  · exact hroutes
  · exact hlabels
  · exact htitles

theorem frameRect_plain_dims (P : Params) (cg : Graph) (run : Run)
    (i : Nat) (node : ProperNode)
    (hplain : (cg.nodes.getD i default).border ≠ -2)
    (hnode : run.proper.nodes[i]? = some node) :
    (frameRect P cg run i).w = node.node.w ∧
      (frameRect P cg run i).h = node.node.h := by
  have hget : run.proper.nodes.getD i default = node := by
    simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  unfold frameRect
  rw [ite_eq_left (by simpa using hplain)]
  change (run.proper.nodes.getD i default).node.w = node.node.w ∧
    (run.proper.nodes.getD i default).node.h = node.node.h
  exact ⟨congrArg (fun n : ProperNode => n.node.w) hget,
    congrArg (fun n : ProperNode => n.node.h) hget⟩

theorem SceneExecution.component_plain_frame_dims
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ index run loops area,
      componentRun execution.params
        (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } ∧
      ∀ (i : Nat) (node : ProperNode),
        run.coordinateProper.nodes[i]? = some node →
        node.node.border = 0 →
        ((componentCandidate execution.graph part.1 index).nodes.getD i default).border ≠ -2 →
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run i).w = node.node.w ∧
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run i).h = node.node.h := by
  obtain ⟨index, run, loops, area, hrun, hpart, hdims⟩ :=
    execution.component_plain_node_dims hpart
  refine ⟨index, run, loops, area, hrun, hpart, ?_⟩
  intro i node hnode hborder hplain
  exact frameRect_plain_dims execution.params _ run i node hplain
    (hdims i node hnode hborder)

theorem indexed_rect_dimensions_preserved
    (expected : Nat → Size) (dx dy : Int) (entries : List (Nat × Rect))
    (a : Array Rect)
    (hinit : ∀ i rect, a[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h)
    (hwrites : ∀ entry ∈ entries,
      entry.2.w = (expected entry.1).w ∧ entry.2.h = (expected entry.1).h) :
    ∀ i rect,
      (entries.foldl (fun out entry =>
        if entry.1 < out.size then
          out.set! entry.1 (shiftRect dx dy entry.2) else out) a)[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h := by
  induction entries generalizing a with
  | nil => exact hinit
  | cons entry entries ih =>
    rw [List.foldl_cons]
    apply ih
    · intro i rect hget
      split at hget
      · rename_i hin
        by_cases heq : entry.1 = i
        · subst i
          rw [getElem?_set!_self hin] at hget
          have hr := Option.some.inj hget
          rw [← hr]
          exact hwrites entry List.mem_cons_self
        · rw [getElem?_set!_ne heq] at hget
          exact hinit i rect hget
      · exact hinit i rect hget
    · intro written hmem
      exact hwrites written (List.mem_cons_of_mem entry hmem)

theorem zipped_rect_dimensions (expected : Nat → Size)
    (keys : List Nat) (rects : List Rect)
    (hdims : rects.map (fun rect => (rect.w, rect.h)) =
      keys.map (fun key => ((expected key).w, (expected key).h))) :
    ∀ entry ∈ keys.zip rects,
      entry.2.w = (expected entry.1).w ∧
        entry.2.h = (expected entry.1).h := by
  induction keys generalizing rects with
  | nil =>
    intro entry hentry
    simp at hentry
  | cons key keys ih =>
    cases rects with
    | nil =>
      simp at hdims
    | cons rect rects =>
      have hcons := List.cons.inj hdims
      have hhead := Prod.mk.inj hcons.1
      intro entry hentry
      simp only [List.zip_cons_cons, List.mem_cons] at hentry
      rcases hentry with rfl | hentry
      · exact hhead
      · exact ih rects hcons.2 entry hentry

theorem layoutFamily_base_sceneExecution
    {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutFamily inp o = .ok res)
    (hflat : inp.boxes.find? (fun box =>
      Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none) :
    Nonempty (SceneExecution inp o res) :=
  layout_sceneExecution (Layered.layoutFamily_success_base h hflat)

theorem genuineFrames_empty (o : Options) : GenuineFrames o [] := by
  intro entry hentry
  cases hentry

theorem genuineFrames_initial {o : Options} {inp : Input}
    (hempty : inp.fixedSizes = []) : GenuineFrames o inp.fixedSizes := by
  rw [hempty]
  exact genuineFrames_empty o

theorem genuineFrames_parent {o : Options} {inp : Input}
    (keep : ModelBox → Bool) {id : String} {size : Size}
    (hframes : GenuineFrames o inp.fixedSizes)
    (origin : FrameOrigin o id size) :
    GenuineFrames o ((selectInput inp keep).fixedSizes ++ [(id, size)]) :=
  genuineFrames_append (genuineFrames_selectInput keep "" hframes) origin

theorem SceneExecution.component_rect_dimensions
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ index run loops area,
      componentRun execution.params
        (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2 = { placeComponent execution.params
        (componentCandidate execution.graph part.1 index) run 0 execution.measured loops
        with area := area } ∧
      part.2.rects.map (fun rect => (rect.w, rect.h)) =
        (List.range (componentCandidate execution.graph part.1 index).nodes.length).map
          (fun i =>
            ((frameRect execution.params
                (componentCandidate execution.graph part.1 index) run i).w,
              (frameRect execution.params
                (componentCandidate execution.graph part.1 index) run i).h)) := by
  obtain ⟨index, run, loops, area, hrun, hplace, _⟩ :=
    execution.component_plain_node_dims hpart
  refine ⟨index, run, loops, area, hrun, hplace, ?_⟩
  rw [hplace]
  exact Layered.placeComponent_rect_dimensions execution.params _ run 0
    execution.measured loops

theorem packAcc_rect_dimensions
    {P : Params} {o : Options} {acc out : Acc}
    (expected : Nat → Size)
    (hpack : packAcc P o acc = .ok out)
    (hinit : ∀ i rect, acc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h)
    (hparts : ∀ part ∈ acc.parts, ∀ entry ∈ part.1.zip part.2.rects,
      entry.2.w = (expected entry.1).w ∧
        entry.2.h = (expected entry.1).h) :
    ∀ i rect, out.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h := by
  unfold packAcc at hpack
  obtain ⟨packed, _, hpack⟩ := bind_ok hpack
  have hout := Except.ok.inj hpack
  subst out
  have preserve : ∀ (pairs : List ((List Nat × Part) × Rect)) (initial : Acc),
      (∀ pair ∈ pairs, pair.1 ∈ acc.parts) →
      (∀ i rect, initial.rects[i]? = some rect →
        rect.w = (expected i).w ∧ rect.h = (expected i).h) →
      ∀ i rect,
        (pairs.foldl (fun state pair =>
          { state with
            rects := (pair.1.1.zip pair.1.2.rects).foldl
              (fun a entry => if entry.1 < a.size then
                a.set! entry.1 (shiftRect pair.2.x pair.2.y entry.2) else a) state.rects
            routes := pair.1.2.routes.foldl
              (fun a entry => a.set! entry.1
                (entry.2.map (shiftPoint pair.2.x pair.2.y))) state.routes
            labels := pair.1.2.labels.foldl
              (fun a entry => a.set! entry.1
                (shiftRect pair.2.x pair.2.y entry.2)) state.labels
            titles := state.titles ++ pair.1.2.titles.map
              (fun entry => (pair.1.1.getD entry.1 0,
                shiftRect pair.2.x pair.2.y entry.2)) }) initial).rects[i]? = some rect →
        rect.w = (expected i).w ∧ rect.h = (expected i).h := by
    intro pairs
    induction pairs with
    | nil =>
      intro initial _ hi
      exact hi
    | cons pair pairs ih =>
      intro initial hp hi
      rw [List.foldl_cons]
      apply ih
      · intro other ho
        exact hp other (List.mem_cons_of_mem pair ho)
      · exact indexed_rect_dimensions_preserved expected pair.2.x pair.2.y
          (pair.1.1.zip pair.1.2.rects) initial.rects hi
          (hparts pair.1 (hp pair List.mem_cons_self))
  apply preserve
  · intro pair hp
    exact (List.of_mem_zip hp).1
  · exact hinit

theorem SceneExecution.packed_rect_dimensions
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (expected : Nat → Size)
    (hinit : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h)
    (hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
        entry.2.w = (expected entry.1).w ∧
          entry.2.h = (expected entry.1).h) :
    ∀ i rect, execution.packedAcc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h :=
  packAcc_rect_dimensions expected execution.packed_eq hinit hparts

theorem SceneExecution.packed_rect_dimensions_of_parts
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (expected : Nat → Size)
    (hinit : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h)
    (hparts : ∀ part ∈ execution.componentsAcc.parts,
      part.2.rects.map (fun rect => (rect.w, rect.h)) =
        part.1.map (fun key => ((expected key).w, (expected key).h))) :
    ∀ i rect, execution.packedAcc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h := by
  apply execution.packed_rect_dimensions expected hinit
  intro part hpart
  exact zipped_rect_dimensions expected part.1 part.2.rects (hparts part hpart)

theorem SceneExecution.owner_rect_dimensions
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (expected : Nat → Size)
    (hinit : ∀ i rect, execution.componentsAcc.rects[i]? = some rect →
      rect.w = (expected i).w ∧ rect.h = (expected i).h)
    (hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
        entry.2.w = (expected entry.1).w ∧
          entry.2.h = (expected entry.1).h)
    {index : Nat} {rect : Rect}
    (hget : execution.packedAcc.rects[index]? = some rect) :
    let placed := shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH rect)
    placed.w = (orientCanvas o.direction (expected index).w (expected index).h).w ∧
      placed.h = (orientCanvas o.direction (expected index).w (expected index).h).h := by
  have hdims := execution.packed_rect_dimensions expected hinit hparts index rect hget
  dsimp only
  unfold shiftRect orientRect orientCanvas
  cases o.direction <;> dsimp only <;> constructor <;> omega

theorem SceneExecution.component_rect_dimension_map
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ index run,
      componentRun execution.params
        (componentCandidate execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok run ∧
      part.2.rects.map (fun rect => (rect.w, rect.h)) =
        (List.range (componentCandidate execution.graph part.1 index).nodes.length).map
          (fun i =>
            ((frameRect execution.params
              (componentCandidate execution.graph part.1 index) run i).w,
             (frameRect execution.params
              (componentCandidate execution.graph part.1 index) run i).h)) := by
  obtain ⟨index, run, loops, area, hrun, _, hplace, _, _, _, _⟩ :=
    execution.actual_component_sizing hpart
  refine ⟨index, run, hrun, ?_⟩
  rw [hplace]
  exact Layered.placeComponent_rect_dimensions execution.params
    (componentCandidate execution.graph part.1 index) run 0 execution.measured loops

theorem genuineFrames_used_caption_fit
    {o : Options} {inp : Input} {id : String} {entry : String × Size}
    (h : GenuineFrames o inp.fixedSizes)
    (used : inp.fixedSizes.find? (fun fixed => fixed.1 == id) = some entry) :
    ∃ origin : FrameOrigin o entry.1 entry.2,
      2 * origin.params.clusterPad ≤ entry.2.w ∧
      origin.params.clusterPad +
        (max 1 origin.titleLines.length : Int) * origin.params.lineH ≤ entry.2.h := by
  obtain ⟨origin⟩ := genuineFrames_used h used
  exact ⟨origin, origin.fallback_fit⟩

theorem SceneExecution.label_source
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {label : SceneLabel}
    (hl : label ∈ res.scene.labels) :
    ∃ (source : ModelLabel) (index : Nat),
      inp.labels[index]? = some source ∧
      inp.boxes.any (fun box => box.id == source.owner && box.exclusive) = false ∧
      label.id = source.id ∧ label.owner = source.owner ∧
      ((∃ measured,
          execution.measured.find? (fun item => item.index == index) = some measured) ∨
        (execution.measured.find? (fun item => item.index == index) = none ∧
          ∃ ownerIndex, inp.boxes.findIdx?
            (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex)) := by
  rw [execution.scene_eq] at hl
  obtain ⟨q, hq, hemitted⟩ := List.mem_filterMap.mp hl
  have hsource := List.mem_zipIdx_iff_getElem?.mp hq
  cases hexclusive : inp.boxes.any
      (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst label
      exact ⟨q.1, q.2, hsource, hexclusive, rfl, rfl, Or.inl ⟨measured, hm⟩⟩
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst label
        exact ⟨q.1, q.2, hsource, hexclusive, rfl, rfl,
          Or.inr ⟨hm, ownerIndex, ho⟩⟩

theorem SceneExecution.boxes_eq_map
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) :
    res.scene.boxes = (inp.boxes.zipIdx.map fun q =>
      Box.mk q.1.id q.1.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD q.2 default)))
        q.1.parent q.1.exclusive) :=
  congrArg (fun s : Scene => s.boxes) execution.scene_eq

theorem SceneExecution.box_role_cases
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res) {b : Box}
    (hb : b ∈ res.scene.boxes) : b.role = "node" ∨ b.role = "group" := by
  rw [execution.boxes_eq_map] at hb
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hb
  subst b
  cases q.1.role
  · exact Or.inl (by simp only [BoxRole.id])
  · exact Or.inr (by simp only [BoxRole.id])

theorem SceneExecution.fallback_of_sizing
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hsizing : ∀ q ∈ res.scene.boxes.zipIdx,
      (q.1.role == "node" →
        ((execution.lines.getD q.2 []).length : Int) * execution.params.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" →
        2 * execution.params.clusterPad ≤ q.1.rect.w ∧
        execution.params.clusterPad +
          (max 1 (execution.lines.getD q.2 []).length : Int) *
            execution.params.lineH ≤ q.1.rect.h))
    {index : Nat} (hi : index < res.scene.boxes.length) :
    Size.containsCellRect res.scene.canvas
      (ownedTextRect execution.params
        (res.scene.boxes.getD index ⟨"", "", default, "", false⟩)
        (execution.lines.getD index [])) = true := by
  have hacc := execution.packedAcc_bounded execution.components_parts_bounded
  have hmargin := checkedParams_canvasMargin_ge_one execution.checked
  have signs := execution.parameter_signs
  have hboxes := sceneOf_boxes_bounded execution.params inp o execution.lines
    execution.packedAcc execution.measured hacc (by omega)
  have hget : res.scene.boxes[index]? = some res.scene.boxes[index] :=
    List.getElem?_eq_getElem hi
  have hmem : (res.scene.boxes[index], index) ∈ res.scene.boxes.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hget
  have hgetD : res.scene.boxes.getD index ⟨"", "", default, "", false⟩ =
      res.scene.boxes[index] := by
    simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]
  have hr : Size.containsCellRect res.scene.canvas res.scene.boxes[index].rect = true := by
    have hb := hboxes (res.scene.boxes[index], index) (by rw [← execution.scene_eq]; exact hmem)
    rw [← execution.scene_eq] at hb
    exact hb
  have hheight : ((execution.lines.getD index []).length : Int) * execution.params.lineH ≤
      (max 1 (execution.lines.getD index []).length : Int) * execution.params.lineH :=
    Int.mul_le_mul_of_nonneg_right (by omega) signs.1
  have key : ∀ b : Box, (b, index) ∈ res.scene.boxes.zipIdx →
      b.role = "node" ∨ b.role = "group" →
      Size.containsCellRect res.scene.canvas b.rect = true →
      Size.containsCellRect res.scene.canvas
        (ownedTextRect execution.params b (execution.lines.getD index [])) = true := by
    intro b hmb hrole hrb
    rcases hrole with hrole | hrole
    · have hn : ((execution.lines.getD index []).length : Int) * execution.params.lineH ≤
          b.rect.h := (hsizing (b, index) hmb).1 (by simp [hrole])
      apply ownedTextRect_containsCellRect execution.params res.scene.canvas _ _ hrb signs.1 hn
      intro hg
      rw [hrole] at hg
      exact absurd hg (by decide)
    · have hg : 2 * execution.params.clusterPad ≤ b.rect.w ∧
          execution.params.clusterPad +
            (max 1 (execution.lines.getD index []).length : Int) *
              execution.params.lineH ≤ b.rect.h :=
        (hsizing (b, index) hmb).2 (by simp [hrole])
      apply ownedTextRect_containsCellRect execution.params res.scene.canvas _ _ hrb signs.1
      · have hclu := signs.2.1
        omega
      · intro _
        exact ⟨signs.2.1, hg.1, hg.2⟩
  rw [hgetD]
  exact key _ hmem (execution.box_role_cases (List.getElem_mem hi)) hr

theorem SceneExecution.labels_bounded_of_ownedTextRects
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hfallback : ∀ index : Nat, index < res.scene.boxes.length →
      Size.containsCellRect res.scene.canvas
        (ownedTextRect execution.params
          (res.scene.boxes.getD index ⟨"", "", default, "", false⟩)
          (execution.lines.getD index [])) = true) :
    ∀ label ∈ res.scene.labels,
      Size.containsCellRect res.scene.canvas label.rect = true := by
  intro label hl
  have hbox := execution.boxes_eq_map
  rw [execution.scene_eq] at hl
  obtain ⟨q, _, hemitted⟩ := List.mem_filterMap.mp hl
  cases hexclusive : inp.boxes.any
      (fun box => box.id == q.1.owner && box.exclusive) with
  | true => simp only [hexclusive, ↓reduceIte] at hemitted; cases hemitted
  | false =>
    simp only [hexclusive, Bool.false_eq_true, ↓reduceIte] at hemitted
    cases hm : execution.measured.find? (fun item => item.index == q.2) with
    | some measured =>
      simp only [hm, Option.some.injEq] at hemitted
      subst label
      exact execution.measured_rect_bounded measured.index
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx?
          (fun box => box.id == q.1.owner && !box.exclusive) with
      | none => simp only [ho] at hemitted; cases hemitted
      | some ownerIndex =>
        simp only [ho, Option.some.injEq] at hemitted
        subst label
        have hlt := (List.findIdx?_eq_some_iff_getElem.mp ho).1
        have hlen : ownerIndex < res.scene.boxes.length := by
          rw [hbox]
          simp only [List.length_map, List.length_zipIdx]
          exact hlt
        have h1 := hfallback ownerIndex hlen
        rw [hbox] at h1
        exact execution.unmeasured_rect_bounded q.1.owner _ h1

theorem SceneExecution.primitiveBounds_of_box_sizing
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hsizing : ∀ q ∈ res.scene.boxes.zipIdx,
      (q.1.role == "node" →
        ((execution.lines.getD q.2 []).length : Int) * execution.params.lineH ≤ q.1.rect.h) ∧
      (q.1.role == "group" →
        2 * execution.params.clusterPad ≤ q.1.rect.w ∧
        execution.params.clusterPad +
          (max 1 (execution.lines.getD q.2 []).length : Int) *
            execution.params.lineH ≤ q.1.rect.h)) :
    res.scene.PrimitiveBounds :=
  execution.primitiveBounds_of_box_sizing_labels hsizing
    (execution.labels_bounded_of_ownedTextRects
      (fun _ hi => execution.fallback_of_sizing hsizing hi))

end PipelineImpl
end Layered
end Elegant
