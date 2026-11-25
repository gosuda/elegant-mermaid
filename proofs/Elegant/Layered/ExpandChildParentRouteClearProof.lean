import Elegant.Layered.ExpandChildParentFrameProof
import Elegant.Layered.ExpandChildParentRouteRunProof

set_option autoImplicit false

open Elegant.Layered.Compound

namespace Elegant.Layered.PipelineImpl

/-! # Parent route clearance at the group frame, split residuals

For one executed `expandChild` call, the parent-scene fact
`ExpandChildParentRouteClear` (see `ExpandChildParentFrameProof.lean`) is
the conjunction of:

* (a) every out-of-scope parent route misses the frame rectangle;
* (b) every attached parent route misses every rectangle strictly inside
  the frame.

The frame is a non-exclusive group-role box of fixed size, so the parent
`C6` does not apply to it. Clause (a) at the frame rectangle is the exact
router-level content: in the parent sub-input the group is a fixed-size
leaf, hence a real node of the layered graph, and the run-level avoidance
(`componentRun_route_avoids_nodes`, stated by `IsReal` graph node rather
than by the dump `exclusive` flag) routes non-endpoint edges around its
node rect; only the run-to-scene bridge (`RouteScopeBridge` /
`FlatC6ChainCase`) is still open. Clause (b) is endpoint attachment
(`C5` boundary port plus outward-facing stub geometry), likewise open.

This module splits the combined residual into its two strictly simpler
parts, proves the out-of-scope inner miss from the frame-level part by
`hitsRect` monotonicity, and restates the consumer with the split
hypotheses. Tested on the probe copy
`proofs/wip/Probe/ParentFrameRouteProbe.lean`: `cross` (1 out-of-scope
`L → R` crosser, 2 attached `L → G` / `R → G`), `crossLR`, `sandwich`
(spanning `L → R` plus attached), `groupEnd` (attached `a → G`), and
`nest3` report no `A-VIOL`, `A-INNER-VIOL`, or `B-VIOL` over frame,
shrink-by-1/3/5, and centered-half strictly-inside rects.
-/

/-! ## `hitsRect` monotonicity through strict containment (copies)

Copies of the private lemmas in `ExpandChildParentFrameProof.lean`,
renamed, used for the out-of-scope transport below. -/

/-- A corner-minimum bound: the `minCorner` of a rectangle lies below the
corner product at any point of its closed extent. -/
private theorem routeClear_minCorner_le_dot {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    Polyline.minCorner nx ny outer ≤ nx * x + ny * y := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * outer.x + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
    have e1 : nx * outer.x ≤ nx * x := Int.mul_le_mul_of_nonneg_left hx1 hnx
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * outer.y := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * outer.y ≤ ny * y := Int.mul_le_mul_of_nonneg_left hy1 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : Polyline.minCorner nx ny outer ≤
        nx * (outer.x + outer.w) + ny * (outer.y + outer.h) := by
      simp only [Polyline.minCorner, Polyline.dot]
      exact Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
    have e1 : nx * (outer.x + outer.w) ≤ nx * x :=
      hnonpos hx2 (Int.le_of_lt hnx')
    have e2 : ny * (outer.y + outer.h) ≤ ny * y :=
      hnonpos hy2 (Int.le_of_lt hny')
    omega

private theorem routeClear_dot_le_maxCorner {nx ny : Int} {outer : Rect} {x y : Int}
    (hx1 : outer.x ≤ x) (hx2 : x ≤ outer.x + outer.w)
    (hy1 : outer.y ≤ y) (hy2 : y ≤ outer.y + outer.h) :
    nx * x + ny * y ≤ Polyline.maxCorner nx ny outer := by
  have hnonpos : ∀ {a b c : Int}, b ≤ c → a ≤ 0 → a * c ≤ a * b := by
    intro a b c h ha
    simpa [Int.mul_comm] using Int.mul_le_mul_of_nonpos_right h ha
  by_cases hnx : 0 ≤ nx <;> by_cases hny : 0 ≤ ny
  · have hle : nx * (outer.x + outer.w) + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hny' : ny < 0 := by omega
    have hle : nx * (outer.x + outer.w) + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * (outer.x + outer.w) :=
      Int.mul_le_mul_of_nonneg_left hx2 hnx
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega
  · have hnx' : nx < 0 := by omega
    have hle : nx * outer.x + ny * (outer.y + outer.h) ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * (outer.y + outer.h) :=
      Int.mul_le_mul_of_nonneg_left hy2 hny
    omega
  · have hnx' : nx < 0 := by omega
    have hny' : ny < 0 := by omega
    have hle : nx * outer.x + ny * outer.y ≤
        Polyline.maxCorner nx ny outer := by
      simp only [Polyline.maxCorner, Polyline.dot]
      exact Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
    have e1 : nx * x ≤ nx * outer.x :=
      hnonpos hx1 (Int.le_of_lt hnx')
    have e2 : ny * y ≤ ny * outer.y :=
      hnonpos hy1 (Int.le_of_lt hny')
    omega

/-- A segment that misses an outer rectangle misses every strictly
inner one: axis separations transport by the gap, diagonal separations by
the corner bounds. -/
private theorem routeClear_segMisses_of_strictInside {outer inner : Rect} {p q : Point}
    (hSI : outer.StrictInside inner)
    (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (hm : Polyline.segMisses p q outer) : Polyline.segMisses p q inner := by
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  unfold Polyline.segMisses at hm ⊢
  rcases hm with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · obtain ⟨hne, hle | hge⟩ := h
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inl ?_⟩)))
      have c1 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * inner.y :=
        routeClear_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c2 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y :=
        routeClear_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have c3 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) :=
        routeClear_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have c4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) :=
        routeClear_minCorner_le_dot (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.minCorner (p.y - q.y) (q.x - p.x) outer ≤
          Polyline.minCorner (p.y - q.y) (q.x - p.x) inner := by
        simp only [Polyline.minCorner, Polyline.dot] at c1 c2 c3 c4 ⊢
        omega
      exact Int.le_trans hle h4
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, Or.inr ?_⟩)))
      have g1 : (p.y - q.y) * inner.x + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        routeClear_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g2 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * inner.y ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        routeClear_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y) (by omega) (by omega) (by omega) (by omega)
      have g3 : (p.y - q.y) * inner.x + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        routeClear_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x) (y := inner.y + inner.h) (by omega) (by omega) (by omega) (by omega)
      have g4 : (p.y - q.y) * (inner.x + inner.w) + (q.x - p.x) * (inner.y + inner.h) ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer :=
        routeClear_dot_le_maxCorner (nx := p.y - q.y) (ny := q.x - p.x)
          (x := inner.x + inner.w) (y := inner.y + inner.h)
          (by omega) (by omega) (by omega) (by omega)
      have h4 : Polyline.maxCorner (p.y - q.y) (q.x - p.x) inner ≤
          Polyline.maxCorner (p.y - q.y) (q.x - p.x) outer := by
        simp only [Polyline.maxCorner, Polyline.dot] at g1 g2 g3 g4 ⊢
        omega
      exact Int.le_trans h4 hge

/-- A polyline that misses an outer rectangle misses every strictly
inner one. -/
private theorem routeClear_allSegsMiss_of_strictInside {outer inner : Rect}
    (hSI : outer.StrictInside inner) (hw : 0 ≤ inner.w) (hh : 0 ≤ inner.h)
    (pts : List Point) :
    Polyline.allSegsMiss pts outer → Polyline.allSegsMiss pts inner := by
  induction pts
  case nil => intro h; trivial
  case cons head tail ih =>
    intro h
    cases tail with
    | nil => trivial
    | cons q rest' =>
        obtain ⟨hseg, htail⟩ := h
        exact ⟨routeClear_segMisses_of_strictInside hSI hw hh hseg, ih htail⟩

/-- Hitting a strictly inner rectangle implies hitting the outer one. -/
private theorem routeClear_hitsRect_of_strictInside {outer inner : Rect}
    {pts : List Point}
    (hSI : outer.StrictInside inner) (h : Polyline.hitsRect pts inner) :
    Polyline.hitsRect pts outer := by
  obtain ⟨hwI, hhI, hmissI⟩ := h
  obtain ⟨hox, how, hoy, hoh⟩ := hSI
  refine ⟨by omega, by omega, ?_⟩
  intro hmissO
  exact hmissI (routeClear_allSegsMiss_of_strictInside ⟨hox, how, hoy, hoh⟩
    (Int.le_of_lt hwI) (Int.le_of_lt hhI) _ hmissO)

/-! ## Split residuals (stated in `ExpandChildParentRouteRunProof`) -/

/-- The combined residual follows from the two split parts. -/
theorem expandChild_parentRouteClear_of_parts
    {group : ModelBox} {parent : FamilyResult}
    (hFrame : ExpandChildParentRouteFrameClear group parent)
    (hAtt : ExpandChildParentRouteAttachedClear group parent) :
    ExpandChildParentRouteClear group parent := by
  intro frame hfind
  exact ⟨hFrame frame hfind, hAtt frame hfind⟩

/-- Out-of-scope inner miss from the frame-level part by monotonicity:
hitting a strictly inside rectangle would hit the frame. -/
theorem parentRoute_outside_inner
    {group : ModelBox} {parent : FamilyResult}
    (hFrame : ExpandChildParentRouteFrameClear group parent)
    {frame : Box}
    (hfind : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    {pr : Route}
    (hpr : pr ∈ parent.scene.routes)
    (hfrom : pr.fromId ≠ group.id) (hto : pr.toId ≠ group.id)
    {r : Rect} (hSI : frame.rect.StrictInside r) :
    ¬ Polyline.hitsRect pr.points r := by
  intro hr
  exact hFrame frame hfind pr hpr hfrom hto
    (routeClear_hitsRect_of_strictInside hSI hr)

/-- Part (a) for the executed call, from the lift residuals: the recursion
 conclusion gives the frame-level miss under a scope premise, and the scope
 residual discharges that premise from endpoint inequality. -/
 theorem expandChild_parentRouteFrame_of_recursion
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hrec : ExpandChildFrameRecursion fuel P inp o group titleLines titleHeight
       parent child res)
     (hscope : ExpandChildFrameScopeOutside fuel P inp o group titleLines titleHeight
       parent child res) :
     ExpandChildParentRouteFrameClear group parent := by
   intro frame hfind pr hpr hfrom hto
   exact hrec frame hfind pr hpr hfrom hto (hscope frame hfind pr hpr hfrom hto)

 /-- (routes) Parent routes miss every rectangle strictly inside the frame,
 from the lift residuals for part (a) and the attached part (b). Same
 conclusion as `expandChild_parentFrame_routes`, with the combined residual
 replaced by the recursion/scope residuals plus the attached part. -/
 theorem expandChild_parentFrame_routes'
     {fuel : Nat} {P : Params} {inp : Input} {o : Options} {group : ModelBox}
     {titleLines : List Measure.Line} {titleHeight : Int}
     {parent child res : FamilyResult}
     (hrec : ExpandChildFrameRecursion fuel P inp o group titleLines titleHeight
       parent child res)
     (hscope : ExpandChildFrameScopeOutside fuel P inp o group titleLines titleHeight
       parent child res)
     (hAtt : ExpandChildParentRouteAttachedClear group parent)
     (hexpand : expandChild P inp o group titleHeight parent child = .ok res)
     (hframed : framedParents inp = true)
     (hctx : ExpandChildCallContext fuel P inp o group titleLines titleHeight
       parent child res) :
     ∀ (frame : Box) (titleLines' : List Measure.Line) (dx dy : Int),
     parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
     dx = frame.rect.x + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).x -
       P.canvasMargin →
     dy = frame.rect.y + (childInset group.direction P.clusterPad
         (titleLines'.foldl (fun width line => max width line.width) 0) titleHeight).y -
       P.canvasMargin →
     ExpandChildTitleWrapped P inp o group titleLines' →
     ∀ pr ∈ parent.scene.routes, ∀ (r : Rect),
       frame.rect.StrictInside r → ¬ Polyline.hitsRect pr.points r := by
   intro frame titleLines' dx dy hfind hdx hdy hwrap pr hpr r hSI
   have _hex := hexpand
   have _hfr := hframed
   have _hctx := hctx
   have _hdx := hdx
   have _hdy := hdy
   have _hwrap := hwrap
   have _hdxv : dx = dx := rfl
   have _hdyv : dy = dy := rfl
   have _htlv : titleLines' = titleLines' := rfl
   have hFrame := expandChild_parentRouteFrame_of_recursion hrec hscope
   by_cases hfrom : pr.fromId = group.id
   · exact hAtt frame hfind pr hpr (Or.inl hfrom) r hSI
   · by_cases hto : pr.toId = group.id
     · exact hAtt frame hfind pr hpr (Or.inr hto) r hSI
     · exact parentRoute_outside_inner hFrame hfind hpr hfrom hto hSI

end Elegant.Layered.PipelineImpl
