import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.LabelRunBridgeFacts

set_option autoImplicit false

namespace Elegant.Layered

namespace PipelineImpl

/-! # Executed part frame cores of the C8b clause

 `ExecutedPartFrameCores` (`LabelsC8bFacts.lean`) is the conjunction of the
 two component-local clearance facts.  This file proves each conjunct's
 transport from the executed placement shift and keeps one strictly smaller
 run-level residual per conjunct:

* `CaptionRunClear` — installed title captions against every frame position
  of one executed component run (no `Acc`/`Part` shift, no packed arrays,
  no input-box lookups);
* `RouteRunClear` — placed route labels against every frame position of one
  executed run.

 The transports (`partCaption_of_run`, `partRoute_of_run`) are proved
 outright from `execution_part_run`, the `placeComponent` shift equations,
 `componentTitles_dimension_source`, and the shift-transport lemmas.  The
 owned-text fallback-caption conjunct was deleted, not repaired:
 `OwnedRunClear` is FALSE as stated (a centered node caption shares `x`/`w`
 with its box, and inflated captions poke out of every ancestor frame), and
 no Part-level statement needs it.
-/

/-! ## Proved composition helpers -/

/-- Strict-inside-through-contained: a rect strictly inside a middle frame
that is contained in an outer frame is strictly inside the outer frame.
Arithmetic over the four strict/non-strict bounds. -/
theorem strictInside_of_contained {outer mid inner : Rect}
    (hinner : mid.StrictInside inner) (hmid : outer.Contained mid) :
    outer.StrictInside inner := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Disjointness through containment: a rect contained in a frame disjoint
from another rect is disjoint from that rect. -/
theorem disjoint_of_sub_disjoint {l f g : Rect}
    (hsub : f.Contained l) (hdisj : Disjoint f g) :
    Disjoint l g := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  omega

/-- The caption resize commutes with the placement shift. -/
theorem captionResize_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl

/-- The placement shift is injective on rectangles. -/
theorem shiftRect_inj {dx dy : Int} {a b : Rect}
    (h : shiftRect dx dy a = shiftRect dx dy b) : a = b := by
  unfold shiftRect at h
  cases a
  cases b
  simp only [Rect.mk.injEq] at h ⊢
  omega

/-! ## `placeComponent` shift equations -/

/-- The titles a placed part stores are the run's installed titles shifted
by the placement negated bounds. -/
theorem placeComponent_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponent P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBounds P cg run labels loops).minX)
          (0 - (placeBounds P cg run labels loops).minY) q.2)) := by
  unfold placeComponent placeBounds
  rfl

 /-- A placed part stores exactly one rect per component node.  Proved by
 unfolding the placement and reducing the record projection and the mapped
 range lengths. -/
 theorem placeComponent_rects_length (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
     (placeComponent P cg run 0 labels loops).rects.length = cg.nodes.length := by
   unfold placeComponent
   dsimp only
   simp only [List.length_map, List.length_range]
 /-- A placed part stores the shifted frame rect at every valid component
 position.  This mirrors the `placeComponent_rects_get` pattern used for the
 C8a transport: unfolding both definitions leaves the mapped range lookup. -/
 theorem placeComponent_rect_get (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement))
     {i : Nat} (hi : i < cg.nodes.length) :
     (placeComponent P cg run 0 labels loops).rects[i]? =
       some (shiftRect (0 - (placeBounds P cg run labels loops).minX)
         (0 - (placeBounds P cg run labels loops).minY)
         (frameRect P cg run i)) := by
   unfold placeComponent placeBounds
   simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-! ## Run-level residuals (one phase each, pinned by `componentRun`) -/

 /-- Residual (title-caption phase): inside one executed component run, every
 installed title caption resized by `capSize` either misses every frame
 position or lies strictly inside it.  This is the run-level content of
 `PartCaptionFrameClear`: no `Acc`/`Part` shift, no packed arrays, no
 input-box or demotion lookups.  The title-side group premise comes from
 `componentTitles_dimension_source`; the frame side is premise-free so the
 transport needs no border link.  The transports apply it only to executed
 runs, pinned by their `componentRun` equations. -/
 def CaptionRunClear (P : Params) (cg : Graph) (run : Run)
     (capSize : Nat → Int × Int) : Prop :=
   ∀ (i : Nat) (stored0 : Rect) (tNode : Node),
     (i, stored0) ∈ componentTitles P cg run →
       cg.nodes[i]? = some tNode → tNode.border = -2 →
       ∀ (pos : Nat) (g0 : Rect),
         pos < cg.nodes.length →
         frameRect P cg run pos = g0 →
         Disjoint g0
             { stored0 with w := (capSize i).1, h := (capSize i).2 } ∨
           g0.StrictInside
             { stored0 with w := (capSize i).1, h := (capSize i).2 }

/-- Residual (route-label phase): inside one executed component run, every
placed route label either misses every frame position or lies strictly
inside it.  This is the run-level content of `PartRouteLabelFrameClear`:
 no `Acc`/`Part` shift, no packed arrays, no input-box lookups.  The
 transports apply it only to executed runs, pinned by their `componentRun`
 equations. -/
def RouteRunClear (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) : Prop :=
  ∀ (k : Nat) (rect : Rect),
    (k, rect) ∈ placedLabels P cg run labels →
    ∀ (pos : Nat) (g0 : Rect),
      pos < cg.nodes.length →
      frameRect P cg run pos = g0 →
       Disjoint g0 rect ∨ g0.StrictInside rect

/-! ## Proved transports: Part-level conjuncts from run-level residuals -/

/-- The caption conjunct of `ExecutedPartFrameCores`, from the run-level
caption residual.  Titles and frames both shift by the same placement
translation, the title-side group node comes from
`componentTitles_dimension_source`, and the resized caption commutes with
the shift. -/
theorem partCaption_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hres : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run),
      ∀ (labels : List MeasuredLabel) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          labels orderOptions = .ok run →
        CaptionRunClear execution.params
          (componentCandidate execution.graph comp candidate) run
          (fun i => ((titleCaptionSize execution.params o
            (execution.lines.getD (comp.getD i 0) [])).w,
            (titleCaptionSize execution.params o
            (execution.lines.getD (comp.getD i 0) [])).h))) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartCaptionFrameClear execution.params inp o execution.lines part := by
  intro part hpart i stored pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  have eT : part.2.titles =
      (componentTitles execution.params
        (componentCandidate execution.graph part.1 index) run).map (fun q =>
        (q.1, shiftRect
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minY) q.2)) := by
    have h1 : part.2.titles =
        (placeComponent execution.params
          (componentCandidate execution.graph part.1 index) run 0
          execution.measured loops).titles := by
      rw [heq]
    rw [h1]
    exact placeComponent_titles_eq _ _ _ _ _
  have eR' : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects := by
    rw [heq]
  rw [eT] at hmem
  obtain ⟨⟨i0, stored0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hstored⟩ := h0eq
  have hlen : part.2.rects.length =
      (componentCandidate execution.graph part.1 index).nodes.length := by
    rw [eR']
    exact placeComponent_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 index).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := placeComponent_rect_get execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured
    loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run pos) = g :=
    Option.some.inj hrect
  obtain ⟨top, htop, hborder, htitleIdx, _hw, _hh⟩ :=
    componentTitles_dimension_source execution.params
      (componentCandidate execution.graph part.1 index) run h0mem
  have hidx : i0 = top.2 := htitleIdx
  have hnode : (componentCandidate execution.graph part.1 index).nodes[i0]? =
      some top.1 := by
    rw [hidx]
    exact List.mem_zipIdx_iff_getElem?.mp htop
  have hclear := hres part.1 hcomp index run execution.measured
    (candidateOrder index) hrun i0 stored0 top.1 h0mem hnode hborder
    pos _ hlt rfl
  dsimp only
  rw [←hg0, ←hstored, captionResize_shift_comm]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- The route-label conjunct of `ExecutedPartFrameCores`, from the run-level
route residual.  Labels come from `placedLabels` through the same placement
shift (`placeComponent_labels_eq`), frames from the shifted frame list. -/
theorem partRoute_of_run {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hres : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run),
      ∀ (labels : List MeasuredLabel) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          labels orderOptions = .ok run →
        RouteRunClear execution.params
          (componentCandidate execution.graph comp candidate) run labels) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part := by
  intro part hpart index rect pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨cindex, run, loops, _area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  have eL : part.2.labels =
      (placedLabels execution.params
        (componentCandidate execution.graph part.1 cindex)
        run execution.measured).map (fun q =>
        (q.1, shiftRect
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 cindex) run
            execution.measured loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 cindex) run
            execution.measured loops).minY) q.2)) := by
    have h1 : part.2.labels =
        (placeComponent execution.params
          (componentCandidate execution.graph part.1 cindex) run 0
          execution.measured loops).labels := by
      rw [heq]
    rw [h1]
    exact placeComponent_labels_eq
  have eR' : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 cindex) run 0
      execution.measured loops).rects := by
    rw [heq]
  rw [eL] at hmem
  obtain ⟨⟨k0, rect0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hrect0⟩ := h0eq
  have hlen : part.2.rects.length =
      (componentCandidate execution.graph part.1 cindex).nodes.length := by
    rw [eR']
    exact placeComponent_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 cindex).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := placeComponent_rect_get execution.params
    (componentCandidate execution.graph part.1 cindex) run execution.measured
    loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 cindex) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 cindex) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 cindex) run pos) = g :=
    Option.some.inj hrect
  have hclear := hres part.1 hcomp cindex run execution.measured
    (candidateOrder cindex) hrun k0 rect0 h0mem pos _ hlt rfl
  rw [←hg0, ←hrect0]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

 /-- The executed component-local cores of the frame-label clause: every
 executed part satisfies the route-label and caption clearance, modulo the
 two single-phase run-level residuals above.  No `WellFormed` or
 `framedParents` premise is needed for the assembly; the marker premises
 (`BracketMarkersAtRank`, `PlainClearOfSideMarker`,
 `SideMarkerSpanAligned`, `ForeignClusterRankSpans`,
 `ForeignBorderLayerOrder`, `ForeignBorderChainXAligned`) belong to the
 future discharge of the residuals and are not consumed here. -/
theorem executedPartFrameCores {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hroute : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run),
      ∀ (labels : List MeasuredLabel) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          labels orderOptions = .ok run →
        RouteRunClear execution.params
          (componentCandidate execution.graph comp candidate) run labels)
    (hcap : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run),
      ∀ (labels : List MeasuredLabel) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          labels orderOptions = .ok run →
        CaptionRunClear execution.params
          (componentCandidate execution.graph comp candidate) run
          (fun i => ((titleCaptionSize execution.params o
            (execution.lines.getD (comp.getD i 0) [])).w,
            (titleCaptionSize execution.params o
            (execution.lines.getD (comp.getD i 0) [])).h)))
    :
    ExecutedPartFrameCores execution := by
  intro part hpart
  exact ⟨partRoute_of_run execution hroute part hpart,
    partCaption_of_run execution hcap part hpart⟩

end PipelineImpl

end Elegant.Layered
