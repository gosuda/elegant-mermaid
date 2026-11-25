import Elegant.Layered.NotesRouterEndsProof
import Elegant.Layered.VisibilityShortestSource

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Both endpoints of the returned list are mapped ports, regardless of rectangle dimensions. -/
theorem routeAround_endpoints_mem
    {inp : Input} {atts : List Attach} {frame : Frame}
    {rects : List (String × Rect)} {labels : List SceneLabel} {titles : List (String × Rect)}
    {r : ModelRoute} {from_ to_ : Rect} {pts : List Point}
    (hFrom : rects.lookup r.fromId = some from_)
    (hTo : rects.lookup r.toId = some to_)
    (hRoute : routeAround inp atts frame rects labels titles r = .ok pts) :
    ∃ p q : Point, pts.head? = some p ∧ pts.getLast? = some q ∧
      p ∈ (Visibility.ports (frame.rect from_)).map frame.output ∧
      q ∈ (Visibility.ports (frame.rect to_)).map frame.output := by
  unfold routeAround at hRoute
  simp only [hFrom, hTo] at hRoute
  split at hRoute
  · simp at hRoute
  · next points hShortest =>
    have hPts : points.map frame.output = pts := Except.ok.inj hRoute
    obtain ⟨p, hp, hHead⟩ := Visibility.newGrid_shortest_start_mem hShortest
    obtain ⟨q, hq, hLast⟩ := nrep_shortest_end_mem _
      (Visibility.ports (frame.rect from_)) (Visibility.ports (frame.rect to_)) points hShortest
    rw [← hPts]
    refine ⟨frame.output p, frame.output q, ?_, ?_,
      List.mem_map.mpr ⟨p, hp, rfl⟩, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
    · simp only [List.head?_map, hHead, Option.map_some]
    · simp only [List.getLast?_map, hLast, Option.map_some]

theorem nriRouterPathExec_of_rects_lookup_nonneg
    (inp : Input) (o : Options) (res contracted : FamilyResult)
    (fragments : List Placed) (atts : List Attach) (margin : Int)
    (hDims : ∀ (id : String) (rect : Rect),
      (notesRectsOf res.scene.boxes).lookup id = some rect → 0 ≤ rect.w ∧ 0 ≤ rect.h) :
    nriRouterPathExec inp o res contracted fragments atts margin := by
  intro r _ from_ to_ hFrom hTo
  obtain ⟨hFromWidth, hFromHeight⟩ := hDims r.fromId from_ hFrom
  obtain ⟨hToWidth, hToHeight⟩ := hDims r.toId to_ hTo
  refine ⟨hFromWidth, hFromHeight, hToWidth, hToHeight, ?_⟩
  intro pts hRoute
  exact routeAround_endpoints_mem hFrom hTo hRoute

end Elegant.Layered.PipelineImpl
