import Elegant.Layered.RegionCrossRunC6
import Elegant.Layered.RecursiveBLiftsB

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Clearance in the coordinates of the placed part, for the same indexed route and
exclusive out-of-scope box that the validator sees. Both local entries must come from
one part selected by the successful components fold. -/
def R6_SamePartClearance {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ {routeKey boxKey : Nat} {route : Route} {box : Box},
    res.scene.routes[routeKey]? = some route →
    res.scene.boxes[boxKey]? = some box →
    box.exclusive = true →
    box.id ∉ LayoutDump.routeScope res.scene.layoutDump route →
    ∀ {c : Nat} {part : List Nat × Part},
      execution.componentsAcc.parts[c]? = some part →
      ∀ {i j : Nat} {pts : List Point} {rect : Rect},
        part.2.routes[i]? = some (routeKey, pts) →
        (part.1.zip part.2.rects)[j]? = some (boxKey, rect) →
        ¬ Polyline.hitsRect pts rect

set_option maxHeartbeats 600000 in
/-- Cross-part cases are discharged by `c6_hit_same_part`. Conversely, every local
pair in the residual is projected to its actual scene pair by the same rigid maps. -/
theorem SceneExecutionR.c6_iff_samePartClearance
    {exactIds : List String} {idSets : List (String × List String)}
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    Validator.C6 res.scene.layoutDump ↔ R6_SamePartClearance execution := by
  constructor
  · intro hc6 routeKey boxKey route box hroute hbox hex hscope c part hpart
      i j pts rect hlocal hentry
    have hmiss := hc6 route (List.mem_of_getElem? hroute) box (List.mem_of_getElem? hbox)
      hex hscope
    obtain ⟨packed, hpacked, _⟩ := packAcc_components_disjoint execution.packed_eq
    have hcount : packed.boxes.length = execution.componentsAcc.parts.length := by
      simpa only [List.length_map] using Pack.pack_count hpacked
    have hc : c < packed.boxes.length := by
      rw [hcount]
      exact (List.getElem?_eq_some_iff.mp hpart).1
    have hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? =
        some (part, packed.boxes[c]'hc) :=
      List.getElem?_zip_eq_some.mpr ⟨hpart, List.getElem?_eq_getElem hc⟩
    have hpoints := execution.chosenPartRoute_points hpacked hselected hlocal hroute
    have hkey := (List.getElem?_eq_some_iff.mp hbox).1
    rw [execution.boxes_eq_mapR] at hkey
    have hk : boxKey < inp.boxes.length := by
      simpa only [List.length_map, List.length_zipIdx] using hkey
    have hsize : boxKey < execution.componentsAcc.rects.size := by
      rw [execution.components_rects_sizeR]
      exact hk
    have hread := actual_components_packed_rect_valueR (by rfl) execution.components_eq
      execution.packed_eq packed hpacked hselected hentry hsize default
    rw [execution.boxes_eq_mapR] at hbox
    simp only [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk,
      Option.map_some, Nat.zero_add, hread] at hbox
    have hrect := congrArg Box.rect (Option.some.inj hbox).symm
    rw [hpoints, hrect, hitsRect_shift_orient, hitsRect_shift] at hmiss
    exact hmiss
  · intro hclear route hroute box hbox hex hscope hhit
    change route ∈ res.scene.routes at hroute
    change box ∈ res.scene.boxes at hbox
    obtain ⟨routeKey, hroute⟩ := List.mem_iff_getElem?.mp hroute
    obtain ⟨boxKey, hbox⟩ := List.mem_iff_getElem?.mp hbox
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hselected,
      _, _, _, _, _, hlocal, hentry, hhitLocal⟩ :=
      execution.c6_hit_same_part hroute hbox hhit
    exact hclear hroute hbox hex hscope (zip_getElem?_left hselected) hlocal hentry hhitLocal

/-- The seam for the reindexing base. The reindexed sets, execution, and successful
layout are all tied to the same input. -/
def R6_ReindexedSamePartClearance (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    WellFormed (inputModel inp o) → framedParents inp = true →
    FixedSizesPositive inp → FrameClearanceSeam inp o res →
    layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
    ∀ (execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res),
      R6_SamePartClearance execution

theorem flatC6B_layoutRIds_reindex_iff_samePart (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC6B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      R6_ReindexedSamePartClearance exactIds idSets := by
  constructor
  · intro hflat inp o res hwf hfp hpos hframe hok execution
    exact execution.c6_iff_samePartClearance.mp (hflat inp o res hwf hfp hpos hframe hok)
  · intro hlocal inp o res hwf hfp hpos hframe hok
    obtain ⟨execution⟩ := layoutRIds_sceneExecution hok
    exact execution.c6_iff_samePartClearance.mpr (hlocal inp o res hwf hfp hpos hframe hok execution)

end Elegant.Layered.PipelineImpl
