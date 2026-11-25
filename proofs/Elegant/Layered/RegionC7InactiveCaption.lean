import Elegant.Layered.RegionSelectedCaptionClearance
import Elegant.Layered.ExactRunTitleBandClosedProof

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace Elegant.Layered.PipelineImpl

open RegionImpl

/-- In a mixed execution, the effective spec is absent exactly when the real
region probe found no set owned by the selected component. The component can
still have groups and install titles. -/
theorem r7Caption_installed_spec_none_iff {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (pair : R7_InstalledCaptionPair execution oi l b) (hempty : idSets ≠ []) :
    pair.spec = none ↔
      newComponentRegions (r7Spec idSets o execution.params execution.lines)
        execution.params inp (componentGraph execution.graph pair.part.1) = .ok none := by
  obtain ⟨rs, hrs, heff⟩ := pair.effective_eq
  have hn : idSets.isEmpty = false := List.isEmpty_eq_false_iff.mpr hempty
  rw [heff, hrs]
  cases rs with
  | none => constructor <;> intro _ <;> rfl
  | some rs =>
    change (r7Spec idSets o execution.params execution.lines = none) ↔
      (Except.ok (some rs) : Except LayoutError (Option ComponentRegions)) = .ok none
    unfold r7Spec
    rw [hn]
    simp

/-- An installed title in an inactive selected component clears its exclusive
plain target, using the exact run that actually produced both rectangles. -/
theorem r7Caption_installed_inactive_clear {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecutionR exactIds idSets inp o res} {l : SceneLabel} {b : Box} {oi : Nat}
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (pair : R7_InstalledCaptionPair execution oi l b) (hs : pair.spec = none) :
    R7_OverlapRowsXGap l.rect b.rect := by
  let context : ExactTitleRunContext exactIds inp o :=
    ⟨execution.params, execution.lines, execution.measured, execution.graph0,
      execution.graph, execution.checked, boxLines_length execution.lines_eq,
      execution.graph0_eq, execution.graph_eq⟩
  have hpart := (List.getElem?_zip_eq_some.mp pair.shelf_eq).1
  have hcomp : pair.part.1 ∈ components context.graph := by
    change pair.part.1 ∈ components execution.graph
    rw [← (actual_components_parts_geometryR (by rfl) execution.components_eq).1]
    exact List.mem_map_of_mem (List.mem_of_getElem? hpart)
  have hrun := pair.run_eq
  rw [hs, componentCandidateR_none] at hrun
  obtain ⟨hrunX, hcg⟩ := r8aC8a_runX_of_none hrun
  have htop := pair.top_eq
  have hraw := pair.top_mem
  have htarget := pair.target_eq
  rw [hcg] at htop hraw htarget
  have hclear := componentRunX_title_clear_of_plain context hwf hfp hcomp
    (candidate := pair.candidate) (stored := pair.raw.2) hrunX htop pair.top_border
    hraw htarget pair.target_plain pair.target_pos pair.target_source
  have hkey : pair.part.1.getD pair.raw.1 0 = oi := by
    simp only [List.getD_eq_getElem?_getD, pair.owner_pos, Option.getD_some]
  change Disjoint
    (frameRect execution.params (componentCandidate execution.graph pair.part.1 pair.candidate)
      pair.run pair.targetPos)
    { pair.raw.2 with
      w := (titleCaptionSize execution.params o
        (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).w
      h := (titleCaptionSize execution.params o
        (execution.lines.getD (pair.part.1.getD pair.raw.1 0) [])).h } at hclear
  rw [hkey, ← hcg] at hclear
  have hscene : Disjoint l.rect b.rect := by
    rw [pair.label_rect, pair.box_rect]
    unfold r7SelectedTransport
    exact disjoint_sceneTransport (not_meetsInterior_shiftRect
      ((Disjoint.comm _ _).mp hclear))
  unfold Disjoint Rect.meetsInterior at hscene
  intro hrows hlw hbw
  omega

/-- The unchanged installed-title and selected-part constraints, restricted to
active components. The route obligation is not changed. -/
def R7_SelectedCaptionActiveResidual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) : Prop :=
  ∀ (l : SceneLabel) (b : Box) (index oi : Nat) (source : ModelLabel),
    l ∈ res.scene.labels → b ∈ res.scene.layoutDump.boxes → b.exclusive = true →
    b.id ∉ source.owner :: res.scene.layoutDump.ancestors source.owner →
    inp.labels[index]? = some source → l.id = source.id →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx? (fun box => box.id == source.owner && !box.exclusive) = some oi →
    max l.rect.y b.rect.y < min (l.rect.y + l.rect.h) (b.rect.y + b.rect.h) →
    0 < l.rect.w → 0 < b.rect.w →
    (let title := (sceneTitlesExpr execution.params inp o execution.lines execution.packedAcc).find?
        (fun row => row.1 == source.owner)
     title.isSome = true ∧ R7_CaptionSharesPart execution oi b ∧ idSets ≠ [] ∧
       ∃ (pair : R7_InstalledCaptionPair execution oi l b) (spec : RegionSpec),
         pair.spec = some spec ∧ pair.targetNode.clusterPath.contains pair.topNode.decl = false ∧
         (rk pair.run.proper.rank pair.targetPos).toNat ≤ (rk pair.run.proper.rank pair.raw.1).toNat) →
    l.rect.x + l.rect.w ≤ b.rect.x ∨ b.rect.x + b.rect.w ≤ l.rect.x

theorem r7Caption_afterInstalled_iff_activeResidual {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true) :
    R7_SelectedCaptionAfterInstalledResidual execution ↔ R7_SelectedCaptionActiveResidual execution := by
  constructor
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    obtain ⟨ht, hshared, hempty, pair, spec, hs, hforeign, hrank⟩ := hcase
    exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
      ⟨ht, hshared, hempty, pair, Or.inr ⟨spec, hs, hforeign, hrank⟩⟩
  · intro h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw hcase
    obtain ⟨ht, hshared, hempty, pair, hspec⟩ := hcase
    rcases hspec with hnone | ⟨spec, hs, hforeign, hrank⟩
    · exact r7Caption_installed_inactive_clear hwf hfp pair hnone hrows hlw hbw
    · exact h l b i oi source hl hb hex hscope hi hid hm ho hrows hlw hbw
        ⟨ht, hshared, hempty, pair, spec, hs, hforeign, hrank⟩

theorem flatC7B_layoutRIds_reindex_iff_captionActive (exactIds : List String)
    (idSets : List (String × List String)) :
    FlatC7B (fun inp o => layoutRIds exactIds (reindexRegionSets idSets inp) inp o) ↔
      (∀ (inp : Input) (o : Options) (res : FamilyResult),
        WellFormed (inputModel inp o) → framedParents inp = true → InputFixedFit inp o →
        Elegant.Layered.PartsSeparated inp o res → LabelRunsClearExclusiveBoxes inp o res →
        SceneCaptionBoxContainment inp o res →
        layoutRIds exactIds (reindexRegionSets idSets inp) inp o = .ok res →
        ∀ execution : SceneExecutionR exactIds (reindexRegionSets idSets inp) inp o res,
          R7_SelectedRouteWithPlainTarget execution ∧ R7_SelectedCaptionActiveResidual execution) := by
  refine (flatC7B_layoutRIds_reindex_iff_captionAfterInstalled exactIds idSets).trans ?_
  constructor
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute, (r7Caption_afterInstalled_iff_activeResidual execution hwf hfp).mp hcaption⟩
  · intro h inp o res hwf hfp hfit hsep hruns hcap hok execution
    obtain ⟨hroute, hcaption⟩ := h inp o res hwf hfp hfit hsep hruns hcap hok execution
    exact ⟨hroute, (r7Caption_afterInstalled_iff_activeResidual execution hwf hfp).mpr hcaption⟩

end Elegant.Layered.PipelineImpl
