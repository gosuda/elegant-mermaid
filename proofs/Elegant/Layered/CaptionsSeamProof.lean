import Elegant.Layered.CaptionsSeamFacts
import Elegant.Layered.CaptionResidualsProof
import Elegant.Layered.CaptionFallbackContainProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- A `findIdx?` hit exposes the box at that index (local copy for the seam). -/
private theorem seam_findIdx_lookup {α : Type} {p : α → Bool}
    {l : List α} {n : Nat} (h : l.findIdx? p = some n) :
    n < l.length ∧ ∃ a, l[n]? = some a ∧ p a = true := by
  induction l generalizing n with
  | nil =>
    rw [List.findIdx?_nil] at h
    exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : n = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨Nat.zero_lt_succ _, a, rfl, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hmlen, x, hxget, hpx⟩ := ih hmfind
      rw [← hmn]
      exact ⟨Nat.succ_lt_succ hmlen, x, (List.getElem?_cons_succ).trans hxget, hpx⟩

/-- A component position key is the measured-graph node at that key (local copy). -/
private theorem seam_component_node_lookup {graph : Graph} {comp : List Nat}
    {cand : Nat} {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- `OwnerScopeSamePartClear` from `WellFormed`, via the fallback cases: under
the installed-title absence the owner is a node or a fixed box, so both it and
the foreign exclusive box are border-0 measured nodes and
`componentRun_positions_disjoint` applies. -/
theorem ownerScopeSamePartClear_of_fallback {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o)) :
    Elegant.Layered.OwnerScopeSamePartClear inp o res := by
  intro execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex
    hscope hd hnone bi k posOwner posB part hbi hk hposO hposB hne candidate run hrun
  obtain ⟨_, obox, hobox, hpobox⟩ := seam_findIdx_lookup hfindIdx
  have heq : obox.id = source.owner := by
    have hpred : (obox.id == source.owner && !obox.exclusive) = true := hpobox
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    exact hpred.1
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [heq]
    exact hnone
  have hfall := execution.fallback_owner_cases hwf hobox hnone'
  have hlinesLen : execution.lines.length = inp.boxes.length := by
    have hl := execution.lines_eq
    unfold boxLines at hl
    calc execution.lines.length = (inp.boxes.zipIdx).length :=
        (mapM_getElem? _ _ _ hl).1
      _ = inp.boxes.length := List.length_zipIdx
  have hOILen : ownerIndex < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hobox).1
  obtain ⟨sb, hsb, _, _, hsbex, _⟩ := sceneBox_source_rect execution hbi
  have hsbexTrue : sb.exclusive = true := by rw [← hsbex]; exact hex
  have hBILen : bi < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨nodeO, hnodeO, hbO⟩ :=
    ownerRes_node_border_zero execution hobox hfall hOILen
  have hngB : sb.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hsb) hsbexTrue
  have hroleB : sb.role = .node := by
    cases h : sb.role with
    | node => rfl
    | group => exact absurd h hngB
  have hBdisj : sb.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) = true := Or.inl hroleB
  obtain ⟨nodeB, hnodeB, hbB⟩ :=
    ownerRes_node_border_zero execution hsb hBdisj hBILen
  have hmap := (actual_components_parts_geometry (P := execution.params)
    (by rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = []) execution.components_eq).1
  have hpartMem : part ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hk
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨part, hpartMem, rfl⟩
  have hnodeOlookup :
      (componentCandidate execution.graph part.1 candidate).nodes[posOwner]? =
      some nodeO := seam_component_node_lookup hposO hnodeO
  have hnodeBlookup :
      (componentCandidate execution.graph part.1 candidate).nodes[posB]? =
      some nodeB := seam_component_node_lookup hposB hnodeB
  exact componentRun_positions_disjoint execution.graph_eq hcomp hrun
    hnodeOlookup hnodeBlookup hbO hbB hne

/-- The layered caption seam from `WellFormed`, `framedParents`, the fixed-size
fit premise, and the three remaining geometric residuals: same-part title
clearance, cross-part title clearance, and frame nesting. The containment comes
from `ownerCaptionContainFallback_of_fit`; the descendant fallback is vacuous. -/
theorem sceneCaptionBoxContainment_of_fit {inp : Input} {o : Options}
    {res : FamilyResult} (hwf : WellFormed (Elegant.Layered.inputModel inp o))
    (hfp : Elegant.Layered.framedParents inp = true)
    (hfit : InputFixedFit inp o)
    (hsameT : TitleExclusiveSamePart inp o res)
    (hcrossT : TitleExclusiveCrossPart inp o res)
    (hframes : ∀ (execution : SceneExecution inp o res),
      LabelFramePackedClear execution.params inp o execution.lines
        execution.packedAcc ∧ FallbackCaptionClear execution) :
    Elegant.Layered.SceneCaptionBoxContainment inp o res := by
  have hcontain : Elegant.Layered.OwnerCaptionContainFallback inp o res :=
    Elegant.Layered.ownerCaptionContainFallback_of_fit (res := res) hwf hfit
  have hsameFull : Elegant.Layered.OwnerScopeSamePartClear inp o res :=
    ownerScopeSamePartClear_of_fallback (res := res) hwf
  have htitle : ∀ (execution : SceneExecution inp o res),
      TitleExclusiveFrameDisjoint execution :=
    fun execution => titleExclusiveFrameDisjoint_of_parts hwf hsameT hcrossT
      execution
  have hdesc :=
    captionDescendantSamePartClear_of_fallback hwf hfp htitle
      (descendantFallbackClear_vacuous hwf hfp)
  exact Elegant.Layered.sceneCaptionBoxContainment_of_residuals hwf hdesc
    hcontain hsameFull hframes htitle

end Elegant.Layered.PipelineImpl
