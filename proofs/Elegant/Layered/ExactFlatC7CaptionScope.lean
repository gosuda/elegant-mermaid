import Elegant.Layered.ExactFlatC7
import Elegant.Layered.CaptionScopeGeometry

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! Exact flat C7 caption scope.

Target: `x_captionScopeClearance_holds : X_CaptionScopeClearance exactIds`,
replaying `captionScopeClearance`
(`Elegant/Layered/CaptionScopeGeometry.lean:337`) over `SceneExecutionX`.

Plain premise map (each X premise below mirrors the named plain `Prop`
field by field, with `SceneExecution` replaced by `SceneExecutionX` and
`captionLabel` by `X_captionLabel`):

* `X_CaptionDescendantClear` mirrors `CaptionDescendantClear`
  (`CaptionScopeGeometry.lean:247`). Plain proof:
  `captionDescendantClear_of_same_part` (`CaptionDescendantFacts.lean:88`),
  carrying `CaptionDescendantSamePartClear` (same file). That same-part
  obligation is discharged in the plain pipeline by `CaptionResidualsProof`
  from `WellFormed`, `framedParents`, `TitleExclusiveFrameDisjoint`, and the
  fallback clearance.
* `X_OwnerCaptionContainFallback` mirrors `OwnerCaptionContainFallback`
  (`CaptionScopeGeometry.lean:89`). Plain proof:
  `ownerCaptionContainFallback_of_fit` (`CaptionFallbackContainProof.lean:55`),
  carrying `WellFormed (inputModel inp o)` and
  `PipelineImpl.InputFixedFit inp o`.
* `X_OwnerScopeExclusiveClear` mirrors `OwnerScopeExclusiveClear`
  (`CaptionScopeGeometry.lean:265`). Plain proof:
  `ownerScopeExclusiveClear_of_same_part` (`CaptionOwnerScopeFacts.lean:247`),
  carrying `OwnerScopeSamePartClear` (same file), discharged in the plain
  pipeline by `CaptionsSeamProof` from `WellFormed` and the frame facts.
* `X_CaptionTitleBranchClear` mirrors `CaptionTitleBranchClear`
  (`CaptionScopeGeometry.lean:291`). Plain proof:
  `captionTitleBranchClear_of_frames` (`CaptionTitleBranchFacts.lean:61`),
  carrying per-execution `LabelFramePackedClear ∧ FallbackCaptionClear` and
  `TitleExclusiveFrameDisjoint` (discharged in the plain pipeline by
  `CaptionResidualsProof`).

The plain caption facts reduce to the single open family seam
`ForeignBorderChainXAligned` (field `LayeredSeams.foreignBorderChainXAligned`,
`FamilyAssembly.lean:123`; def at `ForeignBorderSpansProof.lean:140`), plus
proved narrow facts. Its X mirror is `X_ForeignBorderChainXAligned` below,
stated field by field over `exactGraph` and `componentRunX`.
-/

/-- X mirror of `ForeignBorderChainXAligned` (`ForeignBorderSpansProof.lean`):
in an exact run, two border markers of one declaration and one side share the
same closed `x`-interval. Mirrors the plain def field by field, with the
`measuredGraph`-then-`exactGraph` pipeline and `componentRunX` over
`exactDecls exactIds inp`. -/
def X_ForeignBorderChainXAligned (exactIds : List String) : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph},
    measuredGraph P inp o lines = .ok graph0 →
    exactGraph P exactIds inp o measured graph0 = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRunX P (exactDecls exactIds inp) (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {a b : Nat} {na nb : ProperNode},
      run.coordinateProper.nodes[a]? = some na →
      run.coordinateProper.nodes[b]? = some nb →
      (na.node.border = -1 ∨ na.node.border = 1) →
      (nb.node.border = -1 ∨ nb.node.border = 1) →
      na.node.border = nb.node.border →
      na.node.clusterPath.getLast? = nb.node.clusterPath.getLast? →
      RouteImpl.leftOf run.proper run.xs a = RouteImpl.leftOf run.proper run.xs b ∧
        RouteImpl.leftOf run.proper run.xs a + RouteImpl.nodeW run.proper a =
          RouteImpl.leftOf run.proper run.xs b + RouteImpl.nodeW run.proper b

/-- X mirror of `CaptionDescendantClear`: the descendant case over the exact
execution. -/
def X_CaptionDescendantClear (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    source.owner ∈ res.scene.layoutDump.ancestors b.id →
    ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- X mirror of `OwnerCaptionContainFallback`: the fallback-containment case
over the exact execution. -/
def X_OwnerCaptionContainFallback (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res) (ownerIndex : Nat)
    (obox : ModelBox),
    inp.boxes[ownerIndex]? = some obox →
    (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == obox.id) = none →
    obox.exclusive = false →
    (∃ l ∈ inp.labels, l.owner = obox.id) →
    let ownerBox : Box :=
      (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩
    ownerBox.rect.Contained
      (ownedTextRect execution.params ownerBox
        (execution.lines.getD ownerIndex []))

/-- X mirror of `OwnerScopeExclusiveClear`: the non-descendant case over the
exact execution. -/
def X_OwnerScopeExclusiveClear (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    source.owner ∉ res.scene.layoutDump.ancestors b.id →
    (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
    ¬ b.rect.meetsInterior
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect

/-- X mirror of `CaptionTitleBranchClear`: the installed-title branch over the
exact execution. -/
def X_CaptionTitleBranchClear (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res) (index ownerIndex : Nat)
    (source : ModelLabel) (lines : List String) (b : Box),
    inp.labels[index]? = some source →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    b ∈ res.scene.layoutDump.boxes →
    b.exclusive = true →
    b.id ∉ res.scene.layoutDump.labelOwnerAnc
      (X_captionLabel exactIds execution ownerIndex source lines) →
    ((sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find?
          (fun title => title.1 == source.owner)).isSome = true →
    ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- `XCap_` copy of the private `captionScope_findIdx_lookup`
(`CaptionScopeGeometry.lean`): a `findIdx?` hit exposes the box at that
index and its predicate value. -/
private theorem XCap_captionScope_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
    {n : Nat} (h : l.findIdx? p = some n) :
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

theorem x_captionScopeClearance_holds (exactIds : List String)
    (hdesc : X_CaptionDescendantClear exactIds)
    (hcontain : X_OwnerCaptionContainFallback exactIds)
    (howners : X_OwnerScopeExclusiveClear exactIds)
    (htitle : X_CaptionTitleBranchClear exactIds) :
    X_CaptionScopeClearance exactIds := by
  intro inp o res execution index ownerIndex source lines b hsrc hmeas hfindIdx
    hmem hex hscope
  by_cases hd : source.owner ∈ res.scene.layoutDump.ancestors b.id
  · exact hdesc inp o res execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem hex hscope hd
  · simp only [sceneCaptionRect]
    cases hopt : (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hclr := howners inp o res execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope hd hopt
      obtain ⟨_, obox, hobox, hpobox⟩ := XCap_captionScope_findIdx_lookup hfindIdx
      have heq : obox.id = source.owner := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        exact hpobox.1
      have hnone : (sceneTitlesExpr execution.params inp o execution.lines
          execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
        rw [heq]
        exact hopt
      have hexcl : obox.exclusive = false := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hpobox
        simpa using hpobox.2
      have hown : ∃ l ∈ inp.labels, l.owner = obox.id :=
        ⟨source, List.mem_of_getElem? hsrc, heq.symm⟩
      have hc := hcontain inp o res execution ownerIndex obox hobox hnone hexcl hown
      exact fun hmeet =>
        hclr (rect_meetsInterior_comm (contained_meetsInterior_mono hc hmeet))
    | some t =>
      simp only [Option.map_some, Option.getD_some]
      have ht := htitle inp o res execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope (by rw [hopt]; rfl)
      simp only [sceneCaptionRect] at ht
      rw [hopt] at ht
      simp only [Option.map_some, Option.getD_some] at ht
      exact ht

end PipelineImpl
end Layered
end Elegant
