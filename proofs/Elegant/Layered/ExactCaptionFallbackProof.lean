import Elegant.Layered.ExactCaptionScopeProof
import Elegant.Layered.InputFixedFit

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact fallback caption clearance, fit-conditioned (decision B).

Target: the exact residual `X_CaptionScopeClearance exactIds` that
`flatC7B_layoutX` (`Elegant/Layered/ExactFlatC7.lean:1512`) carries as
hypothesis `hcap`. The tracked assembler `x_captionScopeClearance_holds`
(`ExactFlatC7CaptionScope.lean:180`) and the four-premise form
`X_captionScopeClearance_holds` (`ExactCaptionScopeProof.lean`) reduce the
target to four single-fact residuals, one per plain caption branch.

Decision: (B). The unconditional fallback containment
`X_OwnerCaptionContainFallback` is FALSE as stated: a fixed-size group owner
carries no installed title, so the `ownedTextRect` fallback can escape the
owner rect. Witnesses from `proofs/wip/Probe/ExactCaptionFallbackTProbe1.lean`
(vector profile, `layoutX [] inp tOpts` recomputed phases):

* `fb-fixed-300x200`: owner `g` box `(1898, 1024, 300, 200)`,
  caption `(2922, 2048, 0, 1280)`, contained `false`, width `0`;
* `fb-fixed-0x0`: owner box `(2048, 1024, 0, 0)`,
  caption `(3072, 2048, 0, 1280)`, contained `false`, width `0`;
* `fb-narrow-tall` `(300, 5000)`: contained `false`, width `0`;
* `fb-wide-short` `(5000, 200)`: owner `(1024, 1024, 5000, 200)`,
  caption `(2048, 2048, 2952, 1280)`, contained `false`, width `2952`.

The wide-short row falsifies the repair-(A) disjunction
`Contained or degenerate` as a universal fact: its caption is neither
contained nor degenerate, yet the top-level clearance still holds on the
executed layout (`caps-wide-short`: one outside-scope row,
`meets=false`, cap `(2048, 2048, 2952, 1280)` vs box
`(2500, 4296, 2048, 2304)`, separated vertically by packing).
So containment is not redundant in general, and degeneracy does not cover
every escape: the missing piece is exactly the fixed-size fit premise the
plain pipeline uses (`ownerCaptionContainFallback_of_fit` from `WellFormed`
and `InputFixedFit`). The degenerate-width rows are still explained below by
two pure rect facts (`XCapFb_degenerateWidth_noMeet`,
`XCapFb_degenerateHeight_noMeet`): a zero-width (resp. zero-height) caption
meets no interior, which is why the two named witnesses keep `meets=false`
(`caps-fixed-300x200`, `caps-fixed-0x0`, `caps-fix-desc` descendant row).

This file therefore states the fit-conditioned twin
`X_OwnerCaptionContainFallbackFit` (field for field the tracked
`X_OwnerCaptionContainFallback` plus one `InputFixedFit inp o` premise, the
same shape as the `X_FallbackCaptionClearB8` precedent in
`ExactFlatC8b.lean:102`) and proves the assembled fit-conditioned clearance
`X_captionScopeClearanceFit_holds` from it plus the three unchanged
same-part/title residuals. The fit premise is vacuous exactly where the
witnesses live (their fixed sizes violate the group fit
`2 * clusterPad <= w` and `clusterPad + lineH <= h` at vector
`clusterPad = 1024`, `lineH = 1280`), and it holds with containment on the
fitting probes (`fb-fit-5000` `(5000, 5000)` contained `true`;
`fb-nest-fit` contained `true`; `fb-nofix` fit holds with no fixed entries).

Tracked statements that must gain the fit premise for the family theorems
(`usecase_family_valid_of_exactSeams`, `state_family_valid_of_exactSeams`,
both of which already carry `hfix : InputFixedFit ..`) to consume this:

* `X_CaptionScopeClearance` (`ExactFlatC7.lean:160`): add
  `InputFixedFit inp o` ahead of the execution binder, i.e. adopt
  `X_CaptionScopeClearanceFit` below;
* `FlatC7B` (`RecursiveBLiftsB.lean`): same added premise (its exact
  inhabitant `flatC7B_layoutX` currently takes `hcap` without fit, while the
  base-parametric C7 lift already threads `InputFixedFit` through the
  `captions` seam);
* `ExactSeams.flatC7` (`Kinds/UsecaseValidExact.lean`): point it at the
  fit-conditioned `FlatC7B` form so `exactBaseSeams` can feed `hfix`.

Deep replay route (left open, inventoried here): proving
`X_OwnerCaptionContainFallbackFit` outright replays
`ownerCaptionContainFallback_of_fit` over `SceneExecutionX`. The plain proof
consumes `SceneExecution.boxes_eq_map`, `box_index_origin`,
`fixed_owner_fit`, `fallback_owner_cases`, `ordinary_box_line_height`, and
`parameter_signs`. Of these, only the `boxes_eq_mapX` / `sceneBox_source_rectX`
transport and the `titleRect_contained` / `node_ownedTextRect_contained`
rect glue have exact counterparts today; the exact sizing chain
(`fixed_owner_fit`, `fallback_owner_cases`, `ordinary_box_line_height` over
`SceneExecutionX`) does not exist yet, exactly the gap the file header of
`ExactCaptionScopeProof.lean` records. Until that chain lands, the Fit fact
below stays a hypothesis, in the same way `X_FallbackCaptionClearB8` does.

Residuals kept by `X_captionScopeClearanceFit_holds` (each strictly narrower
than the goal, one fact each, true on every probe row):

* `X_CaptionDescendantSamePartClear`: exercised by `caps-desc`
  (`desc=true`, `title=true`, `meets=false`) and `caps-fix-desc`
  (`desc=true`, `title=false`, degenerate caption, `meets=false`);
* `X_OwnerScopeSamePartClear`: exercised by every `title=false` fallback row
  (`caps-fixed-300x200`, `caps-fixed-0x0`, `caps-fit-5000`,
  `caps-wide-short`, `caps-narrow-tall`, `caps-nest-fit`), all `meets=false`;
* `X_CaptionTitleBranchClear`: exercised by every `title=true` row
  (`caps-empty-title`, `caps-nofix`, both `caps-desc` rows), all
  `meets=false`;
* `X_OwnerCaptionContainFallbackFit`: vacuous on the unfitting rows
  (`300x200`, `0x0`, `wide-short`, `narrow-tall`), direct (`contained=true`)
  on `fb-fit-5000` and `fb-nest-fit`, vacuous-by-antecedent on the
  installed-title rows.
-/

/-- Fit-conditioned X mirror of `OwnerCaptionContainFallback`: field for
field the tracked `X_OwnerCaptionContainFallback`
(`ExactFlatC7CaptionScope.lean:100`) plus the `InputFixedFit inp o`
premise the plain derivation `ownerCaptionContainFallback_of_fit` needs.
Same shape as the `X_FallbackCaptionClearB8` precedent. -/
def X_OwnerCaptionContainFallbackFit (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    InputFixedFit inp o →
    ∀ (ownerIndex : Nat) (obox : ModelBox),
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

/-- Fit-conditioned twin of `X_CaptionScopeClearance`: the tracked
`X_CaptionScopeClearance` (`ExactFlatC7.lean:160`) plus the `InputFixedFit`
premise, i.e. the statement the family theorems (which already carry `hfix`)
can consume once the tracked defs gain the premise. -/
def X_CaptionScopeClearanceFit (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult),
    InputFixedFit inp o →
    ∀ (execution : SceneExecutionX exactIds inp o res)
      (index ownerIndex : Nat) (source : ModelLabel) (lines : List String) (b : Box),
      inp.labels[index]? = some source →
      execution.measured.find? (fun item => item.index == index) = none →
      inp.boxes.findIdx?
        (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
      b ∈ res.scene.layoutDump.boxes →
      b.exclusive = true →
      b.id ∉ res.scene.layoutDump.labelOwnerAnc
        (X_captionLabel exactIds execution ownerIndex source lines) →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
          execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- A zero-width caption rect meets no box interior. Explains the two named
witnesses (`fb-fixed-300x200`, `fb-fixed-0x0`) and the `fb-fix-desc`
descendant row: their fallback captions have width `0`. -/
theorem XCapFb_degenerateWidth_noMeet (cap b : Rect) (hw : cap.w = 0) :
    ¬ cap.meetsInterior b := by
  simp only [Rect.meetsInterior]
  omega

/-- A zero-height caption rect meets no box interior. Covers the empty-text
node-fallback shape (height `(lines.length : Int) * lineH` is `0` when the
owner carries no wrapped lines). -/
theorem XCapFb_degenerateHeight_noMeet (cap b : Rect) (hh : cap.h = 0) :
    ¬ cap.meetsInterior b := by
  simp only [Rect.meetsInterior]
  omega

/-- `XCapFb_` copy of the private `captionScope_findIdx_lookup`
(`CaptionScopeGeometry.lean`): a `findIdx?` hit exposes the box at that
index and its predicate value. Needed for the fallback-branch owner lookup
below; private lemmas do not resolve across modules. -/
private theorem XCapFb_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
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

/-- The fit-conditioned exact caption scope clearance from the four
single-fact residuals: the fallback containment now takes the fit premise,
the descendant / owner-scope same-part cores and the title branch are
unchanged. Replays the `x_captionScopeClearance_holds`
(`ExactFlatC7CaptionScope.lean:180`) case split at the supplied fit, using
the `ExactCaptionScopeProof.lean` same-part transports for the two
frame-separation branches. -/
theorem X_captionScopeClearanceFit_holds (exactIds : List String)
    (hdesc : X_CaptionDescendantSamePartClear exactIds)
    (hcontainFit : X_OwnerCaptionContainFallbackFit exactIds)
    (howners : X_OwnerScopeSamePartClear exactIds)
    (htitle : X_CaptionTitleBranchClear exactIds) :
    X_CaptionScopeClearanceFit exactIds := by
  intro inp o res hfit execution index ownerIndex source lines b hsrc hmeas hfindIdx hmem hex hscope
  have hdescB := XCapScope_captionDescendantClear_of_same_part exactIds hdesc
  have hownB := XCapScope_ownerScopeExclusiveClear_of_same_part exactIds howners
  by_cases hd : source.owner ∈ res.scene.layoutDump.ancestors b.id
  · exact hdescB inp o res execution index ownerIndex source lines b hsrc hmeas hfindIdx
      hmem hex hscope hd
  · simp only [sceneCaptionRect]
    cases hopt : (sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find? (fun title => title.1 == source.owner) with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      have hclr := hownB inp o res execution index ownerIndex source lines b hsrc hmeas
        hfindIdx hmem hex hscope hd hopt
      obtain ⟨_, obox, hobox, hpobox⟩ := XCapFb_findIdx_lookup hfindIdx
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
      have hc := hcontainFit inp o res execution hfit ownerIndex obox hobox hnone hexcl hown
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
