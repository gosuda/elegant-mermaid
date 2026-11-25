import Elegant.Layered.ExactCaptionScopeProof
import Elegant.Layered.ExactFlatC7CaptionScope
import Elegant.Layered.ExactCaptionFallbackProof
import Elegant.Layered.ExactPartFrameCoresProof
import Elegant.Layered.ExactC8aSpansProof
import Elegant.Layered.ExactFlatC8b
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactPipeline
import Elegant.Layered.CaptionScopeGeometry
import Elegant.Layered.InputFixedFit
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC8bFacts
import Elegant.Layered.LabelsClearance
import Elegant.Layered.Pipeline
import Elegant.Layered.SceneBounds
import Elegant.Layered.PlainNodeSizingFacts
import Elegant.Layered.ExecutedLoopPortsFacts
import Elegant.Model

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption fit facts: the per-execution premises of `X_captionScopeClearanceFitW_holds`.

Proves per-execution (`W`) forms of the four leaves of
`X_captionScopeClearanceFitW_holds` (`ExactCaptionScopeFitWProof.lean`).
The title and descendant twins carry local `WellFormed (inputModel inp o)`
and `framedParents inp = true` premises directly after the execution binder;
the containment and owner-scope twins carry the local `WellFormed` premise
(plus `InputFixedFit` for containment), so family theorems discharge them
per executed input instead of over all inputs:

* `x_ownerCaptionContainFallbackFitW_holds`: replay of
  `ownerCaptionContainFallback_of_fit` (`CaptionFallbackContainProof.lean:55`)
  over `SceneExecutionX`, from three narrow exact execution facts
  (fixed-owner fit, fallback-owner cases, ordinary line height).
* `x_captionTitleBranchClearW_holds`: replay of
  `captionTitleBranchClear_of_frames`
  (`CaptionTitleBranchFacts.lean:61`) over `SceneExecutionX`, from the
  W part-local band (`X_TitleSamePartBandXW`, defined below and proved in
  `ExactCaptionBandsProof.lean` from `X_RunTitleBandClearX`) and the
  cross-part plus packed transport premises.
* `x_captionDescendantSamePartClearW_holds`: case split on the installed
  title, title branch by the proved W title fact above, fallback branch by
  the W fallback band (`X_DescendantFallbackBandXW`, defined below and
  proved in `ExactCaptionBandsProof.lean` from the fallback-owner cases).
* `x_ownerScopeSamePartClearW_holds`: replay of the same-part half of
  `ownerScopeSamePartClear_of_fallback` (`CaptionsSeamProof.lean:43`) over
  `SceneExecutionX`, from a local `WellFormed` premise plus the
  fallback-cases residual, via the proved `XS_C8a_PositionsDisjoint_of_run`
  (`ExactC8aSpansProof.lean:1868`) and the in-file
  `x_ownerResNodeBorderZeroX_holds` (plain `ownerRes_node_border_zero` run on
  the measured graph plus `exactGraph_node_key` transport).

Removed 2026-11-19 (`ExactCaptionWCutoverTProbe`): the unconditional
part-local band `X_TitleSamePartBandX` was FALSE (witness `wGroupExclInp`:
group-role exclusive box with an installed title, `BAND-VIOL c=0 posB=0`
over a succeeding `layoutX` run), so it and the holds theorems taking it
(`x_captionTitleBranchClear_holds`,
`x_captionDescendantSamePartClear_holds`) are deleted; the W twins above
are the true forms. The unconditional fallback band
`X_DescendantFallbackBandX` had no falsifier on any probe row but its only
proof needs the admission premises, so it is deleted in favour of its
proved W twin as well. The unguarded installed-title branch
`X_CaptionTitleBranchClear` and descendant clearance
`X_CaptionDescendantSamePartClear` (defined in
`ExactFlatC7CaptionScope.lean` / `ExactCaptionScopeProof.lean`) had no
falsifier (`vacuous` on the group-exclusive witness: no nonexclusive
owner; `descViol=0` on the duplicate-id and dangling rows) and stay
defined where they are; nothing here takes them anymore.

Note on `XF_CaptionRunClearX` (`ExactPartFrameCoresProof.lean:74`): none of the
four conclusions follows from it, so none takes it as a premise. It concludes
a per-run installed-title-vs-frame disjunction (`Disjoint ∨ StrictInside`),
while the targets need frame-frame disjointness (owner scope), pure
`Disjoint` title-vs-exclusive separation (title branch, where the
`StrictInside` alternative would be unsound), scene-caption separation
(descendant), and owner-box containment. The title/descendant branches go
through the part-local band instead, mirroring the plain `TitleSamePartBand`
/ `RunTitleBandClear` route.
-/

/-- `xcf_` copy of the private `captionScope_findIdx_lookup`
(`CaptionScopeGeometry.lean:311`): a `findIdx?` hit exposes the box at that
index and its predicate value. -/
private theorem xcf_findIdx_lookup {α : Type} {p : α → Bool} {l : List α}
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

/-- `xcf_` copy of `SceneExecution.box_index_origin`
(`SizingFacts.lean:846`) over `SceneExecutionX`: the scene box at `index`
comes from the input box at the same index. -/
private theorem xcf_box_index_origin {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) {index : Nat} {box : Box}
    (hbox : res.scene.boxes[index]? = some box) :
    ∃ source, inp.boxes[index]? = some source ∧
      box = Box.mk source.id source.role.id
        (shiftRect execution.params.canvasMargin execution.params.canvasMargin
          (orientRect o.direction execution.packedAcc.canvasH
            (execution.packedAcc.rects.getD index default)))
        source.parent source.exclusive := by
  rw [execution.boxes_eq_mapX] at hbox
  cases hs : inp.boxes[index]? with
  | none => simp [hs] at hbox
  | some source =>
    refine ⟨source, rfl, ?_⟩
    simpa [hs] using hbox.symm

/-- `xcf_` copy of `SceneExecution.parameter_signs`
(`SceneBounds.lean:660`) over `SceneExecutionX`: checked params are
nonnegative in line height and cluster pad. -/
private theorem xcf_parameter_signs {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    0 ≤ execution.params.lineH ∧ 0 ≤ execution.params.clusterPad :=
  ⟨(checkedParams_sizing_nonneg execution.checked).1,
    (checkedParams_sizing_nonneg execution.checked).2.1⟩

/-- `xcf_` copy of the private `node_ownedTextRect_contained`
(`CaptionFallbackContainProof.lean:26`): a node-owner fallback caption is
centred horizontally at full width, so a height fit puts it inside. -/
private theorem xcf_node_ownedTextRect_contained {P : Params} {box : Box}
    {ls : List Measure.Line} (hrole : box.role = "node")
    (hpos : 0 ≤ P.lineH)
    (hf : ((ls.length : Int) * P.lineH) ≤ box.rect.h) :
    box.rect.Contained (ownedTextRect P box ls) := by
  unfold ownedTextRect
  rw [ite_eq_right (by simp [hrole] : ¬((box.role == "group") = true))]
  have hprod : 0 ≤ (ls.length : Int) * P.lineH :=
    Int.mul_nonneg (Int.natCast_nonneg _) hpos
  have hdiff : 0 ≤ box.rect.h - (ls.length : Int) * P.lineH := by
    simpa using hf
  have hfeq : Int.fdiv (box.rect.h - (ls.length : Int) * P.lineH) 2 =
      (box.rect.h - (ls.length : Int) * P.lineH) / 2 :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hhalf_nonneg : 0 ≤ (box.rect.h - (ls.length : Int) * P.lineH) / 2 :=
    Int.ediv_nonneg hdiff (by decide)
  have hhalf_le : (box.rect.h - (ls.length : Int) * P.lineH) / 2 ≤ box.rect.h -
      (ls.length : Int) * P.lineH :=
    Int.ediv_le_self 2 hdiff
  dsimp only
  rw [hfeq]
  show box.rect.x ≤ box.rect.x ∧
    box.rect.x + box.rect.w ≤ box.rect.x + box.rect.w ∧
    box.rect.y ≤ box.rect.y + (box.rect.h - (ls.length : Int) * P.lineH) / 2 ∧
    box.rect.y + (box.rect.h - (ls.length : Int) * P.lineH) / 2 + (ls.length : Int) * P.lineH ≤ box.rect.y + box.rect.h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- `xcf_` lines-length fact: the exact execution lines align with the model
boxes. Same derivation as the plain pipeline (`CaptionFallbackContainProof`
uses `boxLines`/`mapM_getElem?`/`length_zipIdx`). -/
private theorem xcf_lines_length {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hl := execution.lines_eq
  unfold boxLines at hl
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      (mapM_getElem? _ _ _ hl).1
    _ = inp.boxes.length := List.length_zipIdx

/-- Exact mirror of `SceneExecution.fixed_owner_fit`
(`FixedOwnerFit.lean:45`): a fixed-size entry naming a non-exclusive
label-owning box fits that box's exact output rect. Single execution fact,
strictly narrower than the containment goal; true on the fitting probe rows
(`fb-fit-5000`, `fb-nest-fit` contained `true`) and vacuous where the
`InputFixedFit` antecedent fails. -/
def X_FixedOwnerFitX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hfit : InputFixedFit inp o)
    {i : Nat} {box : Box} {source : ModelBox}
    (_hbox : res.scene.boxes[i]? = some box)
    (_hsource : inp.boxes[i]? = some source)
    (_hany : inp.fixedSizes.any (fun e => e.1 == source.id) = true)
    (_hex : source.exclusive = false)
    (_hown : ∃ l ∈ inp.labels, l.owner = source.id),
    FixedSizeFit execution.params source.role (execution.lines.getD i [])
      ⟨box.rect.w, box.rect.h⟩

/-- Exact mirror of `SceneExecution.fallback_owner_cases`
(`CaptionFallbackOwnerProof.lean:63`): an owner with no installed title is a
node-role box or a fixed-size box. Single execution fact, strictly narrower
than the containment goal; true on every probe row (fixed rows discharge via
the fixed disjunct, non-fixed rows via the node disjunct). -/
def X_FallbackOwnerCasesX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o))
    {k : Nat} {obox : ModelBox} (_hbox : inp.boxes[k]? = some obox)
    (_hnone : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none),
    obox.role = .node ∨ inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true

/-- Exact mirror of `SceneExecution.ordinary_box_line_height`
(`SizingCoverageBridge.lean:139`): a non-fixed node box fits its wrapped
lines. Single execution fact, strictly narrower than the containment goal;
true on the probe rows (ordinary node sizing is fixed-size independent). -/
def X_OrdinaryBoxLineHeightX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {index : Nat} {box : Box} (_hbox : res.scene.boxes[index]? = some box)
    {source : ModelBox} (_hsource : inp.boxes[index]? = some source)
    (_hrole : source.role = .node)
    (_hfixed : inp.fixedSizes.any (fun fixed => fixed.1 == source.id) = false)
    {ls : List Measure.Line} (_hline : execution.lines[index]? = some ls),
    (ls.foldl (fun w line => max w line.width) 0) ≤ box.rect.w ∧
      ((ls.length : Int) * execution.params.lineH) ≤ box.rect.h

/-- Fixed-size half of the exact fallback containment: under a fixed-size
entry for the owner, the exact output rect fits the caption by
`X_FixedOwnerFitX`, and the title/node inset contains it. Replays the fixed
branch of `ownerCaptionContainFallback_of_fit`. -/
private theorem xcf_contain_fixed {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hfixed : X_FixedOwnerFitX exactIds)
    (hfit : InputFixedFit inp o)
    {ownerIndex : Nat} {obox : ModelBox} {box : Box}
    (hboxScene : res.scene.boxes[ownerIndex]? = some box)
    (hobox : inp.boxes[ownerIndex]? = some obox)
    (hroleEq : box.role = obox.role.id)
    (hany : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true)
    (hex : obox.exclusive = false)
    (hown : ∃ l ∈ inp.labels, l.owner = obox.id) :
    box.rect.Contained
      (ownedTextRect execution.params box
        (execution.lines.getD ownerIndex [])) := by
  have hfit' := hfixed execution hfit hboxScene hobox hany hex hown
  by_cases hg : obox.role = .group
  · rw [hg] at hfit'
    simp only [FixedSizeFit] at hfit'
    obtain ⟨hgw, hgh⟩ := hfit'
    have hpad : 0 ≤ execution.params.clusterPad :=
      (xcf_parameter_signs execution).2
    have hgroup : box.role = "group" := by
      simp only [hroleEq, hg, BoxRole.id]
    rw [ownedTextRect_group_eq hgroup]
    exact titleRect_contained hpad hgw (Int.le_of_lt hgh)
  · have hroleN : obox.role = .node := by
      cases h : obox.role with
      | node => rfl
      | group => exact absurd h hg
    have hgnode : box.role = "node" := by
      simp only [hroleEq, hroleN, BoxRole.id]
    rw [hroleN] at hfit'
    simp only [FixedSizeFit] at hfit'
    have hpos : 0 ≤ execution.params.lineH :=
      (xcf_parameter_signs execution).1
    exact xcf_node_ownedTextRect_contained hgnode hpos hfit'

/-- Per-execution form of `X_OwnerCaptionContainFallbackFit`: the same
statement with a local `WellFormed (inputModel inp o)` premise directly after
the execution binder, so family theorems discharge it per executed input
instead of over all inputs. -/
def X_OwnerCaptionContainFallbackFitW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) →
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


/-- Per-execution fallback containment, from the narrow residuals only: replay
of `ownerCaptionContainFallback_of_fit` over `SceneExecutionX` with the local
well-formedness premise. No premise over all inputs. -/
theorem x_ownerCaptionContainFallbackFitW_holds (exactIds : List String)
    (hfixed : X_FixedOwnerFitX exactIds)
    (hcases : X_FallbackOwnerCasesX exactIds)
    (hline : X_OrdinaryBoxLineHeightX exactIds) :
    X_OwnerCaptionContainFallbackFitW exactIds := by
  intro inp o res execution hW hfit ownerIndex obox hobox hnone hex hown
  show ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩).rect.Contained
    (ownedTextRect execution.params
      ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩)
      (execution.lines.getD ownerIndex []))
  have hbl : (sceneBoxesExpr execution.params inp o execution.packedAcc).length
      = inp.boxes.length := by
    simp [sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨box, hbox⟩ : ∃ box : Box,
      (sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hboxScene : res.scene.boxes[ownerIndex]? = some box := by
    rw [execution.boxes_eq_mapX]; exact hbox
  have hgetD : (sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = box := by
    rw [List.getD_eq_getElem?_getD, hbox]
    rfl
  rw [hgetD]
  obtain ⟨actual, hactual, hboxeq⟩ := xcf_box_index_origin execution hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hroleEq : box.role = obox.role.id := by rw [hboxeq, hact]
  by_cases hany : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = true
  · exact xcf_contain_fixed execution hfixed hfit hboxScene hobox hroleEq
      hany hex hown
  · have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false :=
      Bool.eq_false_iff.mpr hany
    have hfall := hcases execution hW hobox hnone
    have hroleN : obox.role = .node := by
      rcases hfall with h | h
      · exact h
      · rw [hfixFalse] at h; exact absurd h Bool.false_ne_true
    obtain ⟨ls, hls⟩ : ∃ ls, execution.lines[ownerIndex]? = some ls := by
      have hlinesLen : execution.lines.length = inp.boxes.length :=
        xcf_lines_length execution
      have hi' : ownerIndex < execution.lines.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hi'⟩
    have hfitH :=
      hline execution hboxScene hobox hroleN hfixFalse hls
    have hgetLs : execution.lines.getD ownerIndex [] = ls := by
      rw [List.getD_eq_getElem?_getD, hls]
      rfl
    have hgnode : box.role = "node" := by
      simp only [hroleEq, hroleN, BoxRole.id]
    have hpos : 0 ≤ execution.params.lineH :=
      (xcf_parameter_signs execution).1
    have hf : (((execution.lines.getD ownerIndex []).length : Int) *
        execution.params.lineH) ≤ box.rect.h := by
      rw [hgetLs]; exact hfitH.2
    exact xcf_node_ownedTextRect_contained hgnode hpos hf

/-- Exact mirror of the `ownerRes_node_border_zero` conclusion
(`CaptionResidualsProof.lean:49`): a node-or-fixed owner key is a border-0
node of the exact graph. Single execution fact, strictly narrower than the
owner-scope goal; true on every title-free probe row (owner and foreign keys
both resolve through it). -/
def X_OwnerResNodeBorderZeroX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {key : Nat} {box : ModelBox} (_hbox : inp.boxes[key]? = some box)
    (_hrole : box.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = true)
    (_hlen : key < execution.lines.length),
    ∃ node, execution.graph.nodes[key]? = some node ∧ node.border = 0
/-- Exact node-or-fixed border-zero lookup, proved outright: the plain
`ownerRes_node_border_zero` argument runs on the measured graph
(`execution.graph0_eq`), and `exactGraph_node_key` transports the border-0
node across `exactGraph` preserving the border. -/
theorem x_ownerResNodeBorderZeroX_holds (exactIds : List String) :
    X_OwnerResNodeBorderZeroX exactIds := by
  intro inp o res execution key box hbox hrole hlen
  have hline : execution.lines[key]? = some execution.lines[key] :=
    List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩
  rcases hrole with hnode | hfixedTrue
  · cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
    | none =>
      have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == box.id) = false :=
        List.any_eq_false.mpr (List.find?_eq_none.mp hf)
      obtain ⟨node, hnodeGraph, _, hborder⟩ :=
        measuredGraph_node_border_zero execution.checked execution.graph0_eq
          hline hbox hnode hfalse
      obtain ⟨node', hnode', hborderEq, _, _⟩ :=
        exactGraph_node_key execution.graph_eq hnodeGraph
      exact ⟨node', hnode', by rw [hborderEq]; exact hborder⟩
    | some entry =>
      obtain ⟨_, _, node, _, _, hnodeGraph, hborder, _⟩ :=
        measuredGraph_fixed_loop_reservation execution.graph0_eq
          (List.getElem?_eq_some_iff.mp hline).1 hbox hf
      obtain ⟨node', hnode', hborderEq, _, _⟩ :=
        exactGraph_node_key execution.graph_eq hnodeGraph
      exact ⟨node', hnode', by rw [hborderEq]; exact hborder⟩
  · cases hf : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
    | none =>
      obtain ⟨e, hmem, hid⟩ := List.any_eq_true.mp hfixedTrue
      exact absurd (List.find?_eq_none.mp hf e hmem) (by rw [hid]; decide)
    | some entry =>
      obtain ⟨_, _, node, _, _, hnodeGraph, hborder, _⟩ :=
        measuredGraph_fixed_loop_reservation execution.graph0_eq
          (List.getElem?_eq_some_iff.mp hline).1 hbox hf
      obtain ⟨node', hnode', hborderEq, _, _⟩ :=
        exactGraph_node_key execution.graph_eq hnodeGraph
      exact ⟨node', hnode', by rw [hborderEq]; exact hborder⟩

/-- `xcf_` copy of the private `seam_component_node_lookup`
(`CaptionsSeamProof.lean`): a component position key is the candidate-graph
node at that key. -/
private theorem xcf_seam_component_node_lookup {graph : Graph} {comp : List Nat}
    {cand : Nat} {pos key : Nat} (hkey : comp[pos]? = some key) {node : Node}
    (hnode : graph.nodes[key]? = some node) :
    (componentCandidate graph comp cand).nodes[pos]? = some node := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.getElem?_map, Option.map_some, hkey,
    List.getD_eq_getElem?_getD, hnode, Option.getD_some]

/-- Per-execution form of `X_OwnerScopeSamePartClear`: the same statement
with a local `WellFormed (inputModel inp o)` premise directly after the
execution binder, so family theorems discharge it per executed input instead
of over all inputs. -/
def X_OwnerScopeSamePartClearW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) →
    ∀ (index ownerIndex : Nat)
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
    ∀ (bi k posOwner posB : Nat) (part : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[k]? = some part →
      part.1[posOwner]? = some ownerIndex →
      part.1[posB]? = some bi →
      posOwner ≠ posB →
      ∀ (candidate : Nat) (run : Run),
        componentRunX execution.params (exactDecls exactIds inp)
          (componentCandidate execution.graph part.1 candidate) execution.measured
          (candidateOrder candidate) = .ok run →
        Disjoint
          (frameRect execution.params
            (componentCandidate execution.graph part.1 candidate) run
            posOwner)
          (frameRect execution.params
            (componentCandidate execution.graph part.1 candidate) run
            posB)


/-- Per-execution owner-scope same-part clearance, from the narrow residuals
only: replay of the same-part half of `ownerScopeSamePartClear_of_fallback`
with the local well-formedness premise. No premise over all inputs. -/
theorem x_ownerScopeSamePartClearW_holds (exactIds : List String)
    (hcases : X_FallbackOwnerCasesX exactIds)
    (hnodeB : X_OwnerResNodeBorderZeroX exactIds) :
    X_OwnerScopeSamePartClearW exactIds := by
  intro inp o res execution hW _index ownerIndex source _lines b _hsrc _hmeas
    hfindIdx _hmem hex _hscope _hd hnone bi k posOwner posB part hbi hk
    hposO hposB hne candidate run hrun
  obtain ⟨_, obox, hobox, hpobox⟩ := xcf_findIdx_lookup hfindIdx
  have heq : obox.id = source.owner := by
    have hpred : (obox.id == source.owner && !obox.exclusive) = true := hpobox
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    exact hpred.1
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [heq]
    exact hnone
  have hfall := hcases execution hW hobox hnone'
  have hlinesLen : execution.lines.length = inp.boxes.length :=
    xcf_lines_length execution
  have hOILen : ownerIndex < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hobox).1
  obtain ⟨sb, hsb, _, _, hsbex, _⟩ := sceneBox_source_rectX execution hbi
  have hsbexTrue : sb.exclusive = true := by
    rw [← hsbex]; exact hex
  have hBILen : bi < execution.lines.length := by
    rw [hlinesLen]
    exact (List.getElem?_eq_some_iff.mp hsb).1
  obtain ⟨nodeO, hnodeO, hbO⟩ := hnodeB execution hobox hfall hOILen
  have hngB : sb.role ≠ .group :=
    wellFormed_exclusive_not_group hW (List.mem_of_getElem? hsb)
      hsbexTrue
  have hroleB : sb.role = .node := by
    cases h : sb.role with
    | node => rfl
    | group => exact absurd h hngB
  have hBdisj : sb.role = .node ∨
      inp.fixedSizes.any (fun fixed => fixed.1 == sb.id) = true := Or.inl hroleB
  obtain ⟨nodeB, hnodeB, hbB⟩ := hnodeB execution hsb hBdisj hBILen
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length
        default, false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hmap, _⟩ := actual_components_parts_geometryX hempty
    execution.components_eq
  have hpartMem : part ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hk
  have hcomp : part.1 ∈ components execution.graph := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨part, hpartMem, rfl⟩
  have hnodeOlookup :
      (componentCandidate execution.graph part.1 candidate).nodes[posOwner]? =
        some nodeO := xcf_seam_component_node_lookup hposO hnodeO
  have hnodeBlookup :
      (componentCandidate execution.graph part.1 candidate).nodes[posB]? =
        some nodeB := xcf_seam_component_node_lookup hposB hnodeB
  exact XS_C8a_PositionsDisjoint_of_run execution.graph0_eq
    execution.graph_eq hcomp hrun hnodeOlookup hnodeBlookup hbO hbB hne

/-- Well-formed-local same-part title band: the part-local title/exclusive
disjointness with local admission premises after the execution binder. -/
def X_TitleSamePartBandXW (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (c : Nat) (part : List Nat × Part),
    execution.componentsAcc.parts[c]? = some part →
    ∀ (title : Nat × Rect), title ∈ part.2.titles →
      ∀ (posB : Nat) (k : Nat) (rect : Rect),
        part.1[posB]? = some k →
        part.2.rects[posB]? = some rect →
        ∀ (fBox : ModelBox), inp.boxes[k]? = some fBox →
          fBox.exclusive = true →
          Disjoint rect
            { title.2 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD (part.1.getD title.1 0) [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD (part.1.getD title.1 0) [])).h }

/-- Well-formed-local descendant fallback band: the fallback-caption
disjointness with local admission premises after the execution binder. -/
def X_DescendantFallbackBandXW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    (index ownerIndex bi : Nat)
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
    (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) = none →
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- Exact mirror of the cross-part half `TitleExclusiveCrossPart`
(`CaptionResidualsProof.lean:124`): the packed title caption is disjoint
from the packed rect of the exclusive box when their part indices differ.
The plain def carries an unused `WellFormed` binder; it is dropped here
(the cross-part argument is pure shelf geometry). Single fact, strictly
narrower than the title-branch goal; true on the installed-title probe
rows. Plain path: packed shelf disjointness (`CaptionCrossPartProof`). -/
def X_TitleExclusiveCrossPartX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) (key : Nat)
    (stored : Rect),
    (key, stored) ∈ execution.packedAcc.titles →
    ∀ (k : Nat) (fBox : ModelBox), inp.boxes[k]? = some fBox →
      fBox.exclusive = true →
      ∀ (packed : Pack.State),
        Pack.pack (if o.profile == .cell then o.maxWidth else 0)
          execution.params.nodeGap 0
          (LayoutConst.component_aspect_num.get o.profile)
          (LayoutConst.component_aspect_den.get o.profile)
          (execution.componentsAcc.parts.map fun q =>
            Pack.Item.mk q.2.width q.2.height q.2.area) = .ok packed →
        ∀ (cT : Nat) (partT : List Nat × Part) (boxT : Rect)
          (title : Nat × Rect),
          (execution.componentsAcc.parts.zip packed.boxes)[cT]? =
            some (partT, boxT) →
          title ∈ partT.2.titles →
          key = partT.1.getD title.1 0 →
          stored = shiftRect boxT.x boxT.y title.2 →
          ∀ (cB : Nat) (partB : List Nat × Part) (posB : Nat),
            execution.componentsAcc.parts[cB]? = some partB →
            partB.1[posB]? = some k →
            cT ≠ cB →
            Disjoint (execution.packedAcc.rects.getD k default)
              { stored with
                w := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).w
                h := (titleCaptionSize execution.params o
                  (execution.lines.getD key [])).h }

/-- `xcf_` fold-size fact: packing preserves the rect array size (copy of the
private `X_packFold_rects_size` in `ExactFitClosure.lean`). -/
private theorem xcf_pack_rects_fold_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1
/-- `xcf_` copy of the private `b8_packedAcc_rects_sizeX`
(`ExactFlatC8b.lean:164`): the exact packed rect array matches the model
boxes in size. -/
private theorem xcf_packedAcc_rects_sizeX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width, canvasH := packed.height,
      titles := [] }).rects.size = inp.boxes.length
  rw [xcf_pack_rects_fold_size]
  exact execution.components_rects_size
/-- `xcf_` copy of the private `b8_caption_shift_comm`
(`ExactFlatC8b.lean:121`): the caption resize commutes with the shelf
translation. -/
private theorem xcf_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({shiftRect dx dy stored with w := w, h := h}) =
      shiftRect dx dy {stored with w := w, h := h} := by
  cases stored with
  | mk x y _ _ => rfl

/-- Packed title-vs-exclusive disjointness behind the installed-title branch:
the packed title and the packed exclusive rect live in located parts; equal
indices use the W part-local band `X_TitleSamePartBandXW`, distinct indices
use `X_TitleExclusiveCrossPartX`. Replays the `titleExclusiveSamePart` /
cross-part combination over the exact transport. -/
private theorem xcf_titlePackedDisjointW {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hband : X_TitleSamePartBandXW exactIds)
    (hcross : X_TitleExclusiveCrossPartX exactIds)
    (htransport : X_PackedPartTransportBoundedB8 exactIds)
    {stored : Nat × Rect}
    (hstoredMem : stored ∈ execution.packedAcc.titles)
    {hKey : Nat} {fBox : ModelBox}
    (hKeyBox : inp.boxes[hKey]? = some fBox)
    (hex' : fBox.exclusive = true) :
    Disjoint (execution.packedAcc.rects.getD hKey default)
      { stored.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD stored.1 [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD stored.1 [])).h } := by
  obtain ⟨packed, hpack, hrects, _, htitles, _⟩ := htransport execution
  have hKLEN : hKey < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hKeyBox).1
  have hksize : hKey < execution.packedAcc.rects.size := by
    rw [xcf_packedAcc_rects_sizeX execution]
    exact hKLEN
  obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, _⟩ :=
    hrects hKey hksize (execution.packedAcc.rects.getD hKey default) rfl
  obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, _⟩ :=
    htitles stored.1 stored.2 hstoredMem
  have hgetD : partl.1.getD i 0 = stored.1 := by
    simp only [List.getD, hkeyi, Option.getD_some]
  by_cases hpk : pk = pl
  · subst hpk
    obtain rfl : partk = partl :=
      Option.some.inj (hpartk.symm.trans hpartl)
    obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
    have hclr := hband execution hwf hfp pk partk hpartk (i, stored0) hmeml
      posk hKey r0 hkeyk hr0 fBox hKeyBox hex'
    simp only [hgetD] at hclr
    rw [hreq, hstored, xcf_caption_shift_comm]
    exact disjoint_shiftRect hclr
  · have hzipT : (execution.componentsAcc.parts.zip packed.boxes)[pl]? =
        some (partl, bl) := List.getElem?_zip_eq_some.mpr ⟨hpartl, hbl⟩
    exact hcross execution stored.1 stored.2 hstoredMem hKey fBox hKeyBox hex'
      packed hpack pl partl bl (i, stored0) hzipT hmeml hgetD.symm hstored
      pk partk posk hpartk hkeyk (fun h => hpk h.symm)

/-- Well-formed-local twin of `X_CaptionTitleBranchClear`: the same
installed-title branch with local `WellFormed (inputModel inp o)` and
`framedParents inp = true` premises directly after the execution binder. -/
def X_CaptionTitleBranchClearW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ (index ownerIndex : Nat)
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

/-- The exact installed-title branch, well-formed-local. Replay of
`captionTitleBranchClear_of_frames`
(`CaptionTitleBranchFacts.lean:61`) over `SceneExecutionX`: the scene title
is the transported stored title, the exclusive box is located through
`boxes_eq_mapX`, and the packed disjointness from `xcf_titlePackedDisjointW`
survives the scene transport. -/
theorem x_captionTitleBranchClearW_holds (exactIds : List String)
    (hband : X_TitleSamePartBandXW exactIds)
    (hcross : X_TitleExclusiveCrossPartX exactIds)
    (htransport : X_PackedPartTransportBoundedB8 exactIds) :
    X_CaptionTitleBranchClearW exactIds := by
  intro inp o res execution hwf hfp index ownerIndex source lines b _hsrc _hmeas
    _hfindIdx hmem hex _hscope htitle
  cases hfind : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) with
  | none =>
    rw [hfind] at htitle
    simp at htitle
  | some tsel =>
    have hselMem := List.mem_of_find?_eq_some hfind
    obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hselMem
    cases hbx : inp.boxes[stored.1]? with
    | none => simp only [hbx] at hfeq; cases hfeq
    | some _box0 =>
      simp only [hbx] at hfeq
      have hpair := Option.some.inj hfeq
      have htrect : shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            { stored.2 with
              w := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).w
              h := (titleCaptionSize execution.params o
                (execution.lines.getD stored.1 [])).h }) = tsel.2 :=
        congrArg Prod.snd hpair
      simp only [sceneCaptionRect]
      rw [hfind]
      simp only [Option.map_some, Option.getD_some]
      rw [← htrect]
      simp only [Scene.layoutDump] at hmem
      rw [execution.boxes_eq_mapX] at hmem
      obtain ⟨q, hq, hbeq⟩ := List.mem_map.mp hmem
      obtain ⟨fBox, hKey⟩ := q
      have hKeyBox : inp.boxes[hKey]? = some fBox :=
        List.mem_zipIdx_iff_getElem?.mp hq
      have hex' : fBox.exclusive = true := by
        rw [← hbeq] at hex
        simpa using hex
      rw [← hbeq]
      dsimp only
      have hdp := xcf_titlePackedDisjointW execution hwf hfp hband hcross htransport
        hstoredMem hKeyBox hex'
      exact disjoint_sceneTransport (fun hm => hdp (rect_meetsInterior_comm hm))

/-- Well-formed-local twin of `X_CaptionDescendantSamePartClear`: the same
same-part descendant core with local `WellFormed (inputModel inp o)` and
`framedParents inp = true` premises directly after the execution binder. -/
def X_CaptionDescendantSamePartClearW (exactIds : List String) : Prop :=
  ∀ (inp : Input) (o : Options) (res : FamilyResult)
    (execution : SceneExecutionX exactIds inp o res),
    WellFormed (inputModel inp o) →
    framedParents inp = true →
    ∀ (index ownerIndex bi : Nat)
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
    ∀ (kO kB posO posB : Nat) (partO partB : List Nat × Part),
      res.scene.boxes[bi]? = some b →
      execution.componentsAcc.parts[kO]? = some partO →
      execution.componentsAcc.parts[kB]? = some partB →
      partO.1[posO]? = some ownerIndex →
      partB.1[posB]? = some bi →
      ¬ (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner).meetsInterior b.rect

/-- The exact descendant same-part clearance, well-formed-local. Replay of
`captionDescendantSamePartClear_of_fallback`
(`CaptionResidualsProof.lean:155`) over `SceneExecutionX`: the installed-title
case is the proved W title branch above, the fallback case is the W narrow
band residual. -/
theorem x_captionDescendantSamePartClearW_holds (exactIds : List String)
    (htitle : X_CaptionTitleBranchClearW exactIds)
    (hfall : X_DescendantFallbackBandXW exactIds) :
    X_CaptionDescendantSamePartClearW exactIds := by
  intro inp o res execution hwf hfp index ownerIndex bi source lines b hsrc hmeas
    hfindIdx hmem hex hscope hd kO kB posO posB partO partB hbi hkO hkB
    hposO hposB
  cases hopt : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == source.owner) with
  | none =>
    exact hfall inp o res execution hwf hfp index ownerIndex bi source lines b hsrc
      hmeas hfindIdx hmem hex hscope hd hopt kO kB posO posB partO partB hbi
      hkO hkB hposO hposB

  | some _ =>
    have hsome : ((sceneTitlesExpr execution.params inp o execution.lines
        execution.packedAcc).find?
          (fun title => title.1 == source.owner)).isSome = true := by
      rw [hopt]
      rfl
    exact htitle inp o res execution hwf hfp index ownerIndex source lines b hsrc hmeas
      hfindIdx hmem hex hscope hsome

end PipelineImpl
end Layered
end Elegant
