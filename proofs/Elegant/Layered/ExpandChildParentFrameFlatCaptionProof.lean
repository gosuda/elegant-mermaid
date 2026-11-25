import Elegant.Layered.Pipeline
import Elegant.Layered.ExpandChildParentFrameFlatFactsProof
import Elegant.Layered.SceneBounds
import Elegant.Layered.BoxRouteIdsDisjoint
import Elegant.Layered.InputFixedFit
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.LabelsClearance
import Elegant.Layered.CoordGraph

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-- Private bind inversion for `Except`, mirroring `CoordGraph.bind_ok'`. -/
private theorem pfpBind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {b : β} (h : x >>= f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- Private `findIdx?` element recovery by induction (avoids the exact core
lemma name): a successful search yields the element with a true predicate. -/
private theorem pfpFindIdx?_get {α : Type} {p : α → Bool} {l : List α} {k : Nat}
    (h : l.findIdx? p = some k) : ∃ a, l[k]? = some a ∧ p a = true := by
  induction l generalizing k with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons a as ih =>
    rw [List.findIdx?_cons] at h
    by_cases hp : p a = true
    · rw [ite_eq_left hp] at h
      have hn : k = 0 := (Option.some.inj h).symm
      subst hn
      exact ⟨a, by simp, hp⟩
    · rw [ite_eq_right hp] at h
      obtain ⟨m, hmfind, hmn⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨a', ha', hpa⟩ := ih hmfind
      refine ⟨a', ?_, hpa⟩
      rw [← hmn]
      simpa using ha'

/-! # Flat caption-fit and ancestor-label facts for executed `layout` results

Probe evidence (`proofs/wip/Probe/PfpFlatCaptionTProbe.lean`, 12 inputs under
vector and cell profiles, 24 executed runs, all `.ok`): basic nested, empty
group, zero-size fixed, self-loop, nested groups, empty label text, route-box
id collision, empty box text, huge/tall fixed childless, huge fixed middle,
bad parent. `checkCap` is the scene-level `PfpFlatCaptionFit` conclusion;
`checkAnc` is the scene-level `PfpFlatAncestorLabelClear` conclusion.

`PfpFlatCaptionFit` is FALSE. Witnesses (vector and cell alike):
- `zeroFixed` (well-formed, framed, `fixedSizes = [("x", <0, 0>)]`): caption
  `lx = (1602, 384, 1024, 1280)` is not contained in owner box
  `x = (1602, 1024, 1024, 0)`. Excluded by `InputFixedFit` (`FixedSizeFit`
  for `.node` needs `(1) * 1280 <= 0`; `lineH = 1280` by `#eval`).
- `collide` (well-formed, framed, no fixed sizes): route label
  `l1 = (1024, 5632, 4786, 1280)` owned by `"e1"` is not contained in node
  box `"e1" = (2195, 1024, 2445, 2304)`. Excluded by `BoxRouteIdsDisjoint`.
- `emptyBoxText` (well-formed, framed, fitted, disjoint): captions are
  contained but degenerate, `lx = (2560, 7040, 2048, 0)` and
  `lG = (3584, 2048, 0, 1280)`, because `StyledMeasure.wrap` of `""` is `[]`
  (by `#eval`). Excluded by the wrapped-lines positivity premise below.
`wrap "x"` is one line of width `510` and `wrap "gt"` one line of width `877`.

`PfpFlatAncestorLabelClear` holds on all 24 runs (zero `ANC-VIOL`), including
the ill-formed `badParent` run. Its narrower form below adds the consumer
premises so the flat placement consumer can use it; the missing band fact
stays as the one residual `PfpFlatAncestorLabelDisjointPos`.

Narrower forms (`...Need`) carry the consumer premises of
`pfpFlatBoxClearNarrow_of_flat` / `pfpFlatTitleClear_of_flat` (`hlay`, `hwf`,
`hfp`, `hfit`) plus `BoxRouteIdsDisjoint` (from the recursive context's
`BoxRouteIdsDisjoint inp`) and wrapped-lines positivity, all local to the
executed run. No whole seam record is taken; no other premise is needed.
-/

/-- Narrow caption fit: the consumer conclusion (owner containment plus
positive size) under the consumer premises plus disjointness and
wrapped-lines positivity. Probe-true: violations occur only on `zeroFixed`
(`InputFixedFit` fails), `collide` (`BoxRouteIdsDisjoint` fails), and
`emptyBoxText` (no positive-width wrapped line). -/
def PfpFlatCaptionFitNeed : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → BoxRouteIdsDisjoint inp →
    0 < execution.params.lineH →
    (∀ (i : Nat), i < inp.boxes.length →
      ∃ line ∈ execution.lines.getD i [], 0 < line.width) →
    ∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
    b.id = pl.owner →
    b.rect.Contained pl.rect ∧ 0 < pl.rect.w ∧ 0 < pl.rect.h

/-- The one caption residual: the `sceneOf` caption rect at each labelled
non-exclusive owner index is contained in its scene box with positive size.
This is the scene-level `checkCap` fact at construction granularity; the
holds-theorem lifts it through `label_source_split` to scene labels. -/
def PfpFlatCaptionSceneFit : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → BoxRouteIdsDisjoint inp →
    0 < execution.params.lineH →
    (∀ (i : Nat), i < inp.boxes.length →
      ∃ line ∈ execution.lines.getD i [], 0 < line.width) →
    ∀ (ownerIndex : Nat) (obox : ModelBox),
    inp.boxes[ownerIndex]? = some obox → obox.exclusive = false →
    (∃ l ∈ inp.labels, l.owner = obox.id) →
    ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩).rect.Contained
      (sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex obox.id) ∧
    0 < (sceneCaptionRect execution.params inp o execution.lines
      execution.packedAcc ownerIndex obox.id).w ∧
    0 < (sceneCaptionRect execution.params inp o execution.lines
      execution.packedAcc ownerIndex obox.id).h
/-- Narrow ancestor clearance: an ancestor-owned label is never strictly
inside a descendant frame, under the consumer premises plus disjointness
context. Probe-true on all 24 runs (`checkAnc` has zero violations even on
the ill-formed `badParent` run). -/
def PfpFlatAncestorLabelClearNeed : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → BoxRouteIdsDisjoint inp →
    0 < execution.params.lineH →
    (∀ (i : Nat), i < inp.boxes.length →
      ∃ line ∈ execution.lines.getD i [], 0 < line.width) →
    ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
    ∀ b ∈ res.scene.boxes, b.id = pl.owner →
    b.id ∈ res.scene.layoutDump.ancestors G.id →
    ¬ frame.rect.StrictInside pl.rect

/-- The one ancestor residual: an ancestor-owned label is disjoint from the
descendant frame with positive size, which implies the clearance above (a
positive rect strictly inside would meet the frame interior). Probe
(`checkAncDisj`): `disj` holds on every probed pair; `pos` fails only on
`emptyBoxText`, where the wrapped-lines premise is false. -/
def PfpFlatAncestorLabelDisjointPos : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → framedParents inp = true →
    InputFixedFit inp o → BoxRouteIdsDisjoint inp →
    0 < execution.params.lineH →
    (∀ (i : Nat), i < inp.boxes.length →
      ∃ line ∈ execution.lines.getD i [], 0 < line.width) →
    ∀ (G : ModelBox) (frame : Box),
    res.scene.boxes.find? (fun box => box.id == G.id) = some frame →
    ∀ pl ∈ res.scene.labels, pl.owner ≠ G.id →
    ∀ b ∈ res.scene.boxes, b.id = pl.owner →
    b.id ∈ res.scene.layoutDump.ancestors G.id →
    Disjoint frame.rect pl.rect ∧ 0 < pl.rect.w ∧ 0 < pl.rect.h

/-- The ancestor clearance holds from its disjointness residual. -/
theorem pfpFlatAncestorLabelClear_holds (h : PfpFlatAncestorLabelDisjointPos) :
    PfpFlatAncestorLabelClearNeed := by
  intro inp o res execution hlay hwf hfp hfit hdisj hlineH hlines G frame hframe pl hpl hown b hbmem heq hrel
  obtain ⟨hdis, hpw, hph⟩ := h execution hlay hwf hfp hfit hdisj hlineH hlines G frame hframe pl hpl hown b hbmem heq hrel
  intro hS
  have hmeet : frame.rect.meetsInterior pl.rect := by
    unfold Rect.meetsInterior
    obtain ⟨fx1, fx2, fy1, fy2⟩ := hS
    constructor <;> omega
  exact hdis hmeet

/-- Gap (to prove from `measured_eq` and the `measureLabels` construction): a
measured scene label is owned by a route, which contradicts disjointness when
a scene box carries the same id. -/
private def PfpFlatCaptionMeasuredGap : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) → BoxRouteIdsDisjoint inp →
    ∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
    ∀ (source : ModelLabel) (index : Nat),
    inp.labels[index]? = some source → pl.owner = source.owner →
    b.id = source.owner →
    execution.measured.find? (fun item => item.index == index) ≠ none → False

/-- The measured case is impossible under disjointness: a measured entry
comes from a route-owned model label, so its owner cannot also name a box. -/
private theorem pfpFlatCaptionMeasuredGap_holds : PfpFlatCaptionMeasuredGap := by
  intro inp o res execution hlay hwf hdisj pl hpl b hbmem source index hsrc hown
    howner hne
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists.mp hne
  have hm' : execution.measured.find? (fun item => item.index == index) =
      some m := hm.symm
  have hmem : m ∈ execution.measured := List.mem_of_find?_eq_some hm'
  have hidxeq : m.index = index := by
    simpa using List.find?_some hm'
  obtain ⟨options, ho, hfm⟩ := pfpBind_ok execution.measured_eq
  have hfm' : options.filterMap id = execution.measured := Except.ok.inj hfm
  have hmem' : m ∈ options.filterMap id := by rw [hfm']; exact hmem
  obtain ⟨opt, hopt, hlb⟩ := List.mem_filterMap.mp hmem'
  have he : opt = some m := by simpa using hlb
  have hopt' : some m ∈ options := by rw [he] at hopt; exact hopt
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hopt'
  have hil : i < options.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hlen, hidx⟩ := mapM_getElem? _ _ _ ho
  have his : i < inp.labels.zipIdx.length := by rw [← hlen]; exact hil
  have hget : inp.labels.zipIdx[i]? =
      some (inp.labels[i]'(by simpa using his), i) := by
    simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem (by simpa using his),
      Nat.zero_add, Option.map_some]
  obtain ⟨result, hr, hresult⟩ := hidx i _ hget
  rw [hi] at hresult
  have hrl : result = some m := (Option.some.inj hresult).symm
  subst hrl
  split at hr
  · cases hr
  · next edge heq =>
    obtain ⟨lines, hwrap, hpure⟩ := pfpBind_ok hr
    by_cases hover :
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 ∨
        I32_MAX < (lines.length : Int) * execution.params.lineH ∨
        I32_MAX < lines.foldl (fun w line => max w line.width) 0 +
          (if (execution.metric.profile == .cell) = true then execution.params.slot else 0) ∨
        I32_MAX < (lines.length : Int) * execution.params.lineH +
          (if (execution.metric.profile == .cell) = true then execution.params.slot else 0)
    · simp only [hover, ↓reduceIte] at hpure
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hpure
    · simp only [hover, ↓reduceIte] at hpure
      have hmk : MeasuredLabel.mk i edge (inp.labels[i]'(by simpa using his))
          lines _ _ _ = m :=
        Option.some.inj (Except.ok.inj hpure)
      have hmi : m.index = i := congrArg MeasuredLabel.index hmk.symm
      have hi_eq : i = index := hmi.symm.trans hidxeq
      clear hmi hidxeq
      subst i
      have hilen : index < inp.labels.length :=
        (List.getElem?_eq_some_iff.mp hsrc).1
      have h1 : inp.labels[index]? = some inp.labels[index] :=
        List.getElem?_eq_getElem hilen
      rw [h1] at hsrc
      have hli : inp.labels[index] = source := Option.some.inj hsrc
      rw [hli] at heq
      obtain ⟨r, hrget, hrpred⟩ := pfpFindIdx?_get heq
      have hrid : r.id = source.owner := beq_iff_eq.mp hrpred
      have hrmem : r ∈ inp.routes := List.mem_iff_getElem?.mpr ⟨edge, hrget⟩
      have hrmap : source.owner ∈ inp.routes.map (·.id) :=
        List.mem_map.mpr ⟨r, hrmem, hrid⟩
      rw [execution.boxes_eq_map] at hbmem
      obtain ⟨q, hqmem, hbeq⟩ := List.mem_map.mp hbmem
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hqmem
      have hjlen : j < inp.boxes.zipIdx.length :=
        (List.getElem?_eq_some_iff.mp hj).1
      have hjlen' : j < inp.boxes.length := by
        simpa using hjlen
      have hj2 : inp.boxes.zipIdx[j]? =
          some (inp.boxes[j]'hjlen', j) := by
        simp only [List.getElem?_zipIdx, List.getElem?_eq_getElem hjlen',
          Nat.zero_add, Option.map_some]
      rw [hj2] at hj
      have hq1 : q.1 = inp.boxes[j]'hjlen' :=
        (congrArg Prod.fst (Option.some.inj hj)).symm
      have hqb : q.1 ∈ inp.boxes :=
        List.mem_iff_getElem?.mpr ⟨j, by rw [hq1]; exact List.getElem?_eq_getElem hjlen'⟩
      have hqid : q.1.id = b.id := congrArg Box.id hbeq
      have hboxmap : b.id ∈ inp.boxes.map (·.id) := by
        have hmemid : q.1.id ∈ inp.boxes.map (·.id) :=
          List.mem_map.mpr ⟨q.1, hqb, rfl⟩
        rw [hqid] at hmemid
        exact hmemid
      rw [howner] at hboxmap
      exact hdisj source.owner hboxmap hrmap
/-- Gap (to prove by replaying the `sceneOf` filterMap identification in
`sceneCaptionBoxContainment` at the caption branch): rect equations for the
unmeasured branch plus the owner-index model box facts the residual needs. -/
def PfpFlatCaptionIdentGap : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res),
    layout inp o = .ok res →
    WellFormed (inputModel inp o) →
    ∀ pl ∈ res.scene.labels, ∀ b ∈ res.scene.boxes,
    ∀ (source : ModelLabel) (index ownerIndex : Nat),
    inp.labels[index]? = some source → pl.id = source.id →
    pl.owner = source.owner →
    b.id = source.owner →
    execution.measured.find? (fun item => item.index == index) = none →
    inp.boxes.findIdx?
      (fun box => box.id == source.owner && !box.exclusive) = some ownerIndex →
    ∃ obox : ModelBox, inp.boxes[ownerIndex]? = some obox ∧
      obox.id = source.owner ∧ obox.exclusive = false ∧
      (∃ l ∈ inp.labels, l.owner = obox.id) ∧
      pl.rect = sceneCaptionRect execution.params inp o execution.lines
        execution.packedAcc ownerIndex source.owner ∧
      b.rect = ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
        ownerIndex ⟨"", "", default, "", false⟩).rect

/-- The single remaining caption residual: the scene-level fit together with
the caption-branch identification gap. Both are quantified over executed runs
only and are probe-true on all 24 runs of `PfpFlatCaptionTProbe.lean`
(`#eval runAll` under vector and cell profiles, `#eval showWrapFit` for the
wrap/line-height witnesses cited in the header). -/
def PfpFlatCaptionFitResidual : Prop :=
  PfpFlatCaptionSceneFit ∧ PfpFlatCaptionIdentGap
/-- The narrow caption fit holds from its one named residual. -/
theorem pfpFlatCaptionFit_holds (h : PfpFlatCaptionFitResidual) :
    PfpFlatCaptionFitNeed := by
  obtain ⟨hScene, hIdent⟩ := h
  intro inp o res execution hlay hwf hfp hfit hdisj hlineH hlinesW pl hpl b hbmem heq
  obtain ⟨source, index, hsrc, _, hlid, hown, hor⟩ :=
    label_source_split execution hpl
  have howner : b.id = source.owner := heq.trans hown
  cases hor with
  | inl hmeasured =>
    obtain ⟨m, hm⟩ := hmeasured
    exact False.elim (pfpFlatCaptionMeasuredGap_holds execution hlay hwf hdisj
      pl hpl b hbmem source index hsrc hown howner
      (Option.ne_none_iff_exists.mpr ⟨m, hm.symm⟩))
  | inr hnone =>
    obtain ⟨hmnone, ownerIndex, hfind⟩ := hnone
    obtain ⟨obox, hobox, hid, hexcl, hlabel, hrect, hbox⟩ :=
      hIdent execution hlay hwf pl hpl b hbmem source index ownerIndex hsrc
        hlid hown howner hmnone hfind
    have hfit := hScene execution hlay hwf hfp hfit hdisj hlineH hlinesW ownerIndex
      obox hobox hexcl hlabel
    rw [hrect, hbox] at ⊢
    rw [hid] at hfit
    exact hfit
end Elegant.Layered.PipelineImpl
