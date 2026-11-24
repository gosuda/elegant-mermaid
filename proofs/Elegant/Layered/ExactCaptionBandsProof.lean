import Elegant.Layered.ExactCaptionTitleBranchProof
import Elegant.Layered.ExactCaptionSamePartProof
import Elegant.Layered.ExactCaptionFitFactsProof
import Elegant.Layered.ExactRunTitleBandClosedProof
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC7
import Elegant.Layered.ExactPipeline
import Elegant.Layered.Pipeline
import Elegant.Layered.LabelsC8b
import Elegant.Layered.LabelsC7Captions
import Elegant.Layered.SceneBounds
import Elegant.Layered.RankSiblingDisjoint
import Elegant.Layered.PipelineFacts
import Elegant.Layered.RecursiveC2
import Elegant.Layered.CgShape
import Elegant.Layered.CoordGraph
import Elegant.Model

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open Elegant Layered

/-! # Exact caption band facts (`X_TitleSamePartBandXW`, `X_DescendantFallbackBandXW`).

Two W residuals for the caption seam workers (cut over 2026-11-19: the
unconditional bands are deleted in `ExactCaptionFitFactsProof.lean`):

* `X_TitleSamePartBandXW`: the W same-part band of an installed title
  branch (the `capTitle` seam field needs it via
  `xctb_captionTitleBranchClearW_of_bandW`).
* `X_DescendantFallbackBandXW`: the W same-part band of a descendant
  fallback caption (the `capDesc` seam field needs it via
  `x_captionDescendantSamePartClearW_holds`).

Probe evidence (`proofs/wip/Probe/TitleBandTProbe.lean`, vector profile,
`layoutX [] inp tOpts` recompute; owner box `box=(w,h)`, fallback
caption `cap=(w,h)`):

* title band: zero part-level violations on the eight well-formed inputs
  (`tb-fit-5000`, `tb-fixed-0x0`, `tb-nest-fit`, `tb-empty-title`,
  `tb-nofix`, `tb-self-loop`, `tb-dup-id`, `tb-empty-group` all report
  `title-band ok`; the ill-formed `tb-dup-id` row recomputes without error
  and contributes no titles).
* run band: zero run-level violations on all nine inputs
  (`rb-fit-5000` through `rb-empty-group` plus `rb-group-excl` all report
  `run-band ok`, over executed candidate indices `0-4`): the border-0
  gate excludes the group-exclusive node, so the run residual holds even
  on the witness below.
  (`fb-fit-5000` two boxes no titles, `cap=l1 owner=g box=x hit=false`;
  `fb-fixed-0x0` same with `hit=false`; `fb-nest-fit` three boxes one title,
  `cap=l1 owner=h box=x hit=false`; installed-title rows `fb-empty-title`,
  `fb-nofix`, `fb-self-loop`, `fb-dup-id`, `fb-empty-group` carry titles so
  the fallback conclusion holds vacuously).

Falsity witness for the unconditional title band: `tGroupExclInp`
(flowchart, group-role box `g` with `exclusive := true`, exclusive node
`x`, label `l1` owned by `g`) reports `tb-group-excl VIOL c=0 posB=0`
(scene check `sb-group-excl: boxes=2 titles=[g] labels=[]`, so the
installed-title branch is active on the witness). Hence the unconditional
`X_TitleSamePartBandX` is false as stated; the `WellFormed` premise is
load-bearing (`wellFormed_exclusive_not_group` rules out exactly the
witness shape). An unconditional reduction is therefore not the correct
target; the W form below is the true form the consumer needs. The
unconditional fallback band is not falsified on any probe row, but its
only available proof (vacuity via `Model.boxIds_nodup` and
`framedParents_parent`) essentially needs the same premises; the plain
`DescendantFallbackClear` (`CaptionResidualsProof.lean`) already carries
`_hwf`/`_hfp` binders, so the W form restores parity there as well.

What closes here:

* `X_DescendantFallbackBandXW`: the W form of the fallback band, proved
  from the strictly narrower `X_FallbackOwnerCasesX` (owner-role
  classification) by the vacuity argument of
  `descendantFallbackClear_vacuous` (`xcb_descendantFallbackBandXW_holds`).
* `X_TitleSamePartBandXW`: the W form of the title band, proved from the
  narrower `X_RunTitleBandClearXW` by replaying `titleSamePartBand_of_runBand`
  over the same `SceneExecutionX` and admission premises
  (`xcb_titleSamePartBandXW_of_runX`). The run-level band is proved by
  `x_runTitleBandClearXW_holds` in `ExactRunTitleBandClosedProof.lean`.

The bridge does not require the unconditional `X_RunTitleBandClearX`.
The unconditional part bands are deleted
(the title band was false as stated; the fallback band had no proof
without the admission premises); their W twins are defined in
`ExactCaptionFitFactsProof.lean` and proved here from the strictly
narrower residuals. The seam consumers are cut over to those W bands:
`xctb_captionTitleBranchClearW_of_bandW`
(`ExactCaptionTitleBranchProof.lean`) and
`x_captionDescendantSamePartClearW_holds`
(`ExactCaptionFitFactsProof.lean`).
-/

/-- Exact run-level title band: the stored title caption misses every
exclusive plain frame of the same exact run. Strictly narrower than
the (deleted) unconditional `X_TitleSamePartBandX` (one `componentRunX`
phase, no placement, packing, or part-index reasoning); true on every
probe row (`rb-*` all `run-band ok`, including the group-exclusive
witness, whose node is excluded by the border-0 gate). -/
def X_RunTitleBandClearX (exactIds : List String) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions},
    componentRunX execution.params (exactDecls exactIds inp)
      (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run →
    ∀ {v : Nat} {nd : Node},
    (componentCandidate execution.graph comp candidate).nodes[v]? = some nd →
    nd.border = -2 →
    ∀ (raw : Nat × Rect),
    raw ∈ componentTitles execution.params
      (componentCandidate execution.graph comp candidate) run →
    raw.1 = v →
    ∀ {w : Nat} {nodeW : Node} {k : Nat} {fBox : ModelBox},
    (componentCandidate execution.graph comp candidate).nodes[w]? = some nodeW →
    nodeW.border = 0 →
    comp[w]? = some k →
    inp.boxes[k]? = some fBox →
    fBox.exclusive = true →
    Disjoint (frameRect execution.params
      (componentCandidate execution.graph comp candidate) run w)
      { raw.2 with
        w := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).w
        h := (titleCaptionSize execution.params o
          (execution.lines.getD (comp.getD raw.1 0) [])).h }

/-- `xcb_` copy of the private `bind_ok` (`ExactFlatC7.lean`): splitting an
`Except.bind` success exposes the intermediate value. -/
private theorem xcb_bind_ok {α β : Type} {x : Except LayoutError α} {f : α → Except LayoutError β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- `xcb_` copy of the private `captionScope_findIdx_lookup`
(`CaptionScopeGeometry.lean`): a `findIdx?` hit exposes the box at that
index and its predicate value. -/
private theorem xcb_findIdx_lookup {α : Type} {p : α → Bool}
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

/-- `xcb_` copy of the private `fallback_ancestors_parent`
(`CaptionFallbackOwnerProof.lean`): an ancestor membership yields a dumped
box parented at the ancestor with a nonempty ancestor name. -/
private theorem xcb_ancestors_parent (d : LayoutDump) :
    ∀ (fuel : Nat) (s x : String), x ∈ LayoutDump.ancestors.go d fuel s →
      ∃ c ∈ d.boxes, c.parent = x ∧ x ≠ "" := by
  intro fuel
  induction fuel with
  | zero => intro s x hx; cases hx
  | succ fuel ih =>
    intro s x hx
    have hgo : LayoutDump.ancestors.go d (fuel + 1) s =
        match d.box? s with
        | none => []
        | some b => if b.parent = "" then []
                    else b.parent :: LayoutDump.ancestors.go d fuel b.parent := rfl
    rw [hgo] at hx
    cases hs : d.box? s with
    | none => rw [hs] at hx; cases hx
    | some b =>
      rw [hs] at hx
      simp only at hx
      split at hx
      · cases hx
      · rename_i hpar
        rcases List.mem_cons.mp hx with heq | hx
        · refine ⟨b, ?_, heq.symm, ?_⟩
          · unfold LayoutDump.box? at hs
            exact List.mem_of_find?_eq_some hs
          · rw [heq]
            exact hpar
        · obtain ⟨c, hcMem, hcParent, hxNe⟩ := ih b.parent x hx
          exact ⟨c, hcMem, hcParent, hxNe⟩

/-- `xcb_` lines-length fact: the exact execution lines align with the model
boxes (same derivation as `xcf_lines_length` in `ExactCaptionFitFactsProof`). -/
private theorem xcb_lines_length {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res) :
    execution.lines.length = inp.boxes.length := by
  have hl := execution.lines_eq
  unfold boxLines at hl
  calc execution.lines.length = (inp.boxes.zipIdx).length :=
      (mapM_getElem? _ _ _ hl).1
    _ = inp.boxes.length := List.length_zipIdx

/-- `xcb_` exclusive border-zero lookup: a well-formed exclusive model box
is a border-0 node of the exact graph (measured lookup, then `exactGraph`
key preservation). -/
private theorem xcb_exclusive_border_zeroX {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hwf : WellFormed (inputModel inp o))
    {k : Nat} {fBox : ModelBox} (hbox : inp.boxes[k]? = some fBox)
    (hex : fBox.exclusive = true)
    (hlen : k < execution.lines.length) :
    ∃ node, execution.graph.nodes[k]? = some node ∧ node.border = 0 := by
  have hrole : fBox.role ≠ .group :=
    wellFormed_exclusive_not_group hwf (List.mem_of_getElem? hbox) hex
  have hline : execution.lines[k]? = some execution.lines[k] :=
    List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩
  obtain ⟨node0, hnode0, hborder0⟩ :=
    measuredGraph_exclusive_node_border_zero execution.checked
      execution.graph0_eq hline hbox hrole
  obtain ⟨node, hnode, hborder, _, _⟩ :=
    exactGraph_node_key execution.graph_eq hnode0
  exact ⟨node, hnode, hborder.trans hborder0⟩

/-- `xcb_` copy of the private `placeComponentExact_rects_get`
(`ExactFlatFacts.lean`): the placed rect of component position `i` is the
run's frame rectangle shifted by the exact placement origin. -/
private theorem xcb_placeComponentExact_rects_get {P : Params} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)}
    {cursor : Int} {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- `xcb_` copy of the private `xpr_placeComponentExact_titles_eq`
(`ExactPackedTransportResidualsProof.lean`): exact placed-component titles
are the shared `componentTitles` shifted by the exact placement bounds. -/
private theorem xcb_placeComponentExact_titles_eq (P : Params) (cg : Graph) (run : Run)
    (labels : List MeasuredLabel) (loops : List (Nat × LoopPlacement)) :
    (placeComponentExact P cg run 0 labels loops).titles =
      (componentTitles P cg run).map (fun q =>
        (q.1, shiftRect (0 - (placeBoundsX P cg run labels loops).minX)
          (-(placeBoundsX P cg run labels loops).minY) q.2)) := by
  simp only [placeComponentExact, placeBoundsX]

/-- `xcb_` copy of `shiftRect_disjoint_of` (`RecursiveC2.lean`): a shared
translation preserves rect disjointness. -/
private theorem xcb_shiftRect_disjoint {a b : Rect} {dx dy : Int}
    (h : Disjoint a b) : Disjoint (shiftRect dx dy a)
      (shiftRect dx dy b) :=
  shiftRect_disjoint_of dx dy h

/-- `xcb_` copy of the private `b8_caption_shift_comm` (`ExactFlatC8b.lean`):
the caption resize commutes with the shelf translation. -/
private theorem xcb_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({shiftRect dx dy stored with w := w, h := h}) =
      shiftRect dx dy {stored with w := w, h := h} := by
  cases stored with
  | mk x y _ _ => rfl

/-- The W fallback band from the fallback-owner cases: under a local
well-formedness and framed-parents premise, the owner with no installed
title is a node-or-fixed box, yet an exclusive descendant forces the owner
to be a non-fixed group parent — a contradiction, so the band holds
vacuously. Replays `descendantFallbackClear_vacuous`
(`CaptionFallbackOwnerProof.lean`) over `SceneExecutionX`. -/
theorem xcb_descendantFallbackBandXW_of_cases (exactIds : List String)
    (hcases : X_FallbackOwnerCasesX exactIds) :
    X_DescendantFallbackBandXW exactIds := by
  intro inp o res execution hwf hfp index ownerIndex _bi source _lines b
    _hsrc _hmeas hfindIdx _hmem _hex _hscope hd hnone _kO _kB _posO _posB
    _partO _partB _hbi _hkO _hkB _hposO _hposB
  exfalso
  obtain ⟨_, obox, hobox, hpobox⟩ := xcb_findIdx_lookup hfindIdx
  have hpred : (obox.id == source.owner && !obox.exclusive) = true := hpobox
  simp only [Bool.and_eq_true] at hpred
  have hoboxId : obox.id = source.owner := beq_iff_eq.mp hpred.1
  have hnone' : (sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none := by
    rw [hoboxId]
    exact hnone
  have hfall := hcases execution hwf hobox hnone'
  have hmemAnc : source.owner ∈ LayoutDump.ancestors.go res.scene.layoutDump
      res.scene.layoutDump.boxes.length b.id := hd
  obtain ⟨c, hcMem, hcParent, hxNe⟩ :=
    xcb_ancestors_parent res.scene.layoutDump
      res.scene.layoutDump.boxes.length b.id source.owner hmemAnc
  have hcScene : c ∈ res.scene.boxes := by
    simpa [Scene.layoutDump] using hcMem
  obtain ⟨jc, hjc⟩ := List.mem_iff_getElem?.mp hcScene
  obtain ⟨child, hchildGet, _, hparentEq, _, _⟩ :=
    sceneBox_source_rectX execution hjc
  have hchildMem : child ∈ inp.boxes := List.mem_of_getElem? hchildGet
  have hchildParent : child.parent = source.owner := hparentEq.symm.trans hcParent
  have hchildNe : child.parent ≠ "" := by
    rw [hchildParent]
    exact hxNe
  obtain ⟨parentBox, hparentMem, hparentId, hparentRole, hparentFixed⟩ :=
    framedParents_parent hfp hchildMem hchildNe
  have hids := Model.boxIds_nodup hwf
  have ha : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
    simp [List.getElem?_map, hobox]
  obtain ⟨pi, hpi⟩ := List.mem_iff_getElem?.mp hparentMem
  have hb : (inp.boxes.map (·.id))[pi]? = some parentBox.id := by
    simp [List.getElem?_map, hpi]
  have heq : obox.id = parentBox.id := hoboxId.trans (hparentId.trans hchildParent).symm
  have hlookups : (inp.boxes.map (·.id))[ownerIndex]? =
      (inp.boxes.map (·.id))[pi]? := by
    rw [ha, hb, heq]
  have hbound : ownerIndex < (inp.boxes.map (·.id)).length :=
    (List.getElem?_eq_some_iff.mp ha).1
  have hidxEq : ownerIndex = pi := (List.Nodup.getElem?_inj hbound hids).mp hlookups
  have hboxEq : obox = parentBox := by
    have hsame : inp.boxes[ownerIndex]? = inp.boxes[pi]? := by rw [hidxEq]
    rw [hobox, hpi] at hsame
    exact Option.some.inj hsame
  have hroleGroup : obox.role = .group := by
    rw [hboxEq]
    exact hparentRole
  have hfixFalse : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false := by
    rw [hboxEq]
    exact hparentFixed
  rcases hfall with hnode | hfixedTrue
  · rw [hroleGroup] at hnode
    contradiction
  · rw [hfixFalse] at hfixedTrue
    exact absurd hfixedTrue Bool.false_ne_true

/-- The W title band from the run-level band: equal part indices give one
exact run, so both part rects are the same placement shift of the run-level
rects and the shift preserves the band disjointness. Replays
`titleSamePartBand_of_runBand` (`CaptionSamePartProof.lean`) over
`SceneExecutionX`. -/
theorem xcb_titleSamePartBandXW_of_runX (exactIds : List String)
    (hrun : X_RunTitleBandClearXW exactIds) :
    X_TitleSamePartBandXW exactIds := by
  intro inp o res execution hwf hfp _c part hpart title htitle posB k rect hpos
    hrect fBox hbox hex
  have hpartmem : part ∈ execution.componentsAcc.parts :=
    List.mem_of_getElem? hpart
  have hlinesLen : execution.lines.length = inp.boxes.length :=
    xcb_lines_length execution
  obtain ⟨index, run, loops, area, hcomp, hrunEx, hpartdef⟩ :=
    X_execution_part_run execution hpartmem
  have ht2 : title ∈ (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured
      loops).titles := by
    have h2 := htitle
    rw [hpartdef] at h2
    exact h2
  rw [xcb_placeComponentExact_titles_eq] at ht2
  obtain ⟨raw, hraw, heTitle⟩ := List.mem_map.mp ht2
  have htitle1 : raw.1 = title.1 := by rw [← heTitle]
  have htitle2 : shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured
      loops).minX)
    (-(placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured
      loops).minY) raw.2 = title.2 := by rw [← heTitle]
  obtain ⟨top, htopmem, htopborder, htopidx, _, _⟩ :=
    componentTitles_dimension_source execution.params _ _ hraw
  have htopnode : (componentCandidate execution.graph part.1 index).nodes[top.2]? =
      some top.1 :=
    List.mem_zipIdx_iff_getElem?.mp htopmem
  have hcgLen : (componentCandidate execution.graph part.1 index).nodes.length =
      part.1.length := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.length_map]
  have hposLen : posB < part.1.length := (List.getElem?_eq_some_iff.mp hpos).1
  have hwLen : posB <
      (componentCandidate execution.graph part.1 index).nodes.length := by omega
  obtain ⟨nodeW, hnodeW⟩ : ∃ nodeW,
      (componentCandidate execution.graph part.1 index).nodes[posB]? =
        some nodeW :=
    ⟨_, List.getElem?_eq_getElem hwLen⟩
  have hkLen : k < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hbox).1
  have hlen : k < execution.lines.length := by omega
  obtain ⟨gnode, hgnode, hb0⟩ :=
    xcb_exclusive_border_zeroX execution hwf hbox hex hlen
  have hcglookup : (componentCandidate execution.graph part.1 index).nodes[posB]? =
      some (execution.graph.nodes.getD k default) := by
    rw [componentCandidate_nodes]
    simp only [componentGraph, List.getElem?_map, hpos, Option.map_some]
  have hgetD : execution.graph.nodes.getD k default = gnode := by
    rw [List.getD_eq_getElem?_getD, hgnode]
    rfl
  have hnodeWg : nodeW = gnode := by
    have heq2 : nodeW = execution.graph.nodes.getD k default :=
      Option.some.inj (hnodeW.symm.trans hcglookup)
    rw [hgetD] at heq2
    exact heq2
  have hnodeW0 : nodeW.border = 0 := by rw [hnodeWg]; exact hb0
  have hband := hrun execution hwf hfp hcomp hrunEx htopnode htopborder raw hraw htopidx
    hnodeW hnodeW0 hpos hbox hex
  rw [htitle1] at hband
  have hframeEq : (placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured
      loops).rects[posB]? = some (shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run posB)) :=
    xcb_placeComponentExact_rects_get hwLen
  have hupd : ({placeComponentExact execution.params
      (componentCandidate execution.graph part.1 index) run 0 execution.measured
      loops with area := area} : Part).rects =
      (placeComponentExact execution.params
        (componentCandidate execution.graph part.1 index) run 0
        execution.measured loops).rects := rfl
  have hpartRect : part.2.rects[posB]? = some (shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run posB)) := by
    rw [hpartdef, hupd]
    exact hframeEq
  have hrectEq : rect = shiftRect
      (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run posB) :=
    Option.some.inj (hrect.symm.trans hpartRect)
  have hshiftUpd : ({shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured
      loops).minX)
    (-(placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured
      loops).minY) raw.2 with
      w := (titleCaptionSize execution.params o
        (execution.lines.getD (part.1.getD title.1 0) [])).w,
      h := (titleCaptionSize execution.params o
        (execution.lines.getD (part.1.getD title.1 0) [])).h}) =
      shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured
        loops).minY) {raw.2 with
      w := (titleCaptionSize execution.params o
        (execution.lines.getD (part.1.getD title.1 0) [])).w,
      h := (titleCaptionSize execution.params o
        (execution.lines.getD (part.1.getD title.1 0) [])).h} := by
    cases raw.2 with
    | mk x y w h => rfl
  rw [hrectEq, ← htitle2, hshiftUpd]
  exact xcb_shiftRect_disjoint hband


end PipelineImpl
end Layered
end Elegant
