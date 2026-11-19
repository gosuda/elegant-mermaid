import Elegant.Layered.RegionFlatC8b
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.ExactPartFrameCoresWProof
import Elegant.Layered.RegionReduction
import Elegant.Layered.RegionActualParts
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.PartCaptionRunClearProof
import Elegant.Layered.LabelsC8bFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region part-frame cores, per-execution W form (`R_ExecutedPartFrameCoresB8W`)

Twin of `X_ExecutedPartFrameCoresB8W` (`ExactPartFrameCoresWProof.lean:52`) replayed over `SceneExecutionR`.

Probe evidence (`proofs/wip/Probe/RegionPartFrameCoresTProbe.lean`): Bool mirrors of both core conjuncts are true on 10 executed `layoutRIds` runs: two-region `two[]` ok parts=1 route=true cap=true wf=true fp=true; `two-exactG1[G1]` layoutRIds error domain (exactIds names region parent G1 with children, no execution so cores vacuous) wf=true fp=true; `flat[]` ok parts=1 route=true cap=true wf=true; `nest[]` nested groups ok parts=1 route=true cap=true; `zero[]` zero-size fixed box ok parts=1 route=true cap=true; `empty[]` empty groups ok parts=2 route=true cap=true; `self[]` self-loop ok parts=1 route=true cap=true; `dup[]` duplicate ids ok parts=1 route=true cap=true wf=false; `excl[]` exclusive group ok parts=1 route=true cap=true wf=false; `two-none[]` ok parts=1 route=true cap=true. The W form adds only unused admission premises, so truth transfers from the non-W Bool mirrors. -/

/-- Region mirror of the run-level caption residual `CaptionRunClear`, W form: the `XF_CaptionRunClearXW` conclusion (`ExactCaptionRunClearWProof.lean:123`) over `componentRunR` runs of an executed region scene, with local admission premises directly after the execution binder. -/
def RF_CaptionRunClearRW (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph} {run : Run} {spec' : Option RegionSpec},
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    CaptionRunClear execution.params cg run
      (transportCapSize execution.params o execution.lines comp)

/-- Region mirror of the run-level route residual `RouteRunClear`, W form: the `XF_RouteRunClearXW` conclusion (`ExactPartFrameCoresWProof.lean:37`) over `componentRunR` runs of an executed region scene, with local admission premises directly after the execution binder. -/
def RF_RouteRunClearRW (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
    {comp : List Nat} (_ : comp ∈ components execution.graph)
    {candidate : Nat} {cg : Graph} {run : Run} {spec' : Option RegionSpec},
    componentRunR execution.params (exactDecls exactIds inp) spec' inp
      (componentCandidateR spec' execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok (cg, run) →
    RouteRunClear execution.params cg run execution.measured

/-- R core residual, W form: mirror of `X_ExecutedPartFrameCoresB8W` (`ExactPartFrameCoresWProof.lean:52`) over `SceneExecutionR`, with local admission premises directly after the execution binder. -/
def R_ExecutedPartFrameCoresB8W (exactIds : List String)
    (idSets : List (String × List String)) : Prop :=
  ∀ {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true),
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part
private theorem rpc_execution_part_runR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts) :
    ∃ (index : Nat) (cg : Graph) (run : Run)
      (loops : List (Nat × LoopPlacement)) (area : Int)
      (spec' : Option RegionSpec),
      part.1 ∈ components execution.graph ∧
      componentRunR execution.params (exactDecls exactIds inp) spec' inp
        (componentCandidateR spec' execution.graph part.1 index)
        execution.measured (candidateOrder index) = .ok (cg, run) ∧
      part.2 = { placeComponentExact execution.params cg run 0
        execution.measured loops with area := area } := by
  have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [],
      Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = [] := rfl
  obtain ⟨hm, hall⟩ := actual_components_parts_geometryR hempty
    execution.components_eq
  obtain ⟨index, _chosen, cg, run, loops, area, spec', _hi, _hc, _hv, _hrs,
      hrun, _hl, heq⟩ := hall part hpart
  have _ := componentRunR_specR hrun
  refine ⟨index, cg, run, loops, area, spec', ?_, hrun, heq⟩
  rw [← hm]
  exact List.mem_map_of_mem hpart
private theorem rpc_partCaption_of_runR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hres : RF_CaptionRunClearRW exactIds idSets) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartCaptionFrameClear execution.params inp o execution.lines part := by
  intro part hpart i stored pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨index, cg, run, loops, _area, spec', hcomp, hrun, heq⟩ :=
    rpc_execution_part_runR execution hpart
  have eT : part.2.titles = (componentTitles execution.params cg run).map
      (fun q => (q.1, shiftRect (0 - (placeBoundsX execution.params cg run
        execution.measured loops).minX) (-(placeBoundsX execution.params cg
        run execution.measured loops).minY) q.2)) := by
    have h1 : part.2.titles = (placeComponentExact execution.params cg run 0
      execution.measured loops).titles := by rw [heq]
    rw [h1]; unfold placeComponentExact placeBoundsX; rfl
  have eR' : part.2.rects = (placeComponentExact execution.params cg run 0
      execution.measured loops).rects := by rw [heq]
  rw [eT] at hmem
  obtain ⟨⟨i0, stored0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hstored⟩ := h0eq
  have hlen : part.2.rects.length = cg.nodes.length := by
    rw [eR']; unfold placeComponentExact; dsimp only
    simp only [List.length_map, List.length_range]
  have hlt : pos < cg.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1; omega
  have hframe : (placeComponentExact execution.params cg run 0
      execution.measured loops).rects[pos]? =
      some (shiftRect (0 - (placeBoundsX execution.params cg run
      execution.measured loops).minX) (-(placeBoundsX execution.params cg run
      execution.measured loops).minY) (frameRect execution.params cg run pos)) := by
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some]
  rw [eR'] at hrect; rw [hframe] at hrect
  have hg0 : shiftRect (0 - (placeBoundsX execution.params cg run
      execution.measured loops).minX) (-(placeBoundsX execution.params cg run
      execution.measured loops).minY)
      (frameRect execution.params cg run pos) = g := Option.some.inj hrect
  obtain ⟨top, htop, hborder, htitleIdx, _hw, _hh⟩ :=
    componentTitles_dimension_source execution.params cg run h0mem
  have hidx : i0 = top.2 := htitleIdx
  have hnode : cg.nodes[i0]? = some top.1 := by
    rw [hidx]; exact List.mem_zipIdx_iff_getElem?.mp htop
  have hclear := hres execution hwf hfp hcomp hrun i0 stored0 top.1 h0mem
    hnode hborder pos _ hlt rfl
  dsimp only; rw [←hg0, ←hstored, captionResize_shift_comm]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)
private theorem rpc_partRoute_of_runR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds idSets inp o res)
    (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
    (hres : RF_RouteRunClearRW exactIds idSets) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part := by
  intro part hpart index rect pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨cindex, cg, run, loops, _area, spec', hcomp, hrun, heq⟩ :=
    rpc_execution_part_runR execution hpart
  have eL : part.2.labels = (placedLabels execution.params cg run
      execution.measured).map (fun q => (q.1, shiftRect (0 -
      (placeBoundsX execution.params cg run execution.measured loops).minX)
      (-(placeBoundsX execution.params cg run execution.measured
      loops).minY) q.2)) := by
    have h1 : part.2.labels = (placeComponentExact execution.params cg run 0
      execution.measured loops).labels := by rw [heq]
    rw [h1]; rfl
  have eR' : part.2.rects = (placeComponentExact execution.params cg run 0
      execution.measured loops).rects := by rw [heq]
  rw [eL] at hmem
  obtain ⟨⟨k0, rect0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hrect0⟩ := h0eq
  have hlen : part.2.rects.length = cg.nodes.length := by
    rw [eR']; unfold placeComponentExact; dsimp only
    simp only [List.length_map, List.length_range]
  have hlt : pos < cg.nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1; omega
  have hframe : (placeComponentExact execution.params cg run 0
      execution.measured loops).rects[pos]? =
      some (shiftRect (0 - (placeBoundsX execution.params cg run
      execution.measured loops).minX) (-(placeBoundsX execution.params cg run
      execution.measured loops).minY) (frameRect execution.params cg run
      pos)) := by
    unfold placeComponentExact placeBoundsX
    simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some]
  rw [eR'] at hrect; rw [hframe] at hrect
  have hg0 : shiftRect (0 - (placeBoundsX execution.params cg run
      execution.measured loops).minX) (-(placeBoundsX execution.params cg run
      execution.measured loops).minY)
      (frameRect execution.params cg run pos) = g := Option.some.inj hrect
  have hclear := hres execution hwf hfp hcomp hrun k0 rect0 h0mem pos _ hlt rfl
  rw [←hg0, ←hrect0]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)
theorem R_executedPartFrameCoresW_holds (exactIds : List String)
    (idSets : List (String × List String))
    (hcap : RF_CaptionRunClearRW exactIds idSets)
    (hroute : RF_RouteRunClearRW exactIds idSets) :
    R_ExecutedPartFrameCoresB8W exactIds idSets := by
  intro inp o res execution hwf hfp part hpart
  exact ⟨rpc_partRoute_of_runR execution hwf hfp hroute part hpart,
    rpc_partCaption_of_runR execution hwf hfp hcap part hpart⟩
private theorem rpc_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1
private theorem rpc_packedAcc_rects_sizeR {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res) :
    execution.packedAcc.rects.size = inp.boxes.length := by
  have h := execution.packed_eq
  unfold packAcc at h
  obtain ⟨packed, _, h⟩ := bind_ok h
  have hout := Except.ok.inj h
  rw [← hout]
  change ((execution.componentsAcc.parts.zip packed.boxes).foldl packStep
    { execution.componentsAcc with
      canvasW := packed.width
      canvasH := packed.height
      titles := [] }).rects.size = inp.boxes.length
  rw [rpc_packFold_rects_size]
  exact execution.components_rects_sizeR
private theorem rpc_caption_shift_comm {stored : Rect} {dx dy w h : Int} :
    ({ shiftRect dx dy stored with w := w, h := h } : Rect) =
      shiftRect dx dy { stored with w := w, h := h } := rfl
private theorem rpc_index_eq_of_id_eq {l : List ModelBox}
    (hn : (l.map (·.id)).Nodup) {i j : Nat} {a b : ModelBox}
    (hi : l[i]? = some a) (hj : l[j]? = some b) (hid : a.id = b.id) : i = j := by
  have hin : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjn : j < l.length := (List.getElem?_eq_some_iff.mp hj).1
  have hil : i < (l.map (·.id)).length := by rw [List.length_map]; exact hin
  have hjl : j < (l.map (·.id)).length := by rw [List.length_map]; exact hjn
  have hget : (l.map (·.id))[i]? = (l.map (·.id))[j]? := by
    rw [List.getElem?_map, hi, List.getElem?_map, hj]
    simp only [Option.map_some]
    exact congrArg Option.some hid
  have hv : (l.map (·.id))[i] = (l.map (·.id))[j] := by
    have e1 : (l.map (·.id))[i]? = some ((l.map (·.id))[i]) :=
      List.getElem?_eq_getElem hil
    have e2 : (l.map (·.id))[j]? = some ((l.map (·.id))[j]) :=
      List.getElem?_eq_getElem hjl
    exact Option.some.inj (e1.symm.trans (hget.trans e2))
  have hp := List.pairwise_iff_getElem.mp hn
  by_cases hlt : i < j
  · exact absurd hv (hp i j hil hjl hlt)
  · by_cases hjt : j < i
    · exact absurd hv.symm (hp j i hjl hil hjt)
    · omega
private theorem rpc_labelsClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets)
    (index k : Nat) (gBox : ModelBox) (hbox : inp.boxes[k]? = some gBox)
    (hrole : gBox.role = BoxRole.group) :
    let g := execution.packedAcc.rects.getD k default
    let l := execution.packedAcc.labels.getD index default
    Disjoint g l ∨ g.StrictInside l := by
  obtain ⟨packed, hpack, hrects, hlabels, _htitles, hnonneg⟩ :=
    htransport execution
  dsimp only
  have hksize : k < execution.packedAcc.rects.size := by
    rw [rpc_packedAcc_rects_sizeR execution]
    exact (List.getElem?_eq_some_iff.mp hbox).1
  obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
    hrects k hksize (execution.packedAcc.rects.getD k default) rfl
  rw [hreq] at hboxk
  rcases hlabels index (execution.packedAcc.labels.getD index default) rfl with
    ⟨pl, partl, r0l, bl, hpartl, hmeml, hbl, hreql, hboxl⟩ | hdef
  · rw [hreql] at hboxl
    by_cases hpk : pk = pl
    · subst hpk
      obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
      obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
      obtain ⟨hcore, -⟩ := hcore partk (List.mem_of_getElem? hpartk)
      have hclr := hcore index r0l posk k gBox r0 hmeml hkeyk hbox hrole hr0
      rw [hreq, hreql]
      rcases hclr with h | h
      · exact Or.inl (disjoint_shiftRect h)
      · exact Or.inr (strictInside_shiftRect h)
    · have hpkL : pk < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hpartk).1
      have hplL : pl < execution.componentsAcc.parts.length :=
        (List.getElem?_eq_some_iff.mp hpartl).1
      have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
        rw [Pack.pack_count hpack, List.length_map]
      have hpkBox : pk < packed.boxes.length := by omega
      have hplBox : pl < packed.boxes.length := by omega
      have hd : Disjoint bk bl := by
        have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
          Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
        have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
        have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
        rw [hbk', hbl'] at hd0
        exact hd0
      rw [hreq, hreql]
      exact Or.inl (disjoint_of_contained_disjoint hboxk hboxl hd)
  · rw [hreq, hdef]
    exact Or.inl (disjoint_default_of_nonneg (by
      rw [← hreq]
      exact hnonneg k (execution.packedAcc.rects.getD k default) rfl))
private theorem rpc_titlesClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets)
    (key : Nat) (stored : Rect) (htitle : (key, stored) ∈ execution.packedAcc.titles)
    (k : Nat) (gBox : ModelBox) (hbox : inp.boxes[k]? = some gBox)
    (hrole : gBox.role = BoxRole.group) :
    let g := execution.packedAcc.rects.getD k default
    let caption : Rect :=
      { stored with
        w := (titleCaptionSize execution.params o
        (execution.lines.getD key [])).w
        h := (titleCaptionSize execution.params o
        (execution.lines.getD key [])).h }
    Disjoint g caption ∨ g.StrictInside caption := by
  obtain ⟨packed, hpack, hrects, _hlabels, htitles, _hnonneg⟩ :=
    htransport execution
  dsimp only
  have hksize : k < execution.packedAcc.rects.size := by
    rw [rpc_packedAcc_rects_sizeR execution]
    exact (List.getElem?_eq_some_iff.mp hbox).1
  obtain ⟨pk, partk, posk, r0, bk, hpartk, hkeyk, hr0, hbk, hreq, hboxk⟩ :=
    hrects k hksize (execution.packedAcc.rects.getD k default) rfl
  rw [hreq] at hboxk
  obtain ⟨pl, partl, i, stored0, bl, hpartl, hkeyi, hmeml, hbl, hstored, hboxCap⟩ :=
    htitles key stored htitle
  by_cases hpk : pk = pl
  · subst hpk
    obtain rfl : partk = partl := Option.some.inj (hpartk.symm.trans hpartl)
    obtain rfl : bk = bl := Option.some.inj (hbk.symm.trans hbl)
    obtain ⟨-, hcore⟩ := hcore partk (List.mem_of_getElem? hpartk)
    have hgetD : partk.1.getD i 0 = key := by
      simp only [List.getD, hkeyi, Option.getD_some]
    have hclr := hcore i stored0 posk k gBox r0 hmeml hkeyk hbox hrole hr0
    simp only [hgetD] at hclr
    rw [hreq, hstored, rpc_caption_shift_comm]
    rcases hclr with h | h
    · exact Or.inl (disjoint_shiftRect h)
    · exact Or.inr (strictInside_shiftRect h)
  · have hpkL : pk < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hpartk).1
    have hplL : pl < execution.componentsAcc.parts.length :=
      (List.getElem?_eq_some_iff.mp hpartl).1
    have hlen : packed.boxes.length = execution.componentsAcc.parts.length := by
      rw [Pack.pack_count hpack, List.length_map]
    have hpkBox : pk < packed.boxes.length := by omega
    have hplBox : pl < packed.boxes.length := by omega
    have hd : Disjoint bk bl := by
      have hd0 : Disjoint packed.boxes[pk] packed.boxes[pl] :=
        Pack.pack_boxes_disjoint hpack pk pl hpkBox hplBox hpk
      have hbk' : packed.boxes[pk] = bk := (List.getElem?_eq_some_iff.mp hbk).2
      have hbl' : packed.boxes[pl] = bl := (List.getElem?_eq_some_iff.mp hbl).2
      rw [hbk', hbl'] at hd0
      exact hd0
    rw [hreq, hstored, rpc_caption_shift_comm]
    exact Or.inl (disjoint_of_contained_disjoint hboxk hboxCap hd)
private theorem rpc_labelFramePackedClear_of_boundedW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hcore : ∀ part ∈ execution.componentsAcc.parts,
      PartRouteLabelFrameClear inp part ∧
      PartCaptionFrameClear execution.params inp o execution.lines part)
    (htransport : R_PackedPartTransportBoundedB8 exactIds idSets) :
    LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc := by
  refine ⟨?_, ?_⟩
  · intro index k gBox hbox hrole
    exact rpc_labelsClear_of_boundedW execution hcore htransport index k gBox
      hbox hrole
  · intro key stored htitle k gBox hbox hrole
    exact rpc_titlesClear_of_boundedW execution hcore htransport key stored
      htitle k gBox hbox hrole
private theorem rpc_runR_none_to_X {P : Params} {exact : List Nat} {inp : Input}
    {cgIn cgOut : Graph} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (h : componentRunR P exact none inp cgIn labels orderOptions =
      .ok (cgOut, run)) :
    componentRunX P exact cgIn labels orderOptions = .ok run ∧
      cgOut = cgIn := by
  have hmap := (componentRunR_none P exact inp cgIn labels orderOptions).symm.trans h
  cases hX : componentRunX P exact cgIn labels orderOptions with
  | error e =>
    simp only [hX, Except.map] at hmap
    cases hmap
  | ok r =>
    simp only [hX, Except.map] at hmap
    have hpair : (cgIn, r) = (cgOut, run) := Except.ok.inj hmap
    have hcg : cgIn = cgOut := congrArg Prod.fst hpair
    have hrun : r = run := congrArg Prod.snd hpair
    exact ⟨congrArg Except.ok hrun, hcg.symm⟩
private theorem rpc_RtoX {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionR exactIds [] inp o res) :
    ∃ (execX : SceneExecutionX exactIds inp o res),
      execX.params = execution.params ∧
      execX.measured = execution.measured ∧
      execX.graph = execution.graph ∧
      execX.lines = execution.lines := by
  have hR := execution.components_eq
  have hRnone : ((components execution.graph).foldlM
      (fun acc comp => layoutComponentR execution.params exactIds none inp o
        execution.graph acc comp execution.measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [],
        Array.replicate inp.labels.length default, false, [], []⟩) =
      .ok execution.componentsAcc := hR
  have hfun : ∀ (acc : Acc) (comp : List Nat),
      layoutComponentR execution.params exactIds none inp o execution.graph
        acc comp execution.measured =
      layoutComponentX execution.params exactIds inp o execution.graph
        acc comp execution.measured := fun acc comp =>
    layoutComponentR_none execution.params exactIds inp o execution.graph
      acc comp execution.measured
  have heq : (fun acc comp => layoutComponentR execution.params exactIds none
      inp o execution.graph acc comp execution.measured) =
      (fun acc comp => layoutComponentX execution.params exactIds inp o
      execution.graph acc comp execution.measured) := by
    funext acc comp
    exact hfun acc comp
  have hXcomp : ((components execution.graph).foldlM
      (fun acc comp => layoutComponentX execution.params exactIds inp o
        execution.graph acc comp execution.measured)
      ⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [],
        Array.replicate inp.labels.length default, false, [], []⟩) =
      .ok execution.componentsAcc := by
    rw [←heq]
    exact hRnone
  refine ⟨⟨execution.params, execution.metric, execution.lines,
    execution.measured, execution.graph0, execution.graph,
    execution.componentsAcc, execution.packedAcc, execution.checked,
    execution.metric_eq, execution.lines_eq, execution.measured_eq,
    execution.graph0_eq, execution.graph_eq, hXcomp, execution.packed_eq,
    execution.scene_eq⟩, rfl, rfl, rfl, rfl⟩
theorem RF_captionRunClearRW_none_holds (exactIds : List String)
    (hcapX : XF_CaptionRunClearXW exactIds) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds [] inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {cg : Graph} {run : Run},
      componentRunR execution.params (exactDecls exactIds inp) none inp
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok (cg, run) →
      CaptionRunClear execution.params cg run
        (transportCapSize execution.params o execution.lines comp) := by
  intro inp o res execution hwf hfp comp hcomp candidate cg run hrun
  obtain ⟨hrunX, hcgEq⟩ := rpc_runR_none_to_X hrun
  subst hcgEq
  have _ := componentCandidateR_none execution.graph comp candidate
  obtain ⟨execX, hparams, hmeasured, hgraph, hlines⟩ := rpc_RtoX execution
  have hcompX : comp ∈ components execX.graph := hgraph.symm ▸ hcomp
  have hrunX' : componentRunX execX.params (exactDecls exactIds inp)
      (componentCandidate execX.graph comp candidate) execX.measured
      (candidateOrder candidate) = .ok run := by
    rw [hparams, hmeasured, hgraph]
    exact hrunX
  have hcap := hcapX execX hwf hfp hcompX hrunX'
  rw [hparams, hgraph, hlines] at hcap
  exact hcap
theorem RF_routeRunClearRW_none_holds (exactIds : List String)
    (hrouteX : XF_RouteRunClearXW exactIds) :
    ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds [] inp o res)
      (_hwf : WellFormed (inputModel inp o)) (_hfp : framedParents inp = true)
      {comp : List Nat} (_ : comp ∈ components execution.graph)
      {candidate : Nat} {cg : Graph} {run : Run},
      componentRunR execution.params (exactDecls exactIds inp) none inp
        (componentCandidate execution.graph comp candidate) execution.measured
        (candidateOrder candidate) = .ok (cg, run) →
      RouteRunClear execution.params cg run execution.measured := by
  intro inp o res execution hwf hfp comp hcomp candidate cg run hrun
  obtain ⟨hrunX, hcgEq⟩ := rpc_runR_none_to_X hrun
  subst hcgEq
  have _ := componentCandidateR_none execution.graph comp candidate
  obtain ⟨execX, hparams, hmeasured, hgraph, _hlines⟩ := rpc_RtoX execution
  have hcompX : comp ∈ components execX.graph := hgraph.symm ▸ hcomp
  have hrunX' : componentRunX execX.params (exactDecls exactIds inp)
      (componentCandidate execX.graph comp candidate) execX.measured
      (candidateOrder candidate) = .ok run := by
    rw [hparams, hmeasured, hgraph]
    exact hrunX
  have hroute := hrouteX execX hwf hfp hcompX hrunX'
  rw [hparams, hgraph, hmeasured] at hroute
  exact hroute
set_option maxHeartbeats 1000000 in
/-- W clause 8, condition 2 for a successful region `layoutRIds`: replay of
`r8b_layout_c8b` over the per-execution packed clearance and the unchanged
fallback, with the copied id-equality lemma. -/
private theorem rpc_layout_c8bW {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult}
    (execution : SceneExecutionR exactIds idSets inp o res)
    (hpack : LabelFramePackedClear execution.params inp o execution.lines
      execution.packedAcc)
    (hfall : R_FallbackCaptionClearB8 exactIds idSets)
    (hfit : InputFixedFit inp o)
    (hwf : WellFormed (inputModel inp o)) :
    Validator.C8b res.scene.layoutDump := by
  have hfallApp := hfall execution hfit
  obtain ⟨hpackLabels, hpackTitles⟩ := hpack
  have hidsNodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  intro g hgMem hgRole l hlMem
  simp only [Scene.layoutDump] at hgMem hlMem
  obtain ⟨sl, hsl, hlEq⟩ := List.mem_map.mp hlMem
  rw [execution.scene_eq] at hsl
  obtain ⟨qL, hqL, hemitted⟩ := List.mem_filterMap.mp hsl
  obtain ⟨source, indexL⟩ := qL
  have hsrcL : inp.labels[indexL]? = some source :=
    List.mem_zipIdx_iff_getElem?.mp hqL
  have hslRect : l.rect = sl.rect := by rw [← hlEq]
  rw [execution.boxes_eq_mapR] at hgMem
  obtain ⟨q, hq, hgeq⟩ := List.mem_map.mp hgMem
  obtain ⟨hgBox, hKey⟩ := q
  dsimp only [Prod.fst, Prod.snd] at hgeq hq
  have hk : inp.boxes[hKey]? = some hgBox := List.mem_zipIdx_iff_getElem?.mp hq
  have hgRole0 : g.role = hgBox.role.id := by
    rw [← hgeq]
  have hgroupRole : hgBox.role = BoxRole.group := by
    have hgid : hgBox.role.id = "group" := hgRole0.symm.trans hgRole
    cases hrole : hgBox.role with
    | node =>
      rw [hrole] at hgid
      simp only [BoxRole.id] at hgid
      exact absurd hgid (by decide)
    | group => rfl
  have hgRect : g.rect = shiftRect execution.params.canvasMargin
      execution.params.canvasMargin (orientRect o.direction
        execution.packedAcc.canvasH (execution.packedAcc.rects.getD hKey default)) := by
    rw [← hgeq]
  cases hexcl : inp.boxes.any (fun box : ModelBox =>
      box.id == source.owner && box.exclusive) with
  | true =>
    simp only [hexcl, ↓reduceIte] at hemitted
    cases hemitted
  | false =>
    simp only [hexcl] at hemitted
    cases hm : execution.measured.find?
        (fun item : MeasuredLabel => item.index == indexL) with
    | some measured =>
      have hpm := List.find?_some hm
      have hmIdx : measured.index = indexL := by simpa using hpm
      have hrel := hpackLabels indexL hKey hgBox hk hgroupRole
      simp only [hm] at hemitted
      have hlrect : sl.rect = shiftRect execution.params.canvasMargin
          execution.params.canvasMargin (orientRect o.direction
            execution.packedAcc.canvasH
            (execution.packedAcc.labels.getD indexL default)) := by
        have heq' := Option.some.inj hemitted
        have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
        dsimp only at hrr
        rw [hrr, hmIdx]
      rw [hslRect, hgRect, hlrect]
      cases hrel with
      | inl h => exact Or.inl (disjoint_sceneTransport h)
      | inr h => exact Or.inr (strictInside_sceneTransport h)
    | none =>
      simp only [hm] at hemitted
      cases ho : inp.boxes.findIdx? (fun box : ModelBox =>
          box.id == source.owner && !box.exclusive) with
      | none =>
        simp only [ho] at hemitted
        cases hemitted
      | some ownerIndex =>
        simp only [ho] at hemitted
        obtain ⟨hb, hownerPred, -⟩ := List.findIdx?_eq_some_iff_getElem.mp ho
        have hobGet : inp.boxes[ownerIndex]? = some inp.boxes[ownerIndex] :=
          List.getElem?_eq_some_iff.mpr ⟨hb, rfl⟩
        have hownerId : inp.boxes[ownerIndex].id = source.owner := by
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hownerPred
          exact hownerPred.1
        have heq := hemitted
        have hselD : (sceneTitlesExpr execution.params inp o execution.lines
            execution.packedAcc).find? (fun t => t.1 == source.owner) = none ∨
            ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := by
          cases h : (sceneTitlesExpr execution.params inp o execution.lines
              execution.packedAcc).find? (fun t => t.1 == source.owner) with
          | none => exact Or.inl rfl
          | some t => exact Or.inr ⟨t, rfl⟩
        cases hselD with
        | inl hsel =>
          have hgMemScene : g ∈ res.scene.boxes := by
            rw [execution.scene_eq]
            exact List.mem_map.mpr ⟨(hgBox, hKey), hq, hgeq⟩
          have hlrect : sl.rect = ownedTextRect execution.params
              ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                ownerIndex ⟨"", "", default, "", false⟩)
              (execution.lines.getD ownerIndex []) := by
            have heq' := Option.some.inj heq
            have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
            dsimp only at hrr
            rw [hrr]
            show (Option.map (fun x => x.snd)
                ((sceneTitlesExpr execution.params inp o execution.lines
                  execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                (ownedTextRect execution.params
                  ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                    ownerIndex ⟨"", "", default, "", false⟩)
                  (execution.lines.getD ownerIndex [])) =
              ownedTextRect execution.params
                ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                  ownerIndex ⟨"", "", default, "", false⟩)
                (execution.lines.getD ownerIndex [])
            rw [hsel]
            rfl
          rw [hslRect, hlrect]
          exact hfallApp source indexL ownerIndex g hsrcL ho hsel hgMemScene hgRole
        | inr hts =>
          have hts' : ∃ t : String × Rect,
              (sceneTitlesExpr execution.params inp o execution.lines
                execution.packedAcc).find? (fun t => t.1 == source.owner) = some t := hts
          obtain ⟨tsel, hsel⟩ := hts'
          have hselMem := List.mem_of_find?_eq_some hsel
          obtain ⟨stored, hstoredMem, hfeq⟩ := List.mem_filterMap.mp hselMem
          cases hbx : inp.boxes[stored.1]? with
          | none => simp only [hbx] at hfeq; cases hfeq
          | some box0 =>
            simp only [hbx] at hfeq
            have hpair := Option.some.inj hfeq
            have htid : box0.id = tsel.1 := congrArg Prod.fst hpair
            have htrect : shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) = tsel.2 :=
              congrArg Prod.snd hpair
            have hselKey : tsel.1 = source.owner := by
              simpa using List.find?_some hsel
            have hid' : box0.id = inp.boxes[ownerIndex].id :=
              htid.trans (hselKey.trans hownerId.symm)
            have hkeyEq : stored.1 = ownerIndex :=
              rpc_index_eq_of_id_eq hidsNodup hbx hobGet hid'
            have hrel := hpackTitles stored.1 stored.2 hstoredMem hKey hgBox hk hgroupRole
            have hlrect : sl.rect = shiftRect execution.params.canvasMargin
                execution.params.canvasMargin (orientRect o.direction
                  execution.packedAcc.canvasH
                  { stored.2 with
                    w := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).w
                    h := (titleCaptionSize execution.params o
                      (execution.lines.getD stored.1 [])).h }) := by
              have heq' := Option.some.inj heq
              have hrr := (congrArg (fun s : SceneLabel => s.rect) heq').symm
              dsimp only at hrr
              rw [hrr]
              show (Option.map (fun x => x.snd)
                  ((sceneTitlesExpr execution.params inp o execution.lines
                    execution.packedAcc).find? (fun t => t.1 == source.owner))).getD
                (ownedTextRect execution.params
                  ((sceneBoxesExpr execution.params inp o execution.packedAcc).getD
                    ownerIndex ⟨"", "", default, "", false⟩)
                  (execution.lines.getD ownerIndex [])) =
                shiftRect execution.params.canvasMargin
                  execution.params.canvasMargin (orientRect o.direction
                    execution.packedAcc.canvasH
                    { stored.2 with
                      w := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).w
                      h := (titleCaptionSize execution.params o
                        (execution.lines.getD stored.1 [])).h })
              rw [hsel]
              show tsel.2 = _
              rw [← htrect]
            rw [hslRect, hgRect, hlrect]
            cases hrel with
            | inl h => exact Or.inl (disjoint_sceneTransport h)
            | inr h => exact Or.inr (strictInside_sceneTransport h)
theorem flatC8bB_layoutRIdsW (exactIds : List String)
    (idSets : List (String × List String))
    (hcoresW : R_ExecutedPartFrameCoresB8W exactIds idSets)
    (hfall : R_FallbackCaptionClearB8 exactIds idSets)
    (hsize : ∀ {inp : Input} {o : Options} {res : FamilyResult}
      (execution : SceneExecutionR exactIds idSets inp o res),
      R_PartSizingR execution)
    (hcap : R_ExactTitleCaptionFitB8 exactIds idSets) :
    FlatC8bB (PipelineImpl.layoutRIds exactIds idSets) := by
  intro inp o res hwf hfp hfit h
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hpack :=
    rpc_labelFramePackedClear_of_boundedW execution (hcoresW execution hwf hfp)
      (R_packedPartTransportBounded_closed exactIds idSets hsize hcap)
  exact rpc_layout_c8bW execution hpack hfall hfit hwf

end PipelineImpl
end Layered
end Elegant
