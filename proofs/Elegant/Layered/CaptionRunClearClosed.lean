import Elegant.Layered.CaptionLocalClearProof
import Elegant.Layered.CaptionSelfSidesProof
import Elegant.Layered.CaptionSameDeclMarkerProof
import Elegant.Layered.CaptionDescDisjointProof
import Elegant.Layered.CaptionAncestorFrameProof
import Elegant.Layered.ForeignMemberRankBoundsProof
import Elegant.Layered.SideMarkerTopInCandidateProof
import Elegant.Layered.ForeignBorderAnchorsProof
import Elegant.Layered.SideMarkerPathsProof
import Elegant.Layered.ForeignBorderSpansProof
import Elegant.Layered.ForeignNonGroupSpansProof
import Elegant.Layered.ForeignSpansFacts
import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.PartFrameCoresProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.FrameClearanceFacts
import Elegant.Layered.CgShape
import Elegant.Layered.Compound

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Closed caption clearance for one executed component run

`captionRunClear_closed` discharges `captionRunClear_executed` to the single
open seam `ForeignBorderChainXAligned`. Of the seven per-run hypotheses, six
are executed-run facts: self sides (`CaptionSelfSidesProof`), same-declaration
markers (`CaptionSameDeclMarkerProof`), descendant disjointness
(`CaptionDescDisjointProof`), ancestor group frames and ancestor bottom markers
(`CaptionAncestorFrameProof`). The seventh, `CaptionAncestorOtherClear`, has no
executed supplier, so it is proved here: for a candidate graph the remaining
border is plain (`componentCandidate_marker_shape`), and a plain node whose
declaration lies on the title's cluster path is impossible (the declaration is
then an ancestor index, hence a group in the demoted list, while the plain
node's demoted box is not a group). The foreign span hypothesis comes from the
three foreign seams exactly as `foreignFramesDisjoint_of_run` builds them.
`captionHalf_closed` restates the conclusion in the part-level consumer's
`hcap` form, and `executedPartFrameCores_measured` is the `measured`-only
variant of `executedPartFrameCores` (both transports only ever instantiate
`execution.measured`). -/

/-- Copy of the private `FrameLabelsProof.components_mem_bound`: component
members index valid graph nodes. -/
private theorem components_mem_bound_copy {g : Graph} {comp : List Nat}
    (hmem : comp ∈ components g) {v : Nat} (hv : v ∈ comp) :
    v < g.nodes.length := by
  unfold components at hmem
  dsimp only at hmem
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
  rw [← hr] at hv
  exact List.mem_range.mp (List.mem_filter.mp hv).1

/-- Copy of the private `CaptionOwnerScopeProof.ownerScope_demote_facts`: the
demoted box keeps id, parent, and exclusivity. -/
private theorem otherClear_demote_facts {inp : Input} (box : ModelBox) :
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).id = box.id ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).parent = box.parent ∧
    (if inp.fixedSizes.any (fun fixed => fixed.1 == box.id) then
      { box with role := .node } else box).exclusive = box.exclusive := by
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- Copy of the private `CaptionOwnerScopeProof.ownerScope_getElem_unique`:
injectivity of the id map on a nodup list. -/
private theorem otherClear_getElem_unique {α : Type} {f : α → String} {l : List α}
    (hnd : (l.map f).Nodup) {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hid : f x = f y) :
    x = y := by
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hyj⟩ := List.mem_iff_getElem.mp hy
  by_cases hij : i = j
  · subst hij
    exact hxi.symm.trans hyj
  · exfalso
    have hp := List.pairwise_iff_getElem.mp hnd
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · have h := hp i j (by simpa using hi) (by simpa using hj) hlt
      exact h (by simp only [List.getElem_map, hxi, hyj, hid])
    · exact absurd heq hij
    · have h := hp j i (by simpa using hj) (by simpa using hi) hgt
      exact h (by simp only [List.getElem_map, hyj, hxi, ← hid])

/-- Copy of the private `CaptionOwnerScopeProof.ownerScope_path_group_role`:
every member of a `Compound.ancestors` walk started at a box's parent is a
group in the demoted box list. -/
private theorem otherClear_path_group_role {inp : Input}
    (hfp : framedParents inp = true)
    (hids : (inp.boxes.map (·.id)).Nodup)
    (eff : List ModelBox)
    (heff : eff = inp.boxes.map fun b =>
      if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
        { b with role := .node } else b)
    (fuel : Nat) (c : ModelBox) (hc : c ∈ inp.boxes) :
    ∀ i ∈ Compound.ancestors eff fuel c.parent,
      ∃ b, eff[i]? = some b ∧ b.role = .group := by
  induction fuel generalizing c with
  | zero =>
    intro i hi
    have hempty : Compound.ancestors eff 0 c.parent = [] := rfl
    rw [hempty] at hi
    simp at hi
  | succ fuel ih =>
    intro i hi
    by_cases hcp : c.parent = ""
    · have hnil : Compound.ancestors eff (fuel + 1) c.parent = [] := by
        simp [hcp, Compound.ancestors]
      rw [hnil] at hi
      simp at hi
    · have h3 := Compound.ancestors.eq_3 eff c.parent fuel hcp
      rw [h3] at hi
      cases hf : eff.findIdx? (fun box => box.id == c.parent) with
      | none =>
        simp only [hf] at hi
        simp at hi
      | some j =>
        simp only [hf] at hi
        cases hb : eff[j]? with
        | none =>
          simp only [hb] at hi
          simp at hi
        | some e =>
          simp only [hb] at hi
          obtain ⟨_, hbjEq⟩ := List.getElem?_eq_some_iff.mp hb
          obtain ⟨_, hjid, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
          have heid : e.id = c.parent := by
            rw [← hbjEq]
            exact beq_iff_eq.mp hjid
          have heffj : eff[j]? = (inp.boxes[j]?).map fun b =>
              if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
                { b with role := .node } else b := by
            rw [heff, List.getElem?_map]
          rw [heffj] at hb
          cases hjo : inp.boxes[j]? with
          | none => rw [hjo] at hb; exact absurd hb (by simp)
          | some orig =>
            rw [hjo] at hb
            have heq : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig) = e := Option.some.inj hb
            have horig : orig ∈ inp.boxes := List.mem_of_getElem? hjo
            have hdemParent : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                { orig with role := .node } else orig).parent = orig.parent :=
              (otherClear_demote_facts orig).2.1
            have heid' : orig.id = c.parent := by
              have hroleD : (if inp.fixedSizes.any (fun fixed => fixed.1 == orig.id) then
                  { orig with role := .node } else orig).id = orig.id :=
                (otherClear_demote_facts orig).1
              have heid'' := heid
              rw [← heq] at heid''
              exact hroleD.symm.trans heid''
            have hbE : eff[j]? = some e := by
              rw [heffj, hjo]
              exact congrArg some heq
            simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with hi | rfl
            · rw [← heq, hdemParent] at hi
              exact ih orig horig i hi
            · refine ⟨e, hbE, ?_⟩
              rw [← heq]
              have hall : (c.parent == "" ||
                  inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true :=
                List.all_eq_true.mp hfp c hc
              have hOr : (c.parent == "") = true ∨
                  (inp.boxes.any fun parent =>
                    parent.id == c.parent && parent.role == .group &&
                      !inp.fixedSizes.any (fun fixed => fixed.1 == parent.id)) = true := by
                by_cases hblank : (c.parent == "") = true
                · exact Or.inl hblank
                · right
                  have hfalse : (c.parent == "") = false := by
                    cases h2 : (c.parent == "") with
                    | true => exact absurd h2 hblank
                    | false => rfl
                  simp only [hfalse, Bool.false_or] at hall
                  exact hall
              rcases hOr with hblank | hany
              · exact absurd (beq_iff_eq.mp hblank) hcp
              · obtain ⟨pb, hpbmem, hpb⟩ := List.any_eq_true.mp hany
                simp only [Bool.and_eq_true] at hpb
                obtain ⟨⟨hpbIdB, hpbRoleB⟩, hpbNotFixB⟩ := hpb
                have hpbId : pb.id = c.parent := beq_iff_eq.mp hpbIdB
                have hpbRole : pb.role = .group := beq_iff_eq.mp hpbRoleB
                have hnotfix : inp.fixedSizes.any
                    (fun fixed => fixed.1 == pb.id) = false := by
                  simpa using hpbNotFixB
                have horigEq : orig = pb :=
                  otherClear_getElem_unique hids horig hpbmem (by
                    rw [heid']; exact hpbId.symm)
                have hdem : (if inp.fixedSizes.any (fun fixed => fixed.1 == pb.id) then
                    { pb with role := .node } else pb) = pb := by
                  simp [hnotfix]
                rw [horigEq, hdem]
                exact hpbRole

/-- Executed ancestor-other clearance: an ancestor position that is neither a
group frame nor a bottom marker is vacuous for executed runs. Candidate-graph
nodes have border `0`, `-2` or `2`, so the remaining case is a plain node whose
declaration lies on the title's cluster path. That declaration is then an
ancestor index of the title's box, hence a group in the demoted list, while the
plain node's demoted box is not a group (`prepare_group_title_record`
contrapositive). Probe `wip/Probe/CaptionAncestorMarkerTProbe` observes zero
such pairs across all nested inputs and direction/profile configs. -/
theorem captionAncestorOtherClear_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (_hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run) :
    CaptionAncestorOtherClear execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
  intro _i _stored0 tNode _hmem hnode hborder pos fNode _g0 hfn hne hancrel hne2
    hneB2 _hframe
  have hshape := (componentCandidate_marker_shape execution.graph_eq hfn).1
  rcases hshape with h0 | hm2 | h2
  · obtain ⟨origT, _, hsrcT⟩ := componentCandidate_nonplain_source hnode (by omega)
    rw [componentCandidate_nodes] at hfn
    have hmap : (componentGraph execution.graph comp).nodes =
        comp.map (fun v => execution.graph.nodes.getD v default) := rfl
    rw [hmap, List.getElem?_map] at hfn
    obtain ⟨origP, hcompP, hgetP⟩ := Option.map_eq_some_iff.mp hfn
    have hmemP : origP ∈ comp := List.mem_of_getElem? hcompP
    have hltP : origP < execution.graph.nodes.length :=
      components_mem_bound_copy hcomp hmemP
    obtain ⟨n, hn⟩ : ∃ n, execution.graph.nodes[origP]? = some n :=
      ⟨_, List.getElem?_eq_some_iff.mpr ⟨hltP, rfl⟩⟩
    have hget : execution.graph.nodes.getD origP default = n := by
      simp [List.getD_eq_getElem?_getD, hn]
    rw [hget] at hgetP
    rw [hgetP] at hn
    obtain ⟨boxT, hboxT, hdeclT, hpathT⟩ :=
      execution.group_node_path_source hsrcT hborder
    obtain ⟨boxP, hboxP, hdeclP, _⟩ :=
      execution.plain_node_path_source hn h0
    rw [hpathT, hdeclP] at hancrel
    have hnePO : origP ≠ origT :=
      fun hcon => hne (hdeclT.trans (hcon.symm.trans hdeclP.symm))
    have hmemAppend : origP ∈ Compound.path inp.boxes boxT ++ [origT] := by
      have hdec : decide (origP ∈ Compound.path inp.boxes boxT ++ [origT]) = true := by
        rw [← List.contains_eq_mem]
        exact hancrel
      exact of_decide_eq_true hdec
    rcases List.mem_append.mp hmemAppend with hleft | hright
    · let eff : List ModelBox := inp.boxes.map fun b =>
        if inp.fixedSizes.any (fun fixed => fixed.1 == b.id) then
          { b with role := .node } else b
      let chT : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == boxT.id) then
        { boxT with role := .node } else boxT)
      let chP : ModelBox := (if inp.fixedSizes.any (fun fixed => fixed.1 == boxP.id) then
        { boxP with role := .node } else boxP)
      obtain ⟨_, heffP, _⟩ := fixedSizes_path_index inp hboxP
      obtain ⟨_, _, hpathMapT⟩ := fixedSizes_path_index inp hboxT
      have hpathT_eq : Compound.path eff chT = Compound.path inp.boxes boxT :=
        hpathMapT
      have heffP' : eff[origP]? = some chP := heffP
      have hdemT : chT.parent = boxT.parent := (otherClear_demote_facts boxT).2.1
      have hmemFuel : origP ∈ Compound.ancestors eff eff.length boxT.parent := by
        have hmemChT : origP ∈ Compound.path eff chT := by
          rw [hpathT_eq]
          exact hleft
        rw [← hdemT]
        exact hmemChT
      have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
      obtain ⟨b, hb, hrole⟩ := otherClear_path_group_role hframed hids eff rfl
        eff.length boxT (List.mem_of_getElem? hboxT) origP hmemFuel
      have hbeq : b = chP := Option.some.inj (hb.symm.trans heffP')
      subst hbeq
      obtain ⟨nodes, edges, titles, hprepared, hnodesLen, _⟩ :=
        measuredGraph_prepared_source execution.graph_eq
      have hltLen : origP < nodes.length := by
        rw [hnodesLen, boxLines_length execution.lines_eq]
        exact (List.getElem?_eq_some_iff.mp hboxP).1
      have hpreparedNode : (Compound.prepare eff execution.params.clusterPad titles
          { nodes := nodes, edges := edges,
            slot := execution.params.slot }).nodes[origP]? = some fNode := by
        have h := hn
        rw [hprepared] at h
        exact h
      have hroleNe : chP.role ≠ .group := by
        intro hgroup
        have hrec := Compound.prepare_group_title_record eff execution.params.clusterPad
          titles { nodes := nodes, edges := edges, slot := execution.params.slot }
          hltLen heffP' hgroup
        have heq := Option.some.inj (hpreparedNode.symm.trans hrec)
        have hb2 : fNode.border = -2 := congrArg Node.border heq
        rw [h0] at hb2
        omega
      exact absurd hrole hroleNe
    · have hsingleton : origP = origT := List.mem_singleton.mp hright
      exact absurd hsingleton hnePO
  · exact absurd hm2 hne2
  · exact absurd h2 hneB2

/-- Closed run-level caption clearance for one executed component run: the
seven per-run hypotheses of `captionRunClear_executed`, with the six local
residuals discharged by their executed suppliers and the foreign span
hypothesis built from the three foreign seams exactly as
`foreignFramesDisjoint_of_run` builds it. Only `ForeignBorderChainXAligned`
stays open. -/
theorem captionRunClear_closed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    {comp : List Nat} (hcomp : comp ∈ components execution.graph)
    {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
    (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
      execution.measured orderOptions = .ok run)
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) :
    CaptionRunClear execution.params (componentCandidate execution.graph comp candidate) run
      (transportCapSize execution.params o execution.lines comp) := by
  have hside := captionSelfSidesStrict_executed execution hwf hframed hcomp hrun
  have hmark := captionSameDeclMarkerDisjoint_executed execution hcomp hrun
  have hmemdesc := captionMemberDescDisjoint_executed execution hwf hframed hcomp hrun
  have hnest := captionAncestorGroupFrameStrict_executed execution hwf hframed hcomp hrun
  have hmarkAnc : CaptionAncestorMarkerClear execution.params
      (componentCandidate execution.graph comp candidate) run o execution.lines comp := by
    intro i stored0 tNode hmem hnode hborder pos fNode g0 hfn hne hancrel hbor2 hframe
    exact captionAncestorMarkerClear_executed execution hwf hframed hcomp hrun hmem hnode
      hborder hfn hne hancrel hbor2 hframe
  have hotherAnc := captionAncestorOtherClear_executed execution hwf hframed hcomp hrun
  have hrank : ForeignClusterRankSpans := foreignClusterRankSpans'
  have hbr : BracketMarkersAtRank := bracketMarkersAtRank'
  have hgroups : ForeignBorderSpansSeparated :=
    foreignBorderSpansSeparated hrank foreignBorderLayerOrder' hx
  have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hx
  have hothers : ForeignNonGroupSpansClear :=
    foreignNonGroupSpansClear hbr plainClearOfSideMarker' halign
  have hlines : execution.lines.length = inp.boxes.length :=
    boxLines_length execution.lines_eq
  have hclear : ForeignSpansClear execution.params
      (componentCandidate execution.graph comp candidate) run :=
    foreignSpansClear_of_run hgroups hothers execution.graph_eq hlines hwf hframed hcomp hrun
  exact captionRunClear_executed execution hwf hcomp hrun hclear hside hmark hmemdesc hnest
    hmarkAnc hotherAnc

/-- The part-level consumer's caption-size function is exactly the transport
size: `executedPartFrameCores` states its `hcap` with the unfolded lambda. -/
theorem measuredCapSize_eq_transport (P : Params) (o : Options)
    (lines : List (List Measure.Line)) (comp : List Nat) :
    (fun i => ((titleCaptionSize P o (lines.getD (comp.getD i 0) [])).w,
      (titleCaptionSize P o (lines.getD (comp.getD i 0) [])).h)) =
      transportCapSize P o lines comp := rfl

/-- Bridge to the part-level consumer form: the `hcap` hypothesis
`executedPartFrameCores` needs, with `labels` fixed to `execution.measured`
(the only instantiation both transports use) and the caption size in
`transportCapSize` form (definitionally the consumer's lambda). -/
theorem captionHalf_closed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hframed : framedParents inp = true)
    (hx : ForeignBorderChainXAligned) :
    ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
        componentRun execution.params (componentCandidate execution.graph comp candidate)
          execution.measured orderOptions = .ok run →
        CaptionRunClear execution.params (componentCandidate execution.graph comp candidate) run
          (transportCapSize execution.params o execution.lines comp) := by
  intro comp hcomp candidate run orderOptions hrun
  exact captionRunClear_closed execution hwf hcomp hrun hframed hx

/-- The caption conjunct of `ExecutedPartFrameCores`, from the run-level
caption residual restricted to `execution.measured`: copy of
`partCaption_of_run` with the `labels` argument fixed, since the transport
only ever instantiates the executed labels. -/
theorem partCaption_of_run_measured {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hres : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          execution.measured orderOptions = .ok run →
        CaptionRunClear execution.params
          (componentCandidate execution.graph comp candidate) run
          (transportCapSize execution.params o execution.lines comp)) :
    ∀ part ∈ execution.componentsAcc.parts,
      PartCaptionFrameClear execution.params inp o execution.lines part := by
  intro part hpart i stored pos _key _src g hmem _hkey _hbox _hgrp hrect
  obtain ⟨index, run, loops, _area, hcomp, hrun, heq⟩ :=
    execution_part_run execution hpart
  have eT : part.2.titles =
      (componentTitles execution.params
        (componentCandidate execution.graph part.1 index) run).map (fun q =>
        (q.1, shiftRect
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minX)
          (0 - (placeBounds execution.params
            (componentCandidate execution.graph part.1 index) run
            execution.measured loops).minY) q.2)) := by
    have h1 : part.2.titles =
        (placeComponent execution.params
          (componentCandidate execution.graph part.1 index) run 0
          execution.measured loops).titles := by
      rw [heq]
    rw [h1]
    exact placeComponent_titles_eq _ _ _ _ _
  have eR' : part.2.rects = (placeComponent execution.params
      (componentCandidate execution.graph part.1 index) run 0
      execution.measured loops).rects := by
    rw [heq]
  rw [eT] at hmem
  obtain ⟨⟨i0, stored0⟩, h0mem, h0eq⟩ := List.mem_map.mp hmem
  simp only [Prod.mk.injEq] at h0eq
  obtain ⟨rfl, hstored⟩ := h0eq
  have hlen : part.2.rects.length =
      (componentCandidate execution.graph part.1 index).nodes.length := by
    rw [eR']
    exact placeComponent_rects_length _ _ _ _ _
  have hlt : pos <
      (componentCandidate execution.graph part.1 index).nodes.length := by
    have h := (List.getElem?_eq_some_iff.mp hrect).1
    omega
  have hframe := placeComponent_rect_get execution.params
    (componentCandidate execution.graph part.1 index) run execution.measured
    loops hlt
  rw [eR'] at hrect
  rw [hframe] at hrect
  have hg0 : shiftRect
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minX)
      (0 - (placeBounds execution.params
        (componentCandidate execution.graph part.1 index) run
        execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run pos) = g :=
    Option.some.inj hrect
  obtain ⟨top, htop, hborder, htitleIdx, _hw, _hh⟩ :=
    componentTitles_dimension_source execution.params
      (componentCandidate execution.graph part.1 index) run h0mem
  have hidx : i0 = top.2 := htitleIdx
  have hnode : (componentCandidate execution.graph part.1 index).nodes[i0]? =
      some top.1 := by
    rw [hidx]
    exact List.mem_zipIdx_iff_getElem?.mp htop
  have hclear := hres part.1 hcomp index run
    (candidateOrder index) hrun i0 stored0 top.1 h0mem hnode hborder
    pos _ hlt rfl
  dsimp only
  rw [←hg0, ←hstored, captionResize_shift_comm]
  rcases hclear with h | h
  · exact Or.inl (disjoint_shiftRect h)
  · exact Or.inr (strictInside_shiftRect h)

/-- The `measured`-only variant of `executedPartFrameCores`: copy of its proof,
with `hcap` restricted to `execution.measured` (the only instantiation the
transports use) and stated with `transportCapSize` (definitionally the
consumer's lambda, by `measuredCapSize_eq_transport`). -/
theorem executedPartFrameCores_measured {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    (hroute : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run),
      ∀ (labels : List MeasuredLabel) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          labels orderOptions = .ok run →
        RouteRunClear execution.params
          (componentCandidate execution.graph comp candidate) run labels)
    (hcap : ∀ (comp : List Nat), comp ∈ components execution.graph →
      ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
        componentRun execution.params
          (componentCandidate execution.graph comp candidate)
          execution.measured orderOptions = .ok run →
        CaptionRunClear execution.params
          (componentCandidate execution.graph comp candidate) run
          (transportCapSize execution.params o execution.lines comp)) :
    ExecutedPartFrameCores execution := by
  intro part hpart
  exact ⟨partRoute_of_run execution hroute part hpart,
    partCaption_of_run_measured execution hcap part hpart⟩

end Elegant.Layered.PipelineImpl
