import Elegant.Layered.ExactPipeline
import Elegant.Layered.ExactFlatFacts
import Elegant.Layered.ExactFlatC5SelfRoutes
import Elegant.Layered.ExactPartBounded
import Elegant.Layered.ExactBorder2UnchangedProof
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.RecursiveBLiftsB
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.RecursiveCallParams
import Elegant.Layered.RecursiveC1C3
import Elegant.Layered.RecursiveC2
import Elegant.Layered.RecursiveC6
import Elegant.Layered.RecursiveFit
import Elegant.Layered.InsetFit
import Elegant.Layered.SceneBounds
import Elegant.Layered.SizingFacts
import Elegant.Layered.CoordGraph
import Elegant.Layered.CgShape
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.ExpandChildContainment
import Elegant.Layered.ExpandChildC2Facts
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.Assembly
import Elegant.Layered.Compound
import Elegant.Layered.PipelineFacts
import Elegant.Model

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Exact fit-closure and canvas margins

Closes the two remaining `ExactSeams` fields over `layoutX exactIds`, replaying
the plain `baseSeams_of_layered` proofs (`FamilyAssemblyB.lean`) over the exact
stages.

* `exactCanvasMargins` needs no residual: the exact flat scene is bounded by
  `SceneExecutionX.packedAcc_bounded` over `exactPartsBounded'`, so the exact
  leaf enjoys the same `sceneOf` canvas lower bound as the plain leaf
  (`layout_canvas_margins`), and the `B`-recursion inherits it through
  `expandChild_canvas`, exactly as `layoutRecursive_canvas_margins` does.
* `exactFitClosed` replays the plain `fitClosed` proof (`FamilyAssemblyB.lean`
  lines 270-332): `expandChild` is shared by both pipelines, so the call
  context, title wrap, and lookup transports are base-independent. The
  parent-closure conjuncts replay `X_rec_parent_closed_wellFormed` (copied
  below from `ExactSubInputStepC2.lean`, whose `private` lemmas cannot be
  imported). The frame-fit conjunct replays
  `layoutRecursive_childInset_fits_frame` with `X_ids` (copied below from
  `ExactStepFacts.lean`) in place of `layoutRecursive_ids`. Its one
  base-dependent link is the residual `XExactFixedMin`: the exact parent
  layout output gives its fixed group box at least the reserved
  `childFrameSize`, i.e. the exact-base replay of
  `layoutRecursive_fixed_source_box_minimum_dimensions_with_role`, whose only
  unproved link is the exact leaf fact
  `SceneExecutionX.fixed_source_box_minimum_dimensions_with_role` (the same
  fixed-size mechanism as the plain `SceneExecution` proof, against
  `exactGraph`).
-/

/-- Exact leaf canvas margins: `layoutX` builds its scene with the same
`sceneOf` call as `layout`, so the proof is `layout_canvas_margins` with the
exact execution. No placement hypothesis is needed: `packAcc_canvas_nonneg`
holds for every successful `packAcc`. -/
private theorem X_layout_canvas_margins {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (h : layoutX exactIds inp o = .ok res) :
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.w ∧
    2 * canvasMarginOf o.profile inp.kind ≤ res.scene.canvas.h := by
  obtain ⟨execution⟩ := layoutX_sceneExecution h
  have hb := packAcc_canvas_nonneg execution.packed_eq
  rw [← checkedParams_canvasMargin execution.checked]
  rw [execution.scene_eq]
  change _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).w ∧
    _ ≤ (orientCanvas o.direction
    (execution.packedAcc.canvasW + 2 * _)
    (execution.packedAcc.canvasH + 2 * _)).h
  cases o.direction <;> simp only [orientCanvas] <;> omega

/-- The exact pipeline discharges the base-parametric canvas-margin fact:
every `layoutRecursiveB (layoutX exactIds)` result keeps both margins. The
induction copies `layoutRecursive_canvas_margins`, with the exact leaf fact
above and the shared `expandChild_canvas`. -/
theorem exactCanvasMargins (exactIds : List String) :
    CanvasMarginsB (layoutX exactIds) := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res h P hP
    have hm := X_layout_canvas_margins h
    rw [checkedParams_canvasMargin hP]
    exact hm
  | succ fuel ih =>
    intro inp o res h P hP
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with ⟨_, hlayout⟩ |
      ⟨group, Pm, metric, child, titleLines, parent, hg, hPm, hm, hc, ht, hp, hexpand⟩
    · have hm := X_layout_canvas_margins hlayout
      rw [checkedParams_canvasMargin hP]
      exact hm
    · have hc2 := expandChild_canvas hexpand
      rw [hc2]
      exact ih _ _ _ hp P hP

/-- Residual fixed-size hypothesis for `exactFitClosed`: the exact-base
replay of `layoutRecursive_fixed_source_box_minimum_dimensions_with_role`.
It speaks about one named exact stage only (the fixed group-size bounds of
an exact parent-layout output). It holds for the same reason as the plain
fact: the parent input carries `(group.id, childFrameSize ...)` in
`fixedSizes`, and the exact leaf honors fixed sizes the way the plain leaf
does; the only unproved link is the exact leaf minimum-dimensions fact over
`SceneExecutionX`, plus the `B`-induction which replays the plain one with
`X_ids`. -/
def XExactFixedMin (exactIds : List String) : Prop :=
  ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult)
    (source : ModelBox) (entry : String × Size),
    (inp.boxes.map (·.id)).Nodup → RoutesCovered inp →
    layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    source ∈ inp.boxes →
    inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry →
    ∃ box : Box, res.scene.layoutDump.box? source.id = some box ∧
      box.role = source.role.id ∧ entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h

/-- Exact leaf id fact: `layoutX` builds its scene with the same `sceneOf`
call as `layout`, so the proof is `layout_ids` with one extra bind for the
`exactGraph` step. Copy of the private `X_layout_ids` in
`ExactSubInputStepC2.lean`. -/
private theorem X_layout_ids {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf, List.map_map]
    exact ⟨zipIdx_map_comp (·.id) inp.boxes 0, zipIdx_map_comp (·.id) inp.routes 0⟩

/-- Exact leaf mirror fact: every exact scene box carries the id and parent
pointer of a source input box. Copy of the private `X_layout_box_parent` in
`ExactSubInputStepC2.lean`. -/
private theorem X_layout_box_parent {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutX exactIds inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  unfold layoutX at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  obtain ⟨acc, _, h⟩ := bind_ok h
  split at h
  · simp at h
  · have h := Except.ok.inj h
    subst h
    simp only [sceneOf]
    intro cb hcb
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
    exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Exact flat parent closure, from the two leaf facts above. Copy of the
private `X_layout_parent_closed` in `ExactSubInputStepC2.lean`. -/
private theorem X_layout_parent_closed {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (hf : InputFacts inp) (h : layoutX exactIds inp o = .ok res) :
    SceneParentClosed res.scene := by
  intro bb hbb
  obtain ⟨hidsB, _⟩ := X_layout_ids h
  obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent h bb hbb
  rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
  · rw [hsbpar]; exact Or.inl h0
  · have hqidIn : q.id ∈ res.scene.boxes.map (·.id) := by
      rw [hidsB]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨bb', hbb', hbb'id⟩ := List.mem_map.mp hqidIn
    rw [hsbpar]
    exact Or.inr ⟨bb', hbb', hbb'id.trans hqid⟩

/-- Successor split for `layoutRecursiveB` at the exact base, in the shape of
`layoutRecursive_succ`: the concrete appended tables are generalized to
`∃ a b c` so the induction proofs below copy the plain ones verbatim. Copy
of the private `X_B_succ` in `ExactSubInputStepC2.lean`. -/
private theorem X_B_succ (exactIds : List String) {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (h : layoutRecursiveB (layoutX exactIds) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      layoutX exactIds inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (layoutX exactIds) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (layoutX exactIds) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (layoutX exactIds) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _, _, hc, _, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

/-- Exact `B`-recursion mirror fact: every scene box of a successful exact
recursive layout carries the id and parent pointer of a source input box.
Copy of the private `X_rec_box_parent` in `ExactSubInputStepC2.lean`. -/
private theorem X_rec_box_parent (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact X_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact X_layout_box_parent hlayout
    · have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
          ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
        intro keep root
        rw [selectInput_box_ids]
        exact nodup_filter_map keep (·.id) inp.boxes hnodup
      have hchildNodup : ((selectInput inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
            (·.id)).Nodup := hselNodup _ _
      have hparentNodup : (({ selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } : Input).boxes.map
            (·.id)).Nodup := by
        show ((selectInput inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
            (·.id)).Nodup
        rw [selectInput_box_ids]
        exact nodup_filter_map _ _ _ hnodup
      have hchildParent := ih _ _ _ hchildNodup hchild
      have hparentParent := ih _ _ _ hparentNodup hparent
      obtain ⟨_frame, _metric', _titleLines', _lines, dx, dy, _hframe, _hmetric',
        _htitle', _hlines', _hdx, _hdy, _hcanvas, hboxes⟩ := expandChild_sources hexpand
      intro cb hcb
      rw [hboxes] at hcb
      obtain ⟨_model, _hmodelmem, hfind⟩ := List.mem_filterMap.mp hcb
      have hcbItems : cb ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
          parent.scene.boxes := List.mem_of_find?_eq_some hfind
      rcases List.mem_append.mp hcbItems with hbc | hbp
      · obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
        obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hchildParent cbb hcbbmem
        obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
        have hne : m.parent ≠ "" := by
          have hkeep' : Compound.inside inp.boxes group.id m.id = true := hkeep
          exact inside_parent_ne_empty hnodup hkeep' hmmem rfl
        refine ⟨m, hmmem, ?_, ?_⟩
        · have hcid : cbb.id = cb.id := by
            have h := congrArg (fun b : Box => b.id) hEmbed
            simpa [embedBox] using h
          exact hmsbid.symm.trans (hsbid.trans hcid)
        · have hcpar : cb.parent = (if cbb.parent == "" then group.id else cbb.parent) := by
            have h := congrArg (fun b : Box => b.parent) hEmbed
            simpa [embedBox] using h.symm
          rw [hsbpar, hmsbpar] at hcpar
          exact hcpar.trans (embed_parent_eq hne)
      · obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hparentParent cb hbp
        obtain ⟨m, _hmmem, _hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, _hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · have hsp : sb.parent = m.parent := by
            rw [hmsbpar]
            exact selectInput_parent_root m.parent
          exact hsbpar.trans hsp

/-- Exact `B`-recursion coverage: every nonempty parent pointer of a result
scene box names an input box id of the laid-out input. Copy of the private
`X_rec_parent_in_ids` in `ExactSubInputStepC2.lean`. -/
private theorem X_rec_parent_in_ids (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      ∀ p ∈ res.scene.boxes, p.parent ≠ "" → p.parent ∈ inp.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h p hp hne
      obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent h p hp
      rw [hsbpar] at hne ⊢
      rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
      · exact absurd h0 hne
      · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro inp o res hf h p hp hne
      rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · obtain ⟨sb, hsb, _, hsbpar⟩ := X_layout_box_parent hlayout p hp
        rw [hsbpar] at hne ⊢
        rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
        · exact absurd h0 hne
        · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
      · obtain ⟨_, _metric, _titleLines, _lines, dx, dy, _hframe, _, _, _, _, _, _,
          hboxes⟩ := expandChild_sources hexpand
        rw [hboxes] at hp
        obtain ⟨_, _, hfind⟩ := List.mem_filterMap.mp hp
        have hfound : p ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
            parent.scene.boxes := List.mem_of_find?_eq_some hfind
        rcases List.mem_append.mp hfound with hcb | hpb
        · obtain ⟨cb, hcbmem, hE⟩ := List.mem_map.mp hcb
          have hproj : p.parent = (if cb.parent == "" then group.id else cb.parent) := by
            have hpar := congrArg (fun bx : Box => bx.parent) hE
            simpa [embedBox] using hpar.symm
          by_cases hcb0 : cb.parent = ""
          · rw [hproj]
            split
            · exact List.mem_map.mpr ⟨group, List.mem_of_find?_eq_some hg, rfl⟩
            · rename_i hcond
              exact absurd (beq_iff_eq.mpr hcb0) hcond
          · rw [hproj]
            split
            · rename_i hcond
              exact absurd (beq_iff_eq.mp hcond) hcb0
            · have hchildFacts := selectInput_facts_inside inp group hf
              have hcov := ih _ _ _ hchildFacts hchild cb hcbmem hcb0
              exact selectInput_ids_subset inp
                (fun box => Compound.inside inp.boxes group.id box.id) group.id hcov
        · have hparentFacts : InputFacts { selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) with
              fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
            inputFacts_congr
              (rfl : (selectInput inp
                (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                  { selectInput inp
                    (fun box => !Compound.inside inp.boxes group.id box.id) with
                    fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
            (selectInput_facts_outside inp group hf)
          have hpIn := ih _ _ _ hparentFacts hparent p hpb hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpIn

/-- Exact `B`-recursion parent closure: every nonempty parent pointer of a
result scene stays inside that scene. Copy of the private
`X_rec_parent_closed` in `ExactSubInputStepC2.lean`. -/
private theorem X_rec_parent_closed (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
      SceneParentClosed res.scene := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h
      exact X_layout_parent_closed hf h
  | succ fuel ih =>
      intro inp o res hf h
      rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · exact X_layout_parent_closed hf hlayout
      · have hchildFacts := selectInput_facts_inside inp group hf
        have hparentFacts : InputFacts { selectInput inp
            (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } :=
          inputFacts_congr
            (rfl : (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes =
                { selectInput inp
                  (fun box => !Compound.inside inp.boxes group.id box.id) with
                  fixedSizes := a, fixedChildren := b, fixedAreas := c }.boxes)
            (selectInput_facts_outside inp group hf)
        have hcc := ih _ _ _ hchildFacts hchild
        have hpc := ih _ _ _ hparentFacts hparent
        have hcoverC : ∀ q ∈ child.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hci := X_rec_parent_in_ids exactIds fuel _ _ _ hchildFacts hchild q hq hne
          exact selectInput_ids_subset inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        have hcoverP : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hpi := X_rec_parent_in_ids exactIds fuel _ _ _ hparentFacts hparent q hq hne
          exact selectInput_ids_subset inp
            (fun box => !Compound.inside inp.boxes group.id box.id) "" hpi
        have hgroupRes : ∃ q ∈ res.scene.boxes, q.id = group.id := by
          obtain ⟨frame, _, _, _, dx, dy, hframe, _, _, _, _, _, _, hboxes⟩ :=
            expandChild_sources hexpand
          have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
          cases hF : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
              parent.scene.boxes).find? (fun box => box.id == group.id) with
          | none =>
              have hnone := List.find?_eq_none.mp hF frame
                (List.mem_append_right _ (List.mem_of_find?_eq_some hframe))
              rw [hframeId] at hnone
              simp at hnone
          | some f =>
              refine ⟨f, ?_, ?_⟩
              · rw [hboxes]
                exact filterMap_mem_of_find (fun m : ModelBox => m.id) inp.boxes
                  (fun bx : Box => bx.id) _ group (List.mem_of_find?_eq_some hg) f hF
              · simpa using List.find?_some hF
        exact expandChild_parent_closed hpc hcc hcoverC hcoverP hgroupRes hexpand

/-- Parent closure of a successful exact recursive layout from well-formedness
of the original input model alone. Copy of the private
`X_rec_parent_closed_wellFormed` in `ExactSubInputStepC2.lean`. -/
private theorem X_rec_parent_closed_wellFormed (exactIds : List String)
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o)) :
    ∀ (fuel : Nat) (res : FamilyResult),
      layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
        SceneParentClosed res.scene := by
  intro fuel res h
  exact X_rec_parent_closed exactIds fuel inp o res (inputFacts_of_wellFormed hwf) h

/-- Exact `B`-recursion id fact: scene ids of a successful exact recursive
layout are the sub-input ids. Copies `layoutRecursive_ids` with `X_B_succ`
and the exact leaf fact; copy of the private `XB_ids` in
`ExactStepFacts.lean`. -/
private theorem X_ids (exactIds : List String) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursiveB (layoutX exactIds) fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero => intro inp o res _ h; exact X_layout_ids h
  | succ fuel ih =>
    intro inp o res hc h
    rcases X_B_succ exactIds h with ⟨_, hlayout⟩ |
      ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact X_layout_ids hlayout
    · have hgi := List.find?_some hg
      simp only [Bool.and_eq_true] at hgi
      have hin := independent_inside hgi.1
      have ih1 := ih _ _ _
        (selectInput_routesCovered inp
          (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
      have ih2 := ih
        { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
          fixedSizes := a, fixedChildren := b, fixedAreas := c } o parent
        (selectInput_routesCovered inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "") hparent
      have idsC := selectInput_box_ids inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      have idsP := selectInput_box_ids inp
        (fun box => !Compound.inside inp.boxes group.id box.id) ""
      refine expandChild_ids hexp ?_ ?_
      · intro bx hbx
        by_cases hi : Compound.inside inp.boxes group.id bx.id = true
        · have hm : bx.id ∈ child.scene.boxes.map (·.id) := by
            rw [ih1.1, idsC]
            exact mem_filter_ids inp _ bx hbx hi
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hm : bx.id ∈ parent.scene.boxes.map (·.id) := by
            rw [ih2.1]
            show bx.id ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map (·.id)
            rw [idsP]
            exact mem_filter_ids inp _ bx hbx (by simpa using hi)
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩
      · intro r hr
        obtain ⟨⟨bf, hbf, ef⟩, ⟨bt, hbt, et⟩⟩ := hc r hr
        have heq := hin r hr
        by_cases hi : Compound.inside inp.boxes group.id r.fromId = true
        · have hit : Compound.inside inp.boxes group.id r.toId = true := by
            rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => Compound.inside inp.boxes group.id box.id) group.id).routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsC]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; exact hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; exact hit)
          have hm : r.id ∈ child.scene.routes.map (·.id) := by
            rw [ih1.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_left _ hx, e⟩
        · have hit : ¬ Compound.inside inp.boxes group.id r.toId = true := by
            rw [← heq]; exact hi
          have hmem : r ∈ (selectInput inp
              (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := by
            rw [selectInput_route_mem, any_id_iff, any_id_iff, idsP]
            refine ⟨hr, ?_, ?_⟩
            · rw [← ef]; exact mem_filter_ids inp _ bf hbf (by rw [ef]; simpa using hi)
            · rw [← et]; exact mem_filter_ids inp _ bt hbt (by rw [et]; simpa using hit)
          have hm : r.id ∈ parent.scene.routes.map (·.id) := by
            rw [ih2.2]
            exact List.mem_map.mpr ⟨r, hmem, rfl⟩
          obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
          exact ⟨x, List.mem_append_right _ hx, e⟩

/-- Scene ids of the two exact sub-layouts are disjoint. Copies
`recursive_selected_box_ids_disjoint` with `X_ids`; copy of the private
`XB_disjoint` in `ExactStepFacts.lean`. -/
private theorem X_disjoint (exactIds : List String)
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hchild : layoutRecursiveB (layoutX exactIds) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id) := by
  have hc := X_ids exactIds fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := X_ids exactIds fuel _ _ _ hparentCoverage hparent
  have hcIds := hc.1
  have hpIds := hp.1
  change parent.scene.boxes.map (·.id) =
    (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
      (·.id) at hpIds
  rw [selectInput_box_ids] at hcIds hpIds
  intro id hidChild hidParent
  rw [hcIds] at hidChild
  rw [hpIds] at hidParent
  obtain ⟨childBox, hchildBox, hchildId⟩ := List.mem_map.mp hidChild
  obtain ⟨parentBox, hparentBox, hparentId⟩ := List.mem_map.mp hidParent
  have hinside := (List.mem_filter.mp hchildBox).2
  have houtside := (List.mem_filter.mp hparentBox).2
  have heqId : childBox.id = parentBox.id := hchildId.trans hparentId.symm
  rw [heqId] at hinside
  simp only [hinside, Bool.not_true, Bool.false_eq_true] at houtside

/-- Frame fit for the shifted child *inset* canvas in the actual exact
recursion context. Replays `layoutRecursive_childInset_fits_frame` with the
exact `B`-recursion: the executed-value alignment is unnecessary because the
context already supplies the executed `P`, `child`, and `parent`, and
`X_ids` replaces `layoutRecursive_ids`. The fixed-size link is the
`hfixedMin` residual. -/
private theorem X_childInset_fit (exactIds : List String)
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {child : FamilyResult} {titleLines : List Measure.Line}
    {titleHeight : Int} {parent : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hP : checkedParams o.profile inp.kind = .ok P)
    (hparent : layoutRecursiveB (layoutX exactIds) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hfixedMin : XExactFixedMin exactIds)
    (frame : Box) (fdx fdy : Int)
    (hframe : parent.scene.boxes.find? (fun box => box.id == group.id) = some frame)
    (hdx : fdx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin)
    (hdy : fdy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin)
    (htitleH : titleHeight = (max 1 titleLines.length : Int) * P.lineH) :
    frame.rect.Contained (shiftRect fdx fdy (insetRect child.scene.canvas P.canvasMargin)) := by
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  let baseParent := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
  let size := childFrameSize group.direction P.clusterPad
    (titleLines.foldl (fun width line => max width line.width) 0)
    ((max 1 titleLines.length : Int) * P.lineH)
    ⟨child.scene.canvas.w - 2 * P.canvasMargin,
      child.scene.canvas.h - 2 * P.canvasMargin⟩
  let parentInput : Input := { baseParent with
    fixedSizes := baseParent.fixedSizes ++ [(group.id, size)]
    fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
    fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] }
  have hparentAt : layoutRecursiveB (layoutX exactIds) fuel parentInput o = .ok parent := hparent
  have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
    change (baseParent.boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact List.Nodup.sublist ((List.filter_sublist).map _) hboxIds
  have hparentCovered : RoutesCovered parentInput := by
    change RoutesCovered baseParent
    exact selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hparentOutputIds := (X_ids exactIds fuel _ _ _ hparentCovered hparentAt).1
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hparentSourceId : group.id ∈ parentInput.boxes.map (·.id) := by
    rw [← hparentOutputIds, ← hframeId]
    exact List.mem_map.mpr ⟨frame, List.mem_of_find?_eq_some hframe, rfl⟩
  obtain ⟨source, hsource, hsourceId⟩ := List.mem_map.mp hparentSourceId
  have hsourceBase : source ∈ baseParent.boxes := hsource
  obtain ⟨original, horiginal, _, hsourceEq⟩ :=
    selectInput_box_source inp (fun box => !Compound.inside inp.boxes group.id box.id)
      "" source hsourceBase
  have hsourceOriginalId : source.id = original.id := by
    rw [hsourceEq]
    split <;> rfl
  have horiginalId : original.id = group.id := hsourceOriginalId.symm.trans hsourceId
  have horiginalLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds original horiginal
  have hgroupLookup := Assembly.keyed_lookup_eq (·.id) inp.boxes hboxIds
    group (List.mem_of_find?_eq_some hgroup)
  rw [horiginalId] at horiginalLookup
  have horiginalEq : original = group :=
    Option.some.inj (horiginalLookup.symm.trans hgroupLookup)
  have hnotfixed : inp.fixedSizes.any (fun fixed => fixed.1 == group.id) = false := by
    have hs := List.find?_some hgroup
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hnone : inp.fixedSizes.find? (fun fixed => fixed.1 == group.id) = none :=
    List.find?_eq_none.mpr (List.any_eq_false.mp hnotfixed)
  have hfixed : parentInput.fixedSizes.find? (fun fixed => fixed.1 == source.id) =
      some (group.id, size) := by
    change (inp.fixedSizes ++ [(group.id, size)]).find?
      (fun fixed => fixed.1 == source.id) = some (group.id, size)
    simp [List.find?_append, hsourceId, hnone]
  obtain ⟨actual, hactual, _, hw, hh⟩ :=
    hfixedMin fuel _ _ _ _ _ hparentIds hparentCovered hparentAt hsource hfixed
  rw [hsourceId] at hactual
  have hactualEq : actual = frame := Option.some.inj (hactual.symm.trans hframe)
  subst actual
  have hw' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := by
    have hw'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).w ≤ frame.rect.w := hw
    rw [← htitleH] at hw''
    exact hw''
  have hh' : (childFrameSize group.direction P.clusterPad
      (titleLines.foldl (fun width line => max width line.width) 0) titleHeight
      ⟨child.scene.canvas.w - 2 * P.canvasMargin,
        child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := by
    have hh'' : (childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩).h ≤ frame.rect.h := hh
    rw [← htitleH] at hh''
    exact hh''
  have htw : 0 ≤ titleLines.foldl (fun width line => max width line.width) 0 := by
    suffices key : ∀ (ls : List Measure.Line) (acc : Int), 0 ≤ acc →
        0 ≤ ls.foldl (fun width line => max width line.width) acc by
      exact key titleLines 0 (by omega)
    intro ls ac hac
    induction ls generalizing ac with
    | nil => simpa using hac
    | cons line ls ih =>
      simp only [List.foldl_cons]
      exact ih _ (Int.le_trans hac (Int.le_max_left _ _))
  have hth : 0 ≤ titleHeight := by
    rw [htitleH]
    exact Int.mul_nonneg (by omega) (checkedParams_lineH_nonneg hP)
  rw [hdx, hdy]
  exact childInsetCanvas_contained htw hth (checkedParams_clusterPad_nonneg hP) hw' hh'

/-- Child lookup transport for one exact `expandChild` call: every child box
lookup lands on its shifted image in the merged result. Replays the child
half of `layoutRecursive_embedding_assembly_sources` with `X_ids`. -/
private theorem X_child_transport {inp : Input} {group : ModelBox}
    {child parent res : FamilyResult} {dx dy : Int}
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id)))
    (hcIds : child.scene.boxes.map (·.id) =
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
        (·.id))
    (hnodup : (res.scene.boxes.map (·.id)).Nodup) :
    ∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box) := by
  intro box hbox
  change child.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box at hbox
  have hmember : box ∈ child.scene.boxes := List.mem_of_find?_eq_some hbox
  have hid : box.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hmember
  rw [hcIds, selectInput_box_ids] at hid
  obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hid
  have hmodel := (List.mem_filter.mp hmodelFilter).1
  have hcf : (child.scene.boxes.map (embedBox group.id dx dy)).find?
      (fun candidate => candidate.id == box.id) = some (embedBox group.id dx dy box) := by
    rw [List.find?_map]
    have hinside : (child.scene.boxes.find?
        ((fun candidate : Box => candidate.id == box.id) ∘ embedBox group.id dx dy)) =
        some box := by
      have hpred : ((fun candidate : Box => candidate.id == box.id) ∘
          embedBox group.id dx dy) = (fun cb => cb.id == box.id) := by
        funext cb
        simp only [Function.comp_apply, embedBox]
      rw [hpred]
      exact hbox
    rw [hinside]
    rfl
  have hfind : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes).find? (fun candidate => candidate.id == box.id) =
      some (embedBox group.id dx dy box) := by
    rw [List.find?_append]
    rw [hcf]
    rfl
  have hemitted : embedBox group.id dx dy box ∈ res.scene.boxes := by
    rw [hboxes]
    apply List.mem_filterMap.mpr
    refine ⟨model, hmodel, ?_⟩
    rw [hmodelId]
    exact hfind
  change res.scene.boxes.find? (fun candidate => candidate.id == box.id) =
    some (embedBox group.id dx dy box)
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup (embedBox group.id dx dy box) hemitted

/-- Parent lookup transport for one exact `expandChild` call: every parent
box lookup lands on itself in the merged result. Replays the parent half of
`layoutRecursive_embedding_assembly_sources` with `X_ids` and
`X_disjoint`. -/
private theorem X_parent_transport {inp : Input} {group : ModelBox}
    {child parent res : FamilyResult} {dx dy : Int}
    (hboxes : res.scene.boxes = inp.boxes.filterMap (fun model =>
      ((child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes).find? (fun box => box.id == model.id)))
    (hpIds : parent.scene.boxes.map (·.id) =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
        (·.id))
    (hnodup : (res.scene.boxes.map (·.id)).Nodup)
    (hdisjoint : ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id)) :
    ∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      res.scene.layoutDump.box? box.id = some box := by
  intro box hbox
  change parent.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box at hbox
  have hmember : box ∈ parent.scene.boxes := List.mem_of_find?_eq_some hbox
  have hid : box.id ∈ parent.scene.boxes.map (·.id) := List.mem_map_of_mem hmember
  rw [hpIds, selectInput_box_ids] at hid
  obtain ⟨model, hmodelFilter, hmodelId⟩ := List.mem_map.mp hid
  have hmodel := (List.mem_filter.mp hmodelFilter).1
  have hnone : (child.scene.boxes.map (embedBox group.id dx dy)).find?
      (fun candidate => candidate.id == box.id) = none := by
    apply List.find?_eq_none.mpr
    intro candidate hcandidate
    obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hcandidate
    intro htest
    have heq : native.id = box.id := beq_iff_eq.mp htest
    have hchildId : native.id ∈ child.scene.boxes.map (·.id) := List.mem_map_of_mem hnative
    have hparentId : native.id ∈ parent.scene.boxes.map (·.id) := by
      rw [heq]
      exact List.mem_map_of_mem hmember
    exact hdisjoint native.id hchildId hparentId
  have hfind : ((child.scene.boxes.map (embedBox group.id dx dy)) ++
      parent.scene.boxes).find? (fun candidate => candidate.id == box.id) = some box := by
    simp [List.find?_append, hnone, hbox]
  have hemitted : box ∈ res.scene.boxes := by
    rw [hboxes]
    apply List.mem_filterMap.mpr
    refine ⟨model, hmodel, ?_⟩
    rw [hmodelId]
    exact hfind
  change res.scene.boxes.find? (fun candidate => candidate.id == box.id) = some box
  exact Assembly.keyed_lookup_eq (·.id) res.scene.boxes hnodup box hemitted

/-- `packFold` preserves the rect array size (copy of the private
`packFold_rects_size` in `SizingCoverageBridge.lean`). -/
private theorem X_packFold_rects_size
    (pairs : List ((List Nat × Part) × Rect)) (start : Acc) :
    (pairs.foldl packStep start).rects.size = start.rects.size := by
  induction pairs generalizing start with
  | nil => rfl
  | cons pair rest ih =>
    rw [List.foldl_cons, ih]
    exact (packStep_sizes start pair).1

/-- Exact packed rect array size (copy of `SceneExecution.packed_rects_size`
with the exact components fold). -/
private theorem X_packed_rects_size {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res) :
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
  rw [X_packFold_rects_size]
  exact execution.components_rects_size

/-- Exact packed rect existence (copy of `SceneExecution.packed_rect_exists`). -/
private theorem X_packed_rect_exists {exactIds : List String} {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecutionX exactIds inp o res)
    {i : Nat} (hi : i < inp.boxes.length) :
    ∃ rect, execution.packedAcc.rects[i]? = some rect := by
  have hsize : i < execution.packedAcc.rects.size := by
    rw [X_packed_rects_size execution]
    exact hi
  exact ⟨execution.packedAcc.rects[i],
    Array.getElem?_eq_some_iff.mpr ⟨hsize, rfl⟩⟩


/-- Exact graph node dimensions respect every fixed-size entry. For boxes the
exact run keeps at measured size this is the plain
`measuredGraph_fixed_node_dims`; for exact boxes and fixed groups
`exactGraph` installs the oriented fixed dimensions. Replays the leaf half
of `layoutRecursive_fixed_source_box_minimum_dimensions_with_role` against
`SceneExecutionX`. -/
private theorem X_exactGraph_fixed_node_dims {exactIds : List String} {P : Params} {inp : Input}
    {o : Options} {lines : List (List Measure.Line)} {measured : List MeasuredLabel}
    {graph0 graph : Graph}
    (hg0 : measuredGraph P inp o lines = .ok graph0)
    (hg : exactGraph P exactIds inp o measured graph0 = .ok graph)
    {i : Nat} {ls : List Measure.Line} (hline : lines[i]? = some ls)
    {box : ModelBox} (hbox : inp.boxes[i]? = some box)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) = some entry) :
    ∃ node, graph.nodes[i]? = some node ∧ node.decl = i ∧ node.border = 0 ∧
      (match o.direction with
        | .LR | .RL => entry.2.h
        | .TB | .BT => entry.2.w) ≤ node.w ∧
      (match o.direction with
        | .LR | .RL => entry.2.w
        | .TB | .BT => entry.2.h) ≤ node.h := by
  obtain ⟨node0, hnode0, hdecl0, hborder0, hw0, hh0⟩ :=
    measuredGraph_fixed_node_dims hg0 hline hbox hfixed
  unfold exactGraph at hg
  obtain ⟨nodes, hnodes, h⟩ := bind_ok hg
  have he := Except.ok.inj h
  have hgnodes : graph.nodes = nodes := by simpa using (congrArg Graph.nodes he).symm
  obtain ⟨_, hmapGet⟩ := mapM_getElem? _ _ _ hnodes
  obtain ⟨nodeX, hfX, hmem⟩ := hmapGet i node0 hnode0
  rw [← hgnodes] at hmem
  cases hbox0 : inp.boxes[node0.decl]? with
  | none =>
    simp only [hbox0, pure, Except.pure] at hfX
    have hred : nodeX = node0 := Except.ok.inj hfX.symm
    rw [hred] at hmem
    exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
  | some box' =>
    rw [hdecl0] at hbox0
    have hbeq : box' = box := Option.some.inj (hbox0.symm.trans hbox)
    rw [hbeq] at hbox0
    simp only [hdecl0, hbox0] at hfX
    split at hfX
    · simp only [pure, Except.pure] at hfX
      have hred : nodeX = node0 := Except.ok.inj hfX.symm
      rw [hred] at hmem
      exact ⟨node0, hmem, hdecl0, hborder0, hw0, hh0⟩
    · cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == box.id) with
      | none =>
        simp only [hfind] at hfX
        cases hfX
      | some fixed =>
        simp only [hfind] at hfX
        have hentry : fixed = entry := Option.some.inj (hfind.symm.trans hfixed)
        rw [hentry] at hfX
        split at hfX
        · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hfX
          cases hfX
        · split at hfX
          · simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hfX
            cases hfX
          · simp only [pure, Except.pure] at hfX
            obtain rfl := Except.ok.inj hfX
            refine ⟨_, hmem, ?_, ?_, ?_, ?_⟩
            · cases hd : o.direction <;> rfl
            · cases hd : o.direction <;> exact hborder0
            · cases hd : o.direction <;> exact Int.le_refl _
            · cases hd : o.direction <;> exact Int.le_refl _

/-- Part rects of an exact component are shifted `frameRect`s (copy of the
private `placeComponentExact_rects_get` in `ExactFlatFacts.lean`). -/
private theorem X_placeComponentExact_rects_get {P : Params} {cg : Graph} {run : Run}
    {labels : List MeasuredLabel} {loops : List (Nat × LoopPlacement)} {cursor : Int}
    {i : Nat} (hi : i < cg.nodes.length) :
    (placeComponentExact P cg run cursor labels loops).rects[i]? =
      some (shiftRect (cursor - (placeBoundsX P cg run labels loops).minX)
        (-(placeBoundsX P cg run labels loops).minY)
        (frameRect P cg run i)) := by
  unfold placeComponentExact placeBoundsX
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some]

/-- Coordinate construction through `coordinateGraphX` preserves the
anchor node dimensions (copy of `coordinateGraph_plain_anchor_dims` with
the `sizeProperPortsX` first step; all later steps are shared). -/
private theorem X_coordinateGraphX_plain_anchor_dims (P : Params) {exact : List Nat} {p : Proper}
    {i : Nat} {nd : ProperNode} (hp : p.nodes[i]? = some nd)
    (hb : nd.node.border = 0) :
    ∃ out, (coordinateGraphX P exact p).nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨sized, hs, he, hb', hw, hh⟩ :
      ∃ sized, (sizeProperPortsX P exact p).nodes[i]? = some sized ∧
        sized.edge = nd.edge ∧ sized.node.border = 0 ∧
        nd.node.w ≤ sized.node.w ∧ sized.node.h = nd.node.h := by
    unfold sizeProperPortsX
    simp only [List.getElem?_map, List.getElem?_zipIdx, hp, Option.map_some]
    split
    · exact ⟨nd, rfl, rfl, hb, Int.le_refl _, rfl⟩
    · refine ⟨_, rfl, rfl, hb, ?_, rfl⟩
      exact Int.le_max_left _ _
  have hi := (List.getElem?_eq_some_iff.mp hs).1
  have htitle : (titleReservations (sizeProperPortsX P exact p)).nodes[i]? = some sized := by
    rw [titleReservations_nodes,
      List.getElem?_append_left (by simpa only [List.length_map] using hi)]
    simp [List.getElem?_map, hs, titleF, hb']
  obtain ⟨extra, hborder, _⟩ := addClusterBorders_extra
    (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW
  have hplaced : (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW).nodes[i]? = some sized := by
    rw [hborder,
      List.getElem?_append_left (List.getElem?_eq_some_iff.mp htitle).1]
    exact htitle
  have hclear : (clearProxyExtents (OrderImpl.addClusterBorders
      (titleReservations (sizeProperPortsX P exact p)) P.clusterBorderW)).nodes[i]? =
        some sized := by
    rw [clearProxyExtents_nodes]
    simp [List.getElem?_map, hplaced, clearF, hb']
  unfold coordinateGraphX materializeDummyPaths
  simp only [List.getElem?_map, List.getElem?_zipIdx, hclear, Option.map_some]
  split <;> exact ⟨_, rfl, he, hb', hw, hh⟩

/-- Proxy materialization keeps the X coordinate anchor (copy of
`componentRun_plain_node_dims` with `componentRunX_spec`). -/
private theorem X_componentRun_plain_node_dims {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {nd : ProperNode}
    (hnode : run.coordinateProper.nodes[i]? = some nd)
    (hborder : nd.node.border = 0) :
    run.proper.nodes[i]? = some nd := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hproxy, hdrop, _, _, _⟩ := componentRunX_spec h
  have hprojected := proxyWidths_plain_node hproxy hnode hborder
  rw [← hdrop]
  exact hprojected

/-- Coordinate anchor dimensions through the exact run (copy of
`componentRun_coordinateGraph_plain_node_dims`). -/
private theorem X_componentRun_coordinateGraph_plain_node_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {p : Proper} (hcoordinate : coordinateGraphX P exact p = run.coordinateProper)
    {i : Nat} {nd : ProperNode}
    (hnode : p.nodes[i]? = some nd) (hborder : nd.node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧
      out.edge = nd.edge ∧ out.node.border = 0 ∧
      nd.node.w ≤ out.node.w ∧ out.node.h = nd.node.h := by
  obtain ⟨out, hout, hedge, hplain, hw, hh⟩ :=
    X_coordinateGraphX_plain_anchor_dims P hnode hborder
  rw [hcoordinate] at hout
  exact ⟨out, X_componentRun_plain_node_dims h hout hplain, hedge, hplain, hw, hh⟩

/-- Exact run proper nodes dominate the source graph nodes (copy of
`componentRun_original_node_dims` with the exact front end; `normalize`
and `addLabelNodes` are shared). -/
private theorem X_componentRun_original_node_dims {P : Params} {exact : List Nat} {cg : Graph}
    {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    ∃ out, run.proper.nodes[i]? = some out ∧ out.edge = none ∧
      out.node.border = 0 ∧ node.w ≤ out.node.w ∧ out.node.h = node.h := by
  obtain ⟨_, _, _, _, hnormalize, hlabels, hcoordinate, _, _, _, _, _, _, _⟩ :=
    componentRunX_spec h
  have hp := normalize_node_record hnormalize hn
  have hl := addLabelNodes_untouched_node hlabels hp rfl
  exact X_componentRun_coordinateGraph_plain_node_dims h hcoordinate hl hb

/-- Exact `frameRect` dimensions dominate the source node dimensions (copy of
`componentRun_original_frame_minimum_dims`; `frameRect_plain_dims` is run-generic). -/
private theorem X_componentRun_original_frame_minimum_dims {P : Params} {exact : List Nat}
    {cg : Graph} {run : Run} {labels : List MeasuredLabel} {orderOptions : OrderOptions}
    (h : componentRunX P exact cg labels orderOptions = .ok run)
    {i : Nat} {node : Node} (hn : cg.nodes[i]? = some node)
    (hb : node.border = 0) :
    node.w ≤ (frameRect P cg run i).w ∧ node.h ≤ (frameRect P cg run i).h := by
  obtain ⟨out, hout, _, _, hw, hh⟩ := X_componentRun_original_node_dims h hn hb
  have hget : cg.nodes.getD i default = node := by
    simp only [List.getD_eq_getElem?_getD, hn, Option.getD_some]
  have hplain : (cg.nodes.getD i default).border ≠ -2 := by
    rw [hget, hb]
    decide
  have hdims := frameRect_plain_dims P cg run i out hplain hout
  refine ⟨hdims.1.symm ▸ hw, ?_⟩
  rw [hdims.2, hh]
  exact Int.le_refl _

/-- Exact part rects dominate the source graph node dimensions (copy of
`SceneExecution.component_rect_minimum_dims` with the exact part geometry). -/
private theorem X_component_rect_minimum_dims {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    {part : List Nat × Part} (hpart : part ∈ execution.componentsAcc.parts)
    {i key : Nat} (hkey : part.1[i]? = some key)
    {node : Node} (hnode : execution.graph.nodes[key]? = some node)
    (hborder : node.border = 0)
    {rect : Rect} (hrect : part.2.rects[i]? = some rect) :
    node.w ≤ rect.w ∧ node.h ≤ rect.h := by
  obtain ⟨index, _chosen, run, loops, _area, _, _, _, hrun, _hloops, hpartdef⟩ :=
    (actual_components_parts_geometryX (rfl : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
      Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
      false, [], []⟩ : Acc).parts = []) execution.components_eq).2 part hpart
  have hnodes : (componentCandidate execution.graph part.1 index).nodes =
      part.1.map (fun key => execution.graph.nodes.getD key default) := by
    unfold componentCandidate
    dsimp only
    split
    · split <;> rfl
    · unfold cycleGraph
      split <;> rfl
  have hlocal : (componentCandidate execution.graph part.1 index).nodes[i]? =
      some node := by
    rw [hnodes]
    simp only [List.getElem?_map, hkey, Option.map_some,
      List.getD_eq_getElem?_getD, hnode, Option.getD_some]
  have hminimum := X_componentRun_original_frame_minimum_dims hrun hlocal hborder
  have hi : i < (componentCandidate execution.graph part.1 index).nodes.length :=
    (List.getElem?_eq_some_iff.mp hlocal).1
  have hrectEq : part.2.rects[i]? =
      some (shiftRect (0 - (placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
        (-(placeBoundsX execution.params
          (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
        (frameRect execution.params
          (componentCandidate execution.graph part.1 index) run i)) := by
    rw [hpartdef]
    exact X_placeComponentExact_rects_get hi
  have heq : rect = shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i) :=
    Option.some.inj (hrect.symm.trans hrectEq)
  have hwS : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i)).w =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i).w := rfl
  have hhS : (shiftRect (0 - (placeBoundsX execution.params
      (componentCandidate execution.graph part.1 index) run execution.measured loops).minX)
      (-(placeBoundsX execution.params
        (componentCandidate execution.graph part.1 index) run execution.measured loops).minY)
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i)).h =
      (frameRect execution.params
        (componentCandidate execution.graph part.1 index) run i).h := rfl
  rw [heq, hwS, hhS]
  exact hminimum

/-- Exact leaf minimum-dimensions fact: every fixed-size entry bounds the
corresponding exact output box. Replays the leaf half of
`layoutRecursive_fixed_source_box_minimum_dimensions_with_role` against
`SceneExecutionX`. -/
private theorem X_execution_fixed_source {exactIds : List String} {inp : Input}
    {o : Options} {res : FamilyResult}
    (execution : SceneExecutionX exactIds inp o res)
    (hids : (inp.boxes.map (·.id)).Nodup)
    {key : Nat} {source : ModelBox} (hsource : inp.boxes[key]? = some source)
    {entry : String × Size}
    (hfixed : inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry) :
    ∃ box : Box, res.scene.layoutDump.box? source.id = some box ∧
      box.role = source.role.id ∧ entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h := by
  have hlines := execution.lines_eq
  unfold boxLines at hlines
  obtain ⟨_, hlineLookup⟩ := mapM_getElem? _ _ _ hlines
  obtain ⟨lines, _, hline⟩ := hlineLookup key (source, key)
    (by simp only [List.getElem?_zipIdx, hsource, Option.map_some, Nat.zero_add])
  obtain ⟨node, hnode, _hdecl, hborder, hw, hh⟩ :=
    X_exactGraph_fixed_node_dims execution.graph0_eq execution.graph_eq
      hline hsource hfixed
  obtain ⟨rect, hrect⟩ :=
    X_packed_rect_exists execution (List.getElem?_eq_some_iff.mp hsource).1
  let Xminimum : Nat → Size := fun i =>
    match execution.graph.nodes[i]? with
    | some n => if n.border = 0 then ⟨n.w, n.h⟩ else ⟨0, 0⟩
    | none => ⟨0, 0⟩
  have X_hparts : ∀ part ∈ execution.componentsAcc.parts,
      ∀ entry ∈ part.1.zip part.2.rects,
      (Xminimum entry.1).w ≤ entry.2.w ∧ (Xminimum entry.1).h ≤ entry.2.h := by
    intro part hpart entry hentry
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hentry
    simp only [List.length_zip] at hi
    have hil : i < part.1.length := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hir : i < part.2.rects.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hpair : (part.1[i], part.2.rects[i]) = entry := by
      simpa only [List.getElem_zip] using heq
    have hkey : part.1[i]? = some entry.1 := by
      rw [List.getElem?_eq_getElem hil, ← hpair]
    have hget : part.2.rects[i]? = some entry.2 := by
      rw [List.getElem?_eq_getElem hir, ← hpair]
    have hn : 0 ≤ entry.2.w ∧ 0 ≤ entry.2.h := by
      have hb := exactPartsBounded' execution part hpart
      have hm := (List.of_mem_zip hentry).2
      exact ⟨(hb.2.2.1 entry.2 hm).2.2.2.2.1, (hb.2.2.1 entry.2 hm).2.2.2.2.2⟩
    dsimp only [Xminimum]
    cases hlookup : execution.graph.nodes[entry.1]? with
    | none => exact hn
    | some n =>
      by_cases hb : n.border = 0
      · simp only [hb, ↓reduceIte]
        exact X_component_rect_minimum_dims execution hpart hkey hlookup hb hget
      · simpa only [hb, ↓reduceIte] using hn
  have hminimum := packAcc_rect_minimum_dimensions_of_coverage Xminimum execution.packed_eq
    (fun i r hr => Or.inr (execution.parts_coverage i r hr)) X_hparts key rect hrect
  have hmin : node.w ≤ rect.w ∧ node.h ≤ rect.h := by
    have h1 := hminimum.1
    have h2 := hminimum.2
    dsimp only [Xminimum] at h1 h2
    simp only [hnode] at h1 h2
    rw [ite_eq_left hborder] at h1 h2
    exact ⟨h1, h2⟩
  have hget : execution.packedAcc.rects.getD key default = rect := by
    obtain ⟨hi, heq⟩ := Array.getElem?_eq_some_iff.mp hrect
    simpa [Array.getD, hi] using heq
  have hbox := execution.source_box_lookup_of_box_ids_nodupX hids hsource
  rw [hget] at hbox
  refine ⟨Box.mk source.id source.role.id
    (shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH rect))
    source.parent source.exclusive, hbox, rfl, ?_, ?_⟩
  all_goals cases hd : o.direction <;> simp only [hd, shiftRect, orientRect] at hw hh ⊢ <;> omega

/-- The exact-base replay of
`layoutRecursive_fixed_source_box_minimum_dimensions_with_role`: every
fixed-size entry bounds the corresponding box of every exact `B`-recursion
result. The induction mirrors the plain proof with `X_B_succ`-style concrete
sources (`layoutRecursiveB_succ_sources`), the exact leaf fact above, and
the exact transports. -/
theorem xExactFixedMin (exactIds : List String) : XExactFixedMin exactIds := by
  unfold XExactFixedMin
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res source entry hids hcovered hsuccess hsource hfixed
    obtain ⟨key, hkey⟩ := List.mem_iff_getElem?.mp hsource
    let execution := Classical.choice (layoutX_sceneExecution hsuccess)
    exact X_execution_fixed_source execution hids hkey hfixed
  | succ fuel ih =>
    intro inp o res source entry hids hcovered hsuccess hsource hfixed
    rcases layoutRecursiveB_succ_sources (layoutX exactIds) hsuccess with ⟨_, hflat⟩ |
      ⟨group, P, metric, child, titleLines, parent, hg, hP, hm, hc, ht, hp, hexpand⟩
    · obtain ⟨key, hkey⟩ := List.mem_iff_getElem?.mp hsource
      let execution := Classical.choice (layoutX_sceneExecution hflat)
      exact X_execution_fixed_source execution hids hkey hfixed
    · obtain ⟨frame, _fm, _ftl, _fl, dx, dy, hframe, _hmS, _htS, _hlS, hdx, hdy, _hcanvas,
        hboxes⟩ :=
        expandChild_sources hexpand
      have hchildCov : RoutesCovered
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id) :=
        selectInput_routesCovered inp _ _
      have hcIds := (X_ids exactIds fuel _ _ _ hchildCov hc).1
      let baseParent := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
      have hparentCov : RoutesCovered { baseParent with
          fixedSizes := baseParent.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
            (titleLines.foldl (fun width line => max width line.width) 0)
            ((max 1 titleLines.length : Int) * P.lineH)
            ⟨child.scene.canvas.w - 2 * P.canvasMargin,
              child.scene.canvas.h - 2 * P.canvasMargin⟩)]
          fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
          fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] } := by
        change RoutesCovered baseParent
        exact selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
      have hpIds : parent.scene.boxes.map (·.id) =
          (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
            (·.id) :=
        (X_ids exactIds fuel _ _ _ hparentCov hp).1
      have hdisjoint := X_disjoint exactIds hc hp
      have hresultIds := (X_ids exactIds (fuel + 1) inp o res hcovered hsuccess).1
      have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
        rw [hresultIds]
        exact hids
      have hchildLookup := X_child_transport hboxes hcIds hnodup
      have hparentLookup := X_parent_transport hboxes hpIds hnodup hdisjoint
      let childInput := selectInput inp
        (fun box => Compound.inside inp.boxes group.id box.id) group.id
      let size := childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩
      let parentInput : Input := { baseParent with
        fixedSizes := baseParent.fixedSizes ++ [(group.id, size)]
        fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
        fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] }
      change layoutRecursiveB (layoutX exactIds) fuel childInput
        { o with direction := directionOf group.direction } = .ok child at hc
      change layoutRecursiveB (layoutX exactIds) fuel parentInput o = .ok parent at hp
      by_cases hins : Compound.inside inp.boxes group.id source.id = true
      · let next := if source.parent == group.id then { source with parent := "" } else source
        obtain ⟨sourceIndex, hsourceIndex⟩ := List.mem_iff_getElem?.mp hsource
        have hnext : next ∈ childInput.boxes := by
          change next ∈ ((inp.boxes.zipIdx.filter fun q =>
            Compound.inside inp.boxes group.id q.1.id).map fun q =>
            if q.1.parent == group.id then { q.1 with parent := "" } else q.1)
          exact List.mem_map.mpr ⟨(source, sourceIndex),
            List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hsourceIndex, hins⟩, rfl⟩
        have hid : next.id = source.id := by dsimp only [next]; split <;> rfl
        have hnextRole : next.role = source.role := by dsimp only [next]; split <;> rfl
        have hchildIds : (childInput.boxes.map (·.id)).Nodup := by
          rw [selectInput_box_ids]
          exact List.Nodup.sublist ((List.filter_sublist).map _) hids
        have hnextFixed :
            childInput.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry := by
          change inp.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry
          rw [hid]
          exact hfixed
        obtain ⟨box, hbox, hrole, hw, hh⟩ :=
          ih _ _ _ _ _ hchildIds (selectInput_routesCovered inp _ group.id) hc hnext hnextFixed
        have hboxId : box.id = next.id := by
          change child.scene.boxes.find? (fun box => box.id == next.id) = some box at hbox
          simpa using List.find?_some hbox
        have htransport := hchildLookup box (by simpa only [hboxId] using hbox)
        rw [hboxId, hid] at htransport
        refine ⟨embedBox group.id dx dy box, ?_, ?_, ?_, ?_⟩
        · simpa only [hboxId, hid] using htransport
        · have hrw : (embedBox group.id dx dy box).role = box.role := rfl
          rw [hrw]
          simpa only [hnextRole] using hrole
        · exact hw
        · exact hh
      · have hout : (!Compound.inside inp.boxes group.id source.id) = true := by
          cases hi : Compound.inside inp.boxes group.id source.id <;> simp_all
        let next := if source.parent == "" then { source with parent := "" } else source
        obtain ⟨sourceIndex, hsourceIndex⟩ := List.mem_iff_getElem?.mp hsource
        have hnext : next ∈ parentInput.boxes := by
          change next ∈ ((inp.boxes.zipIdx.filter fun q =>
            !Compound.inside inp.boxes group.id q.1.id).map fun q =>
            if q.1.parent == "" then { q.1 with parent := "" } else q.1)
          exact List.mem_map.mpr ⟨(source, sourceIndex),
            List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hsourceIndex, hout⟩, rfl⟩
        have hid : next.id = source.id := by dsimp only [next]; split <;> rfl
        have hnextRole : next.role = source.role := by dsimp only [next]; split <;> rfl
        have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
          change (baseParent.boxes.map (·.id)).Nodup
          rw [selectInput_box_ids]
          exact List.Nodup.sublist ((List.filter_sublist).map _) hids
        have hnextFixed :
            parentInput.fixedSizes.find? (fun fixed => fixed.1 == next.id) = some entry := by
          change (inp.fixedSizes ++ [(group.id, size)]).find?
            (fun fixed => fixed.1 == next.id) = some entry
          simp [List.find?_append, hid, hfixed]
        have hparentCovered : RoutesCovered parentInput := by
          change RoutesCovered baseParent
          exact selectInput_routesCovered inp
            (fun box => !Compound.inside inp.boxes group.id box.id) ""
        obtain ⟨box, hbox, hrole, hw, hh⟩ :=
          ih _ _ _ _ _ hparentIds hparentCovered hp hnext hnextFixed
        have hboxId : box.id = next.id := by
          change parent.scene.boxes.find? (fun box => box.id == next.id) = some box at hbox
          simpa using List.find?_some hbox
        have htransport := hparentLookup box (by simpa only [hboxId] using hbox)
        rw [hboxId, hid] at htransport
        exact ⟨box, htransport, by simpa only [hnextRole] using hrole, hw, hh⟩

/-- Conditional fit/closure discharge over an explicit fixed-size hypothesis
(kept private; the public `exactFitClosed` below supplies `xExactFixedMin`). -/
private theorem X_exactFitClosed_of (exactIds : List String)
    (hfixedMin : XExactFixedMin exactIds) :
    ExpandChildFitClosedB (layoutX exactIds) := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hctxB hparams
  obtain ⟨hP, htitleH, hwrap⟩ := hparams
  subst htitleH
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, _hexpand⟩ := hctxB
  obtain ⟨metric, hm, hwrap'⟩ := hwrap
  simp only [childSubInput, childSubOptions] at hchild
  simp only [parentSubInput] at hparent
  have hrecB : layoutRecursiveB (layoutX exactIds) (fuel + 1) inp o = .ok res := by
    unfold layoutRecursiveB
    rw [hgroup]
    simp only [hP, hm, hchild, hwrap', hparent, hexpand, Bind.bind, Except.bind]
  obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
  have hclosedP : SceneParentClosed parent.scene :=
    X_rec_parent_closed_wellFormed exactIds (hparentWF _ _ _) fuel parent hparent
  have hclosedC : SceneParentClosed child.scene :=
    X_rec_parent_closed_wellFormed exactIds hwfChild fuel child hchild
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  have hresultIds := (X_ids exactIds (fuel + 1) inp o res hcovered hrecB).1
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hresultIds]
    exact hboxIds
  have hchildCov : RoutesCovered
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id) :=
    selectInput_routesCovered inp _ _
  have hcIds : child.scene.boxes.map (·.id) =
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
        (·.id) :=
    (X_ids exactIds fuel _ _ _ hchildCov hchild).1
  let baseParent := selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id)
  have hparentCov : RoutesCovered { baseParent with
      fixedSizes := baseParent.fixedSizes ++ [(group.id, childFrameSize group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0)
        ((max 1 titleLines.length : Int) * P.lineH)
        ⟨child.scene.canvas.w - 2 * P.canvasMargin,
          child.scene.canvas.h - 2 * P.canvasMargin⟩)]
      fixedChildren := baseParent.fixedChildren ++ [(group.id, child.scene)]
      fixedAreas := baseParent.fixedAreas ++ [(group.id, child.itemArea)] } := by
    change RoutesCovered baseParent
    exact selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hpIds : parent.scene.boxes.map (·.id) =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes.map
        (·.id) :=
    (X_ids exactIds fuel _ _ _ hparentCov hparent).1
  have hdisjoint := X_disjoint exactIds hchild hparent
  have hfit : ExpandChildFitsInset P inp o group
      ((max 1 titleLines.length : Int) * P.lineH) parent child res := by
    intro frm tl fdx fdy hfrmLook hfdxEq hfdyEq hwrapTl
    obtain ⟨metricTl, hmTl, htlTl⟩ := hwrapTl
    have hmetricEq : metricTl = metric := Except.ok.inj (hmTl.symm.trans hm)
    have htlEq : tl = titleLines := by
      rw [hmetricEq] at htlTl
      exact Except.ok.inj (htlTl.symm.trans hwrap')
    obtain ⟨frame, fmS, ftl, _fl, dx, dy, hframe, hmS, htS, _hlS, hdx, hdy, _hcanvas,
      hboxes⟩ :=
      expandChild_sources hexpand
    have hmEq0 : fmS = metric := Except.ok.inj (hmS.symm.trans hm)
    have htlEq0 : ftl = titleLines := by
      rw [hmEq0] at htS
      exact Except.ok.inj (htS.symm.trans hwrap')
    rw [htlEq0] at hdx hdy
    have hframeEq : frm = frame := Option.some.inj (hfrmLook.symm.trans hframe)
    have hfdxDx : fdx = dx := by
      rw [hfdxEq, hframeEq, htlEq, ← hdx]
    have hfdyDy : fdy = dy := by
      rw [hfdyEq, hframeEq, htlEq, ← hdy]
    refine ⟨?_, ?_, ?_⟩
    · rw [hfdxDx, hfdyDy, hframeEq]
      exact X_childInset_fit exactIds hwf hgroup hP hparent hfixedMin frame dx dy hframe hdx
        hdy rfl
    · intro box hbox
      rw [hfdxDx, hfdyDy]
      exact X_child_transport hboxes hcIds hnodup box hbox
    · intro box hbox
      exact X_parent_transport hboxes hpIds hnodup hdisjoint box hbox
  exact ⟨hfit, hclosedP, hclosedC⟩

/-- The exact pipeline discharges the base-parametric fit/closure fact, with
the fixed-size hypothesis proved by `xExactFixedMin`. -/
theorem exactFitClosed (exactIds : List String) :
    ExpandChildFitClosedB (layoutX exactIds) :=
  X_exactFitClosed_of exactIds (xExactFixedMin exactIds)

end PipelineImpl
end Layered
end Elegant
