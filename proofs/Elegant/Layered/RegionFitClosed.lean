import Elegant.Layered.RecursiveBLiftsA
import Elegant.Layered.SubInputWellFormedFacts
import Elegant.Layered.RegionPipeline
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RecursiveBEq
import Elegant.Layered.RecursiveCallContext
import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.RecursiveC2

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-! # Region fit closure (`RegionSeams.fitClosed`).

Packet P12 of `local://region-tower-plan.md` (field `fitClosed`):
`ExpandChildFitClosedB` over the reindexing base
`fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'`
(locally `rfcBase`; the same lambda as the private `RegionSeams.rsmBase`).

## Verdict: the closure holds under admission, modulo one residual.

`ExpandChildCallContextB` (`RecursiveBEq.lean`) pins
`!inp.fixedSizes.any (fun fixed => fixed.1 == box.id)` for the expanded group:
a user-fixed group is never an `expandChild` frame. Hence the spilling fixed
parents below are not counterexamples to `fitClosed`; they fail cluster C3
(the `flatC3` clause), which the family level already rejects through
`framedParents = false`. What the closure needs beyond the base-independent
assembly is exactly the region analogue of `XExactFixedMin`: every fixed entry
is dominated by its output box over the region B-recursion. That fact is the
single residual `R_RegionFixedMinB` below, stated in the admitted conditional
form; the main theorem replays `X_exactFitClosed_of`
(`ExactFitClosure.lean`) over `SceneExecutionR` and the region leaf facts.

Executed probes in `proofs/wip/Probe/RegionFitClosedTProbe.lean` (2026-11-19,
`lake env lean wip/Probe/RegionFitClosedTProbe.lean`), two-region inputs with
region sets `[("G1", ["A", "B"]), ("G2", ["C", "D"])]`, profile vector,
direction TB. `honor` = every fixed-size entry is dominated by its output box;
`firstFailure` = `Validator.firstFailure` (clause order c1..c8, so `some 2` is C3).

- P1 fixed region parent with children (`fixedSizes = [("G1", 10x10)]`,
  `exactIds = ["G1"]`): `framed = false`, `admFit = false`. `layoutRIds` ok,
  keeps G1 at `(1024, 1024, 10, 10)` verbatim, `honor = true`,
  `firstFailure = some 2`, `c3 = false`, `c7 = true`. Fuel-1 `layoutRecursiveB`
  over the reindexing base: ok, `honor = true`, `firstFailure = some 2`.
- P2 region minimum exceeds fixed size (P1 with a 200-char G1 title):
  identical outcome (`some 2`, `c3 = false`). The fixed frame is never enlarged
  to the title minimum.
- P3 zero-size fixed box (`fixedSizes = [("a1", 0x0)]`, leaf node,
  `exactIds = ["a1"]`): `framed = true`, `admFit = true`. `layoutRIds` ok, keeps
  a1 at `(4096, 12928, 0, 0)`, `honor = true`, `firstFailure = none`.
- P4 plain no-region input (`idSets = []`, no fixed sizes): ok, `honor = true`
  (vacuous), `firstFailure = none`.
- P5 ill-formed input (duplicate box id `a1`): `wf = false`. `layoutRIds` still
  succeeds (!) with `firstFailure = some 7` (C8), `c3 = true`, `honor = true`.
- P6 big fixed region parent (`fixedSizes = [("G1", 800x600)]`): G1 kept at
  `(1024, 1024, 800, 600)` verbatim, `honor = true`, `firstFailure = some 2`,
  `c3 = false`.

`honor = true` on all six probes (including the admission-violating P1/P2/P6):
the leaf keeps each fixed entry verbatim, so the residual holds on every
executed probe as stated. The admission is a sufficient condition for the
residual's future proof, not a necessity suggested by the probes; turning the
admission into a global guard is pending user decision 9.
-/

/-- The reindexing base of the region tower (same lambda as `RegionSeams.rsmBase`,
which is private to that module). -/
private abbrev rfcBase (exactIds : List String) (idSets : List (String × List String)) :
    Input → Options → Except LayoutError FamilyResult :=
  fun sub o' => layoutRIds exactIds (reindexRegionSets idSets sub) sub o'

/-- Admission premise for region fit closure: every fixed-size entry names a
nonempty id with no children in the input. Pending user decision 9 turns this
into a global guard; until then it is carried per input by the residual. -/
def RegionFixedParentFit (inp : Input) : Prop :=
  ∀ entry ∈ inp.fixedSizes, entry.1 ≠ "" ∧ ∀ box ∈ inp.boxes, box.parent ≠ entry.1

/-- Residual narrow true form (lemma on the way to `fitClosed`): the admitted
conditional fixed-minimum over the region B-recursion. This is the region analogue
of `XExactFixedMin` (`ExactFitClosure.lean`), additionally conditioned on the
admission per input. True on every executed probe (`honor = true` on P1-P6 of
`RegionFitClosedTProbe`). -/
def R_RegionFixedMinB (exactIds : List String) (idSets : List (String × List String)) : Prop :=
  ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult)
    (source : ModelBox) (entry : String × Size),
    RegionFixedParentFit inp →
    (inp.boxes.map (·.id)).Nodup → RoutesCovered inp →
    layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
    source ∈ inp.boxes →
    inp.fixedSizes.find? (fun fixed => fixed.1 == source.id) = some entry →
    ∃ box : Box, res.scene.layoutDump.box? source.id = some box ∧
      box.role = source.role.id ∧ entry.2.w ≤ box.rect.w ∧ entry.2.h ≤ box.rect.h

/-- Region leaf id fact (prefixed copy of `RB_layout_ids`, which is private to
`RegionSubInputStepC2`): a successful `layoutRIds` run keeps the input box and
route id lists. -/
private theorem rfc_layout_ids {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  have hb : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
    rw [execution.boxes_eq_mapR, List.map_map]
    exact zipIdx_map_comp (·.id) inp.boxes 0
  have hr : res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
    rw [execution.scene_eq]
    simp only [sceneOf, List.map_map]
    exact zipIdx_map_comp (·.id) inp.routes 0
  exact ⟨hb, hr⟩

/-- Region leaf mirror fact (prefixed copy of `RB_layout_box_parent`): every
region scene box carries the id and parent pointer of a source input box. -/
private theorem rfc_layout_box_parent {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (h : layoutRIds exactIds idSets inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  obtain ⟨execution⟩ := layoutRIds_sceneExecution h
  rw [execution.boxes_eq_mapR]
  intro cb hcb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcb
  exact ⟨q.1, List.fst_mem_of_mem_zipIdx hq, rfl, rfl⟩

/-- Successor split for `layoutRecursiveB` at the reindexing base (prefixed copy
of `RB_B_succ`, in the shape of `layoutRecursive_succ`). -/
private theorem rfc_B_succ (exactIds : List String)
    (idSets : List (String × List String)) {fuel : Nat} {inp : Input} {o : Options}
    {res : FamilyResult}
    (h : layoutRecursiveB (rfcBase exactIds idSets) (fuel + 1) inp o = .ok res) :
    (inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = none ∧
      rfcBase exactIds idSets inp o = .ok res) ∨
    ∃ group, inp.boxes.find? (fun box => Compound.independent inp.boxes inp.routes box &&
        !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group ∧
      ∃ P titleHeight child parent a b c,
        layoutRecursiveB (rfcBase exactIds idSets) fuel
          (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
          { o with direction := directionOf group.direction } = .ok child ∧
        layoutRecursiveB (rfcBase exactIds idSets) fuel
          { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
            fixedSizes := a, fixedChildren := b, fixedAreas := c } o = .ok parent ∧
        expandChild P inp o group titleHeight parent child = .ok res := by
  rcases layoutRecursiveB_succ_sources (rfcBase exactIds idSets) h with hflat |
    ⟨group, P, _metric, child, _titleLines, parent, hg, _hP, _hm, hc, _ht, hp, hexpand⟩
  · exact Or.inl hflat
  · exact Or.inr ⟨group, hg, P, _, child, parent, _, _, _, hc, hp, hexpand⟩

/-- Region `B`-recursion mirror fact (prefixed copy of `RB_rec_box_parent`): every
scene box of a successful region recursive layout carries the id and parent
pointer of a source input box. -/
private theorem rfc_rec_box_parent (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact rfc_layout_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases rfc_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact rfc_layout_box_parent hlayout
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

/-- Region `B`-recursion coverage (prefixed copy of `RB_rec_parent_in_ids`): every
nonempty parent pointer of a result scene box names an input box id. -/
private theorem rfc_rec_parent_in_ids (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
      ∀ p ∈ res.scene.boxes, p.parent ≠ "" → p.parent ∈ inp.boxes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h p hp hne
      obtain ⟨sb, hsb, _, hsbpar⟩ := rfc_layout_box_parent h p hp
      rw [hsbpar] at hne ⊢
      rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
      · exact absurd h0 hne
      · rw [← hqid]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro inp o res hf h p hp hne
      rcases rfc_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · obtain ⟨sb, hsb, _, hsbpar⟩ := rfc_layout_box_parent hlayout p hp
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
              have hci := ih _ _ _ hchildFacts hchild cb hcbmem hcb0
              exact selectInput_ids_subset inp
                (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
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

/-- Region flat parent closure (prefixed copy of `RB_layout_parent_closed`). -/
private theorem rfc_layout_parent_closed {exactIds : List String}
    {idSets : List (String × List String)} {inp : Input} {o : Options}
    {res : FamilyResult} (hf : InputFacts inp)
    (h : layoutRIds exactIds idSets inp o = .ok res) :
    SceneParentClosed res.scene := by
  intro bb hbb
  obtain ⟨hidsB, _⟩ := rfc_layout_ids h
  obtain ⟨sb, hsb, _, hsbpar⟩ := rfc_layout_box_parent h bb hbb
  rcases hf.parents sb hsb with h0 | ⟨q, hq, hqid⟩
  · rw [hsbpar]; exact Or.inl h0
  · have hqidIn : q.id ∈ res.scene.boxes.map (·.id) := by
      rw [hidsB]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
    obtain ⟨bb', hbb', hbb'id⟩ := List.mem_map.mp hqidIn
    rw [hsbpar]
    exact Or.inr ⟨bb', hbb', hbb'id.trans hqid⟩

/-- Region `B`-recursion parent closure (prefixed copy of `RB_rec_parent_closed`). -/
private theorem rfc_rec_parent_closed (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      InputFacts inp →
      layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
      SceneParentClosed res.scene := by
  intro fuel
  induction fuel with
  | zero =>
      intro inp o res hf h
      exact rfc_layout_parent_closed hf h
  | succ fuel ih =>
      intro inp o res hf h
      rcases rfc_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
        ⟨group, hg, _P, _th, child, parent, a, b, c, hchild, hparent, hexpand⟩
      · exact rfc_layout_parent_closed hf hlayout
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
          have hci := rfc_rec_parent_in_ids exactIds idSets fuel _ _ _ hchildFacts hchild q hq hne
          exact selectInput_ids_subset inp
            (fun box => Compound.inside inp.boxes group.id box.id) group.id hci
        have hcoverP : ∀ q ∈ parent.scene.boxes, q.parent ≠ "" →
            q.parent ∈ inp.boxes.map (·.id) := by
          intro q hq hne
          have hpi := rfc_rec_parent_in_ids exactIds idSets fuel _ _ _ hparentFacts hparent q hq hne
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

/-- Parent closure of a successful region recursive layout from well-formedness
alone (prefixed copy of `RB_rec_parent_closed_wellFormed`). -/
private theorem rfc_rec_parent_closed_wellFormed (exactIds : List String)
    (idSets : List (String × List String))
    {inp : Input} {o : Options} (hwf : WellFormed (inputModel inp o)) :
    ∀ (fuel : Nat) (res : FamilyResult),
      layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
        SceneParentClosed res.scene := by
  intro fuel res h
  exact rfc_rec_parent_closed exactIds idSets fuel inp o res (inputFacts_of_wellFormed hwf) h

/-- Region `B`-recursion ids (replay of `X_ids` over `rfcBase`): every recursive
result keeps the input box and route id lists. -/
private theorem rfc_ids (exactIds : List String)
    (idSets : List (String × List String)) :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
    RoutesCovered inp → layoutRecursiveB (rfcBase exactIds idSets) fuel inp o = .ok res →
    res.scene.boxes.map (·.id) = inp.boxes.map (·.id) ∧
      res.scene.routes.map (·.id) = inp.routes.map (·.id) := by
  intro fuel
  induction fuel with
  | zero => intro inp o res _ h; exact rfc_layout_ids h
  | succ fuel ih =>
    intro inp o res hc h
    rcases rfc_B_succ exactIds idSets h with ⟨_, hlayout⟩ |
      ⟨group, hg, P, th, child, parent, a, b, c, hchild, hparent, hexp⟩
    · exact rfc_layout_ids hlayout
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

/-- Scene ids of the two region sub-layouts are disjoint (replay of `X_disjoint`). -/
private theorem rfc_disjoint (exactIds : List String)
    (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o childOptions : Options} {group : ModelBox}
    {child parent : FamilyResult}
    {sizes : List (String × Size)} {children : List (String × Scene)}
    {areas : List (String × Int)}
    (hchild : layoutRecursiveB (rfcBase exactIds idSets) fuel
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
      childOptions = .ok child)
    (hparent : layoutRecursiveB (rfcBase exactIds idSets) fuel
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } o = .ok parent) :
    ∀ id ∈ child.scene.boxes.map (·.id), id ∉ parent.scene.boxes.map (·.id) := by
  have hc := rfc_ids exactIds idSets fuel _ _ _
    (selectInput_routesCovered inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id) hchild
  have hparentCoverage : RoutesCovered
      { selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) with
        fixedSizes := sizes, fixedChildren := children, fixedAreas := areas } :=
    selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hp := rfc_ids exactIds idSets fuel _ _ _ hparentCoverage hparent
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

/-- Child lookup transport for one region `expandChild` call (copy of
`X_child_transport`, base-independent). -/
private theorem rfc_child_transport {inp : Input} {group : ModelBox}
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

/-- Parent lookup transport for one region `expandChild` call (copy of
`X_parent_transport`, base-independent). -/
private theorem rfc_parent_transport {inp : Input} {group : ModelBox}
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

/-- Frame fit for the shifted child inset canvas in the actual region recursion
context (replay of `X_childInset_fit`): the parent frame dominates the child
frame size through the admitted fixed-minimum residual. -/
private theorem rfc_childInset_fit (exactIds : List String)
    (idSets : List (String × List String))
    {fuel : Nat} {inp : Input} {o : Options} {group : ModelBox}
    {P : Params} {child : FamilyResult} {titleLines : List Measure.Line}
    {titleHeight : Int} {parent : FamilyResult}
    (hwf : WellFormed (inputModel inp o))
    (hgroup : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hP : checkedParams o.profile inp.kind = .ok P)
    (hparent : layoutRecursiveB (rfcBase exactIds idSets) fuel
      (parentSubInput inp group P titleLines child) o = .ok parent)
    (hadm : ∀ inp : Input, RegionFixedParentFit inp)
    (hmin : R_RegionFixedMinB exactIds idSets)
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
  have hparentAt : layoutRecursiveB (rfcBase exactIds idSets) fuel parentInput o = .ok parent :=
    hparent
  have hparentIds : (parentInput.boxes.map (·.id)).Nodup := by
    change (baseParent.boxes.map (·.id)).Nodup
    rw [selectInput_box_ids]
    exact List.Nodup.sublist ((List.filter_sublist).map _) hboxIds
  have hparentCovered : RoutesCovered parentInput := by
    change RoutesCovered baseParent
    exact selectInput_routesCovered inp (fun box => !Compound.inside inp.boxes group.id box.id) ""
  have hparentOutputIds := (rfc_ids exactIds idSets fuel _ _ _ hparentCovered hparentAt).1
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
    hmin fuel _ _ _ _ _ (hadm _) hparentIds hparentCovered hparentAt hsource hfixed
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

/-- Conditional discharge of the `fitClosed` clause (replay of
`X_exactFitClosed_of`): under the global admission guard and the admitted
fixed-minimum residual, the region reindexing base satisfies fit closure.
Turning the admission into a global guard is pending user decision 9. -/
theorem rfc_fitClosed_of_fixedMin (exactIds : List String)
    (idSets : List (String × List String))
    (hadm : ∀ inp : Input, RegionFixedParentFit inp)
    (hmin : R_RegionFixedMinB exactIds idSets) :
    ExpandChildFitClosedB (rfcBase exactIds idSets) := by
  intro fuel P inp o group titleLines titleHeight parent child res hexpand hctxB hparams
  obtain ⟨hP, htitleH, hwrap⟩ := hparams
  subst htitleH
  obtain ⟨hwf, hgroup, _hpboxes, hchild, hparent, _hexpand⟩ := hctxB
  obtain ⟨metric, hm, hwrap'⟩ := hwrap
  simp only [childSubInput, childSubOptions] at hchild
  simp only [parentSubInput] at hparent
  have hrecB : layoutRecursiveB (rfcBase exactIds idSets) (fuel + 1) inp o = .ok res := by
    unfold layoutRecursiveB
    rw [hgroup]
    simp only [hP, hm, hchild, hwrap', hparent, hexpand, Bind.bind, Except.bind]
  obtain ⟨hwfChild, hparentWF⟩ := subInputWellFormedC2 inp o group hwf
  have hclosedP : SceneParentClosed parent.scene :=
    rfc_rec_parent_closed_wellFormed exactIds idSets (hparentWF _ _ _) fuel parent hparent
  have hclosedC : SceneParentClosed child.scene :=
    rfc_rec_parent_closed_wellFormed exactIds idSets hwfChild fuel child hchild
  have hboxIds : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hcovered : RoutesCovered inp := inputRoutesCovered hwf
  have hresultIds := (rfc_ids exactIds idSets (fuel + 1) inp o res hcovered hrecB).1
  have hnodup : (res.scene.boxes.map (·.id)).Nodup := by
    rw [hresultIds]
    exact hboxIds
  have hchildCov : RoutesCovered
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id) :=
    selectInput_routesCovered inp _ _
  have hcIds : child.scene.boxes.map (·.id) =
      (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id).boxes.map
        (·.id) :=
    (rfc_ids exactIds idSets fuel _ _ _ hchildCov hchild).1
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
    (rfc_ids exactIds idSets fuel _ _ _ hparentCov hparent).1
  have hdisjoint := rfc_disjoint exactIds idSets hchild hparent
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
      exact rfc_childInset_fit exactIds idSets hwf hgroup hP hparent hadm hmin
        frame dx dy hframe hdx hdy rfl
    · intro box hbox
      rw [hfdxDx, hfdyDy]
      exact rfc_child_transport hboxes hcIds hnodup box hbox
    · intro box hbox
      exact rfc_parent_transport hboxes hpIds hnodup hdisjoint box hbox
  exact ⟨hfit, hclosedP, hclosedC⟩

end PipelineImpl

end Layered
end Elegant
