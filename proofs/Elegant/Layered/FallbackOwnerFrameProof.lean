import Elegant.Layered.FallbackCaptionClearProof
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Assembly
import ElegantGeometry.Validator

set_option autoImplicit false

namespace Elegant.Layered

/-! # Fallback owner frame clearance for an executed layout

`FallbackOwnerFrameClear` (in `FallbackCaptionClearProof.lean`) says that the
scene frame of a fallback caption owner (an input box with no installed title)
is disjoint from, or strictly contained in, every other group scene box. This
file proves it for an executed flat layout from `WellFormed`, `framedParents`,
and two scene-shape hypotheses.

Truth analysis. A fallback owner is a node-role box or a fixed-size box
(`SceneExecution.fallback_owner_cases`): a non-fixed group always records a
title. Under `framedParents`, no input box may be parented at a node or at a
fixed box, so a fallback owner has no scene descendants at all
(`owner_not_in_ancestors_of_framed` below). Every other group scene box is
therefore either an ancestor of the owner, in which case the owner frame lies
strictly inside it by parent-chain induction (`ancestor_strict_of_step`), or
unrelated to it, in which case the scene C8a clause gives disjointness. A
titled group with a nested group genuinely violates the statement (the child
frame is inside the owner, which is neither disjunct), which is why the
no-title premise is load bearing.

The two scene-shape hypotheses are validator-adjacent geometric facts, each
strictly narrower than the target (one disjunct each, no titles or labels):

* `Validator.C8a res.scene.layoutDump`: every group frame is disjoint from
  boxes that are neither its ancestors nor its descendants. For the flat
  layout this is `layout_c8a` modulo its foreign-frame residual; for the
  recursive layout it is a `LayeredSeams` field. It is taken in its exact
  existing form.
* `FallbackOwnerStrictStep res`: every non-root scene box lies strictly
  inside its looked-up group parent. This is the flat-scene form of the
  `ExpandChildParentStrictStep` residual (`ExpandChildParentFrameProof.lean`);
  the mechanism is the same cluster-pad/title reservation the flat layout
  wraps members in, established at component level by
  `SceneExecution.component_member_strictInside'` and
  `SceneExecution.component_child_frame_strictInside'`.

Probe evidence (`proofs/wip/Probe/FallbackOwnerFrameProbe.lean`, all of
`vecTB`/`vecLR`/`cell`): the target holds on a node in two nested groups, on
siblings with an empty group, on a fixed group owner, and on a fixed group
with a nested group child (which is unframed: the child is placed disjoint,
so the target still holds). The strict-step executable form holds on every
framed probe layout and fails exactly on the unframed nested-fixed-group
layout, where the child sits outside its fixed parent and C3 fails too. -/

/-- One strict step for the executed flat scene: every non-root scene box
lies strictly inside its looked-up group parent. -/
def FallbackOwnerStrictStep (res : FamilyResult) : Prop :=
  ∀ (b : Box), b ∈ res.scene.boxes → b.parent ≠ "" →
    ∀ (p : Box), res.scene.layoutDump.box? b.parent = some p →
      p.role = "group" → p.rect.StrictInside b.rect

/-- One unfolded step of the ancestor walk. -/
private theorem go_succ_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hne : b.parent ≠ "") :
    LayoutDump.ancestors.go d (k + 1) s =
      b.parent :: LayoutDump.ancestors.go d k b.parent := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hne, ↓reduceIte]

/-- The ancestor walk from a missing id is empty. -/
private theorem go_none_step {d : LayoutDump} {k : Nat} {s : String}
    (h : d.box? s = none) :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = none := h
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind]

/-- The ancestor walk from a root box is empty. -/
private theorem go_root_step {d : LayoutDump} {k : Nat} {s : String} {b : Box}
    (hb : d.box? s = some b) (hpar : b.parent = "") :
    LayoutDump.ancestors.go d (k + 1) s = [] := by
  have hfind : d.boxes.find? (fun b => b.id == s) = some b := hb
  simp only [LayoutDump.ancestors.go, LayoutDump.box?, hfind, hpar, ↓reduceIte]

/-- Strict-inside transitivity for the ancestor induction. -/
private theorem strictInside_trans_step {o m i : Rect}
    (h1 : o.StrictInside m) (h2 : m.StrictInside i) : o.StrictInside i := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Ancestor membership yields a scene box parented at the member id. -/
private theorem ancestors_member_parent {d : LayoutDump} {x : String}
    {n : Nat} {s : String}
    (hmem : x ∈ LayoutDump.ancestors.go d n s) :
    ∃ c ∈ d.boxes, c.parent = x := by
  induction n generalizing s with
  | zero =>
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hmem
      cases hmem
  | succ n ih =>
      cases h : d.box? s with
      | none =>
          rw [go_none_step h] at hmem
          cases hmem
      | some b =>
          by_cases hpar : b.parent = ""
          · rw [go_root_step h hpar] at hmem
            cases hmem
          · rw [go_succ_step h hpar] at hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · exact ⟨b, List.mem_of_find?_eq_some h, heq.symm⟩
            · exact ih hmem'

/-- Members of an ancestor walk are never the empty id: only non-empty
parents are ever prepended. -/
private theorem ancestors_mem_ne {d : LayoutDump} {x : String}
    {n : Nat} {s : String}
    (hmem : x ∈ LayoutDump.ancestors.go d n s) : x ≠ "" := by
  induction n generalizing s with
  | zero =>
      have e : LayoutDump.ancestors.go d 0 s = [] := rfl
      rw [e] at hmem
      cases hmem
  | succ n ih =>
      cases h : d.box? s with
      | none =>
          rw [go_none_step h] at hmem
          cases hmem
      | some b =>
          by_cases hpar : b.parent = ""
          · rw [go_root_step h hpar] at hmem
            cases hmem
          · rw [go_succ_step h hpar] at hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · rw [heq]
              exact hpar
            · exact ih hmem'

/-- Every scene box comes from the input box at the same index, keeping id,
parent, and role. -/
private theorem scene_box_source
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    {b : Box} (hb : b ∈ res.scene.boxes) :
    ∃ (idx : Nat) (src : ModelBox), inp.boxes[idx]? = some src ∧
      b.id = src.id ∧ b.parent = src.parent ∧ b.role = src.role.id := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨src, hsrc, hboxeq⟩ := execution.box_index_origin hidx
  refine ⟨idx, src, hsrc, ?_, ?_, ?_⟩ <;> rw [hboxeq]

/-- A fallback owner never appears in any scene ancestor walk: any box
parented at the owner forces the owner to be a non-fixed group, against the
fallback cases. The empty-id owner needs no exclusion: the empty id never
appears in an ancestor walk. -/
private theorem owner_not_in_ancestors_of_framed
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    {ownerIndex : Nat} {obox : ModelBox}
    (hobox : inp.boxes[ownerIndex]? = some obox)
    (hnone : (PipelineImpl.sceneTitlesExpr execution.params inp o execution.lines
      execution.packedAcc).find? (fun title => title.1 == obox.id) = none)
    {g : Box} :
    obox.id ∉ res.scene.layoutDump.ancestors g.id := by
  intro hmem
  have hmemGo : obox.id ∈ LayoutDump.ancestors.go res.scene.layoutDump
      res.scene.layoutDump.boxes.length g.id := hmem
  have hneid : obox.id ≠ "" := ancestors_mem_ne hmemGo
  obtain ⟨c, hcMem, hcPar⟩ := ancestors_member_parent hmemGo
  obtain ⟨cIdx, cSrc, hsrc, -, hcpar, -⟩ := scene_box_source execution hcMem
  have hspe : cSrc.parent = obox.id := hcpar.symm.trans hcPar
  have hsrcMem : cSrc ∈ inp.boxes := List.mem_of_getElem? hsrc
  have hne : cSrc.parent ≠ "" := by rw [hspe]; exact hneid
  obtain ⟨par, hparMem, hparId, hparRole, hparNotFixed⟩ :=
    framedParents_parent hfp hsrcMem hne
  have hparIdOb : par.id = obox.id := hparId.trans hspe
  obtain ⟨pIdx, hpIdx⟩ := List.mem_iff_getElem?.mp hparMem
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have ha : (inp.boxes.map (·.id))[pIdx]? = some obox.id := by
    simp [List.getElem?_map, hpIdx, hparIdOb]
  have hb : (inp.boxes.map (·.id))[ownerIndex]? = some obox.id := by
    simp [List.getElem?_map, hobox]
  have hlookups : (inp.boxes.map (·.id))[pIdx]? =
      (inp.boxes.map (·.id))[ownerIndex]? := by rw [ha, hb]
  have hbound : pIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hpIdx).1
  have hidxEq : pIdx = ownerIndex :=
    (List.Nodup.getElem?_inj hbound hids).mp hlookups
  have hparOb : par = obox := by
    have hsame : inp.boxes[pIdx]? = inp.boxes[ownerIndex]? := by rw [hidxEq]
    rw [hpIdx, hobox] at hsame
    exact Option.some.inj hsame
  have hfall := execution.fallback_owner_cases hwf hobox hnone
  rcases hfall with hnode | hfixed
  · have hgr : obox.role = .group := hparOb ▸ hparRole
    rw [hnode] at hgr
    exact absurd hgr (by decide)
  · have hnf : inp.fixedSizes.any (fun fixed => fixed.1 == obox.id) = false := by
      rw [← hparIdOb]
      exact hparNotFixed
    rw [hfixed] at hnf
    exact absurd hnf (by decide)

/-- A non-root scene box is looked up at a group-role parent: every
non-empty input parent is a group under `framedParents`. -/
private theorem scene_parent_is_group
    {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true) :
    ∀ (b : Box), b ∈ res.scene.boxes → b.parent ≠ "" →
      ∀ (p : Box), res.scene.layoutDump.box? b.parent = some p →
        p.role = "group" := by
  intro b hb hparNe p hlook
  obtain ⟨bIdx, bSrc, hbsrc, hbid, hbpar, -⟩ := scene_box_source execution hb

  have hsrcMem : bSrc ∈ inp.boxes := List.mem_of_getElem? hbsrc
  have hne : bSrc.parent ≠ "" := by rw [← hbpar]; exact hparNe
  have hlookF : res.scene.boxes.find? (fun c => c.id == b.parent) = some p := hlook
  have hpid : p.id = b.parent := beq_iff_eq.mp
    (List.find?_some (p := fun (c : Box) => c.id == b.parent) hlookF)
  obtain ⟨par, hparMem, hparId, hparRole, -⟩ :=
    framedParents_parent hfp hsrcMem hne
  obtain ⟨pIdx, pSrc, hpsrc, hpsid, -, hprole⟩ := scene_box_source execution
    (List.mem_of_find?_eq_some hlook)
  have hparIdP : par.id = p.id := hparId.trans (hbpar.symm.trans hpid.symm)
  have hsrcIdP : pSrc.id = par.id := hpsid.symm.trans hparIdP.symm
  obtain ⟨qIdx, hqIdx⟩ := List.mem_iff_getElem?.mp hparMem
  have hids : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have ha : (inp.boxes.map (·.id))[qIdx]? = some pSrc.id := by
    simp [List.getElem?_map, hqIdx, hsrcIdP]
  have hbmap : (inp.boxes.map (·.id))[pIdx]? = some pSrc.id := by
    simp [List.getElem?_map, hpsrc]
  have hlookups : (inp.boxes.map (·.id))[qIdx]? =
      (inp.boxes.map (·.id))[pIdx]? := by rw [ha, hbmap]
  have hbound : qIdx < (inp.boxes.map (·.id)).length := by
    rw [List.length_map]
    exact (List.getElem?_eq_some_iff.mp hqIdx).1
  have hidxEq : qIdx = pIdx :=
    (List.Nodup.getElem?_inj hbound hids).mp hlookups
  have hparSrc : par = pSrc := by
    have hsame : inp.boxes[qIdx]? = inp.boxes[pIdx]? := by rw [hidxEq]
    rw [hqIdx, hpsrc] at hsame
    exact Option.some.inj hsame
  rw [hprole, ← hparSrc, hparRole]
  rfl

/-- Ancestor groups strictly contain the descendant box, by parent-chain
induction with one strict step per link. -/
private theorem ancestor_strict_of_step (res : FamilyResult)
    (hstep : FallbackOwnerStrictStep res)
    (hpar : ∀ (b : Box), b ∈ res.scene.boxes → b.parent ≠ "" →
      ∀ (p : Box), res.scene.layoutDump.box? b.parent = some p → p.role = "group")
    (g : Box) (hgRole : g.role = "group")
    (hfindg : res.scene.layoutDump.box? g.id = some g) :
    ∀ (n : Nat) (s : String) (b : Box),
      res.scene.layoutDump.box? s = some b →
      g.id ∈ LayoutDump.ancestors.go res.scene.layoutDump n s →
      g.rect.StrictInside b.rect := by
  intro n
  induction n with
  | zero =>
      intro s b hb hm
      have e : LayoutDump.ancestors.go res.scene.layoutDump 0 s = [] := rfl
      rw [e] at hm
      cases hm
  | succ n ih =>
      intro s b hb hm
      have hbmem : b ∈ res.scene.boxes := List.mem_of_find?_eq_some hb
      by_cases hparNe : b.parent = ""
      · rw [go_root_step hb hparNe] at hm
        cases hm
      · rw [go_succ_step hb hparNe] at hm
        rcases List.mem_cons.mp hm with heq | hmem
        · have hlook : res.scene.layoutDump.box? b.parent = some g := heq ▸ hfindg
          exact hstep b hbmem hparNe g hlook hgRole
        · cases hq : res.scene.layoutDump.box? b.parent with
          | none =>
              cases hn : n with
              | zero =>
                  have e : LayoutDump.ancestors.go res.scene.layoutDump 0 b.parent = [] :=
                    rfl
                  rw [hn] at hmem
                  rw [e] at hmem
                  cases hmem
              | succ m =>
                  rw [hn, go_none_step hq] at hmem
                  cases hmem
          | some q1 =>
              have hIH := ih b.parent q1 hq hmem
              have hrole := hpar b hbmem hparNe q1 hq
              have hst := hstep b hbmem hparNe q1 hq hrole
              exact strictInside_trans_step hIH hst

/-- The fallback owner frame fact for an executed flat layout: the owner's
scene frame is disjoint from, or strictly contains, every other group frame.
Unrelated groups are disjoint by the scene C8a clause (the owner has no scene
descendants under `framedParents`); ancestor groups strictly contain the
owner by parent-chain induction. -/
theorem fallbackOwnerFrameClear_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hC8a : Validator.C8a res.scene.layoutDump)
    (hstep : FallbackOwnerStrictStep res) :
    FallbackOwnerFrameClear execution := by
  intro ownerIndex obox g hobox hnone hgMem hgRole hne
  have hbl : (PipelineImpl.sceneBoxesExpr execution.params inp o
      execution.packedAcc).length = inp.boxes.length := by
    simp [PipelineImpl.sceneBoxesExpr]
  have hlt : ownerIndex < inp.boxes.length :=
    (List.getElem?_eq_some_iff.mp hobox).1
  have hi : ownerIndex <
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).length := by
    omega
  obtain ⟨ob, hobb⟩ : ∃ box : Box,
      (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc)[ownerIndex]? =
        some box := ⟨_, List.getElem?_eq_getElem hi⟩
  have hboxScene : res.scene.boxes[ownerIndex]? = some ob := by
    rw [execution.boxes_eq_map]
    exact hobb
  have hgetD : (PipelineImpl.sceneBoxesExpr execution.params inp o execution.packedAcc).getD
      ownerIndex ⟨"", "", default, "", false⟩ = ob := by
    rw [List.getD_eq_getElem?_getD, hobb]
    rfl
  obtain ⟨actual, hactual, hboxeq⟩ := execution.box_index_origin hboxScene
  rw [hobox] at hactual
  have hact : actual = obox := (Option.some.inj hactual).symm
  have hobId : ob.id = obox.id := by rw [hboxeq, hact]
  have hobMem : ob ∈ res.scene.boxes := List.mem_of_getElem? hboxScene
  have hids : (res.scene.boxes.map (·.id)).Nodup := by
    have hmap : res.scene.boxes.map (·.id) = inp.boxes.map (·.id) := by
      rw [execution.boxes_eq_map, List.map_map]
      exact PipelineImpl.zipIdx_map_comp (·.id) inp.boxes 0
    rw [hmap]
    exact Model.boxIds_nodup hwf
  have hpar := scene_parent_is_group execution hwf hfp
  by_cases hanc : g.id ∈ res.scene.layoutDump.ancestors ob.id
  · have hmem : g.id ∈ LayoutDump.ancestors.go res.scene.layoutDump
        res.scene.layoutDump.boxes.length ob.id := hanc
    have hfindg : res.scene.layoutDump.box? g.id = some g :=
      Assembly.keyed_lookup_eq (fun b : Box => b.id) res.scene.boxes hids g hgMem
    have hfindob : res.scene.layoutDump.box? ob.id = some ob :=
      Assembly.keyed_lookup_eq (fun b : Box => b.id) res.scene.boxes hids ob hobMem
    have hstrict := ancestor_strict_of_step res hstep hpar g hgRole hfindg
      res.scene.layoutDump.boxes.length ob.id ob hfindob hmem

    rw [hgetD]
    exact Or.inr hstrict
  · have hgMemD : g ∈ res.scene.layoutDump.boxes := hgMem
    have hobMemD : ob ∈ res.scene.layoutDump.boxes := hobMem
    have hneOb : ob.id ≠ g.id := by rw [hobId]; exact Ne.symm hne
    have h2 : ob.id ∉ res.scene.layoutDump.ancestors g.id := by
      rw [hobId]
      exact owner_not_in_ancestors_of_framed execution hwf hfp hobox hnone
    have hdisj := hC8a g hgMemD hgRole ob hobMemD hneOb hanc h2
    rw [hgetD]
    exact Or.inl hdisj

/-- The executed fallback-caption clearance from the fixed-size fit premise:
the owner-frame fact above discharges the residual of
`fallbackCaptionClear_of_fit`. -/
theorem fallbackCaptionClear_of_executed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : PipelineImpl.SceneExecution inp o res)
    (hwf : WellFormed (inputModel inp o))
    (hfp : framedParents inp = true)
    (hfit : PipelineImpl.InputFixedFit inp o)
    (hC8a : Validator.C8a res.scene.layoutDump)
    (hstep : FallbackOwnerStrictStep res) :
    PipelineImpl.FallbackCaptionClear execution :=
  fallbackCaptionClear_of_fit execution hwf hfp hfit
    (fallbackOwnerFrameClear_executed execution hwf hfp hC8a hstep)

end Elegant.Layered
