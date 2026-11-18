import Elegant.Layered.RecursiveC2

set_option autoImplicit false

/-!
# `ExpandChildC2Step` for the `expandChild` calls `layoutRecursive` performs

`layoutRecursive_c2_of_flat` consumes, for every successful `expandChild`
call, the package `ExpandChildC2Step`: unique nonempty input box ids, both
result scenes parent-closed, and the mirror facts that every child-scene box
comes from a kept source box inside the expanded group (with the group-facing
parent rewritten to `""`) and every parent-scene box comes from a kept source
box outside the group.

This file proves the mirror facts for the actual recursion. The engine is
`layoutRecursive_scene_box_parent`: scene boxes of a successful
`layoutRecursive` carry the id and the parent pointer of a source input box.
Transporting that through `selectInput` (`selectInput_box_spec`) yields exactly
the two mirror equations, because `selectInput` rewrites a source parent only
when it equals the selection root — the group id for the child input, `""`
(the identity) for the parent input.

The input side contributes nodup ids from `Model.boxIds_nodup` and group
membership from the `find?` witness. Two premises remain seams, stated
explicitly rather than derived:

* `hids : ∀ m ∈ inp.boxes, m.id ≠ ""` — `modelWellFormed` does not reject
  empty box ids, so well-formedness alone does not supply this conjunct.
* `hclosed` — `SceneParentClosed` of both recursive results; the same fact
  `layoutRecursive_c1_c3` consumes (`expandChild_parent_closed` /
  `layoutRecursive_parent_closed`), proved by the C1/C3 lane.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- Rewriting the empty parent to the empty parent is the identity, so a
`selectInput` selection rooted at `""` keeps every parent pointer. -/
theorem selectInput_parent_root (s : String) :
    (if s == "" then "" else s) = s := by
  cases h : (s == "") with
  | true =>
    have hs : s = "" := beq_iff_eq.mp h
    subst hs
    rfl
  | false => rfl

/-- Embedding a child box rewrites an empty parent to the group id; when the
source parent is already the group id (so `selectInput` blanked it) or any
other nonempty id, the result is the source parent itself. -/
theorem embed_parent_eq {g mpar : String} (hne : mpar ≠ "") :
    (if (if mpar == g then "" else mpar) == "" then g else
      (if mpar == g then "" else mpar)) = mpar := by
  by_cases hmg : mpar = g
  · subst hmg
    simp
  · have h1 : (mpar == g) = false := by
      cases hb : (mpar == g) with
      | true => exact absurd (beq_iff_eq.mp hb) hmg
      | false => rfl
    have h2 : (mpar == "") = false := by
      cases hb : (mpar == "") with
      | true => exact absurd (beq_iff_eq.mp hb) hne
      | false => rfl
    simp [h1, h2]

/-- A box that is properly inside `group` has a nonempty parent: `inside`
requires the group index on the ancestor path of the parent, and the empty
parent's ancestor list is empty. -/
theorem inside_parent_ne_empty {boxes : List ModelBox}
    (hnodup : (boxes.map (·.id)).Nodup)
    {group x : String} (h : Compound.inside boxes group x = true)
    {m : ModelBox} (hm : m ∈ boxes) (hx : m.id = x) : m.parent ≠ "" := by
  obtain ⟨m', hm'mem, hm'id, gidx, _, _, _, _, hmem⟩ := inside_spec h
  have hmm : m' = m := eq_of_mem_id hnodup hm'mem hm (hm'id.trans hx.symm)
  subst hmm
  intro hmp
  have hlen : 0 < boxes.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
  have hsucc : boxes.length = boxes.length - 1 + 1 := (Nat.succ_pred_eq_of_pos hlen).symm
  rw [hsucc, hmp] at hmem
  rw [Elegant.Layered.Compound.ancestors.eq_2] at hmem
  simp at hmem

/-- Leaf case of `layoutRecursive_scene_box_parent`: `sceneOf` builds each
scene box from the input box at the same `zipIdx` position, keeping the id
and the parent pointer verbatim. -/
theorem layout_scene_box_parent {inp : Input} {o : Options} {res : FamilyResult}
    (h : layout inp o = .ok res) :
    ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  unfold layout at h
  dsimp only at h
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

/-- Scene boxes of a successful `layoutRecursive` mirror input boxes: every
scene box has the id and the parent pointer of a source input box. Proved by
induction on the recursion fuel; the expansion step transports the property
through `selectInput` on both sides and the `embedBox` parent rewrite. -/
theorem layoutRecursive_scene_box_parent :
    ∀ (fuel : Nat) (inp : Input) (o : Options) (res : FamilyResult),
      (inp.boxes.map (·.id)).Nodup →
      layoutRecursive fuel inp o = .ok res →
      ∀ cb ∈ res.scene.boxes, ∃ sb ∈ inp.boxes, sb.id = cb.id ∧ cb.parent = sb.parent := by
  intro fuel
  induction fuel with
  | zero =>
    intro inp o res _hnodup h
    exact layout_scene_box_parent h
  | succ fuel ih =>
    intro inp o res hnodup h
    rcases layoutRecursive_succ h with ⟨_, hlayout⟩ |
      ⟨group, _hg, _P, _titleHeight, child, parent, a, b, c, hchild, hparent, hexpand⟩
    · exact layout_scene_box_parent hlayout
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
      · -- cb is an embedded child-scene box
        obtain ⟨cbb, hcbbmem, hEmbed⟩ := List.mem_map.mp hbc
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
      · -- cb is a parent-scene box
        obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hparentParent cb hbp
        obtain ⟨m, _hmmem, _hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
          (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
        refine ⟨m, _hmmem, ?_, ?_⟩
        · exact hmsbid.symm.trans hsbid
        · have hsp : sb.parent = m.parent := by
            rw [hmsbpar]
            exact selectInput_parent_root m.parent
          exact hsbpar.trans hsp

/-- Discharge of `ExpandChildC2Step` for an `expandChild` call
`layoutRecursive` performs. The recursion context is the `Or.inr` data of
`layoutRecursive_succ_sources`; `pInput` is the parent sub-input, required to
have the `selectInput` box list (`hpboxes`, satisfied by the actual recursive
call's `.boxes` projection). `hids` and `hclosed` are the two premises the
step cannot derive from well-formedness: nonempty box ids (not a
`modelWellFormed` clause) and parent closure of both recursive scenes (the
C1/C3 lane's `layoutRecursive_parent_closed`). -/
theorem expandChild_c2_step_of_recursion
    {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    {group : ModelBox} {P : Params} {child parent : FamilyResult}
    {titleHeight : Int} {pInput : Input}
    (hwf : WellFormed (inputModel inp o))
    (hids : ∀ m ∈ inp.boxes, m.id ≠ "")
    (hclosed : SceneParentClosed parent.scene ∧ SceneParentClosed child.scene)
    (hgroup : inp.boxes.find? (fun box =>
        Compound.independent inp.boxes inp.routes box &&
          !inp.fixedSizes.any (fun fixed => fixed.1 == box.id)) = some group)
    (hpboxes : pInput.boxes = (selectInput inp
        (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes)
    (hchild : layoutRecursive fuel
        (selectInput inp (fun box => Compound.inside inp.boxes group.id box.id) group.id)
        { o with direction := directionOf group.direction } = .ok child)
    (hparent : layoutRecursive fuel pInput o = .ok parent)
    (_hexpand : expandChild P inp o group titleHeight parent child = .ok res) :
    ExpandChildC2Step P inp o group titleHeight parent child res := by
  have hnodup : (inp.boxes.map (·.id)).Nodup := Model.boxIds_nodup hwf
  have hselNodup : ∀ (keep : ModelBox → Bool) (root : String),
      ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
    intro keep root
    rw [selectInput_box_ids]
    exact nodup_filter_map keep (·.id) inp.boxes hnodup
  have hchildParent := layoutRecursive_scene_box_parent _ _ _ _ (hselNodup _ _) hchild
  have hparentParent := layoutRecursive_scene_box_parent _ _ _ _
    (by rw [hpboxes]; exact hselNodup _ _) hparent
  refine ⟨⟨hnodup, List.mem_of_find?_eq_some hgroup, hids⟩, hclosed.1, hclosed.2, ?_, ?_⟩
  · intro cb hcb
    obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hchildParent cb hcb
    obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
      (fun box => Compound.inside inp.boxes group.id box.id) group.id hsbmem
    refine ⟨m, hmmem, ?_, ?_, ?_⟩
    · exact hkeep
    · exact hmsbid.symm.trans hsbid
    · exact hsbpar.trans hmsbpar
  · intro pb hpb
    obtain ⟨sb, hsbmem, hsbid, hsbpar⟩ := hparentParent pb hpb
    rw [hpboxes] at hsbmem
    obtain ⟨m, hmmem, hkeep, hmsbid, hmsbpar⟩ := selectInput_box_spec inp
      (fun box => !Compound.inside inp.boxes group.id box.id) "" hsbmem
    refine ⟨m, hmmem, ?_, ?_, ?_⟩
    · exact hkeep
    · exact hmsbid.symm.trans hsbid
    · have hsp : sb.parent = m.parent := by
        rw [hmsbpar]
        exact selectInput_parent_root m.parent
      exact hsbpar.trans hsp

end Elegant.Layered.PipelineImpl
