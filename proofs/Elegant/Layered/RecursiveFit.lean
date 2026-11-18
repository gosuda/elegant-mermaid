import Elegant.Layered.ExecutedPortsFacts
import Elegant.Layered.SceneBounds
import Elegant.Layered.CaptionWidthFacts
import Elegant.Layered.SelectFacts
import Elegant.Layered.ExpandChildContainment

set_option autoImplicit false

/-!
# Recursive fit: C1, C2, C3 through `layoutRecursive`

This file discharges the geometric premises left open by
`layoutRecursive_c1_c3_of_flat`: for every successful `expandChild` the
recursion performs, the shifted child canvas fits inside the group frame
(because the frame size is `childFrameSize` of the child canvas plus insets),
box lookups transport, and parent pointers stay inside their own scene.

`ExpandChildFits` as stated in `ExpandChildContainment` quantifies the title
lines, title height, and shift freely, which no execution can satisfy; the
theorems here use the execution-instantiated form produced by
`expandChild_sources` / `layoutRecursive_embedding_assembly_sources`.
-/

namespace Elegant.Layered.PipelineImpl

open Validator
open Elegant.Layered.Compound

/-- Parent chains that terminate within the box list, mirroring the private
`parentTerminates` of `Model` but indexed like `Compound.ancestors`. -/
def chainTerm (boxes : List ModelBox) : Nat → String → Bool
  | _, "" => true
  | 0, _ => false
  | n + 1, id =>
    match boxes.findIdx? (fun b => b.id == id) with
    | none => false
    | some i =>
      match boxes[i]? with
      | none => false
      | some b => chainTerm boxes n b.parent

/-- The input-side facts every successful recursive layout relies on: unique
box ids, parent pointers that resolve inside the input, and parent chains
that terminate with enough fuel for `Compound.path`. -/
structure InputFacts (inp : Input) : Prop where
  nodup : (inp.boxes.map (·.id)).Nodup
  parents : ∀ b ∈ inp.boxes, b.parent = "" ∨ ∃ p ∈ inp.boxes, p.id = b.parent
  term : ∀ b ∈ inp.boxes, ∀ n, inp.boxes.length ≤ n + 1 →
    chainTerm inp.boxes n b.parent = true


namespace CompoundHelpers

theorem ancestors_empty (boxes : List ModelBox) (k : Nat) :
    Elegant.Layered.Compound.ancestors boxes k "" = [] := by
  cases k with
  | zero => rfl
  | succ k => exact Elegant.Layered.Compound.ancestors.eq_2 _ _

/-- One extra unit of fuel either changes nothing or prepends one index. -/
theorem ancestors_succ_step (boxes : List ModelBox) : ∀ (k : Nat) (id : String),
    Elegant.Layered.Compound.ancestors boxes k.succ id =
      Elegant.Layered.Compound.ancestors boxes k id ∨
      ∃ x, Elegant.Layered.Compound.ancestors boxes k.succ id =
        x :: Elegant.Layered.Compound.ancestors boxes k id := by
  intro k
  induction k with
  | zero =>
    intro id
    by_cases hid : id = ""
    · subst hid
      left
      rw [Elegant.Layered.Compound.ancestors.eq_2,
        Elegant.Layered.Compound.ancestors.eq_1]
    · rw [Elegant.Layered.Compound.ancestors.eq_3 boxes id 0 (fun h => hid h),
        Elegant.Layered.Compound.ancestors.eq_1]
      split
      · left; rfl
      · rename_i idx heq
        split
        · left; rfl
        · rename_i opt b hb
          right
          exact ⟨idx, rfl⟩
  | succ k ih =>
    intro id
    by_cases hid : id = ""
    · subst hid
      left
      rw [Elegant.Layered.Compound.ancestors.eq_2, ancestors_empty]
    · rw [Elegant.Layered.Compound.ancestors.eq_3 boxes id k.succ (fun h => hid h),
        Elegant.Layered.Compound.ancestors.eq_3 boxes id k (fun h => hid h)]
      split
      · left; rfl
      · rename_i idx heq
        split
        · left; rfl
        · rename_i opt b hb
          rcases ih b.parent with heq2 | ⟨x, hx⟩
          · left; rw [heq2]
          · right
            refine ⟨x, ?_⟩
            rw [hx]
            rfl

/-- Membership is monotone in fuel. -/
theorem ancestors_mem_mono (boxes : List ModelBox) {k : Nat} {id : String} {i : Nat}
    (h : i ∈ Elegant.Layered.Compound.ancestors boxes k id) :
    i ∈ Elegant.Layered.Compound.ancestors boxes k.succ id := by
  rcases ancestors_succ_step boxes k id with heq | ⟨x, hx⟩
  · rw [heq]; exact h
  · rw [hx]; exact List.mem_cons_of_mem _ h

/-- One step down in fuel either keeps membership or peels the head index. -/
theorem ancestors_mem_pred (boxes : List ModelBox) {k : Nat} {id : String} {i : Nat}
    (h : i ∈ Elegant.Layered.Compound.ancestors boxes k.succ id) :
    i ∈ Elegant.Layered.Compound.ancestors boxes k id ∨
      ∃ x, i = x ∧ Elegant.Layered.Compound.ancestors boxes k.succ id =
        x :: Elegant.Layered.Compound.ancestors boxes k id := by
  rcases ancestors_succ_step boxes k id with heq | ⟨x, hx⟩
  · left; rw [heq] at h; exact h
  · rw [hx] at h
    rcases List.mem_cons.mp h with hix | hmem
    · exact Or.inr ⟨x, hix, hx⟩
    · exact Or.inl hmem

/-- A terminating chain is stable: one more unit of fuel changes nothing. -/
theorem ancestors_stable (boxes : List ModelBox) : ∀ (n : Nat) (id : String),
    chainTerm boxes n id = true →
    Elegant.Layered.Compound.ancestors boxes n.succ id =
      Elegant.Layered.Compound.ancestors boxes n id := by
  intro n
  induction n with
  | zero =>
    intro id h
    have hid : id = "" := by
      by_cases hne : id = ""
      · exact hne
      · rw [chainTerm.eq_2 _ _ (fun hh => hne hh)] at h
        contradiction
    subst hid
    rw [Elegant.Layered.Compound.ancestors.eq_2,
      Elegant.Layered.Compound.ancestors.eq_1]
  | succ n ih =>
    intro id h
    by_cases hid : id = ""
    · subst hid
      rw [Elegant.Layered.Compound.ancestors.eq_2,
        Elegant.Layered.Compound.ancestors.eq_2]
    · rw [chainTerm.eq_3 _ _ _ (fun hh => hid hh)] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i idx heq opt b hb
          have hterm : chainTerm boxes n b.parent = true := h
          rw [Elegant.Layered.Compound.ancestors.eq_3 boxes id n.succ (fun hh => hid hh),
              Elegant.Layered.Compound.ancestors.eq_3 boxes id n (fun hh => hid hh)]
          split
          · rfl
          · rename_i j hj
            split
            · rfl
            · rename_i opt2 b2 hb2
              have hidxj : idx = j := Option.some.inj (heq.symm.trans hj)
              have hbj : b = b2 := by
                have h1 : boxes[idx]? = boxes[j]? := by rw [hidxj]
                rw [hb, hb2] at h1
                exact Option.some.inj h1
              rw [← hidxj, ← hbj, ih b.parent hterm]

end CompoundHelpers

/-- The shifted child canvas fits inside a frame whose width and height
dominate `childFrameSize`, provided the canvas margin does not exceed the
cluster pad. Pure arithmetic over the direction branches; no content
nonnegativity is needed because the content size appears linearly on both
sides of every comparison. -/
theorem childCanvas_contained {direction : String} {pad titleWidth titleHeight margin cw ch fw fh fx fy : Int}
    (htw : 0 ≤ titleWidth) (hth : 0 ≤ titleHeight)
    (hmargins : margin ≤ pad)
    (hfw : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).w ≤ fw)
    (hfh : (childFrameSize direction pad titleWidth titleHeight
      ⟨cw - 2 * margin, ch - 2 * margin⟩).h ≤ fh) :
    (⟨fx, fy, fw, fh⟩ : Rect).Contained
      (shiftRect (fx + (childInset direction pad titleWidth titleHeight).x - margin)
        (fy + (childInset direction pad titleWidth titleHeight).y - margin)
        (⟨0, 0, cw, ch⟩ : Rect)) := by
  unfold childInset shiftRect Rect.Contained
  unfold childFrameSize at hfw hfh
  split <;> split at hfw <;> split at hfh <;> simp_all <;> omega


/-- Execution-instantiated form of `ExpandChildFits`: the frame, metric,
title lines, box lines, and shift are pinned by the measurement equations
that `expandChild_sources` produces, so the fit is required only at the
values the recursion actually computed. Unlike `ExpandChildFits`, which
quantifies the title lines freely and is therefore not provable from frame
size facts alone, every universally quantified value here is constrained by
an equation that has at most one solution. -/
def ExpandChildFitAt (P : Params) (inp : Input) (o : Options) (group : ModelBox)
    (titleHeight : Int) (parent child result : FamilyResult) : Prop :=
  ∀ (frame : Box) (metric : Measure.Metric) (titleLines : List Measure.Line)
    (lines : List (List Measure.Line)) (dx dy : Int),
    parent.scene.boxes.find? (fun box => box.id == group.id) = some frame →
    metricOf o.profile = .ok metric →
    StyledMeasure.wrap metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      (inp.texts.getD
        ((inp.boxes.findIdx? (fun box => box.id == group.id)).getD 0) group.id).toList =
          .ok titleLines →
    boxLines metric
      (Measure.wrapTarget metric.profile P.wrapWidth
        (if o.profile == .cell then o.maxWidth else 0))
      inp = .ok lines →
    dx = frame.rect.x + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).x -
      P.canvasMargin →
    dy = frame.rect.y + (childInset group.direction P.clusterPad
        (titleLines.foldl (fun width line => max width line.width) 0) titleHeight).y -
      P.canvasMargin →
    frame.rect.Contained
        (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)) ∧
    (∀ box : Box, child.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some (embedBox group.id dx dy box)) ∧
    (∀ box : Box, parent.scene.layoutDump.box? box.id = some box →
      result.scene.layoutDump.box? box.id = some box)

/-- `expandChild` preserves C1 and C3 when the fit premise is stated at the
execution-instantiated measurement values. The proof is the
`expandChild_c1_c3` argument with `hfit` applied to the values extracted by
`expandChild_sources`, which also discharge its measurement premises. -/
theorem expandChild_c1_c3_at {P : Params} {inp : Input} {o : Options}
    {group : ModelBox} {titleHeight : Int}
    {parent child result : FamilyResult}
    (hparentC1 : Validator.C1 parent.scene.layoutDump)
    (hchildC1 : Validator.C1 child.scene.layoutDump)
    (hparentC3 : Validator.C3 parent.scene.layoutDump)
    (hchildC3 : Validator.C3 child.scene.layoutDump)
    (hfit : ExpandChildFitAt P inp o group titleHeight parent child result)
    (hparentClosed : SceneParentClosed parent.scene)
    (hchildClosed : SceneParentClosed child.scene)
    (h : expandChild P inp o group titleHeight parent child = .ok result) :
    Validator.C1 result.scene.layoutDump ∧ Validator.C3 result.scene.layoutDump := by
  obtain ⟨frame, metric, titleLines, lines, dx, dy, hframe, hmetric, htitle,
    hlines, hdx, hdy, hcanvas, hboxes⟩ := expandChild_sources h
  have hframeMem : frame ∈ parent.scene.boxes := List.mem_of_find?_eq_some hframe
  have hfit' := hfit frame metric titleLines lines dx dy hframe hmetric htitle hlines hdx hdy
  have hframeId : frame.id = group.id := by simpa using List.find?_some hframe
  have hcanvasRect : Validator.canvasRect result.scene.layoutDump =
      Validator.canvasRect parent.scene.layoutDump := by
    unfold Validator.canvasRect
    have : result.scene.layoutDump.canvas = parent.scene.layoutDump.canvas := hcanvas
    rw [this]
  have hframeC1 : (Validator.canvasRect result.scene.layoutDump).Contained frame.rect := by
    rw [hcanvasRect]
    exact hparentC1 frame hframeMem
  constructor
  · intro b hb
    have hbMem : b ∈ result.scene.layoutDump.boxes := hb
    simp only [Scene.layoutDump] at hbMem
    change b ∈ result.scene.boxes at hbMem
    rw [hboxes] at hbMem
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hbMem
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hbc
      have hshift : (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
          (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildC1 c hc)
      exact Rect.Contained.trans hframeC1 (Rect.Contained.trans hfit'.1 hshift)
    · rw [hcanvasRect]
      exact hparentC1 b hbp
  · intro b hb hne p hp
    simp only [Scene.layoutDump] at hb
    change b ∈ result.scene.boxes at hb
    rw [hboxes] at hb
    obtain ⟨_, -, hfind⟩ := List.mem_filterMap.mp hb
    have hbItems : b ∈ (child.scene.boxes.map (embedBox group.id dx dy)) ++
        parent.scene.boxes := List.mem_of_find?_eq_some hfind
    rcases List.mem_append.mp hbItems with hbc | hbp
    · obtain ⟨c, hc, hbEq⟩ := List.mem_map.mp hbc
      by_cases hcRoot : c.parent = ""
      · have hbParent : b.parent = group.id := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcRoot]
        have hframeSelf : parent.scene.layoutDump.box? frame.id = some frame := by
          rw [hframeId]
          exact hframe
        have hresultLookup := hfit'.2.2 frame hframeSelf
        rw [hframeId] at hresultLookup
        rw [hbParent] at hp
        rw [hresultLookup] at hp
        have hpEq : frame = p := Option.some.inj hp
        subst hpEq
        have hshift : (shiftRect dx dy (Validator.canvasRect child.scene.layoutDump)).Contained
            (shiftRect dx dy c.rect) := (contained_shiftRect dx dy).mpr (hchildC1 c hc)
        rw [← hbEq]
        exact Rect.Contained.trans hfit'.1 hshift
      · have hbParent : b.parent = c.parent := by
          have hproj : b.parent = (if c.parent == "" then group.id else c.parent) := by
            rw [← hbEq]; rfl
          rw [hproj]
          simp [hcRoot]
        rcases hchildClosed c hc with hcpEmpty | ⟨p', hp'mem, hp'id⟩
        · exact absurd hcpEmpty hcRoot
        · have hfindNe : child.scene.boxes.find? (fun candidate => candidate.id == c.parent) ≠ none := by
            intro hnone
            rw [List.find?_eq_none] at hnone
            exact absurd (hnone p' hp'mem) (by simp [hp'id])
          cases hfind2 : child.scene.boxes.find? (fun candidate => candidate.id == c.parent) with
          | none => exact absurd hfind2 hfindNe
          | some p'' =>
            have hchildLookup : child.scene.layoutDump.box? c.parent = some p'' := hfind2
            have hp''cont := hchildC3 c hc hcRoot p'' hchildLookup
            have hp''id : p''.id = c.parent := by simpa using List.find?_some hfind2
            have hp''self : child.scene.layoutDump.box? p''.id = some p'' := by
              rw [hp''id]; exact hchildLookup
            have hchildLookup' := hfit'.2.1 p'' hp''self
            rw [hp''id] at hchildLookup'
            rw [hbParent] at hp
            rw [hchildLookup'] at hp
            have hpEq : embedBox group.id dx dy p'' = p := Option.some.inj hp
            subst hpEq
            have hshift : (shiftRect dx dy p''.rect).Contained (shiftRect dx dy c.rect) :=
              (contained_shiftRect dx dy).mpr hp''cont
            rw [← hbEq]
            exact hshift
    · rcases hparentClosed b hbp with hbEmpty | ⟨p', hp'mem, hp'id⟩
      · exact absurd hbEmpty hne
      · have hfindNe : parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) ≠ none := by
          intro hnone
          rw [List.find?_eq_none] at hnone
          exact absurd (hnone p' hp'mem) (by simp [hp'id])
        cases hfind2 : parent.scene.boxes.find? (fun candidate => candidate.id == b.parent) with
        | none => exact absurd hfind2 hfindNe
        | some p'' =>
          have hparentLookup : parent.scene.layoutDump.box? b.parent = some p'' := hfind2
          have hp''cont := hparentC3 b hbp hne p'' hparentLookup
          have hp''id : p''.id = b.parent := by simpa using List.find?_some hfind2
          have hp''self : parent.scene.layoutDump.box? p''.id = some p'' := by
            rw [hp''id]; exact hparentLookup
          have hparentLookup' := hfit'.2.2 p'' hp''self
          rw [hp''id] at hparentLookup'
          rw [hparentLookup'] at hp
          have hpEq : p'' = p := Option.some.inj hp
          subst hpEq
          exact hp''cont
/-- More fuel never hurts a terminating chain: the lookups are deterministic,
so a chain that reaches `""` within `n` steps also reaches it within `m ≥ n`. -/
theorem chainTerm_mono_fuel (boxes : List ModelBox) :
    ∀ (n m : Nat) (id : String), n ≤ m →
    chainTerm boxes n id = true → chainTerm boxes m id = true := by
  intro n
  induction n with
  | zero =>
    intro m id _ h
    by_cases hid : id = ""
    · subst hid
      exact chainTerm.eq_1 _ _
    · rw [chainTerm.eq_2 _ _ hid] at h
      contradiction
  | succ n ih =>
    intro m id hnm h
    by_cases hid : id = ""
    · subst hid
      exact chainTerm.eq_1 _ _
    · rw [chainTerm.eq_3 _ _ _ hid] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i idx heq opt b hb
          have hterm : chainTerm boxes n b.parent = true := h
          cases m with
          | zero => exact absurd hnm (by omega)
          | succ m' =>
            rw [chainTerm.eq_3 _ _ _ hid, heq]
            dsimp only
            rw [hb]
            dsimp only
            exact ih m' b.parent (by omega) hterm



/-- Two model boxes with equal ids coincide in a list with nodup ids. -/
theorem eq_of_mem_id {boxes : List ModelBox} (hnodup : (boxes.map (·.id)).Nodup)
    {a b : ModelBox} (ha : a ∈ boxes) (hb : b ∈ boxes) (h : a.id = b.id) : a = b := by
  induction boxes generalizing a b with
  | nil => cases ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | hal
    · rcases List.mem_cons.mp hb with rfl | hbl
      · rfl
      · exact absurd (List.mem_map.mpr ⟨b, hbl, h.symm⟩) (List.nodup_cons.mp hnodup).1
    · rcases List.mem_cons.mp hb with rfl | hbl
      · exact absurd (List.mem_map.mpr ⟨a, hal, h⟩) (List.nodup_cons.mp hnodup).1
      · exact ih (List.nodup_cons.mp hnodup).2 hal hbl h

/-- In a nodup-id list, `find?` returns the unique box with the wanted id. -/
theorem find?_unique {boxes : List ModelBox} (hnodup : (boxes.map (·.id)).Nodup)
    {x : String} {m : ModelBox}
    (h : boxes.find? (fun b => b.id == x) = some m) :
    m.id = x ∧ ∀ b ∈ boxes, b.id = x → b = m := by
  constructor
  · simpa only [beq_iff_eq] using List.find?_some h
  · intro b hb hbx
    have hmx : m.id = x := by
      simpa only [beq_iff_eq] using List.find?_some h
    exact (eq_of_mem_id hnodup (List.mem_of_find?_eq_some h) hb
      (hmx.trans hbx.symm)).symm

theorem mem_getElem? {α : Type} {l : List α} {a : α} (h : a ∈ l) :
    ∃ i : Nat, l[i]? = some a := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := ih h
      exact ⟨i + 1, by rw [List.getElem?_cons_succ, hi]⟩

theorem getElem?_mem' {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp h
  have hm : l[i] ∈ l := List.getElem_mem hi
  rwa [hget] at hm

/-- Membership in a `selectInput` box list comes from a kept input box, with
the parent pointer rewritten at `root`. -/
theorem selectInput_box_spec (inp : Input) (keep : ModelBox → Bool) (root : String)
    {b : ModelBox} (hb : b ∈ (selectInput inp keep root).boxes) :
    ∃ m ∈ inp.boxes, keep m = true ∧ b.id = m.id ∧
      b.parent = (if m.parent == root then "" else m.parent) := by
  unfold selectInput at hb
  dsimp only at hb
  obtain ⟨q, hq, hbq⟩ := List.mem_map.mp hb
  obtain ⟨hqzip, hkq⟩ := List.mem_filter.mp hq
  have hget : inp.boxes[q.2]? = some q.1 := List.mem_zipIdx_iff_getElem?.mp hqzip
  refine ⟨q.1, getElem?_mem' hget, hkq, ?_, ?_⟩
  · rw [← hbq]; split <;> rfl
  · rw [← hbq]; split <;> rfl

/-- A kept input box has an image in the `selectInput` box list with the
rewritten parent pointer. -/
theorem selectInput_box_exists (inp : Input) (keep : ModelBox → Bool) (root : String)
    {m : ModelBox} (hm : m ∈ inp.boxes) (hk : keep m = true) :
    ∃ b ∈ (selectInput inp keep root).boxes, b.id = m.id ∧
      b.parent = (if m.parent == root then "" else m.parent) := by
  obtain ⟨i, hi⟩ := mem_getElem? hm
  refine ⟨(if m.parent == root then { m with parent := "" } else m), ?_, by split <;> rfl, ?_⟩
  · unfold selectInput
    dsimp only
    refine List.mem_map.mpr ⟨(m, i), ?_, rfl⟩
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hi, hk⟩
  · split <;> rfl

/-- `inside` locates the endpoint box, the group index, and puts the group
index on the endpoint's ancestor path. -/
theorem inside_spec {boxes : List ModelBox} {group x : String}
    (h : Compound.inside boxes group x = true) :
    ∃ m ∈ boxes, m.id = x ∧
    ∃ gidx : Nat, boxes.findIdx? (fun b => b.id == group) = some gidx ∧
      ∃ gbox : ModelBox, boxes[gidx]? = some gbox ∧ gbox.id = group ∧
        gidx ∈ Elegant.Layered.Compound.ancestors boxes boxes.length m.parent := by
  unfold Compound.inside Compound.path at h
  split at h
  · rename_i box index hbox hidx
    obtain ⟨hlt, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hidx
    have hboxget : boxes[index]? = some boxes[index] := List.getElem?_eq_getElem hlt
    have hmem : index ∈ Elegant.Layered.Compound.ancestors boxes boxes.length box.parent := by
      simpa [Compound.path] using h
    refine ⟨box, List.mem_of_find?_eq_some hbox, ?_, index, hidx,
      boxes[index], hboxget, ?_, hmem⟩
    · have hbeq : (box.id == x) = true :=
        List.find?_some (p := fun (b : ModelBox) => b.id == x) hbox
      simpa only [beq_iff_eq] using hbeq
    · exact beq_iff_eq.mp hmatch
  · simp at h

/-- `ancestors` at fuel `boxes.length` equals fuel `boxes.length - 1` when the
chain terminates: one application of `ancestors_stable`. -/
theorem ancestors_length_pred {boxes : List ModelBox} {id : String}
    (hlen : 0 < boxes.length) (hterm : chainTerm boxes (boxes.length - 1) id = true) :
    Elegant.Layered.Compound.ancestors boxes boxes.length id =
      Elegant.Layered.Compound.ancestors boxes (boxes.length - 1) id := by
  have h := CompoundHelpers.ancestors_stable boxes (boxes.length - 1) id hterm
  rw [show boxes.length = boxes.length - 1 + 1 from by omega]
  exact h

/-- Rebuild `inside` from membership and ancestor-path evidence. -/
theorem inside_of_ancestors {boxes : List ModelBox} {group x : String} {gidx : Nat}
    (hnodup : (boxes.map (·.id)).Nodup) {m : ModelBox}
    (hm : m ∈ boxes) (hx : m.id = x)
    (hg : boxes.findIdx? (fun b => b.id == group) = some gidx)
    (hmem : gidx ∈ Elegant.Layered.Compound.ancestors boxes boxes.length m.parent) :
    Compound.inside boxes group x = true := by
  unfold Compound.inside Compound.path
  split
  · rename_i m' index hfind hfindIdx
    have hmx : m'.id = x := by
      have hbeq : (m'.id == x) = true :=
        List.find?_some (p := fun (b : ModelBox) => b.id == x) hfind
      exact beq_iff_eq.mp hbeq
    have hmm : m' = m := eq_of_mem_id hnodup (List.mem_of_find?_eq_some hfind) hm
      (hmx.trans hx.symm)
    have hig : index = gidx := by
      have := hfindIdx.symm.trans hg
      exact Option.some.inj this
    subst hig
    rw [hmm]
    show (Elegant.Layered.Compound.ancestors boxes boxes.length m.parent).contains index = true
    exact (List.contains_iff_mem).mpr hmem
  · rename_i h
    -- catch-all: derive False from h using find? = some _ and findIdx? = some gidx
    cases hf : boxes.find? (fun box => box.id == x) with
    | none => exact (List.find?_eq_none.mp hf m hm (beq_iff_eq.mpr hx)).elim
    | some b => exact (h b _ hf hg).elim

/-- Upward closure of `inside` along a resolved parent pointer. -/
theorem inside_parent_step {boxes : List ModelBox} (hnodup : (boxes.map (·.id)).Nodup)
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 →
      chainTerm boxes n b.parent = true)
    {group : String} {m p : ModelBox}
    (hm : m ∈ boxes) (hp : p ∈ boxes) (hpid : p.id = m.parent)
    (hinside : Compound.inside boxes group m.id = true) :
    m.parent = group ∨ Compound.inside boxes group p.id = true := by
  obtain ⟨m', hm'mem, hm'id, gidx, hfindIdx, gbox, hgget, hgboxid, hmem⟩ :=
    inside_spec hinside
  have hmm : m' = m := eq_of_mem_id hnodup hm'mem hm hm'id
  rw [hmm] at hmem
  have hlen1 : 0 < boxes.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
  by_cases hmp : m.parent = ""
  · have hnil : Elegant.Layered.Compound.ancestors boxes boxes.length "" = [] := by
      cases hL : boxes.length with
      | zero => exact Elegant.Layered.Compound.ancestors.eq_1 _ _
      | succ n => exact Elegant.Layered.Compound.ancestors.eq_2 _ _
    rw [hmp, hnil] at hmem
    simp at hmem
  · have hsucc : boxes.length = (boxes.length - 1).succ :=
      (Nat.succ_pred_eq_of_pos hlen1).symm
    conv at hmem => rw [hsucc]
    rw [Elegant.Layered.Compound.ancestors.eq_3 boxes m.parent
      (boxes.length - 1) hmp] at hmem
    split at hmem
    · simp at hmem
    · rename_i i heq
      split at hmem
      · simp at hmem
      · rename_i opt b hb
        obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp heq
        obtain ⟨_, hboxesi⟩ := List.getElem?_eq_some_iff.mp hb
        have hb' : boxes[i].id = m.parent := beq_iff_eq.mp hmatch
        rw [hboxesi] at hb'
        have hbp : b.id = p.id := hb'.trans hpid.symm
        have hbeq : b = p := eq_of_mem_id hnodup (getElem?_mem' hb) hp hbp
        rw [hbeq] at hmem
        rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hgid
        · right
          have htermL : chainTerm boxes (boxes.length - 1) p.parent :=
            hterm p hp _ (by omega)
          have hmemL : gidx ∈ Elegant.Layered.Compound.ancestors boxes
              boxes.length p.parent := by
            rw [ancestors_length_pred hlen1 htermL]
            exact hmem
          exact inside_of_ancestors hnodup hp rfl hfindIdx hmemL
        · left
          obtain ⟨_, hgmatch2, _⟩ := List.findIdx?_eq_some_iff_getElem.mp heq
          have hgm : boxes[i].id = m.parent := beq_iff_eq.mp hgmatch2
          obtain ⟨hglt2, hgeq⟩ := List.getElem?_eq_some_iff.mp hgget
          simp only [hgid] at hgeq
          have hgi : boxes[i].id = group := by rw [hgeq]; exact hgboxid
          exact hgm.symm.trans hgi

theorem inside_ancestor_forward {boxes : List ModelBox} (hnodup : (boxes.map (·.id)).Nodup)
    (hterm : ∀ b ∈ boxes, ∀ n, boxes.length ≤ n + 1 →
      chainTerm boxes n b.parent = true)
    {group : String} {m p : ModelBox}
    (hm : m ∈ boxes) (hp : p ∈ boxes) (hpid : p.id = m.parent)
    (hmp : m.parent ≠ "")
    (hinside : Compound.inside boxes group p.id = true) :
    Compound.inside boxes group m.id = true := by
  obtain ⟨p', hp'mem, hp'id, gidx, hfindIdx, gbox, hgget, hgboxid, hpmem⟩ :=
    inside_spec hinside
  have hpp : p' = p := eq_of_mem_id hnodup hp'mem hp hp'id
  rw [hpp] at hpmem
  have hlen1 : 0 < boxes.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hm)
  have hterm' : chainTerm boxes (boxes.length - 1) p.parent :=
    hterm p hp _ (by omega)
  have hpmem' : gidx ∈ Elegant.Layered.Compound.ancestors boxes
      (boxes.length - 1) p.parent := by
    have := hpmem
    rw [ancestors_length_pred hlen1 hterm'] at this
    exact this
  apply inside_of_ancestors hnodup hm rfl hfindIdx
  rw [← hpid]
  have hsucc : boxes.length = (boxes.length - 1).succ :=
    (Nat.succ_pred_eq_of_pos hlen1).symm
  conv => rw [hsucc]
  rw [Elegant.Layered.Compound.ancestors.eq_3 boxes p.id
    (boxes.length - 1) (by
      intro h
      apply hmp
      rw [← hpid]
      exact h)]
  split
  · rename_i hnone
    have hne := List.findIdx?_eq_none_iff.mp hnone p hp
    simp at hne
  · rename_i i hfindp
    obtain ⟨hi, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfindp
    split
    · rename_i hnone2
      simp [List.getElem?_eq_getElem hi] at hnone2
    · rename_i opt b hb
      obtain ⟨_, hboxesi⟩ := List.getElem?_eq_some_iff.mp hb
      have hb' : boxes[i].id = p.id := beq_iff_eq.mp hmatch
      rw [hboxesi] at hb'
      have hbeq : b = p := eq_of_mem_id hnodup (getElem?_mem' hb) hp hb'
      rw [hbeq]
      rw [List.mem_append]
      exact Or.inl hpmem'


/-! ### generic list helpers -/

theorem find?_eq_some_of_mem_unique {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) :
    ∀ (l : List α) (a : α), p a = true → a ∈ l → (∀ b ∈ l, p b = true → b = a) →
    l.find? p = some a := by
  intro l
  induction l with
  | nil => intro a _ ha _; cases ha
  | cons c l ih =>
    intro a hpa ha huniq
    by_cases hpc : p c = true
    · have hca : c = a := huniq c List.mem_cons_self hpc
      subst hca
      simp [hpa]
    · rcases List.mem_cons.mp ha with hac | hal
      · rw [hac] at hpa
        exact absurd hpa hpc
      · simp only [List.find?_cons_of_neg hpc]
        exact ih a hpa hal
          (fun b hb hpb => huniq b (List.mem_cons_of_mem c hb) hpb)

theorem zipIdx_map_proj {α : Type} {β : Type} (f : α → β) (n : Nat) (l : List α) :
    ((l.zipIdx n).map fun q => f q.1) = l.map f := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih => simp [List.zipIdx_cons, ih (n + 1)]

theorem nodup_filter_map {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.map f).Nodup → ((l.filter p).map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
    intro h
    by_cases hp : p a = true
    · rw [show (a :: l).filter p = a :: l.filter p from by simp [hp]]
      refine List.nodup_cons.mpr ⟨?_, ih ((List.nodup_cons.mp h).2)⟩
      intro hc
      obtain ⟨b, hbmem, hbf⟩ := List.mem_map.mp hc
      obtain ⟨hbIn, hbP⟩ := List.mem_filter.mp hbmem
      exact (List.nodup_cons.mp h).1 (List.mem_map.mpr ⟨b, hbIn, hbf⟩)
    · rw [show (a :: l).filter p = l.filter p from by simp [hp]]
      exact ih ((List.nodup_cons.mp h).2)

theorem filterMap_lookup_ids {inp : List ModelBox} (pool : List Box)
    (hsome : ∀ m ∈ inp, ∃ b : Box, pool.find? (fun (box : Box) => box.id == m.id) = some b) :
    (inp.filterMap (fun (m : ModelBox) => pool.find? (fun (box : Box) => box.id == m.id))).map (·.id) =
      inp.map (·.id) := by
  induction inp with
  | nil => rfl
  | cons m inp ih =>
    obtain ⟨b, hb⟩ := hsome m List.mem_cons_self
    have hbid : b.id = m.id :=
      beq_iff_eq.mp (List.find?_some (p := fun (box : Box) => box.id == m.id) hb)
    have hfm : (m :: inp).filterMap (fun (m : ModelBox) => pool.find? (fun (box : Box) => box.id == m.id)) =
        b :: inp.filterMap (fun (m : ModelBox) => pool.find? (fun (box : Box) => box.id == m.id)) := by
      simp [hb]
    rw [hfm, List.map_cons, List.map_cons, hbid]
    exact congrArg (fun l : List String => m.id :: l)
      (ih (fun (x : ModelBox) (hx : x ∈ inp) => hsome x (List.mem_cons_of_mem _ hx)))

theorem selectInput_mapped_mem (inp : Input) (keep : ModelBox → Bool) (root : String)
    {m : ModelBox} (hm : m ∈ inp.boxes) (hk : keep m = true) :
    (if m.parent == root then { m with parent := "" } else m) ∈
      (selectInput inp keep root).boxes := by
  obtain ⟨i, hi⟩ := mem_getElem? hm
  unfold selectInput
  dsimp only
  refine List.mem_map.mpr ⟨(m, i),
    List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hi, hk⟩, ?_⟩
  show (if m.parent == root then { m with parent := "" } else m) =
    (if m.parent == root then { m with parent := "" } else m)
  dsimp only


/-! ### chain termination helpers -/

theorem chainTerm_self_loop (boxes : List ModelBox) (hnodup : (boxes.map (·.id)).Nodup)
    {c : String} (hc : c ≠ "") (hb : ∃ b ∈ boxes, b.id = c ∧ b.parent = c) :
    ∀ k, chainTerm boxes k c = false := by
  intro k
  induction k with
  | zero => exact chainTerm.eq_2 boxes c hc
  | succ k ih =>
    obtain ⟨b, hbmem, hbid, hbp⟩ := hb
    obtain ⟨j, hj⟩ := mem_getElem? hbmem
    obtain ⟨hjlt, hsj⟩ := List.getElem?_eq_some_iff.mp hj
    have hxj : ((boxes[j].id == c) = true) := by
      rw [hsj, hbid]; exact beq_self_eq_true c
    have hmemj : boxes[j] ∈ boxes := List.getElem_mem hjlt
    have hjb : boxes[j] = b := by
      refine eq_of_mem_id hnodup hmemj hbmem ?_
      rw [hsj, hbid]
    rw [chainTerm.eq_3 boxes c k (fun hh => hc hh)]
    cases hres : boxes.findIdx? (fun (b0 : ModelBox) => b0.id == c) with
    | none =>
      exact absurd hxj
        (fun hc => Bool.noConfusion
          ((List.findIdx?_eq_none_iff.mp hres boxes[j] hmemj).symm.trans hc))
    | some j'' =>
      obtain ⟨hjlt2, hxj2, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hres
      have hmemj2 : boxes[j''] ∈ boxes := List.getElem_mem hjlt2
      have hxj2eq : boxes[j''].id = c := beq_iff_eq.mp hxj2
      have hjb2 : boxes[j''] = b := eq_of_mem_id hnodup hmemj2 hbmem
        (hxj2eq.trans hbid.symm)
      split
      · rename_i heqnone
        simp at heqnone
      · rename_i i heq
        have hij : i = j'' := Option.some.inj heq.symm
        rw [hij, List.getElem?_eq_getElem hjlt2]
        split
        · rename_i heqnone2
          simp at heqnone2
        · rename_i b0 hb0
          have hb0eq : boxes[j''] = b0 := Option.some.inj hb0
          rw [← hb0eq, hjb2, hbp]
          exact ih

/-! ### `selectInput` keeps the `InputFacts` invariant -/

theorem chainTerm_selectInput_mono (inp : Input) (keep : ModelBox → Bool) (root : String)
    (hnodup : (inp.boxes.map (·.id)).Nodup)
    (hclose : ∀ b ∈ inp.boxes, keep b = true →
      b.parent = "" ∨ (b.parent == root) = true ∨
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ keep p = true) :
    ∀ (n : Nat) (x : String), chainTerm inp.boxes n x = true →
      (x = "" ∨ ∃ m ∈ inp.boxes, m.id = x ∧ keep m = true) →
      chainTerm (selectInput inp keep root).boxes n x = true := by
  have hselNodup : ((selectInput inp keep root).boxes.map (·.id)).Nodup := by
    rw [selectInput_box_ids inp keep root]
    exact nodup_filter_map keep (·.id) inp.boxes hnodup
  intro n
  induction n with
  | zero =>
    intro x hx hreach
    by_cases hxe : x = ""
    · subst hxe; exact chainTerm.eq_1 _ _
    · rw [chainTerm.eq_2 _ _ hxe] at hx; contradiction
  | succ n ih =>
    intro x hx hreach
    by_cases hxe : x = ""
    · subst hxe; exact chainTerm.eq_1 _ _
    · rw [chainTerm.eq_3 inp.boxes x n hxe] at hx
      split at hx
      · contradiction
      · split at hx
        · contradiction
        · rename_i idx heq opt b hb
          obtain ⟨m, hmmem, hmx, hkm⟩ := hreach.resolve_left hxe
          have hmapped : (if m.parent == root then { m with parent := "" } else m) ∈
              (selectInput inp keep root).boxes :=
            selectInput_mapped_mem inp keep root hmmem hkm
          have hmapid : (if m.parent == root then { m with parent := "" } else m).id = x := by
            split <;> exact hmx
          obtain ⟨j, hj⟩ := mem_getElem? hmapped
          obtain ⟨hlt, hsj⟩ := List.getElem?_eq_some_iff.mp hj
          have hxj : ((selectInput inp keep root).boxes[j].id == x) = true := by
            rw [hsj, hmapid]; exact beq_self_eq_true x
          have hfiNone : (selectInput inp keep root).boxes.findIdx?
              (fun b0 => b0.id == x) ≠ none := by
            intro hnone
            have h2f : ((if m.parent == root then { m with parent := "" } else m).id == x) =
                false :=
              List.findIdx?_eq_none_iff.mp hnone
                (if m.parent == root then { m with parent := "" } else m) hmapped
            rw [hmapid] at h2f
            exact Bool.noConfusion ((beq_self_eq_true x).symm.trans h2f)
          rw [chainTerm.eq_3 (selectInput inp keep root).boxes x n hxe]
          cases hfi : (selectInput inp keep root).boxes.findIdx?
              (fun b0 => b0.id == x) with
          | none => exact absurd hfi hfiNone
          | some i =>
            obtain ⟨hi, hmatchi, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
            have hxi : (selectInput inp keep root).boxes[i].id = x := beq_iff_eq.mp hmatchi
            have hmemi : (selectInput inp keep root).boxes[i] ∈
                (selectInput inp keep root).boxes := List.getElem_mem hi
            have himapped : (selectInput inp keep root).boxes[i] =
                (if m.parent == root then { m with parent := "" } else m) :=
              eq_of_mem_id hselNodup hmemi hmapped (hxi.trans hmapid.symm)
            split
            · rename_i heqnone
              simp at heqnone
            · rename_i i2 heq2
              have hi2 : i2 = i := (Option.some.inj heq2).symm
              rw [hi2, List.getElem?_eq_getElem hi]
              split
              · rename_i heqnone2
                simp at heqnone2
              · rename_i b0 hb0
                have hb0eq : (selectInput inp keep root).boxes[i] = b0 :=
                  Option.some.inj hb0
                rw [← hb0eq, himapped]
                show chainTerm (selectInput inp keep root).boxes n
                  (if m.parent == root then { m with parent := "" } else m).parent = true
                split
                · exact chainTerm.eq_1 _ _
                · rename_i hnotroot
                  obtain ⟨hilt, hmatchb, _⟩ := List.findIdx?_eq_some_iff_getElem.mp heq
                  obtain ⟨_, hbi⟩ := List.getElem?_eq_some_iff.mp hb
                  have hbx : b.id = x := by rw [← hbi]; exact beq_iff_eq.mp hmatchb
                  have hbmem : b ∈ inp.boxes := getElem?_mem' hb
                  have hbm : b = m := eq_of_mem_id hnodup hbmem hmmem (hbx.trans hmx.symm)
                  rw [hbm] at hx
                  rcases hclose m hmmem hkm with h0 | h1 | ⟨p, hpmem, hpid, hkp⟩
                  · exact ih m.parent hx (Or.inl h0)
                  · exact absurd h1 hnotroot
                  · exact ih m.parent hx (Or.inr ⟨p, hpmem, hpid, hkp⟩)

/-! ### keep-closure lemmas -/

theorem keepInside_close {inp : Input} {group : String} (hf : InputFacts inp)
    {b : ModelBox} (hb : b ∈ inp.boxes)
    (hkept : Compound.inside inp.boxes group b.id = true) :
    b.parent = "" ∨ (b.parent == group) = true ∨
      ∃ p ∈ inp.boxes, p.id = b.parent ∧ Compound.inside inp.boxes group p.id = true := by
  rcases hf.parents b hb with h0 | ⟨p, hpmem, hpid⟩
  · exact Or.inl h0
  · rcases inside_parent_step hf.nodup hf.term hb hpmem hpid hkept with h1 | h2
    · exact Or.inr (Or.inl (by rw [h1]; exact beq_self_eq_true group))
    · exact Or.inr (Or.inr ⟨p, hpmem, hpid, h2⟩)

theorem keepOutside_close {inp : Input} {group : String} (hf : InputFacts inp)
    {b : ModelBox} (hb : b ∈ inp.boxes)
    (hkept : (!Compound.inside inp.boxes group b.id) = true) :
    b.parent = "" ∨ (b.parent == "") = true ∨
      ∃ p ∈ inp.boxes, p.id = b.parent ∧
        (!Compound.inside inp.boxes group p.id) = true := by
  by_cases hbe : b.parent = ""
  · exact Or.inl hbe
  · rcases hf.parents b hb with h0 | ⟨p, hpmem, hpid⟩
    · exact Or.inl h0
    · by_cases hin : Compound.inside inp.boxes group p.id = true
      · exact absurd (inside_ancestor_forward hf.nodup hf.term hb hpmem hpid hbe hin)
          (fun hc => by rw [hc] at hkept; simp at hkept)
      · refine Or.inr (Or.inr ⟨p, hpmem, hpid, ?_⟩)
        rw [show Compound.inside inp.boxes group p.id = false from by
          cases h : Compound.inside inp.boxes group p.id
          · rfl
          · exact absurd h hin]
        rfl

end Elegant.Layered.PipelineImpl
