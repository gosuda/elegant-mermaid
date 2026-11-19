import Elegant.ForInFacts
import Elegant.Kinds.Eventmodeling
import ElegantGeometry.Validator

set_option autoImplicit false

/-! Scene-validity obligations for the eventmodeling family adapter.

The layout path is `Kinds.Eventmodeling.layout`, which runs `scene`, which runs
`decode` followed by `Lanes.Eventmodeling.layout`.  `eventmodeling_c1` already
lives in `Elegant.Kinds.Eventmodeling`; this file develops the remaining
`eventmodeling_c3` obligation by pushing invariants through the actual
executed `decode` loops.

`decode`'s first loop carries two mutable variables (`g : Family` and
`ids : List String`), so its `forIn` state is `Family × List String` with
`.1 = g`, `.2 = ids`.  The invariant to push through that loop is
`FrameParentsD`: the lane lookup is required only when the parent string is
realized by a group box of the sources, which is exactly what clause C3
needs (`Validator.C3` is vacuous for a parent that names no box).  This
avoids the private `parentTerminates` check in `Elegant.Model`. The prefix
lemmas below preserve frame provenance and conditional parent lookup through
the group, existing-lane, and fallback-lane updates.
`decode_first_loop_processed_groups` carries group coverage through the actual
first `forIn`, including both caption-measurement branches. `CompleteDecodePrefix`
also tracks conditional indexed lane identity, real-group lane provenance,
and nonempty lane-ID uniqueness. Synthetic fallback keys retain the source
parent string while their lanes retain the empty ID. The final proof carries
these invariants through the executed relation and caption loops and uses
the actual parent-box lookup to establish C3. -/

namespace Elegant.Kinds.Eventmodeling

open Common

/-! ### Small bridges -/

private theorem bind_ok {α β : Type} {x : Except LayoutError α}
    {f : α → Except LayoutError β} {out : β} (h : x.bind f = .ok out) :
    ∃ a, x = .ok a ∧ f a = .ok out := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem forIn_yield_foldlM {α β : Type} (step : α → β → Except LayoutError β)
    (xs : List α) (init : β) :
    (ForIn.forIn (m := Except LayoutError) xs init
        (fun a s => (step a s).map ForInStep.yield)) =
      List.foldlM (fun acc a => step a acc) init xs := by
  induction xs generalizing init with
  | nil => rfl
  | cons a rest ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    simp only [Bind.bind, Except.bind]
    cases hs : step a init with
    | error e => rfl
    | ok v => exact ih v

private theorem mem_id_unique {boxes : List ModelBox}
    (h : (boxes.map (·.id)).Nodup)
    {x y : ModelBox} (hx : x ∈ boxes) (hy : y ∈ boxes) (hid : x.id = y.id) : x = y := by
  induction boxes with
  | nil => cases hx
  | cons a rest ih =>
    have hn := List.nodup_cons.mp h
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · have hy_mem : y.id ∈ rest.map (·.id) := List.mem_map_of_mem hy'
        rw [← hid] at hy_mem
        exact absurd hy_mem hn.1
    · rcases List.mem_cons.mp hy with rfl | hy'
      · have hx_mem : x.id ∈ rest.map (·.id) := List.mem_map_of_mem hx'
        rw [hid] at hx_mem
        exact absurd hx_mem hn.1
      · exact ih hn.2 hx' hy'

private theorem nodup_of_map_id_nodup {boxes : List ModelBox}
    (h : (boxes.map (·.id)).Nodup) : boxes.Nodup := by
  induction boxes with
  | nil => exact List.nodup_nil
  | cons box rest ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun hm => h.1 (List.mem_map_of_mem hm), ih h.2⟩


/-! ### The conditional parent invariant -/

/-- `FrameParents` with the parent lookup required only when the parent string
is realized by a group box of `sources`.  Clause C3 only asks for containment
when `box? parent` returns a box, so this is the invariant the scene needs. -/
def FrameParentsD (sources : List ModelBox) (g : Family) : Prop :=
  ∀ f ∈ g.frames, ∀ b ∈ sources, b.role ≠ .group →
    f.id = b.id → b.parent ≠ "" →
    (∃ p ∈ sources, p.role = .group ∧ p.id = b.parent) →
    (g.lanes[f.lane]?).map (·.id) = some b.parent

/-- Appending lanes keeps the conditional invariant. -/
theorem frameParentsD_append_lanes {sources : List ModelBox} {g : Family}
    (h : FrameParentsD sources g) (suffix : List Lanes.Eventmodeling.Lane) :
    FrameParentsD sources { g with lanes := g.lanes ++ suffix } := by
  intro f hf b hb hrole hid hparent hex
  exact lane_append_frame_parent g.lanes suffix f b.parent
    (h f hf b hb hrole hid hparent hex)

/-- Relations do not touch lanes or frames. -/
theorem frameParentsD_relations {sources : List ModelBox} {g : Family}
    (h : FrameParentsD sources g) (relations : List Lanes.Eventmodeling.Relation) :
    FrameParentsD sources { g with relations := relations } := by
  intro f hf b hb hrole hid hparent hex
  exact h f hf b hb hrole hid hparent hex

/-- Captions change `lane.caption`, not `lane.id`. -/
theorem frameParentsD_caption {sources : List ModelBox} {g : Family}
    (h : FrameParentsD sources g) (i : Nat) (lane : Lanes.Eventmodeling.Lane)
    (caption : Lanes.Caption) (hi : g.lanes[i]? = some lane) :
    FrameParentsD sources
      { g with lanes := g.lanes.set i { lane with caption := some caption } } := by
  intro f hf b hb hrole hid hparent hex
  exact lane_caption_update_frame_parent g.lanes i lane caption f b.parent hi
    (h f hf b hb hrole hid hparent hex)

theorem frameParentsD_empty (sources : List ModelBox) :
    FrameParentsD sources { lanes := [], frames := [], relations := [] } := by
  intro f hf
  simp at hf

theorem frameParentsD_append_frame {sources : List ModelBox} {g : Family}
    (h : FrameParentsD sources g) (frame : Lanes.Eventmodeling.Frame)
    (hframe : ∀ b ∈ sources, b.role ≠ .group →
      frame.id = b.id → b.parent ≠ "" →
      (∃ p ∈ sources, p.role = .group ∧ p.id = b.parent) →
      (g.lanes[frame.lane]?).map (·.id) = some b.parent) :
    FrameParentsD sources { g with frames := g.frames ++ [frame] } := by
  intro f hf b hb hrole hid hparent hex
  rcases List.mem_append.mp hf with hf | hf
  · exact h f hf b hb hrole hid hparent hex
  · have he : f = frame := by simpa only [List.mem_singleton] using hf
    subst f
    exact hframe b hb hrole hid hparent hex

def DecodePrefix (sources processed : List ModelBox)
    (state : Family × List String) : Prop :=
  FrameParentsD sources state.1 ∧
    ∀ frame ∈ state.1.frames, ∃ b ∈ processed, b.role ≠ .group ∧ frame.id = b.id

theorem decodePrefix_empty (sources : List ModelBox) :
    DecodePrefix sources []
      (({ lanes := [], frames := [], relations := [] } : Family), []) := by
  refine ⟨frameParentsD_empty sources, ?_⟩
  intro frame hf
  simp at hf

theorem decodePrefix_group {sources processed : List ModelBox}
    {state : Family × List String} (h : DecodePrefix sources processed state)
    (b : ModelBox) :
    DecodePrefix sources (processed ++ [b])
      ({ state.1 with lanes := state.1.lanes ++
        [{ id := b.id, index := laneIndex b.shape, caption := none }] },
        state.2 ++ [b.id]) := by
  refine ⟨frameParentsD_append_lanes h.1 _, ?_⟩
  intro frame hf
  obtain ⟨source, hs, hrole, hid⟩ := h.2 frame hf
  exact ⟨source, List.mem_append.mpr (Or.inl hs), hrole, hid⟩

theorem decodePrefix_frame {sources processed : List ModelBox}
    {state : Family × List String}
    (hunique : (sources.map (·.id)).Nodup)
    (h : DecodePrefix sources processed state)
    {b : ModelBox} (hb : b ∈ sources) (hrole : b.role ≠ .group)
    (frame : Lanes.Eventmodeling.Frame) (hid : frame.id = b.id)
    (hlane : b.parent ≠ "" →
      (∃ p ∈ sources, p.role = .group ∧ p.id = b.parent) →
      (state.1.lanes[frame.lane]?).map (·.id) = some b.parent) :
    DecodePrefix sources (processed ++ [b])
      ({ state.1 with frames := state.1.frames ++ [frame] }, state.2) := by
  refine ⟨frameParentsD_append_frame h.1 frame ?_, ?_⟩
  · intro source hs _ he hparent hex
    have hsame : b = source :=
      mem_id_unique hunique hb hs (hid.symm.trans he)
    subst source
    exact hlane hparent hex
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨source, hs, hr, he⟩ := h.2 f hf
      exact ⟨source, List.mem_append.mpr (Or.inl hs), hr, he⟩
    · have he : f = frame := by simpa only [List.mem_singleton] using hf
      subst f
      exact ⟨b, List.mem_append.mpr (Or.inr (by simp)), hrole, hid⟩

theorem decodePrefix_fallback {sources processed : List ModelBox}
    {state : Family × List String} (h : DecodePrefix sources processed state)
    (parent : String) :
    DecodePrefix sources processed
      ({ state.1 with lanes := state.1.lanes ++
        [{ id := "", index := state.2.length, caption := none }] },
        state.2 ++ [parent]) := by
  exact ⟨frameParentsD_append_lanes h.1 _, h.2⟩

private theorem findIdx_none_not_mem (ids : List String) (parent : String)
    (h : ids.findIdx? (· == parent) = none) : parent ∉ ids := by
  induction ids with
  | nil => simp
  | cons first rest ih =>
    rw [List.findIdx?_cons] at h
    by_cases he : first = parent
    · simp [he] at h
    · have hrest : rest.findIdx? (· == parent) = none := by
        cases hr : rest.findIdx? (· == parent) with
        | none => rfl
        | some i => simp [he, hr] at h
      simp only [List.mem_cons]
      intro hm
      rcases hm with hm | hm
      · exact he hm.symm
      · exact ih hrest hm

theorem decodePrefix_fallback_frame {sources processed : List ModelBox}
    {state : Family × List String}
    (hunique : (sources.map (·.id)).Nodup)
    (h : DecodePrefix sources processed state)
    {b : ModelBox} (hb : b ∈ sources) (hrole : b.role ≠ .group)
    (hparents : ∀ p ∈ sources, p.role = .group → p.id = b.parent → p ∈ processed)
    (hgroups : ∀ p ∈ processed, p.role = .group → p.id ∈ state.2)
    (hmiss : state.2.findIdx? (· == b.parent) = none)
    (frame : Lanes.Eventmodeling.Frame) (hid : frame.id = b.id) :
    DecodePrefix sources (processed ++ [b])
      ({ state.1 with
          lanes := state.1.lanes ++
            [{ id := "", index := state.2.length, caption := none }]
          frames := state.1.frames ++ [frame] },
        state.2 ++ [b.parent]) := by
  have hmissing : b.parent ∉ state.2 :=
    findIdx_none_not_mem state.2 b.parent hmiss
  have hnoGroup : ¬ ∃ p ∈ sources, p.role = .group ∧ p.id = b.parent := by
    rintro ⟨p, hp, hr, he⟩
    have hm := hgroups p (hparents p hp hr he) hr
    rw [he] at hm
    exact hmissing hm
  exact decodePrefix_frame hunique (decodePrefix_fallback h b.parent)
    hb hrole frame hid (fun _ hex => False.elim (hnoGroup hex))

def ProcessedGroups (processed : List ModelBox) (ids : List String) : Prop :=
  ∀ b ∈ processed, b.role = .group → b.id ∈ ids

theorem processedGroups_empty : ProcessedGroups [] [] := by
  intro b hb
  simp at hb

theorem processedGroups_group {processed : List ModelBox} {ids : List String}
    (h : ProcessedGroups processed ids) (b : ModelBox) :
    ProcessedGroups (processed ++ [b]) (ids ++ [b.id]) := by
  intro p hp hr
  rcases List.mem_append.mp hp with hp | hp
  · exact List.mem_append.mpr (Or.inl (h p hp hr))
  · have he : p = b := by simpa only [List.mem_singleton] using hp
    subst p
    simp

theorem processedGroups_frame {processed : List ModelBox} {ids : List String}
    (h : ProcessedGroups processed ids) {b : ModelBox} (hr : b.role ≠ .group) :
    ProcessedGroups (processed ++ [b]) ids := by
  intro p hp hrole
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp hrole
  · have he : p = b := by simpa only [List.mem_singleton] using hp
    subst p
    exact False.elim (hr hrole)

theorem processedGroups_append_ids {processed : List ModelBox} {ids : List String}
    (h : ProcessedGroups processed ids) (suffix : List String) :
    ProcessedGroups processed (ids ++ suffix) := by
  intro p hp hr
  exact List.mem_append.mpr (Or.inl (h p hp hr))


theorem decode_first_loop_processed_groups (m : Model)
    (output : Family × List String)
    (h : ForIn.forIn (m := Except LayoutError) m.boxes
      (({ lanes := [], frames := [], relations := [] } : Family), ([] : List String))
      (fun b state => do
        let mut g := state.1
        let mut ids := state.2
        if b.role == .group then
          ids := ids ++ [b.id]
          g := { g with lanes := g.lanes ++
            [{ id := b.id, index := laneIndex b.shape, caption := none }] }
        else
          let lane ← match ids.findIdx? (· == b.parent) with
            | some i => pure i
            | none => do
              let i := ids.length
              ids := ids ++ [b.parent]
              g := { g with lanes := g.lanes ++
                [{ id := "", index := i, caption := none }] }
              pure i
          let parts := (boxText m b).splitOn "\n\n"
          let name ← measureCaption m.profile .label
            (Lanes.EventConsts.load m.profile).boxMaxWidth (parts.headD "")
          let data ← if parts.length ≤ 1 then pure none else do
            let text := (String.intercalate "\n\n" parts.tail).replace "\n" "<br>"
            pure (some (← measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth text))
          g := { g with frames := g.frames ++
            [{ id := b.id, lane, category := b.shape, name, data }] }
        pure (.yield (g, ids))) = .ok output) :
    ProcessedGroups m.boxes output.2 := by
  apply forIn_processed [] m.boxes _ output _
    (fun done state => ProcessedGroups done state.2)
    processedGroups_empty _ h
  intro done b rest state next _ hp hs
  by_cases hr : b.role = .group
  · have he : ForInStep.yield
        ({ state.1 with lanes := state.1.lanes ++
          [{ id := b.id, index := laneIndex b.shape, caption := none }] },
          state.2 ++ [b.id]) = next := by
      simpa [hr, Bind.bind, Except.bind, pure, Except.pure] using hs
    exact ⟨_, he.symm, processedGroups_group hp b⟩
  · cases hi : state.2.findIdx? (· == b.parent) with
    | none =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e =>
        simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, processedGroups_frame
            (processedGroups_append_ids hp [b.parent]) hr⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e =>
            simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, processedGroups_frame
              (processedGroups_append_ids hp [b.parent]) hr⟩
    | some i =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e =>
        simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, processedGroups_frame hp hr⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e =>
            simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, processedGroups_frame hp hr⟩

theorem decode_processed_parent_coverage {m : Model} {g : Family}
    (hdecode : decode m = .ok g)
    {processed remaining : List ModelBox} {b parent : ModelBox}
    (hsplit : m.boxes = processed ++ b :: remaining)
    (hindexed : (b, processed.length) ∈ m.boxes.zipIdx)
    (hrole : b.role ≠ .group)
    (hp : parent ∈ m.boxes) (hgroup : parent.role = .group)
    (hid : parent.id = b.parent) :
    parent ∈ processed := by
  have hnotlater := decode_parent_not_later (parent := parent) hdecode hindexed hrole
  rw [hsplit] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hp
  · rcases List.mem_cons.mp hp with he | hp
    · subst parent
      exact False.elim (hrole hgroup)
    · have hdrop : parent ∈ m.boxes.drop (processed.length + 1) := by
        simpa [hsplit, List.drop_append] using
          (Or.inr hp : parent ∈ processed.drop (processed.length + 1) ∨ parent ∈ remaining)
      exact False.elim (hnotlater hdrop hgroup hid)

theorem decode_processed_parent_ids {m : Model} {g : Family}
    (hdecode : decode m = .ok g)
    {processed remaining : List ModelBox} {b : ModelBox}
    {ids : List String}
    (hsplit : m.boxes = processed ++ b :: remaining)
    (hindexed : (b, processed.length) ∈ m.boxes.zipIdx)
    (hrole : b.role ≠ .group)
    (hgroups : ProcessedGroups processed ids)
    (hparent : ∃ parent ∈ m.boxes,
      parent.role = .group ∧ parent.id = b.parent) :
    b.parent ∈ ids := by
  obtain ⟨parent, hp, hgroup, hid⟩ := hparent
  have hprocessed := decode_processed_parent_coverage hdecode hsplit
    hindexed hrole hp hgroup hid
  rw [← hid]
  exact hgroups parent hprocessed hgroup

theorem frameParentsD_parent_index {sources : List ModelBox} {g : Family}
    (hparents : FrameParentsD sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup)
    {b : ModelBox} (hb : b ∈ sources) (hrole : b.role ≠ .group)
    (hparent : b.parent ≠ "")
    (hex : ∃ parent ∈ sources, parent.role = .group ∧ parent.id = b.parent)
    {f : Lanes.Eventmodeling.Frame}
    (hf : f ∈ g.frames) (hid : f.id = b.id) :
    g.lanes.findIdx? (·.id == b.parent) = some f.lane := by
  have hp := hparents f hf b hb hrole hid hparent hex
  cases hlane : g.lanes[f.lane]? with
  | none => simp only [hlane, Option.map_none, reduceCtorEq] at hp
  | some lane =>
    have he : lane.id = b.parent := by
      simpa only [hlane, Option.map_some, Option.some.injEq] using hp
    rw [← he]
    exact lane_findIdx_of_get_nonempty hids hlane (he.symm ▸ hparent)

theorem placeBox_parent_containment_of_frameParentsD
    {sources : List ModelBox} {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result}
    (hparents : FrameParentsD sources g)
    (hids : ((g.lanes.map (·.id)).filter (· != "")).Nodup)
    (hr : Lanes.Eventmodeling.layout g profile = .ok r)
    {b parent : ModelBox} {out parentOut : Box}
    (hb : b ∈ sources) (hpmem : parent ∈ sources)
    (hrole : b.role ≠ .group) (hparent : b.parent ≠ "")
    (hid : parent.id = b.parent) (hgroup : parent.role = .group)
    (hp : placeBox g r b = .ok out) (hpp : placeBox g r parent = .ok parentOut) :
    parentOut.rect.Contained out.rect := by
  apply placeBox_parent_lane_containment hr hrole hp hgroup hpp
  intro i f hi hf
  obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
  have he : g.frames[i] = f := by
    have hget : g.frames[i]? = some g.frames[i] := List.getElem?_eq_getElem hib
    exact Option.some.inj (hget.symm.trans hf)
  have hfid : f.id = b.id := by
    rw [he] at hmatch
    exact beq_iff_eq.mp hmatch
  rw [hid]
  exact frameParentsD_parent_index hparents hids hb hrole hparent
    ⟨parent, hpmem, hgroup, hid⟩ (List.mem_of_getElem? hf) hfid

theorem scene_c3_of_decode_parent_witnesses {m : Model} {s : Scene}
    (h : scene m = .ok s)
    (hdecode : ∀ g, decode m = .ok g →
      FrameParentsD m.boxes g ∧
        ((g.lanes.map (·.id)).filter (· != "")).Nodup) :
    Validator.C3 s.layoutDump := by
  obtain ⟨g, r, hg, hr, _⟩ := scene_boxes_correspond h
  obtain ⟨hparents, hids⟩ := hdecode g hg
  intro out hout hnonempty parent hlookup
  have houtmem : out ∈ s.boxes := hout
  have hfind : s.boxes.find? (fun b => b.id == out.parent) = some parent := hlookup
  have hparentmem := List.mem_of_find?_eq_some hfind
  have hparentid : parent.id = out.parent := by
    simpa only [beq_iff_eq] using List.find?_some hfind
  obtain ⟨g', r', b, hg', hr', hb, hp⟩ := scene_output_origin h houtmem
  have heg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have her : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨g', r', p, hg', hr', hpmem, hpp⟩ :=
    scene_output_origin h hparentmem
  have heg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have her : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  obtain ⟨_, hbparent, _, _⟩ := placeBox_metadata hp
  obtain ⟨hpid, _, hprole, _⟩ := placeBox_metadata hpp
  have hrole : b.role ≠ .group := by
    intro he
    exact hnonempty (hbparent.trans (decode_group_parent hg hb he))
  have hnoderole : out.role = "node" := by
    have hm := (placeBox_metadata hp).2.2.1
    cases he : b.role with
    | node => simpa only [he, BoxRole.id] using hm
    | group => exact False.elim (hrole he)
  have hpgroup : p.role = .group := by
    have hs := scene_node_parent_is_group h houtmem hparentmem hnoderole hparentid
    cases he : p.role with
    | group => rfl
    | node => simp [he, BoxRole.id, hs] at hprole
  exact placeBox_parent_containment_of_frameParentsD hparents hids hr hb hpmem hrole
    (fun he => hnonempty (hbparent.trans he))
    (hpid.symm.trans (hparentid.trans hbparent)) hpgroup hp hpp

inductive LaneIdentity (sources : List ModelBox) :
    List String → List Lanes.Eventmodeling.Lane → Prop where
  | nil : LaneIdentity sources [] []
  | cons {id : String} {lane : Lanes.Eventmodeling.Lane}
      {ids : List String} {lanes : List Lanes.Eventmodeling.Lane}
      (head : ∀ p ∈ sources, p.role = .group → p.id = id → lane.id = id)
      (tail : LaneIdentity sources ids lanes) :
      LaneIdentity sources (id :: ids) (lane :: lanes)

theorem LaneIdentity.append {sources : List ModelBox}
    {ids moreIds : List String} {lanes moreLanes : List Lanes.Eventmodeling.Lane}
    (h : LaneIdentity sources ids lanes)
    (hmore : LaneIdentity sources moreIds moreLanes) :
    LaneIdentity sources (ids ++ moreIds) (lanes ++ moreLanes) := by
  induction h with
  | nil => exact hmore
  | cons hhead _ ih => exact .cons hhead ih

structure CompleteDecodePrefix (sources processed : List ModelBox)
    (state : Family × List String) : Prop where
  decodedPrefix : DecodePrefix sources processed state
  groups : ProcessedGroups processed state.2
  identity : LaneIdentity sources state.2 state.1.lanes
  origin : ∀ lane ∈ state.1.lanes, lane.id ≠ "" →
    ∃ p ∈ processed, p.role = .group ∧ p.id = lane.id
  unique : ((state.1.lanes.map (·.id)).filter (· != "")).Nodup
  relationsEmpty : state.1.relations = []

theorem laneIdentity_lookup {sources : List ModelBox} {ids : List String}
    {lanes : List Lanes.Eventmodeling.Lane}
    (h : LaneIdentity sources ids lanes) {i : Nat} {id : String}
    (hi : ids[i]? = some id)
    (hp : ∃ p ∈ sources, p.role = .group ∧ p.id = id) :
    (lanes[i]?).map (·.id) = some id := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons key lane keys lanes hhead htail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst key
      obtain ⟨p, hp, hr, he⟩ := hp
      simp only [List.getElem?_cons_zero, Option.map_some,
        hhead p hp hr he]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi ⊢
      exact ih hi

theorem completeDecodePrefix_empty (sources : List ModelBox) :
    CompleteDecodePrefix sources []
      (({ lanes := [], frames := [], relations := [] } : Family), []) := by
  refine ⟨decodePrefix_empty sources, processedGroups_empty, .nil, ?_, ?_, rfl⟩
  · intro lane hl
    simp at hl
  · simp

theorem completeDecodePrefix_frame {sources processed : List ModelBox}
    {state : Family × List String}
    (hunique : (sources.map (·.id)).Nodup)
    (h : CompleteDecodePrefix sources processed state)
    {b : ModelBox} (hb : b ∈ sources) (hr : b.role ≠ .group)
    {i : Nat} (hi : state.2.findIdx? (· == b.parent) = some i)
    (name : Lanes.Caption) (data : Option Lanes.Caption) :
    CompleteDecodePrefix sources (processed ++ [b])
      ({ state.1 with frames := state.1.frames ++
        [{ id := b.id, lane := i, category := b.shape, name, data }] }, state.2) := by
  refine ⟨decodePrefix_frame hunique h.decodedPrefix hb hr _ rfl ?_,
    processedGroups_frame h.groups hr, h.identity, ?_, h.unique, h.relationsEmpty⟩
  · intro _ hp
    obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
    have he : state.2[i] = b.parent := beq_iff_eq.mp hmatch
    apply laneIdentity_lookup h.identity
    · simpa only [he] using List.getElem?_eq_getElem hib
    · exact hp
  · intro lane hl hn
    obtain ⟨p, hp, hgroup, hid⟩ := h.origin lane hl hn
    exact ⟨p, List.mem_append.mpr (Or.inl hp), hgroup, hid⟩

theorem completeDecodePrefix_group {sources processed : List ModelBox}
    {state : Family × List String}
    (h : CompleteDecodePrefix sources processed state) (b : ModelBox)
    (hgroup : b.role = .group)
    (hfresh : b.id ∉ processed.map (·.id)) :
    CompleteDecodePrefix sources (processed ++ [b])
      ({ state.1 with lanes := state.1.lanes ++
        [{ id := b.id, index := laneIndex b.shape, caption := none }] },
        state.2 ++ [b.id]) := by
  refine ⟨decodePrefix_group h.decodedPrefix b, processedGroups_group h.groups b,
    h.identity.append (.cons (by intros; rfl) .nil), ?_, ?_, h.relationsEmpty⟩
  · intro lane hl hn
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨p, hp, hr, he⟩ := h.origin lane hl hn
      exact ⟨p, List.mem_append.mpr (Or.inl hp), hr, he⟩
    · have he : lane =
          { id := b.id, index := laneIndex b.shape, caption := none } := by
        simpa only [List.mem_singleton] using hl
      subst lane
      exact ⟨b, by simp, hgroup, rfl⟩
  · by_cases hempty : b.id = ""
    · simpa [List.map_append, List.filter_append, hempty] using h.unique
    · have hnot : b.id ∉ (state.1.lanes.map (·.id)).filter (· != "") := by
        intro hm
        obtain ⟨lane, hl, he⟩ := List.mem_map.mp (List.mem_filter.mp hm).1
        have hn : lane.id ≠ "" := he.symm ▸ hempty
        obtain ⟨p, hp, _, hid⟩ := h.origin lane hl hn
        exact hfresh (List.mem_map.mpr ⟨p, hp, hid.trans he⟩)
      simpa [List.map_append, List.filter_append, hempty] using
        (List.nodup_append.mpr ⟨h.unique, by simp, by
          intro id hi other ho he
          have ho' : other = b.id := by simpa using ho
          exact hnot ((he.trans ho') ▸ hi)⟩)

theorem completeDecodePrefix_fallback_frame {sources processed : List ModelBox}
    {state : Family × List String}
    (hunique : (sources.map (·.id)).Nodup)
    (h : CompleteDecodePrefix sources processed state)
    {b : ModelBox} (hb : b ∈ sources) (hr : b.role ≠ .group)
    (hparents : ∀ p ∈ sources, p.role = .group → p.id = b.parent → p ∈ processed)
    (hmiss : state.2.findIdx? (· == b.parent) = none)
    (name : Lanes.Caption) (data : Option Lanes.Caption) :
    CompleteDecodePrefix sources (processed ++ [b])
      ({ state.1 with
        lanes := state.1.lanes ++
          [{ id := "", index := state.2.length, caption := none }]
        frames := state.1.frames ++
          [{ id := b.id, lane := state.2.length, category := b.shape, name, data }] },
        state.2 ++ [b.parent]) := by
  have hno : ¬ ∃ p ∈ sources, p.role = .group ∧ p.id = b.parent := by
    rintro ⟨p, hp, hgroup, hid⟩
    have hm := h.groups p (hparents p hp hgroup hid) hgroup
    rw [hid] at hm
    exact findIdx_none_not_mem state.2 b.parent hmiss hm
  refine ⟨decodePrefix_fallback_frame hunique h.decodedPrefix hb hr hparents h.groups
      hmiss _ rfl,
    processedGroups_frame (processedGroups_append_ids h.groups [b.parent]) hr,
    h.identity.append (.cons ?_ .nil), ?_,
    nonempty_lane_ids_append_fallback state.1 state.2.length h.unique, h.relationsEmpty⟩
  · intro p hp hgroup hid
    exact False.elim (hno ⟨p, hp, hgroup, hid⟩)
  · intro lane hl hn
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨p, hp, hgroup, hid⟩ := h.origin lane hl hn
      exact ⟨p, List.mem_append.mpr (Or.inl hp), hgroup, hid⟩
    · have he : lane =
          { id := "", index := state.2.length, caption := none } := by
        simpa only [List.mem_singleton] using hl
      exact False.elim (hn (congrArg Lanes.Eventmodeling.Lane.id he))

theorem decode_first_loop_complete (m : Model) (hwf : WellFormed m)
    (decoded : Family) (hdecode : decode m = .ok decoded)
    (output : Family × List String)
    (h : ForIn.forIn (m := Except LayoutError) m.boxes
      (({ lanes := [], frames := [], relations := [] } : Family), ([] : List String))
      (fun b state => do
        let mut g := state.1
        let mut ids := state.2
        if b.role == .group then
          ids := ids ++ [b.id]
          g := { g with lanes := g.lanes ++
            [{ id := b.id, index := laneIndex b.shape, caption := none }] }
        else
          let lane ← match ids.findIdx? (· == b.parent) with
            | some i => pure i
            | none => do
              let i := ids.length
              ids := ids ++ [b.parent]
              g := { g with lanes := g.lanes ++
                [{ id := "", index := i, caption := none }] }
              pure i
          let parts := (boxText m b).splitOn "\n\n"
          let name ← measureCaption m.profile .label
            (Lanes.EventConsts.load m.profile).boxMaxWidth (parts.headD "")
          let data ← if parts.length ≤ 1 then pure none else do
            let text := (String.intercalate "\n\n" parts.tail).replace "\n" "<br>"
            pure (some (← measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth text))
          g := { g with frames := g.frames ++
            [{ id := b.id, lane, category := b.shape, name, data }] }
        pure (.yield (g, ids))) = .ok output) :
    CompleteDecodePrefix m.boxes m.boxes output := by
  have hunique := Model.boxIds_nodup hwf
  apply forIn_processed [] m.boxes _ output _
    (CompleteDecodePrefix m.boxes) (completeDecodePrefix_empty m.boxes) _ h
  intro done b rest state next hsplit hp hs
  have hsplit' : m.boxes = done ++ b :: rest := by simpa using hsplit
  have hb : b ∈ m.boxes := by rw [hsplit']; simp
  have hindexed : (b, done.length) ∈ m.boxes.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp [hsplit']
  have hfresh : b.id ∉ done.map (·.id) := by
    have hn : ((done.map (·.id)) ++ b.id :: rest.map (·.id)).Nodup := by
      simpa [hsplit'] using hunique
    have hd := (List.nodup_append.mp hn).2.2
    intro hm
    exact hd b.id hm b.id (by simp) rfl
  by_cases hr : b.role = .group
  · have he : ForInStep.yield
        ({ state.1 with lanes := state.1.lanes ++
          [{ id := b.id, index := laneIndex b.shape, caption := none }] },
          state.2 ++ [b.id]) = next := by
      simpa [hr, Bind.bind, Except.bind, pure, Except.pure] using hs
    exact ⟨_, he.symm, completeDecodePrefix_group hp b hr hfresh⟩
  · have hparents : ∀ p ∈ m.boxes, p.role = .group →
        p.id = b.parent → p ∈ done := by
      intro p hpm hpg hpid
      exact decode_processed_parent_coverage hdecode hsplit' hindexed hr hpm hpg hpid
    cases hi : state.2.findIdx? (· == b.parent) with
    | none =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e => simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, completeDecodePrefix_fallback_frame hunique hp hb hr
            hparents hi name none⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e => simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, completeDecodePrefix_fallback_frame hunique hp hb hr
              hparents hi name (some data)⟩
    | some i =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e => simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, completeDecodePrefix_frame hunique hp hb hr hi name none⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e => simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, completeDecodePrefix_frame hunique hp hb hr hi name (some data)⟩

theorem laneIdentity_lengths {sources : List ModelBox} {ids : List String}
    {lanes : List Lanes.Eventmodeling.Lane}
    (h : LaneIdentity sources ids lanes) : ids.length = lanes.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem decode_route_loop_parent_witnesses {sources : List ModelBox}
    (routes : List ModelRoute) (initial output : Family)
    (hparents : FrameParentsD sources initial)
    (hids : ((initial.lanes.map (·.id)).filter (· != "")).Nodup)
    (h : ForIn.forIn (m := Except LayoutError) routes initial (fun route state => do
      let some src := state.frames.findIdx? (·.id == route.fromId) | throw .domain
      let some dst := state.frames.findIdx? (·.id == route.toId) | throw .domain
      pure (.yield { state with relations := state.relations ++ [{ id := route.id, src, dst }] }))
        = .ok output) :
    FrameParentsD sources output ∧
      ((output.lanes.map (·.id)).filter (· != "")).Nodup := by
  apply forIn_processed [] routes initial output _
    (fun _ state => FrameParentsD sources state ∧
      ((state.lanes.map (·.id)).filter (· != "")).Nodup)
    ⟨hparents, hids⟩ _ h
  intro _ route _ state next _ hp hs
  cases hsrc : state.frames.findIdx? (·.id == route.fromId) with
  | none => simp [hsrc, throw, throwThe, MonadExceptOf.throw] at hs
  | some src =>
    cases hdst : state.frames.findIdx? (·.id == route.toId) with
    | none => simp [hsrc, hdst, throw, throwThe, MonadExceptOf.throw] at hs
    | some dst =>
      have he : ForInStep.yield
          { state with relations := state.relations ++ [{ id := route.id, src, dst }] }
            = next := by
        simpa [hsrc, hdst, Bind.bind, Except.bind, pure, Except.pure] using hs
      exact ⟨_, he.symm, frameParentsD_relations hp.1 _, hp.2⟩

theorem decode_label_loop_parent_witnesses {sources : List ModelBox}
    (m : Model) (ids : List String) (labels : List ModelLabel)
    (initial output : Family) (hparents : FrameParentsD sources initial)
    (hids : ((initial.lanes.map (·.id)).filter (· != "")).Nodup)
    (h : ForIn.forIn (m := Except LayoutError) labels initial (fun label state => do
      let some i := ids.findIdx? (· == label.owner) | throw .domain
      let some lane := state.lanes[i]? | throw .domain
      let c := Lanes.EventConsts.load m.profile
      let caption ← measureCaption m.profile .label
        (c.contentStartX - 4 * c.lanePadding) label.text
      pure (.yield { state with lanes := state.lanes.set i { lane with caption := some caption } }))
        = .ok output) :
    FrameParentsD sources output ∧
      ((output.lanes.map (·.id)).filter (· != "")).Nodup := by
  apply forIn_processed [] labels initial output _
    (fun _ state => FrameParentsD sources state ∧
      ((state.lanes.map (·.id)).filter (· != "")).Nodup)
    ⟨hparents, hids⟩ _ h
  intro _ label _ state next _ hp hs
  cases hi : ids.findIdx? (· == label.owner) with
  | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at hs
  | some i =>
    cases hlane : state.lanes[i]? with
    | none => simp [hi, hlane, throw, throwThe, MonadExceptOf.throw] at hs
    | some lane =>
      cases hcap : measureCaption m.profile .label
          ((Lanes.EventConsts.load m.profile).contentStartX -
            4 * (Lanes.EventConsts.load m.profile).lanePadding) label.text with
      | error e => simp [hi, hlane, hcap, Bind.bind, Except.bind] at hs
      | ok caption =>
        have he : ForInStep.yield
            { state with lanes := state.lanes.set i { lane with caption := some caption } }
              = next := by
          simpa [hi, hlane, hcap, Bind.bind, Except.bind, pure, Except.pure] using hs
        refine ⟨_, he.symm, frameParentsD_caption hp.1 i lane caption hlane, ?_⟩
        change (((state.lanes.set i { lane with caption := some caption }).map (·.id)).filter
          (· != "")).Nodup
        rw [lane_caption_update_ids state.lanes i lane caption hlane]
        exact hp.2

theorem decode_parent_witnesses {m : Model} {g : Family}
    (hwf : WellFormed m) (hdecode : decode m = .ok g) :
    FrameParentsD m.boxes g ∧
      ((g.lanes.map (·.id)).filter (· != "")).Nodup := by
  have hc := decode_parentsConsistent hdecode
  have ho := decode_parentDeclarationOrder hdecode
  have h := hdecode
  unfold decode at h
  simp only [hc, ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨first, hfirst, h⟩ := bind_ok h
  have hp := decode_first_loop_complete m hwf g hdecode first hfirst
  obtain ⟨related, hrelated, h⟩ := bind_ok h
  have hrel := decode_route_loop_parent_witnesses m.routes first.1 related
    hp.decodedPrefix.1 hp.unique hrelated
  obtain ⟨captioned, hcaptioned, h⟩ := bind_ok h
  have hcap := decode_label_loop_parent_witnesses m first.2 m.labels related captioned
    hrel.1 hrel.2 hcaptioned
  have he : captioned = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using h
  subst captioned
  exact hcap

theorem eventmodeling_c3 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C3 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c3_of_decode_parent_witnesses hs
    (fun _ hg => decode_parent_witnesses hwf hg)

theorem tidyPush_head (stack : List Point) (p : Point) :
    (Lanes.Eventmodeling.tidyPush stack p).head? = some p := by
  induction stack with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      by_cases he : a = p
      · simp [Lanes.Eventmodeling.tidyPush, he]
      · simp [Lanes.Eventmodeling.tidyPush, he]
    | cons b tail =>
      by_cases he : a = p
      · simp [Lanes.Eventmodeling.tidyPush, he]
      · simp only [Lanes.Eventmodeling.tidyPush, show (a == p) = false from by
          simpa using he, Bool.false_eq_true, ↓reduceIte]
        split
        · exact ih
        · rfl

theorem tidyPush_last (stack : List Point) (p : Point) :
    (Lanes.Eventmodeling.tidyPush stack p).getLast? =
      some (stack.getLast?.getD p) := by
  induction stack with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      by_cases he : a = p
      · simp [Lanes.Eventmodeling.tidyPush, he]
      · simp [Lanes.Eventmodeling.tidyPush, he]
    | cons b tail =>
      by_cases he : a = p
      · simp [Lanes.Eventmodeling.tidyPush, he, List.getLast?_cons]
      · simp only [Lanes.Eventmodeling.tidyPush, show (a == p) = false from by
          simpa using he, Bool.false_eq_true, ↓reduceIte]
        split
        · simpa only [List.getLast?_cons_cons] using ih
        · simp only [List.getLast?_cons, Option.getD_some]

theorem tidy_fold_last (points stack : List Point) (first : Point)
    (hfirst : stack.getLast? = some first) :
    (points.foldl Lanes.Eventmodeling.tidyPush stack).getLast? = some first := by
  induction points generalizing stack with
  | nil => exact hfirst
  | cons p rest ih =>
    apply ih
    rw [tidyPush_last, hfirst]
    rfl

theorem tidy_fold_head (points : List Point) (p : Point) (stack : List Point) :
    (points.foldl Lanes.Eventmodeling.tidyPush
      (Lanes.Eventmodeling.tidyPush stack p)).head? =
      (p :: points).getLast? := by
  induction points generalizing p stack with
  | nil => exact tidyPush_head stack p
  | cons q rest ih =>
    simpa only [List.foldl_cons, List.getLast?_cons_cons] using
      ih q (Lanes.Eventmodeling.tidyPush stack p)

theorem tidy_endpoints (first : Point) (rest : List Point) :
    (Lanes.Eventmodeling.tidy (first :: rest)).head? = some first ∧
      (Lanes.Eventmodeling.tidy (first :: rest)).getLast? =
        (first :: rest).getLast? := by
  constructor
  · change (rest.foldl Lanes.Eventmodeling.tidyPush [first]).reverse.head? = some first
    rw [List.head?_reverse]
    exact tidy_fold_last rest [first] first rfl
  · change (rest.foldl Lanes.Eventmodeling.tidyPush
      (Lanes.Eventmodeling.tidyPush [] first)).reverse.getLast? = _
    rw [List.getLast?_reverse]
    exact tidy_fold_head rest first []

theorem eventmodeling_start_boundary (src : Rect) (below : Prop) [Decidable below]
    (hw : 0 ≤ src.w) (hh : 0 ≤ src.h) :
    Validator.onBoundary
      ⟨src.x + Int.fdiv (2 * src.w) 3, if below then src.y + src.h else src.y⟩
      src := by
  unfold Validator.onBoundary
  dsimp only
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  split <;> omega

theorem eventmodeling_finish_boundary (dst : Rect) (below : Prop) [Decidable below]
    (hw : 0 ≤ dst.w) (hh : 0 ≤ dst.h) :
    Validator.onBoundary
      ⟨dst.x + Int.fdiv dst.w 3, if below then dst.y + dst.h else dst.y⟩
      dst := by
  unfold Validator.onBoundary
  dsimp only
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  split <;> omega

theorem family_route_endpoints (g : Family) (profile : Profile)
    (plan : Lanes.Eventmodeling.Plan) (relation : Lanes.Eventmodeling.Relation)
    (points : List Point)
    (h : Lanes.Eventmodeling.route g profile plan relation = .ok points) :
    let src := plan.frames.getD relation.src Lanes.zeroRect
    let dst := plan.frames.getD relation.dst Lanes.zeroRect
    let a := Lanes.Eventmodeling.rank g
      (((g.frames[relation.src]?).map (·.lane)).getD 0)
    let b := Lanes.Eventmodeling.rank g
      (((g.frames[relation.dst]?).map (·.lane)).getD 0)
    points.head? = some
        ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩ ∧
      points.getLast? = some
        ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩ := by
  let src := plan.frames.getD relation.src Lanes.zeroRect
  let dst := plan.frames.getD relation.dst Lanes.zeroRect
  let a := Lanes.Eventmodeling.rank g
    (((g.frames[relation.src]?).map (·.lane)).getD 0)
  let b := Lanes.Eventmodeling.rank g
    (((g.frames[relation.dst]?).map (·.lane)).getD 0)
  let start : Point :=
    ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩
  let finish : Point :=
    ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩
  let ca := plan.corridors.getD (if a < b then a + 1 else a) 0
  let cb := plan.corridors.getD (if b < a then b + 1 else b) 0
  change points.head? = some start ∧ points.getLast? = some finish
  have htidy : ∀ column : Int,
      (Lanes.Eventmodeling.tidy
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish]).head? = some start ∧
      (Lanes.Eventmodeling.tidy
        [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
          ⟨finish.x, cb⟩, finish]).getLast? = some finish := by
    intro column
    exact tidy_endpoints start _
  change (do
    if profile == Profile.vector && a != b then
      if !(← Lanes.Eventmodeling.hits plan relation [start, finish]) then
        return [start, finish]
    let mut column := plan.maxR
    if !(← Lanes.Eventmodeling.hits plan relation
        [⟨start.x, ca⟩, ⟨start.x, cb⟩]) then
      column := start.x
    else if !(← Lanes.Eventmodeling.hits plan relation
        [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]) then
      column := finish.x
    return Lanes.Eventmodeling.tidy
      [start, ⟨start.x, ca⟩, ⟨column, ca⟩, ⟨column, cb⟩,
        ⟨finish.x, cb⟩, finish]) = .ok points at h
  cases hd : Lanes.Eventmodeling.hits plan relation [start, finish] <;>
    cases hs : Lanes.Eventmodeling.hits plan relation
      [⟨start.x, ca⟩, ⟨start.x, cb⟩] <;>
    cases ht : Lanes.Eventmodeling.hits plan relation
      [⟨finish.x, ca⟩, ⟨finish.x, cb⟩]
  all_goals
    simp_all only [Bind.bind, Except.bind] <;>
      (try split at h) <;> (try split at h) <;>
      (try split at h) <;> (try split at h) <;>
      (try dsimp only [pure, Except.pure] at h) <;>
      first
        | contradiction
        | (cases h; exact htidy _)
        | (cases h; exact ⟨rfl, rfl⟩)

inductive RelationIdentity (frames : List Lanes.Eventmodeling.Frame) :
    List ModelRoute → List Lanes.Eventmodeling.Relation → Prop where
  | nil : RelationIdentity frames [] []
  | cons {route : ModelRoute} {relation : Lanes.Eventmodeling.Relation}
      {routes : List ModelRoute} {relations : List Lanes.Eventmodeling.Relation}
      (src : frames.findIdx? (·.id == route.fromId) = some relation.src)
      (dst : frames.findIdx? (·.id == route.toId) = some relation.dst)
      (tail : RelationIdentity frames routes relations) :
      RelationIdentity frames (route :: routes) (relation :: relations)

theorem RelationIdentity.append {frames : List Lanes.Eventmodeling.Frame}
    {routes moreRoutes : List ModelRoute}
    {relations moreRelations : List Lanes.Eventmodeling.Relation}
    (h : RelationIdentity frames routes relations)
    (hmore : RelationIdentity frames moreRoutes moreRelations) :
    RelationIdentity frames (routes ++ moreRoutes) (relations ++ moreRelations) := by
  induction h with
  | nil => exact hmore
  | cons hsrc hdst _ ih => exact .cons hsrc hdst ih

theorem RelationIdentity.lookup {frames : List Lanes.Eventmodeling.Frame}
    {routes : List ModelRoute} {relations : List Lanes.Eventmodeling.Relation}
    (h : RelationIdentity frames routes relations) {i : Nat}
    {route : ModelRoute} {relation : Lanes.Eventmodeling.Relation}
    (hr : routes[i]? = some route) (hl : relations[i]? = some relation) :
    frames.findIdx? (·.id == route.fromId) = some relation.src ∧
      frames.findIdx? (·.id == route.toId) = some relation.dst := by
  induction h generalizing i with
  | nil => simp at hr
  | @cons input output inputs outputs hsrc hdst htail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr hl
      subst input
      subst output
      exact ⟨hsrc, hdst⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hr hl
      exact ih hr hl

theorem decode_route_loop_identity
    (routes : List ModelRoute) (initial output : Family)
    (hempty : initial.relations = [])
    (h : ForIn.forIn (m := Except LayoutError) routes initial (fun route state => do
      let some src := state.frames.findIdx? (·.id == route.fromId) | throw .domain
      let some dst := state.frames.findIdx? (·.id == route.toId) | throw .domain
      pure (.yield { state with relations := state.relations ++ [{ id := route.id, src, dst }] }))
        = .ok output) :
    output.frames = initial.frames ∧
      RelationIdentity output.frames routes output.relations := by
  have hinitial : initial.frames = initial.frames ∧
      RelationIdentity initial.frames [] initial.relations := by
    rw [hempty]
    exact ⟨rfl, .nil⟩
  have hp : output.frames = initial.frames ∧
      RelationIdentity initial.frames routes output.relations := by
    apply forIn_processed [] routes initial output _
      (fun done state => state.frames = initial.frames ∧
        RelationIdentity initial.frames done state.relations) hinitial _ h
    intro _ route _ state next _ hp hs
    cases hsrc : state.frames.findIdx? (·.id == route.fromId) with
    | none => simp [hsrc, throw, throwThe, MonadExceptOf.throw] at hs
    | some src =>
      cases hdst : state.frames.findIdx? (·.id == route.toId) with
      | none => simp [hsrc, hdst, throw, throwThe, MonadExceptOf.throw] at hs
      | some dst =>
        have he : ForInStep.yield
            { state with relations := state.relations ++ [{ id := route.id, src, dst }] }
              = next := by
          simpa [hsrc, hdst, Bind.bind, Except.bind, pure, Except.pure] using hs
        refine ⟨_, he.symm, hp.1, hp.2.append (.cons ?_ ?_ .nil)⟩
        · simpa only [hp.1] using hsrc
        · simpa only [hp.1] using hdst
  refine ⟨hp.1, ?_⟩
  rw [hp.1]
  exact hp.2

theorem decode_label_loop_references
    (m : Model) (ids : List String) (labels : List ModelLabel)
    (initial output : Family)
    (h : ForIn.forIn (m := Except LayoutError) labels initial (fun label state => do
      let some i := ids.findIdx? (· == label.owner) | throw .domain
      let some lane := state.lanes[i]? | throw .domain
      let c := Lanes.EventConsts.load m.profile
      let caption ← measureCaption m.profile .label
        (c.contentStartX - 4 * c.lanePadding) label.text
      pure (.yield { state with lanes := state.lanes.set i { lane with caption := some caption } }))
        = .ok output) :
    output.frames = initial.frames ∧ output.relations = initial.relations := by
  apply forIn_processed [] labels initial output _
    (fun _ state => state.frames = initial.frames ∧ state.relations = initial.relations)
    ⟨rfl, rfl⟩ _ h
  intro _ label _ state next _ hp hs
  cases hi : ids.findIdx? (· == label.owner) with
  | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at hs
  | some i =>
    cases hlane : state.lanes[i]? with
    | none => simp [hi, hlane, throw, throwThe, MonadExceptOf.throw] at hs
    | some lane =>
      cases hcap : measureCaption m.profile .label
          ((Lanes.EventConsts.load m.profile).contentStartX -
            4 * (Lanes.EventConsts.load m.profile).lanePadding) label.text with
      | error e => simp [hi, hlane, hcap, Bind.bind, Except.bind] at hs
      | ok caption =>
        have he : ForInStep.yield
            { state with lanes := state.lanes.set i { lane with caption := some caption } }
              = next := by
          simpa [hi, hlane, hcap, Bind.bind, Except.bind, pure, Except.pure] using hs
        exact ⟨_, he.symm, hp⟩

theorem decode_relation_identity {m : Model} {g : Family}
    (hwf : WellFormed m) (hdecode : decode m = .ok g) :
    RelationIdentity g.frames m.routes g.relations ∧
      ∀ frame ∈ g.frames, ∃ b ∈ m.boxes, b.role ≠ .group ∧ frame.id = b.id := by
  have hc := decode_parentsConsistent hdecode
  have ho := decode_parentDeclarationOrder hdecode
  have h := hdecode
  unfold decode at h
  simp only [hc, ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨first, hfirst, h⟩ := bind_ok h
  have hp := decode_first_loop_complete m hwf g hdecode first hfirst
  obtain ⟨related, hrelated, h⟩ := bind_ok h
  have hrel := decode_route_loop_identity m.routes first.1 related hp.relationsEmpty hrelated
  obtain ⟨captioned, hcaptioned, h⟩ := bind_ok h
  have hcap := decode_label_loop_references m first.2 m.labels related captioned hcaptioned
  have he : captioned = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using h
  subst captioned
  refine ⟨?_, ?_⟩
  · rw [hcap.1, hcap.2]
    exact hrel.2
  · rw [hcap.1, hrel.1]
    exact hp.decodedPrefix.2
/-- The first decode loop records the position of every frame's parent string: the lane
index of a frame is the `findIdx?` of its parent in the id list. -/
structure LaneTrace (sources : List ModelBox) (g : Family) (ids : List String) : Prop where
  lengths : g.lanes.length = ids.length
  entry : ∀ (i : Nat) (p : String), ids[i]? = some p →
    (g.lanes[i]?).map (·.id) = some p ∨ (g.lanes[i]?).map (·.id) = some ""
  frameLane : ∀ f ∈ g.frames, ∀ b ∈ sources, b.role ≠ .group → f.id = b.id →
    ids.findIdx? (· == b.parent) = some f.lane

theorem findIdx?_append_found (ids extra : List String) (p : String) {i : Nat}
    (h : ids.findIdx? (· == p) = some i) :
    (ids ++ extra).findIdx? (· == p) = some i := by
  induction ids generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    rw [List.findIdx?_cons] at h
    by_cases ha : (a == p) = true
    · rw [ha] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst i
      rw [List.cons_append, List.findIdx?_cons, ha]
      rfl
    · have hbeq : (a == p) = false := by simpa using ha
      rw [hbeq] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hr : rest.findIdx? (· == p) with
      | none => rw [hr] at h; simp at h
      | some j =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst i
        rw [List.cons_append, List.findIdx?_cons, hbeq]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ih hr]
        rfl

theorem findIdx?_append_self (ids : List String) (p : String)
    (h : ids.findIdx? (· == p) = none) :
    (ids ++ [p]).findIdx? (· == p) = some ids.length := by
  induction ids with
  | nil => simp
  | cons a rest ih =>
    rw [List.findIdx?_cons] at h
    by_cases ha : (a == p) = true
    · rw [ha] at h
      simp at h
    · have hbeq : (a == p) = false := by simpa using ha
      rw [hbeq] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hrest : rest.findIdx? (· == p) = none := by
        cases hr : rest.findIdx? (· == p) with
        | none => rfl
        | some j => rw [hr] at h; simp at h
      rw [List.cons_append, List.findIdx?_cons, hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rw [ih hrest]
      rfl

theorem findIdx?_some_mem (ids : List String) (p : String) {i : Nat}
    (h : ids.findIdx? (· == p) = some i) : ids[i]? = some p := by
  induction ids generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    rw [List.findIdx?_cons] at h
    by_cases ha : (a == p) = true
    · rw [ha] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst i
      simp only [List.getElem?_cons_zero]
      simpa using ha
    · have hbeq : (a == p) = false := by simpa using ha
      rw [hbeq] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hr : rest.findIdx? (· == p) with
      | none => rw [hr] at h; simp at h
      | some j =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst i
        simp only [List.getElem?_cons_succ]
        exact ih hr

theorem laneTrace_empty (sources : List ModelBox) :
    LaneTrace sources { lanes := [], frames := [], relations := [] } [] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i p hp
    simp at hp
  · intro f hf
    simp at hf

theorem laneTrace_entry_append {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) {laneId : String} {lane : Lanes.Eventmodeling.Lane}
    (hnon : lane.id = laneId ∨ lane.id = "") :
    ∀ (i : Nat) (p : String), (ids ++ [laneId])[i]? = some p →
      ((g.lanes ++ [lane])[i]?).map (·.id) = some p ∨
        ((g.lanes ++ [lane])[i]?).map (·.id) = some "" := by
  intro i p hs
  rcases Nat.lt_or_ge i g.lanes.length with hi | hi
  · have hidlen : g.lanes.length = ids.length := ht.lengths
    rw [List.getElem?_append_left (show i < ids.length by omega)] at hs
    have ho := ht.entry i p hs
    rw [List.getElem?_append_left hi]
    exact ho
  · have hlt : i < ids.length + 1 := by
      obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hs
      simpa only [List.length_append, List.length_singleton] using hbound
    have hlen : ids.length = g.lanes.length := ht.lengths.symm
    have hie : i = ids.length := by omega
    subst hie
    have hget : (ids ++ [laneId])[ids.length]? = some laneId := by
      rw [List.getElem?_append_right (l₁ := ids) (l₂ := [laneId]) (i := ids.length) (Nat.le_refl _)]
      simp
    rw [hget] at hs
    have hsp : p = laneId := (Option.some.inj hs).symm
    subst hsp
    rw [show ids.length = g.lanes.length from ht.lengths.symm]
    rw [List.getElem?_append_right (l₁ := g.lanes) (l₂ := [lane]) (i := g.lanes.length) (Nat.le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.map_some, Option.some.injEq]
    exact hnon

theorem laneTrace_group {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) (b : ModelBox) :
    LaneTrace sources
      ({ g with lanes := g.lanes ++
        [{ id := b.id, index := laneIndex b.shape, caption := none }] })
      (ids ++ [b.id]) := by
  refine ⟨by simp [ht.lengths], ?_, ?_⟩
  · exact laneTrace_entry_append ht (Or.inl rfl)
  · intro f hf b' hb' hr' hid'
    exact findIdx?_append_found ids [b.id] b'.parent (ht.frameLane f hf b' hb' hr' hid')

theorem laneTrace_frame {sources : List ModelBox} {g : Family} {ids : List String}
    (hunique : (sources.map (·.id)).Nodup)
    (ht : LaneTrace sources g ids)
    {b : ModelBox} (hb : b ∈ sources) (_hr : b.role ≠ .group)
    {i : Nat} (hi : ids.findIdx? (· == b.parent) = some i)
    (name : Lanes.Caption) (data : Option Lanes.Caption) :
    LaneTrace sources
      ({ g with frames := g.frames ++
        [{ id := b.id, lane := i, category := b.shape, name, data }] }) ids := by
  refine ⟨ht.lengths, ht.entry, ?_⟩
  intro f hf b' hb' hr' hid'
  rcases List.mem_append.mp hf with hf | hf
  · exact ht.frameLane f hf b' hb' hr' hid'
  · have he : f = { id := b.id, lane := i, category := b.shape, name, data } := by
      simpa only [List.mem_singleton] using hf
    subst he
    have hbid : b.id = b'.id := by simpa using hid'
    have hsame : b = b' := mem_id_unique hunique hb hb' hbid
    subst hsame
    exact hi

theorem laneTrace_fallback_frame {sources : List ModelBox} {g : Family} {ids : List String}
    (hunique : (sources.map (·.id)).Nodup)
    (ht : LaneTrace sources g ids)
    {b : ModelBox} (hb : b ∈ sources) (_hr : b.role ≠ .group)
    (hmiss : ids.findIdx? (· == b.parent) = none)
    (name : Lanes.Caption) (data : Option Lanes.Caption) :
    LaneTrace sources
      ({ g with
          lanes := g.lanes ++ [{ id := "", index := ids.length, caption := none }]
          frames := g.frames ++
            [{ id := b.id, lane := ids.length, category := b.shape, name, data }] })
      (ids ++ [b.parent]) := by
  refine ⟨by simp [ht.lengths], ?_, ?_⟩
  · exact laneTrace_entry_append ht (Or.inr rfl)
  · intro f hf b' hb' hr' hid'
    rcases List.mem_append.mp hf with hf | hf
    · exact findIdx?_append_found ids [b.parent] b'.parent
        (ht.frameLane f hf b' hb' hr' hid')
    · have he : f = { id := b.id, lane := ids.length, category := b.shape, name, data } := by
        simpa only [List.mem_singleton] using hf
      subst he
      have hbid : b.id = b'.id := by simpa using hid'
      have hsame : b = b' := mem_id_unique hunique hb hb' hbid
      subst hsame
      exact findIdx?_append_self ids b.parent hmiss

theorem laneTrace_relations {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) (relations : List Lanes.Eventmodeling.Relation) :
    LaneTrace sources { g with relations := relations } ids :=
  ⟨ht.lengths, ht.entry, ht.frameLane⟩

theorem laneTrace_caption {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) (i : Nat) (lane : Lanes.Eventmodeling.Lane)
    (caption : Lanes.Caption) (hi : g.lanes[i]? = some lane) :
    LaneTrace sources { g with lanes := g.lanes.set i { lane with caption := some caption } } ids := by
  refine ⟨by simpa using ht.lengths, ?_, ht.frameLane⟩
  intro j p hp
  have hids := lane_caption_update_lookup g.lanes i j lane caption hi
  have ho := ht.entry j p hp
  rw [hids]
  exact ho

theorem decode_first_loop_lane_trace (m : Model) (hwf : WellFormed m)
    (output : Family × List String)
    (h : ForIn.forIn (m := Except LayoutError) m.boxes
      (({ lanes := [], frames := [], relations := [] } : Family), ([] : List String))
      (fun b state => do
        let mut g := state.1
        let mut ids := state.2
        if b.role == .group then
          ids := ids ++ [b.id]
          g := { g with lanes := g.lanes ++
            [{ id := b.id, index := laneIndex b.shape, caption := none }] }
        else
          let lane ← match ids.findIdx? (· == b.parent) with
            | some i => pure i
            | none => do
              let i := ids.length
              ids := ids ++ [b.parent]
              g := { g with lanes := g.lanes ++
                [{ id := "", index := i, caption := none }] }
              pure i
          let parts := (boxText m b).splitOn "\n\n"
          let name ← measureCaption m.profile .label
            (Lanes.EventConsts.load m.profile).boxMaxWidth (parts.headD "")
          let data ← if parts.length ≤ 1 then pure none else do
            let text := (String.intercalate "\n\n" parts.tail).replace "\n" "<br>"
            pure (some (← measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth text))
          g := { g with frames := g.frames ++
            [{ id := b.id, lane, category := b.shape, name, data }] }
        pure (.yield (g, ids))) = .ok output) :
    LaneTrace m.boxes output.1 output.2 := by
  have hunique := Model.boxIds_nodup hwf
  apply forIn_processed [] m.boxes _ output _
    (fun _ state => LaneTrace m.boxes state.1 state.2) (laneTrace_empty m.boxes) _ h
  intro done b rest state next hsplit ht hs
  have hsplit' : m.boxes = done ++ b :: rest := by simpa using hsplit
  have hb : b ∈ m.boxes := by rw [hsplit']; simp
  by_cases hr : b.role = .group
  · have he : ForInStep.yield
        ({ state.1 with lanes := state.1.lanes ++
          [{ id := b.id, index := laneIndex b.shape, caption := none }] },
          state.2 ++ [b.id]) = next := by
      simpa [hr, Bind.bind, Except.bind, pure, Except.pure] using hs
    exact ⟨_, he.symm, laneTrace_group ht b⟩
  · cases hi : state.2.findIdx? (· == b.parent) with
    | none =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e => simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, laneTrace_fallback_frame hunique ht hb hr hi name none⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e => simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, laneTrace_fallback_frame hunique ht hb hr hi name (some data)⟩
    | some i =>
      simp [hr, hi, Bind.bind, Except.bind, pure, Except.pure] at hs
      cases hn : measureCaption m.profile .label
          (Lanes.EventConsts.load m.profile).boxMaxWidth
          (((boxText m b).splitOn "\n\n").head?.getD "") with
      | error e => simp [hn] at hs
      | ok name =>
        simp only [hn] at hs
        by_cases hparts : ((boxText m b).splitOn "\n\n").length ≤ 1
        · simp only [ite_eq_left hparts] at hs
          cases hs
          exact ⟨_, rfl, laneTrace_frame hunique ht hb hr hi name none⟩
        · cases hd : measureCaption m.profile .body
              (Lanes.EventConsts.load m.profile).boxMaxWidth
              ((String.intercalate "\n\n" ((boxText m b).splitOn "\n\n").tail).replace
                "\n" "<br>") with
          | error e => simp [hparts, hd] at hs
          | ok data =>
            simp only [ite_eq_right hparts, hd] at hs
            cases hs
            exact ⟨_, rfl, laneTrace_frame hunique ht hb hr hi name (some data)⟩

theorem decode_route_loop_lane_trace (sources : List ModelBox)
    (routes : List ModelRoute) (initial output : Family) (ids : List String)
    (ht : LaneTrace sources initial ids)
    (h : ForIn.forIn (m := Except LayoutError) routes initial (fun route state => do
      let some src := state.frames.findIdx? (·.id == route.fromId) | throw .domain
      let some dst := state.frames.findIdx? (·.id == route.toId) | throw .domain
      pure (.yield { state with relations := state.relations ++ [{ id := route.id, src, dst }] }))
        = .ok output) :
    LaneTrace sources output ids := by
  apply forIn_processed [] routes initial output _
    (fun _ state => LaneTrace sources state ids) ht _ h
  intro _ route _ state next _ hp hs
  cases hsrc : state.frames.findIdx? (·.id == route.fromId) with
  | none => simp [hsrc, throw, throwThe, MonadExceptOf.throw] at hs
  | some src =>
    cases hdst : state.frames.findIdx? (·.id == route.toId) with
    | none => simp [hsrc, hdst, throw, throwThe, MonadExceptOf.throw] at hs
    | some dst =>
      have he : ForInStep.yield
          { state with relations := state.relations ++ [{ id := route.id, src, dst }] }
            = next := by
        simpa [hsrc, hdst, Bind.bind, Except.bind, pure, Except.pure] using hs
      exact ⟨_, he.symm, laneTrace_relations hp _⟩

theorem decode_label_loop_lane_trace (m : Model) (ids : List String) (labels : List ModelLabel)
    (initial output : Family) (ht : LaneTrace m.boxes initial ids)
    (h : ForIn.forIn (m := Except LayoutError) labels initial (fun label state => do
      let some i := ids.findIdx? (· == label.owner) | throw .domain
      let some lane := state.lanes[i]? | throw .domain
      let c := Lanes.EventConsts.load m.profile
      let caption ← measureCaption m.profile .label
        (c.contentStartX - 4 * c.lanePadding) label.text
      pure (.yield { state with lanes := state.lanes.set i { lane with caption := some caption } }))
        = .ok output) :
    LaneTrace m.boxes output ids := by
  apply forIn_processed [] labels initial output _
    (fun _ state => LaneTrace m.boxes state ids) ht _ h
  intro _ label _ state next _ hp hs
  cases hi : ids.findIdx? (· == label.owner) with
  | none => simp [hi, throw, throwThe, MonadExceptOf.throw] at hs
  | some i =>
    cases hlane : state.lanes[i]? with
    | none => simp [hi, hlane, throw, throwThe, MonadExceptOf.throw] at hs
    | some lane =>
      cases hcap : measureCaption m.profile .label
          ((Lanes.EventConsts.load m.profile).contentStartX -
            4 * (Lanes.EventConsts.load m.profile).lanePadding) label.text with
      | error e => simp [hi, hlane, hcap, Bind.bind, Except.bind] at hs
      | ok caption =>
        have he : ForInStep.yield
            { state with lanes := state.lanes.set i { lane with caption := some caption } }
              = next := by
          simpa [hi, hlane, hcap, Bind.bind, Except.bind, pure, Except.pure] using hs
        exact ⟨_, he.symm, laneTrace_caption hp i lane caption hlane⟩

theorem decode_lane_trace {m : Model} {g : Family}
    (hwf : WellFormed m) (hdecode : decode m = .ok g) :
    ∃ ids, LaneTrace m.boxes g ids := by
  have hc := decode_parentsConsistent hdecode
  have ho := decode_parentDeclarationOrder hdecode
  have h := hdecode
  unfold decode at h
  simp only [hc, ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨first, hfirst, h⟩ := bind_ok h
  have hp := decode_first_loop_lane_trace m hwf first hfirst
  obtain ⟨related, hrelated, h⟩ := bind_ok h
  have hrel := decode_route_loop_lane_trace m.boxes m.routes first.1 related first.2 hp hrelated
  obtain ⟨captioned, hcaptioned, h⟩ := bind_ok h
  have hcap := decode_label_loop_lane_trace m first.2 m.labels related captioned hrel
    hcaptioned
  have he : captioned = g := by
    simpa only [pure, Except.pure, Except.ok.injEq] using h
  subst he
  exact ⟨first.2, hcap⟩

theorem laneTrace_lane_eq_of_parent {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) {f f' : Lanes.Eventmodeling.Frame}
    (hf : f ∈ g.frames) (hf' : f' ∈ g.frames)
    {b b' : ModelBox} (hb : b ∈ sources) (hb' : b' ∈ sources)
    (hr : b.role ≠ .group) (hr' : b'.role ≠ .group)
    (hid : f.id = b.id) (hid' : f'.id = b'.id) (hparent : b.parent = b'.parent) :
    f.lane = f'.lane := by
  have h1 := ht.frameLane f hf b hb hr hid
  have h2 := ht.frameLane f' hf' b' hb' hr' hid'
  rw [hparent] at h1
  rw [h1] at h2
  exact Option.some.inj h2

theorem laneTrace_lane_entry {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) {f : Lanes.Eventmodeling.Frame} (hf : f ∈ g.frames)
    {b : ModelBox} (hb : b ∈ sources) (hr : b.role ≠ .group) (hid : f.id = b.id) :
    (g.lanes[f.lane]?).map (·.id) = some b.parent ∨
      (g.lanes[f.lane]?).map (·.id) = some "" := by
  have hfind := ht.frameLane f hf b hb hr hid
  have hmem := findIdx?_some_mem ids b.parent hfind
  exact ht.entry f.lane b.parent hmem

theorem laneTrace_same_lane_of_frame {sources : List ModelBox} {g : Family} {ids : List String}
    (ht : LaneTrace sources g ids) {i : Nat} {p : String}
    (hp : ids[i]? = some p) : (g.lanes[i]?).map (·.id) = some p ∨
      (g.lanes[i]?).map (·.id) = some "" :=
  ht.entry i p hp

theorem family_routes_correspond (g : Family) (profile : Profile)
    (plan : Lanes.Eventmodeling.Plan) :
    ∀ (input : List Lanes.Eventmodeling.Relation) (output : List (List Point)),
      input.mapM (Lanes.Eventmodeling.route g profile plan) = .ok output →
      input.length = output.length ∧
        ∀ pair ∈ input.zip output,
          Lanes.Eventmodeling.route g profile plan pair.1 = .ok pair.2 := by
  intro input
  induction input with
  | nil =>
    intro output h
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst output
    exact ⟨rfl, by simp⟩
  | cons relation rest ih =>
    intro output h
    rw [List.mapM_cons] at h
    obtain ⟨points, hroute, h⟩ := bind_ok h
    obtain ⟨paths, hrest, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst output
    obtain ⟨hlen, hrel⟩ := ih paths hrest
    refine ⟨by simpa using hlen, ?_⟩
    intro pair hp
    rcases List.mem_cons.mp hp with he | hp
    · cases he
      exact hroute
    · exact hrel pair hp

theorem family_route_translation {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r) :
    let raw := Lanes.Eventmodeling.rows g (Lanes.EventConsts.load profile)
      (Lanes.Eventmodeling.columns g (Lanes.EventConsts.load profile))
    ∃ paths dx dy,
      g.relations.mapM (Lanes.Eventmodeling.route g profile raw) = .ok paths ∧
      r.frames = raw.frames.map (Lanes.shiftRect dx dy) ∧
      r.routes = paths.map (List.map (Lanes.shiftPoint dx dy)) := by
  unfold Lanes.Eventmodeling.layout at h
  by_cases hg : ((!g.frames.all (fun f => decide (f.lane < g.lanes.length))) ||
      !g.relations.all (fun relation =>
        decide (relation.src < g.frames.length ∧ relation.dst < g.frames.length))) = true
  · simp only [hg, ↓reduceIte, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at h
    cases h
  · simp only [hg, bind, Except.bind] at h
    obtain ⟨paths, hpaths, h⟩ := bind_ok h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst r
      exact ⟨paths, _, _, hpaths, rfl, rfl⟩

theorem route_boundary_shift (dx dy : Int) {p : Point} {rect : Rect}
    (h : Validator.onBoundary p rect) :
    Validator.onBoundary (Lanes.shiftPoint dx dy p) (Lanes.shiftRect dx dy rect) := by
  unfold Validator.onBoundary Lanes.shiftPoint Lanes.shiftRect at *
  dsimp only at *
  omega

theorem columnWalk_dimensions (profile : Profile) (frames : List Lanes.Eventmodeling.Frame)
    (reach : Int) (floor : List Int) :
    ∀ rect ∈ Lanes.Eventmodeling.columnWalk (Lanes.EventConsts.load profile)
      reach floor frames, 0 ≤ rect.w ∧ 0 ≤ rect.h := by
  induction frames generalizing reach floor with
  | nil =>
    intro rect hm
    simp [Lanes.Eventmodeling.columnWalk] at hm
  | cons frame rest ih =>
    intro rect hm
    rw [Lanes.Eventmodeling.columnWalk] at hm
    rcases List.mem_cons.mp hm with he | hm
    · subst rect
      dsimp only
      have hw : 0 ≤ (Lanes.EventConsts.load profile).boxMinWidth := by
        cases profile <;> decide
      have hh : 0 ≤ (Lanes.EventConsts.load profile).boxMinHeight := by
        cases profile <;> decide
      have hpad : 0 ≤ (Lanes.EventConsts.load profile).boxPadding := by
        cases profile <;> decide
      simp only [Lanes.Eventmodeling.frameSize, Lanes.Eventmodeling.clamp]
      constructor <;> omega
    · exact ih _ _ rect hm

theorem raw_frame_dimensions (g : Family) (profile : Profile) :
    let c := Lanes.EventConsts.load profile
    let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
    ∀ rect ∈ raw.frames, 0 ≤ rect.w ∧ 0 ≤ rect.h := by
  dsimp only
  intro rect hm
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hm
  subst rect
  exact columnWalk_dimensions profile g.frames _ _ pair.2 (List.of_mem_zip hp).2

theorem family_route_ports {g : Family} {profile : Profile}
    {r : Lanes.Eventmodeling.Result} (h : Lanes.Eventmodeling.layout g profile = .ok r)
    {i : Nat} {relation : Lanes.Eventmodeling.Relation} {points : List Point}
    (hrelation : g.relations[i]? = some relation)
    (hpoints : r.routes[i]? = some points)
    (hsrc : relation.src < g.frames.length) (hdst : relation.dst < g.frames.length) :
    ∃ p q : Point, ∃ src dst : Rect,
      points.head? = some p ∧ points.getLast? = some q ∧
      r.frames[relation.src]? = some src ∧ r.frames[relation.dst]? = some dst ∧
      Validator.onBoundary p src ∧ Validator.onBoundary q dst := by
  let c := Lanes.EventConsts.load profile
  let raw := Lanes.Eventmodeling.rows g c (Lanes.Eventmodeling.columns g c)
  obtain ⟨paths, dx, dy, hpaths, hframes, hroutes⟩ := family_route_translation h
  rw [hroutes, List.getElem?_map] at hpoints
  cases hi : paths[i]? with
  | none => simp only [hi, Option.map_none, reduceCtorEq] at hpoints
  | some path =>
    have he : path.map (Lanes.shiftPoint dx dy) = points := by
      simpa only [hi, Option.map_some, Option.some.injEq] using hpoints
    subst points
    obtain ⟨_, hcorr⟩ := family_routes_correspond g profile raw g.relations paths hpaths
    have hzip : (g.relations.zip paths)[i]? = some (relation, path) :=
      List.getElem?_zip_eq_some.mpr ⟨hrelation, hi⟩
    have hroute := hcorr (relation, path) (List.mem_of_getElem? hzip)
    have hwalk : ∀ (frames : List Lanes.Eventmodeling.Frame)
        (reach : Int) (floor : List Int),
        (Lanes.Eventmodeling.columnWalk c reach floor frames).length = frames.length := by
      intro frames
      induction frames with
      | nil => intro reach floor; rfl
      | cons frame rest ih =>
        intro reach floor
        simp only [Lanes.Eventmodeling.columnWalk, List.length_cons]
        rw [ih]
    have hlen : raw.frames.length = g.frames.length := by
      simp only [raw, Lanes.Eventmodeling.rows, List.length_map, List.length_zip,
        Lanes.Eventmodeling.columns, hwalk, Nat.min_self]
    have hs : relation.src < raw.frames.length := by omega
    have ht : relation.dst < raw.frames.length := by omega
    have hsr : raw.frames[relation.src]? = some raw.frames[relation.src] :=
      List.getElem?_eq_getElem hs
    have htr : raw.frames[relation.dst]? = some raw.frames[relation.dst] :=
      List.getElem?_eq_getElem ht
    let src := raw.frames[relation.src]
    let dst := raw.frames[relation.dst]
    let a := Lanes.Eventmodeling.rank g
      (((g.frames[relation.src]?).map (·.lane)).getD 0)
    let b := Lanes.Eventmodeling.rank g
      (((g.frames[relation.dst]?).map (·.lane)).getD 0)
    let p : Point :=
      ⟨src.x + Int.fdiv (2 * src.w) 3, if a < b then src.y + src.h else src.y⟩
    let q : Point :=
      ⟨dst.x + Int.fdiv dst.w 3, if b < a then dst.y + dst.h else dst.y⟩
    have hend : path.head? = some p ∧ path.getLast? = some q := by
      have hend := family_route_endpoints g profile raw relation path hroute
      simpa only [List.getD_eq_getElem?_getD, hsr, htr, Option.getD_some] using hend
    have hsrcdims := raw_frame_dimensions g profile src (List.getElem_mem hs)
    have hdstdims := raw_frame_dimensions g profile dst (List.getElem_mem ht)
    refine ⟨Lanes.shiftPoint dx dy p, Lanes.shiftPoint dx dy q,
      Lanes.shiftRect dx dy src, Lanes.shiftRect dx dy dst,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head?_map, hend.1]
      rfl
    · rw [List.getLast?_map, hend.2]
      rfl
    · rw [hframes, List.getElem?_map, hsr]
      rfl
    · rw [hframes, List.getElem?_map, htr]
      rfl
    · exact route_boundary_shift dx dy
        (eventmodeling_start_boundary src (a < b) hsrcdims.1 hsrcdims.2)
    · exact route_boundary_shift dx dy
        (eventmodeling_finish_boundary dst (b < a) hdstdims.1 hdstdims.2)

theorem RelationIdentity.lengths {frames : List Lanes.Eventmodeling.Frame}
    {routes : List ModelRoute} {relations : List Lanes.Eventmodeling.Relation}
    (h : RelationIdentity frames routes relations) : routes.length = relations.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

theorem scene_route_origin {m : Model} {s : Scene}
    (h : scene m = .ok s) {out : Route} (hout : out ∈ s.routes) :
    ∃ (g : Family) (r : Lanes.Eventmodeling.Result) (i : Nat) (route : ModelRoute),
      decode m = .ok g ∧ Lanes.Eventmodeling.layout g m.profile = .ok r ∧
      m.routes[i]? = some route ∧ r.routes[i]? = some out.points ∧
      out.fromId = route.fromId ∧ out.toId = route.toId ∧
      out.orthogonal = route.orthogonal := by
  unfold scene at h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨boxes, _, h⟩ := bind_ok h
  obtain ⟨labels, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst s
  obtain ⟨pair, hp, he⟩ := List.mem_map.mp hout
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  obtain ⟨hinput, hpoints⟩ := List.getElem?_zip_eq_some.mp hi
  cases he
  exact ⟨g, r, i, pair.1, hg, hr, hinput, hpoints, rfl, rfl, rfl⟩

theorem box_find_of_mem {boxes : List Box}
    (hunique : (boxes.map (·.id)).Nodup) {out : Box} (hout : out ∈ boxes) :
    boxes.find? (·.id == out.id) = some out := by
  induction boxes with
  | nil => simp at hout
  | cons first rest ih =>
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hunique
    rcases List.mem_cons.mp hout with he | hm
    · subst out
      simp
    · have hne : first.id ≠ out.id := by
        intro he
        exact hnot (List.mem_map.mpr ⟨out, hm, he.symm⟩)
      simp only [List.find?_cons, show (first.id == out.id) = false from by
        simpa using hne]
      exact ih hrest hm

theorem scene_frame_box {m : Model} {s : Scene} {g : Family}
    {r : Lanes.Eventmodeling.Result} (hwf : WellFormed m)
    (hs : scene m = .ok s) (hg : decode m = .ok g)
    (hr : Lanes.Eventmodeling.layout g m.profile = .ok r)
    {id : String} {index : Nat}
    (hfind : g.frames.findIdx? (·.id == id) = some index) :
    ∃ out : Box, s.layoutDump.box? id = some out ∧
      r.frames[index]? = some out.rect := by
  obtain ⟨hib, hmatch, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfind
  have hframeid : g.frames[index].id = id := beq_iff_eq.mp hmatch
  obtain ⟨b, hb, hrole, hbid⟩ :=
    (decode_relation_identity hwf hg).2 g.frames[index] (List.getElem_mem hib)
  have hid : b.id = id := hbid.symm.trans hframeid
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨g', r', out, hg', hr', hout, hplace, hmetadata⟩ := scene_box_at hs hi
  have heg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst g'
  have her : r' = r := Except.ok.inj (hr'.symm.trans hr)
  subst r'
  have hlookup := placeBox_lookup hplace
  simp only [show (b.role == .group) = false from by simpa using hrole,
    Bool.false_eq_true, ↓reduceIte] at hlookup
  obtain ⟨j, hj, hrect⟩ := hlookup
  have hfind' : g.frames.findIdx? (·.id == b.id) = some index := by
    simpa only [hid] using hfind
  have heindex : j = index := Option.some.inj (hj.symm.trans hfind')
  subst j
  refine ⟨out, ?_, hrect⟩
  change s.boxes.find? (·.id == id) = some out
  have houtid : out.id = id := hmetadata.1.trans hid
  rw [← houtid]
  exact box_find_of_mem (scene_boxIds_nodup hwf hs) (List.mem_of_getElem? hout)

theorem scene_c5 {m : Model} {s : Scene}
    (hwf : WellFormed m) (h : scene m = .ok s) : Validator.C5 s.layoutDump := by
  intro out hout
  have hout' : out ∈ s.routes := hout
  obtain ⟨g, r, i, route, hg, hr, hinput, hpoints, hfrom, hto, _⟩ :=
    scene_route_origin h hout'
  have hidentity := (decode_relation_identity hwf hg).1
  have hlen := hidentity.lengths
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hinput
  have hirel : i < g.relations.length := by omega
  have hrelation : g.relations[i]? = some g.relations[i] :=
    List.getElem?_eq_getElem hirel
  obtain ⟨hsrc, hdst⟩ := hidentity.lookup hinput hrelation
  obtain ⟨hsrcbound, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hsrc
  obtain ⟨hdstbound, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hdst
  obtain ⟨p, q, src, dst, hp, hq, hsrcRect, hdstRect, hpb, hqb⟩ :=
    family_route_ports hr hrelation hpoints hsrcbound hdstbound
  obtain ⟨srcBox, hsrcBox, hsrcBoxRect⟩ := scene_frame_box hwf h hg hr hsrc
  obtain ⟨dstBox, hdstBox, hdstBoxRect⟩ := scene_frame_box hwf h hg hr hdst
  have hesrc : src = srcBox.rect := Option.some.inj (hsrcRect.symm.trans hsrcBoxRect)
  have hedst : dst = dstBox.rect := Option.some.inj (hdstRect.symm.trans hdstBoxRect)
  refine ⟨p, q, srcBox, dstBox, hp, hq, ?_, ?_, ?_, ?_⟩
  · simpa only [hfrom] using hsrcBox
  · simpa only [hto] using hdstBox
  · exact hesrc ▸ hpb
  · exact hedst ▸ hqb

theorem eventmodeling_c5 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : layout m = .ok result) :
    Validator.C5 result.scene.layoutDump := by
  obtain ⟨s, hs, hdump⟩ := layout_scene h
  rw [hdump]
  exact scene_c5 hwf hs


end Elegant.Kinds.Eventmodeling
