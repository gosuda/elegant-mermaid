import Elegant.Kinds.JourneySceneFacts

set_option autoImplicit false

namespace Elegant.Kinds.JourneySceneFacts

open Elegant Kinds Lanes
open Lanes.Journey
open Journey Common JourneyValid

private theorem contained_disjoint_left {outer inner other : Rect}
    (hc : inner.Contained outer) (hd : Disjoint inner other) : Disjoint outer other := by
  simp only [Rect.Contained, Disjoint, Rect.meetsInterior] at hc hd ⊢
  intro hm
  exact hd ⟨by omega, by omega⟩

private theorem section_frame_data (g : Input) (c : Constants)
    (top taskTop taskH : Int) {frames : List Rect}
    (heq : frames = g.sections.zipIdx.map
      (fun e => sectionFrame g c top taskTop taskH e.2))
    (hguards : ∀ entry ∈ g.sections.zipIdx,
      ∃ first, (sectionIndices g entry.2).head? = some first ∧
        (g.tasks.zipIdx.all fun (t, k) =>
          decide (first ≤ k ∧ k ≤ (sectionIndices g entry.2).getLast?.getD first) ==
            (t.band == (entry.2 : Int))) = true)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx) :
    ∃ first last : Nat,
      frames.getD j zeroRect =
        sectionRect c top (taskTop + taskH - top) first last ∧
      first ≤ last ∧ last < g.tasks.length ∧
      (g.tasks.zipIdx.all fun (t, k) =>
        decide (first ≤ k ∧ k ≤ last) == (t.band == (j : Int))) = true ∧
      (∀ (t : Task) (k : Nat), (t, k) ∈ g.tasks.zipIdx →
        (t.band = (j : Int) ↔ first ≤ k ∧ k ≤ last)) := by
  obtain ⟨first, hhead, hguard⟩ := hguards (s, j) hs
  have hfirstmem := List.mem_of_head? hhead
  unfold sectionIndices at hfirstmem
  obtain ⟨pair, hpair, hpk⟩ := List.mem_map.mp hfirstmem
  obtain ⟨hz0, hb0⟩ := List.mem_filter.mp hpair
  have hz0 : (pair.1, pair.2) ∈ g.tasks.zipIdx := hz0
  have hband0 : pair.1.band = (j : Int) := beq_iff_eq.mp hb0
  have htget := List.mem_zipIdx_iff_getElem?.mp hz0
  obtain ⟨hk0lt, hte⟩ := List.getElem?_eq_some_iff.mp htget
  have hidx0 : pair.2 = first := hpk
  refine ⟨first, (sectionIndices g j).getLast?.getD first, ?_, ?_, ?_, hguard, ?_⟩

  · exact frame_rect_eq heq (zipIdx_mem_bounds g.sections hs).1 hhead
  · have ht := (List.all_eq_true.mp hguard) (pair.1, pair.2) hz0
    have hdec : decide (first ≤ pair.2 ∧ pair.2 ≤ (sectionIndices g j).getLast?.getD first) =
        (pair.1.band == (j : Int)) := beq_iff_eq.mp ht
    have hrhs : (pair.1.band == (j : Int)) = true := by simp [hband0]
    rw [hrhs] at hdec
    have hle' : first ≤ pair.2 ∧ pair.2 ≤ (sectionIndices g j).getLast?.getD first :=
      of_decide_eq_true hdec
    simp only [hidx0] at hle'
    exact hle'.2
  · have hlastmem : (sectionIndices g j).getLast?.getD first ∈ sectionIndices g j := by
      cases hl : (sectionIndices g j).getLast? with
      | none => exact List.mem_of_head? hhead
      | some l => exact List.mem_of_getLast? hl
    unfold sectionIndices at hlastmem
    obtain ⟨kt, htf, hval⟩ := List.mem_map.mp hlastmem
    obtain ⟨hz, hb⟩ := List.mem_filter.mp htf
    have htk : (kt.1, kt.2) ∈ g.tasks.zipIdx := hz
    have hkt2 : kt.2 = (sectionIndices g j).getLast?.getD first := hval
    rw [← hkt2]
    exact (zipIdx_mem_bounds g.tasks htk).1
  · intro t k hz
    have ht := (List.all_eq_true.mp hguard) (t, k) hz
    have hdec : decide (first ≤ k ∧ k ≤ (sectionIndices g j).getLast?.getD first) =
        (t.band == (j : Int)) := beq_iff_eq.mp ht
    constructor
    · intro hbandk
      have hb : (t.band == (j : Int)) = true := beq_iff_eq.mpr hbandk
      rw [hb] at hdec
      exact of_decide_eq_true hdec
    · intro hle
      have hb : (t.band == (j : Int)) = true := by
        rw [← hdec]; exact decide_eq_true hle
      exact beq_iff_eq.mp hb

private theorem origin_shape {m : Model} {c : Constants} {g : Input}
    {frames : List Rect} {dx dy : Int} {id : String} {rect : Rect}
    (horig : PlacementOrigin m c g frames dx dy (id, rect)) :
    (∃ s j, (s, j) ∈ g.sections.zipIdx ∧ id = s.id ∧
      rect = shiftRect dx dy (frames.getD j zeroRect)) ∨
    (∃ t, g.title = some t ∧ id = t.id ∧ rect = shiftRect dx dy (titleBox g)) ∨
    (∃ t i, (t, i) ∈ g.tasks.zipIdx ∧ id = t.id ∧
      rect = shiftRect dx dy ((taskRects c g).getD i zeroRect)) ∨
    (∃ p, p ∈ m.boxes ∧ ∃ t i, (t, i) ∈ g.tasks.zipIdx ∧ shapeKind p = "people" ∧
      id = p.id ∧ p.parent = t.id ∧ rect = shiftRect dx dy (peopleBox c g t i)) := by
  cases horig with
  | «section» s j hs => exact Or.inl ⟨s, j, hs, rfl, rfl⟩
  | title t ht => exact Or.inr (Or.inl ⟨t, ht, rfl, rfl⟩)
  | task t i ht => exact Or.inr (Or.inr (Or.inl ⟨t, i, ht, rfl, rfl⟩))
  | people p hp t i ht hk hpp =>
    exact Or.inr (Or.inr (Or.inr ⟨p, hp, t, i, ht, hk, rfl, hpp, rfl⟩))

private theorem source_parent_of_section {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {src : ModelBox} (hsrc : src ∈ m.boxes)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx)
    (hid : src.id = s.id) : src.parent = "" := by
  have hshape := section_id_shape m c g hwf hi hsrc hs hid
  exact hi.parentRoots src hsrc (Or.inr (by simp [isSecBox, hshape]))

private theorem source_parent_of_title {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {src : ModelBox} (hsrc : src ∈ m.boxes)
    {t : Card} (ht : g.title = some t) (hid : src.id = t.id) : src.parent = "" := by
  have hshape := title_id_shape m c g hwf hi hsrc ht hid
  exact hi.parentRoots src hsrc (Or.inl (by simp [isTitleBox, hshape]))

private theorem cards_disjoint_shifted (c : Constants) (taskTop taskH dx dy : Int)
    (i j : Nat) (hp : 0 ≤ c.taskWidth + c.columnGap) (hgp : 0 ≤ c.columnGap)
    (hij : i ≠ j) :
    Disjoint (shiftRect dx dy (taskRect c taskTop taskH i))
      (shiftRect dx dy (taskRect c taskTop taskH j)) := by
  rcases Nat.lt_or_ge i j with h | h
  · exact journey_shifted_tasks_disjoint c taskTop taskH dx dy i j hp hgp h
  · exact disjoint_symm
      (journey_shifted_tasks_disjoint c taskTop taskH dx dy j i hp hgp (by omega))

private theorem title_rect_value {g : Input} {t : Card} (ht : g.title = some t) :
    titleBox g = (⟨0, 0, t.caption.w, t.caption.h⟩ : Rect) := by
  simp [titleBox, ht]

private theorem frame_task_disjoint_of_data (g : Input) (c : Constants)
    (top taskTop taskH dx dy : Int) (j : Nat) {frames : List Rect}
    (hdata :
      ∃ first last : Nat,
        frames.getD j zeroRect =
          sectionRect c top (taskTop + taskH - top) first last ∧
        first ≤ last ∧ last < g.tasks.length ∧
        (g.tasks.zipIdx.all fun (t, k) =>
          decide (first ≤ k ∧ k ≤ last) == (t.band == (j : Int))) = true)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hgp : 0 ≤ c.columnGap)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) (hband : t.band ≠ (j : Int)) :
    Disjoint (shiftRect dx dy (frames.getD j zeroRect))
      (shiftRect dx dy (taskRect c taskTop taskH i)) := by
  obtain ⟨first, last, hrect, _, _, hguard⟩ := hdata
  rw [hrect]
  exact admitted_section_disjoint_foreign_task g c j first last top
    (taskTop + taskH - top) taskTop taskH dx dy hguard hp hgp ht hband

private theorem frame_people_disjoint_of_data (g : Input) (c : Constants)
    (top taskTop taskH dx dy : Int) (j : Nat) {frames : List Rect}
    (hdata :
      ∃ first last : Nat,
        frames.getD j zeroRect =
          sectionRect c top (taskTop + taskH - top) first last ∧
        first ≤ last ∧ last < g.tasks.length ∧
        (g.tasks.zipIdx.all fun (t, k) =>
          decide (first ≤ k ∧ k ≤ last) == (t.band == (j : Int))) = true)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hgp : 0 ≤ c.columnGap)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) (hband : t.band ≠ (j : Int))
    (hpc : (taskRect c taskTop taskH i).Contained (peopleBox c g t i)) :
    Disjoint (shiftRect dx dy (frames.getD j zeroRect))
      (shiftRect dx dy (peopleBox c g t i)) := by
  obtain ⟨first, last, hrect, _, _, hguard⟩ := hdata
  rw [hrect]
  exact journey_people_disjoint_foreign_section g c j first last top
    (taskTop + taskH - top) taskTop taskH dx dy hguard hp hgp ht hband _ hpc

/-! ### Shared layout expressions of the journey scene -/

private def jTop (g : Input) (c : Constants) : Int :=
  (g.title.map fun t => t.caption.h + c.scoreStep).getD 0

private def jBandH (g : Input) (c : Constants) : Int :=
  g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY)) c.bandHeight

private def jTaskH (g : Input) (c : Constants) : Int :=
  g.tasks.foldl (fun h t => max h
    (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight

private def jTaskTop (g : Input) (c : Constants) : Int :=
  jTop g c + jBandH g c + 6 * c.scoreStep

private theorem section_parent_ne_task_id {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {parent : String} (hmem : parent ∈ g.sections.map (·.id))
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) : parent ≠ t.id := by
  intro hpar
  rw [hi.secIds] at hmem
  obtain ⟨srcS, hsS, hidS⟩ := List.mem_map.mp hmem
  obtain ⟨hsrcS, hkSec⟩ := List.mem_filter.mp hsS
  have hshape := task_id_shape m c g hwf hi hsrcS ht (hidS.trans hpar)
  have hsec : shapeKind srcS = "section" := beq_iff_eq.mp hkSec
  rw [hsec] at hshape
  simp at hshape

set_option maxHeartbeats 1600000 in
/-- Clause 2: exclusive journey boxes that share a parent are disjoint. Titles, sections,
and unparented tasks are root siblings separated vertically or by column; people cards never
share a parent with any sibling. -/
theorem journey_c2 {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (h : Journey.layout m = .ok result) :
    Validator.C2 result.scene.layoutDump := by
  classical
  obtain ⟨c, g, frames, _bands, dx, dy, hc, hg, hforIn, _, hplaced⟩ :=
    successful_journey_scene h
  have hi := decode_ok m c hwf hg
  have hmeta := successful_box_origins h
  have hids_ne := layout_box_ids_nonempty h
  obtain ⟨hwt, hht, hbandHeight0, hgap, hss, _, _, _, _⟩ := load_pos hc
  have hposcol : 0 ≤ c.taskWidth + c.columnGap := by omega
  have hposgap : 0 ≤ c.columnGap := Int.le_of_lt hgap

  have hbandHge : 0 ≤ g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY))
      c.bandHeight :=
    Int.le_trans (Int.le_of_lt hbandHeight0)
      (foldl_max_bound (fun s : Card => s.caption.h + 2 * c.padY) g.sections
        c.bandHeight).1
  have htaskHge : 0 ≤ g.tasks.foldl (fun h t => max h
      (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight :=
    Int.le_trans (Int.le_of_lt hht)
      (foldl_max_bound (fun t : Task =>
        t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY) g.tasks c.taskHeight).1
  clear hwt hht hbandHeight0
  obtain ⟨heq, hguards⟩ := section_frames_trace g c
    ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0)
    ((g.title.map fun t => t.caption.h + c.scoreStep).getD 0 +
      (g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY)) c.bandHeight) +
      6 * c.scoreStep)
    (g.tasks.foldl (fun h t => max h
      (t.caption.h + (t.people.map (·.h)).getD 0 + 2 * c.padY)) c.taskHeight)
    (g.sections.foldl (fun h s => max h (s.caption.h + 2 * c.padY)) c.bandHeight)
    hforIn
  unfold Validator.C2 Scene.layoutDump
  intro b hbout o hcout bidne _ _ hpar
  rcases origin_shape (hplaced b hbout) with ⟨s1, j1, hsec1, hid1, hrect1⟩ |
    ⟨t1, ht1, hid1, hrect1⟩ |
    ⟨tt1, i1, htk1, hid1, hrect1⟩ |
    ⟨p1, hp1, tt1, i1, htk1, hk1, hid1, hparP1, hrect1⟩
  · -- b is a section
    rcases origin_shape (hplaced o hcout) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · -- section vs section
      obtain ⟨f1, l1, hr1, hle1, hlt1, hg1, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec1
      obtain ⟨f2, l2, hr2, hle2, hlt2, hg2, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec2
      have hj : j1 ≠ j2 := by
        intro he
        have h1 := List.mem_zipIdx_iff_getElem?.mp hsec1
        have h2 := List.mem_zipIdx_iff_getElem?.mp hsec2
        rw [he] at h1
        rw [h1] at h2
        have h3 : s1 = s2 := Option.some.inj h2
        exact bidne (by rw [hid1, hid2, h3])
      have hran := section_ranges_disjoint hj hg1 hg2 hle1 hle2 hlt1 hlt2
      rw [hrect1, hrect2, hr1, hr2]
      rcases hran with hbd | hbd
      · exact shift_disjoint dx dy
          (journey_section_bands_disjoint c _ _ f1 l1 f2 l2 hposcol hposgap hle1 hbd)
      · exact disjoint_symm (shift_disjoint dx dy
          (journey_section_bands_disjoint c _ _ f2 l2 f1 l1 hposcol hposgap hle2 hbd))
    · -- section vs title: the frame starts below the title's bottom edge
      obtain ⟨f1, l1, hr1, _, _, _, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec1
      rw [hrect1, hrect2, hr1, title_rect_value ht2]
      have htop : (g.title.map fun t => t.caption.h + c.scoreStep).getD 0 =
          t2.caption.h + c.scoreStep := by simp [ht2]
      apply disjoint_symm
      apply shift_disjoint_y dx dy
      dsimp only [sectionRect]
      rw [htop]
      omega
    · -- section vs task: equal parents force an unparented task, whose band misses the frame
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsp1 := source_parent_of_section hwf hi hsrcB hsec1 (hidm1.symm.trans hid1)
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      obtain ⟨srcT2, hsrcT2, _, hidT2, hband2, _⟩ := task_source m c g hi htk2
      have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hsrcT2
        (hidm2.symm.trans (hid2.trans hidT2.symm))
      rw [hsame] at hpar2
      have hroot : srcT2.parent = "" :=
        hpar2.symm.trans (hpar.symm.trans (hpar1.trans hsp1))
      have hb2 : tt2.band ≠ (j1 : Int) := by
        rw [hband2, hroot]
        simp [bandVal] <;> omega
      obtain ⟨f1, l1, hr1, hle1, hlt1, hg1, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec1
      rw [hrect1, hrect2, task_rect_lookup c g htk2]
      exact frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c) dx dy j1
        ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2 hb2
    · -- section vs people: the people parent is a task id, never the section's root parent
      exfalso
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsp1 := source_parent_of_section hwf hi hsrcB hsec1 (hidm1.symm.trans hid1)
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb2] at hpar2
      rw [hparP2] at hpar2
      rw [hpar1, hsp1] at hpar
      rw [hpar2] at hpar
      obtain ⟨srcT, hsrcT, _, hidT, _, _⟩ := task_source m c g hi htk2
      exact hids_ne srcT hsrcT (hidT.trans hpar.symm)
  · -- b is the title
    rcases origin_shape (hplaced o hcout) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · rw [hrect1, hrect2, title_rect_value ht1]
      obtain ⟨f2, l2, hr2, _, _, _, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec2
      rw [hr2]
      have htop : (g.title.map fun t => t.caption.h + c.scoreStep).getD 0 =
          t1.caption.h + c.scoreStep := by simp [ht1]
      skip
      apply shift_disjoint_y dx dy
      dsimp only [sectionRect]
      rw [htop]
      omega
    · exfalso
      have heq : t1 = t2 := Option.some.inj (ht1.symm.trans ht2)
      exact bidne (by rw [hid1, hid2, heq])
    · rw [hrect1, hrect2, title_rect_value ht1, task_rect_lookup c g htk2]
      have htop : (g.title.map fun t => t.caption.h + c.scoreStep).getD 0 =
          t1.caption.h + c.scoreStep := by simp [ht1]
      apply shift_disjoint_y dx dy
      dsimp only [taskRect]
      rw [htop]
      omega
    · exfalso
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsp1 := source_parent_of_title hwf hi hsrcB ht1 (hidm1.symm.trans hid1)
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb2] at hpar2
      rw [hparP2] at hpar2
      rw [hpar1, hsp1] at hpar
      rw [hpar2] at hpar
      obtain ⟨srcT, hsrcT, _, hidT, _, _⟩ := task_source m c g hi htk2
      exact hids_ne srcT hsrcT (hidT.trans hpar.symm)
  · -- b is a task
    rw [task_rect_lookup c g htk1] at hrect1
    rcases origin_shape (hplaced o hcout) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · -- task vs section: equal parents force an unparented task
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsp2 := source_parent_of_section hwf hi hsrcO hsec2 (hidm2.symm.trans hid2)
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      obtain ⟨srcT1, hsrcT1, _, hidT1, hband1, _⟩ := task_source m c g hi htk1
      have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hsrcT1
        (hidm1.symm.trans (hid1.trans hidT1.symm))
      rw [hsame] at hpar1
      have hroot : srcT1.parent = "" :=
        hpar1.symm.trans (hpar.trans (hpar2.trans hsp2))
      have hb1 : tt1.band ≠ (j2 : Int) := by
        rw [hband1, hroot]
        simp [bandVal] <;> omega
      obtain ⟨f2, l2, hr2, hle2, hlt2, hg2, _⟩ :=
        section_frame_data g c _ _ _ heq hguards hsec2
      rw [hrect1, hrect2]
      exact disjoint_symm (frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c)
        (jTaskH g c) dx dy j2
        ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ hposcol hposgap htk1 hb1)
    · rw [hrect1, hrect2, title_rect_value ht2]
      have htop : (g.title.map fun t => t.caption.h + c.scoreStep).getD 0 =
          t2.caption.h + c.scoreStep := by simp [ht2]
      apply disjoint_symm
      apply shift_disjoint_y dx dy
      dsimp only [taskRect]
      rw [htop]
      omega
    · rw [hrect1, hrect2, task_rect_lookup c g htk2]
      have hidx : i1 ≠ i2 := by
        intro he
        have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
        have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
        rw [he] at h1
        rw [h1] at h2
        have h3 : tt1 = tt2 := Option.some.inj h2
        exact bidne (by rw [hid1, hid2, h3])
      exact cards_disjoint_shifted c _ _ dx dy i1 i2 hposcol hposgap hidx
    · -- task vs people: the people parent is a task id, never the task's own parent
      exfalso
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      obtain ⟨srcT1, hsrcT1, _, hidT1, _, hparOK1⟩ := task_source m c g hi htk1
      have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hsrcT1
        (hidm1.symm.trans (hid1.trans hidT1.symm))
      rw [hsame] at hpar1
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb2] at hpar2
      rw [hparP2] at hpar2
      rw [hpar1] at hpar
      rw [hpar2] at hpar
      rcases hparOK1 with hroot | hmem
      · rw [hroot] at hpar
        obtain ⟨srcT2, hsrcT2, _, hidT2, _, _⟩ := task_source m c g hi htk2
        exact hids_ne srcT2 hsrcT2 (hidT2.trans hpar.symm)
      · exact section_parent_ne_task_id hwf hi hmem htk2 hpar
  · -- b is a people card
    rcases origin_shape (hplaced o hcout) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · -- people vs section: the section's parent is the root marker, the people's is a task id
      exfalso
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsp2 := source_parent_of_section hwf hi hsrcO hsec2 (hidm2.symm.trans hid2)
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsb1 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hp1
        (hidm1.symm.trans hid1)
      rw [hsb1] at hpar1
      rw [hparP1] at hpar1
      rw [hpar1] at hpar
      rw [hpar2, hsp2] at hpar
      obtain ⟨srcT, hsrcT, _, hidT, _, _⟩ := task_source m c g hi htk1
      exact hids_ne srcT hsrcT (hidT.trans hpar)
    · -- people vs title
      exfalso
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsp2 := source_parent_of_title hwf hi hsrcO ht2 (hidm2.symm.trans hid2)
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsb1 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hp1
        (hidm1.symm.trans hid1)
      rw [hsb1] at hpar1
      rw [hparP1] at hpar1
      rw [hpar1] at hpar
      rw [hpar2, hsp2] at hpar
      obtain ⟨srcT, hsrcT, _, hidT, _, _⟩ := task_source m c g hi htk1
      exact hids_ne srcT hsrcT (hidT.trans hpar)
    · -- people vs task: the task's parent is root or a section id, never a task id
      exfalso
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      obtain ⟨srcT2, hsrcT2, _, hidT2, _, hparOK2⟩ := task_source m c g hi htk2
      have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hsrcT2
        (hidm2.symm.trans (hid2.trans hidT2.symm))
      rw [hsame] at hpar2
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      have hsb1 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hp1
        (hidm1.symm.trans hid1)
      rw [hsb1] at hpar1
      rw [hparP1] at hpar1
      rw [hpar1] at hpar
      rw [hpar2] at hpar
      rcases hparOK2 with hroot | hmem
      · rw [hroot] at hpar
        obtain ⟨srcT1, hsrcT1, _, hidT1, _, _⟩ := task_source m c g hi htk1
        exact hids_ne srcT1 hsrcT1 (hidT1.trans hpar)
      · exact section_parent_ne_task_id hwf hi hmem htk1 hpar.symm
    · exfalso
      -- two people cards share the owner, contradicting unique decoded people parents
      have huniq := layout_unique_decoded_people_parents h
      have hnodup : ((m.boxes.filter fun b => shapeKind b == "people").map (·.parent)).Nodup :=
        of_decide_eq_true huniq
      obtain ⟨srcB, hsrcB, hidm1, _, hpar1, _⟩ := hmeta b hbout
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o hcout
      have hsb1 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcB hp1
        (hidm1.symm.trans hid1)
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb1] at hpar1
      rw [hsb2] at hpar2
      rw [hpar1, hpar2, hparP1, hparP2] at hpar
      have hmem1 : p1 ∈ m.boxes.filter fun b => shapeKind b == "people" :=
        List.mem_filter.mpr ⟨hp1, by rw [hk1]; rfl⟩
      have hmem2 : p2 ∈ m.boxes.filter fun b => shapeKind b == "people" :=
        List.mem_filter.mpr ⟨hp2, by rw [hk2]; rfl⟩
      have hparEq : p1.parent = p2.parent := by
        rw [hparP1, hparP2, ← hpar]
      have hsame := map_inj_of_nodup hnodup hmem1 hmem2 hparEq
      exact bidne (by rw [hid1, hid2, ← hsame])

/-! ### Id distinctness across journey box kinds -/

private theorem people_task_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {p : ModelBox} (hpm : p ∈ m.boxes) (hkp : shapeKind p = "people")
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx) : p.id ≠ tt.id := by
  obtain ⟨srcT, hsrcT, hkT, hidT, _, _⟩ := task_source m c g hi htk
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hpm hsrcT (he.trans hidT.symm)
  rw [hsame] at hkp
  have h1 : shapeKind srcT = "task" := beq_iff_eq.mp hkT
  rw [hkp] at h1
  simp at h1

private theorem people_section_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {p : ModelBox} (hpm : p ∈ m.boxes) (hkp : shapeKind p = "people")
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx) : p.id ≠ s.id := by
  obtain ⟨srcS, hsrcS, hkS, hidS⟩ := section_source m c g hi hs
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hpm hsrcS (he.trans hidS.symm)
  rw [hsame] at hkp
  have h1 : shapeKind srcS = "section" := beq_iff_eq.mp hkS
  rw [hkp] at h1
  simp at h1

private theorem people_title_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {p : ModelBox} (hpm : p ∈ m.boxes) (hkp : shapeKind p = "people")
    {t : Card} (ht : g.title = some t) : p.id ≠ t.id := by
  obtain ⟨srcT, hsrcT, hkT, hidT⟩ := title_source m c g hi ht
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hpm hsrcT (he.trans hidT.symm)
  rw [hsame] at hkp
  have h1 : shapeKind srcT = "title" := beq_iff_eq.mp hkT
  rw [hkp] at h1
  simp at h1

private theorem task_section_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx) : tt.id ≠ s.id := by
  obtain ⟨srcT, hsrcT, hkT, hidT, _, _⟩ := task_source m c g hi htk
  obtain ⟨srcS, hsrcS, hkS, hidS⟩ := section_source m c g hi hs
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcT hsrcS
    (hidT.trans (he.trans hidS.symm))
  rw [hsame] at hkT
  have h1 : shapeKind srcS = "section" := beq_iff_eq.mp hkS
  simp [isTaskBox, h1] at hkT

private theorem task_title_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx)
    {t : Card} (ht : g.title = some t) : tt.id ≠ t.id := by
  obtain ⟨srcT, hsrcT, hkT, hidT, _, _⟩ := task_source m c g hi htk
  obtain ⟨srcL, hsrcL, hkL, hidL⟩ := title_source m c g hi ht
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcT hsrcL
    (hidT.trans (he.trans hidL.symm))
  rw [hsame] at hkT
  have h1 : shapeKind srcL = "title" := beq_iff_eq.mp hkL
  simp [isTaskBox, h1] at hkT

private theorem section_title_id_ne {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {s : Card} {j : Nat} (hs : (s, j) ∈ g.sections.zipIdx)
    {t : Card} (ht : g.title = some t) : s.id ≠ t.id := by
  obtain ⟨srcS, hsrcS, hkS, hidS⟩ := section_source m c g hi hs
  obtain ⟨srcL, hsrcL, hkL, hidL⟩ := title_source m c g hi ht
  intro he
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcS hsrcL
    (hidS.trans (he.trans hidL.symm))
  rw [hsame] at hkS
  have h1 : shapeKind srcL = "title" := beq_iff_eq.mp hkL
  simp [isSecBox, h1] at hkS

/-! ### Task band values from the dump parents -/

private theorem root_band {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {X : Box} {srcX : ModelBox} (hsrcX : srcX ∈ m.boxes)
    (hidMeta : X.id = srcX.id) (hparMeta : X.parent = srcX.parent)
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx)
    (hid : X.id = tt.id) (hroot : X.parent = "") :
    tt.band = (-1 : Int) := by
  obtain ⟨srcT, hsrcT, _, hidT, hband, _⟩ := task_source m c g hi htk
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcX hsrcT
    ((hidMeta.symm.trans hid).trans hidT.symm)
  rw [hsame] at hparMeta
  have hsp : srcT.parent = "" := hparMeta.symm.trans hroot
  rw [hband, hsp]
  simp [bandVal]

private theorem sectioned_band {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    {X : Box} {srcX : ModelBox} (hsrcX : srcX ∈ m.boxes)
    (hidMeta : X.id = srcX.id) (hparMeta : X.parent = srcX.parent)
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx)
    (hid : X.id = tt.id)
    {sec : Card} {j : Nat} (hsec : (sec, j) ∈ g.sections.zipIdx)
    (hsecid : X.parent = sec.id) (hsecne : sec.id ≠ "") :
    tt.band = (j : Int) := by
  obtain ⟨srcT, hsrcT, _, hidT, hband, _⟩ := task_source m c g hi htk
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcX hsrcT
    ((hidMeta.symm.trans hid).trans hidT.symm)
  rw [hsame] at hparMeta
  have hsp : srcT.parent = sec.id := hparMeta.symm.trans hsecid
  rw [hband, hsp]
  exact section_band_index g hi.secIdsNodup hsec hsecne

/-! ### People containment and pairwise clearance -/

private theorem card_people_disjoint (c : Constants) (taskTop taskH dx dy : Int)
    (g : Input) (i j : Nat) (tt : Task) (hij : i ≠ j)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hgp : 0 ≤ c.columnGap)
    (hpc : (taskRect c taskTop taskH j).Contained (peopleBox c g tt j)) :
    Disjoint (shiftRect dx dy (taskRect c taskTop taskH i))
      (shiftRect dx dy (peopleBox c g tt j)) :=
  journey_contained_disjoint_right _ _ _
    (journey_origin_preserves_containment _ _ dx dy hpc)
    (cards_disjoint_shifted c taskTop taskH dx dy i j hp hgp hij)

private theorem people_people_disjoint (c : Constants) (taskTop taskH dx dy : Int)
    (g : Input) (i j : Nat) (tt1 tt2 : Task) (hij : i ≠ j)
    (hp : 0 ≤ c.taskWidth + c.columnGap) (hgp : 0 ≤ c.columnGap)
    (hpc1 : (taskRect c taskTop taskH i).Contained (peopleBox c g tt1 i))
    (hpc2 : (taskRect c taskTop taskH j).Contained (peopleBox c g tt2 j)) :
    Disjoint (shiftRect dx dy (peopleBox c g tt1 i))
      (shiftRect dx dy (peopleBox c g tt2 j)) :=
  contained_disjoint_left (journey_origin_preserves_containment _ _ dx dy hpc1)
    (card_people_disjoint c taskTop taskH dx dy g i j tt2 hij hp hgp hpc2)

private theorem title_people_disjoint (c : Constants) (g : Input)
    (taskTop taskH dx dy : Int)
    {t : Card} (ht : g.title = some t) (hle : t.caption.h ≤ taskTop)
    {tt : Task} {i : Nat}
    (hpc : (taskRect c taskTop taskH i).Contained (peopleBox c g tt i)) :
    Disjoint (shiftRect dx dy (titleBox g))
      (shiftRect dx dy (peopleBox c g tt i)) := by
  have hycard : Disjoint (shiftRect dx dy (titleBox g))
      (shiftRect dx dy (taskRect c taskTop taskH i)) := by
    rw [title_rect_value ht]
    apply shift_disjoint_y dx dy
    simp only [taskRect]
    omega
  exact journey_contained_disjoint_right _ _ _
    (journey_origin_preserves_containment _ _ dx dy hpc) hycard

private theorem task_rect_lookup' (c : Constants) (g : Input)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    (taskRects c g).getD i zeroRect =
      taskRect c (jTaskTop g c) (jTaskH g c) i := by
  rw [task_rect_lookup c g ht]
  rfl

private theorem people_in_card' {m : Model} {c : Constants} {g : Input}
    (hi : DecodeInv m c m.boxes g) (hc : LoadPos c)
    {t : Task} {i : Nat} (ht : (t, i) ∈ g.tasks.zipIdx) :
    (taskRect c (jTaskTop g c) (jTaskH g c) i).Contained (peopleBox c g t i) := by
  rw [← task_rect_lookup' c g ht]
  exact people_inside_card m c g hi hc ht

private theorem jBandH_nonneg (g : Input) (c : Constants)
    (h0 : 0 < c.bandHeight) :
    0 ≤ jBandH g c := by
  have h1 := (foldl_max_bound (fun s : Card => s.caption.h + 2 * c.padY)
    g.sections c.bandHeight).1
  unfold jBandH
  omega

private theorem jTaskTop_ge_title (g : Input) (c : Constants)
    (hss : 0 ≤ c.scoreStep) (h0 : 0 < c.bandHeight) {t : Card} (ht : g.title = some t) :
    t.caption.h ≤ jTaskTop g c := by
  have h1 : jTop g c = t.caption.h + c.scoreStep := by unfold jTop; simp [ht]
  have h2 := jBandH_nonneg g c h0
  unfold jTaskTop
  omega

private theorem jTop_ge_title (g : Input) (c : Constants)
    (hss : 0 ≤ c.scoreStep) {t : Card} (ht : g.title = some t) :
    t.caption.h ≤ jTop g c := by
  have h1 : jTop g c = t.caption.h + c.scoreStep := by unfold jTop; simp [ht]
  omega

set_option maxHeartbeats 1600000 in
/-- The band of a journey task dump box: unparented tasks sit at band `-1`; parented tasks
sit at their section's index. -/
private theorem task_band_cases {m : Model} {c : Constants} {g : Input}
    (hwf : WellFormed m) (hi : DecodeInv m c m.boxes g)
    (hids : ∀ b ∈ m.boxes, b.id ≠ "")
    {X : Box} {srcX : ModelBox} (hsrcX : srcX ∈ m.boxes)
    (hidMeta : X.id = srcX.id) (hparMeta : X.parent = srcX.parent)
    {tt : Task} {i : Nat} (htk : (tt, i) ∈ g.tasks.zipIdx) (hid : X.id = tt.id) :
    tt.band = (-1 : Int) ∨
      ∃ sec : Card, ∃ j : Nat, (sec, j) ∈ g.sections.zipIdx ∧ X.parent = sec.id ∧
        tt.band = (j : Int) := by
  obtain ⟨srcT, hsrcT, _, hidT, hband, hparOK⟩ := task_source m c g hi htk
  have hsame := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcX hsrcT
    ((hidMeta.symm.trans hid).trans hidT.symm)
  rw [hsame] at hparMeta
  rcases hparOK with hroot | hmem
  · left
    rw [hband, hroot]
    simp [bandVal]
  · right
    obtain ⟨sc, hsc, hidsc⟩ := List.mem_map.mp hmem
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hsc
    have hsec : (sc, j) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj
    obtain ⟨srcS, hsrcS, _, hidS⟩ := section_source m c g hi hsec
    refine ⟨sc, j, hsec, hparMeta.trans hidsc.symm, ?_⟩
    rw [hband, ← hidsc]
    exact section_band_index g hi.secIdsNodup hsec
      (fun h => hids srcS hsrcS (hidS.trans h))

private theorem people_boxes_same_task_eq {m : Model} {result : Layered.FamilyResult}
    (h : Journey.layout m = .ok result) {p1 p2 : ModelBox}
    (hp1 : p1 ∈ m.boxes) (hp2 : p2 ∈ m.boxes)
    (hk1 : shapeKind p1 = "people") (hk2 : shapeKind p2 = "people")
    (hpar : p1.parent = p2.parent) : p1 = p2 := by
  have huniq := layout_unique_decoded_people_parents h
  have hnodup : ((m.boxes.filter fun b => shapeKind b == "people").map (·.parent)).Nodup :=
    of_decide_eq_true huniq
  have hmem1 : p1 ∈ m.boxes.filter fun b => shapeKind b == "people" :=
    List.mem_filter.mpr ⟨hp1, by rw [hk1]; rfl⟩
  have hmem2 : p2 ∈ m.boxes.filter fun b => shapeKind b == "people" :=
    List.mem_filter.mpr ⟨hp2, by rw [hk2]; rfl⟩
  exact map_inj_of_nodup hnodup hmem1 hmem2 hpar

set_option maxHeartbeats 1600000 in
/-- Clause 8a: a journey group-role frame never overlaps a foreign box. Section frames
separate by task-index ranges, task columns separate by index, titles sit above everything,
and the ancestor walk exempts containment pairs. -/
theorem journey_c8a {m : Model} {result : Layered.FamilyResult}
    (hwf : WellFormed m) (_hlimits : WithinLimits m) (h : Journey.layout m = .ok result) :
    Validator.C8a result.scene.layoutDump := by
  classical
  obtain ⟨c, g, frames, _bands, dx, dy, hc, hg, hforIn, _, hplaced⟩ :=
    successful_journey_scene h
  have hi := decode_ok m c hwf hg
  have hmeta := successful_box_origins h
  have hids_ne := layout_box_ids_nonempty h
  obtain ⟨hwt, hht, hbandHeight0, hgap, hss, _, _, _, _⟩ := load_pos hc
  have hposcol : 0 ≤ c.taskWidth + c.columnGap := by omega
  have hposgap : 0 ≤ c.columnGap := Int.le_of_lt hgap
  have hbandHge := jBandH_nonneg g c hbandHeight0
  obtain ⟨heq, hguards⟩ := section_frames_trace g c (jTop g c) (jTaskTop g c)
    (jTaskH g c) (jBandH g c) hforIn
  have hlookup : ∀ out : Box, out ∈ result.scene.boxes →
      result.scene.layoutDump.box? out.id = some out := fun out hmem =>
    dump_lookup_self hwf h out hmem
  have hdataSec : ∀ (s : Card) (j : Nat), (s, j) ∈ g.sections.zipIdx →
      ∃ f l : Nat, frames.getD j zeroRect =
        sectionRect c (jTop g c) (jTaskTop g c + jTaskH g c - jTop g c) f l ∧
        f ≤ l ∧ l < g.tasks.length ∧
        (g.tasks.zipIdx.all fun (t, k) =>
          decide (f ≤ k ∧ k ≤ l) == (t.band == (j : Int))) = true := by
    intro s j hs
    obtain ⟨f, l, hr, hle, hlt, hguard, _⟩ :=
      section_frame_data g c (jTop g c) (jTaskTop g c) (jTaskH g c) heq hguards hs
    exact ⟨f, l, hr, hle, hlt, hguard⟩
  have hpc : ∀ (tt : Task) (i : Nat), (tt, i) ∈ g.tasks.zipIdx →
      (taskRect c (jTaskTop g c) (jTaskH g c) i).Contained (peopleBox c g tt i) :=
    fun tt i ht => people_in_card' hi (load_pos hc) ht
  unfold Validator.C8a
  intro gb hgmem _hgrole o homem oidne hn1 hn2
  rcases origin_shape (hplaced gb hgmem) with ⟨s1, j1, hsec1, hidg, hrectg⟩ |
    ⟨t1, ht1, hidg, hrectg⟩ |
    ⟨tt1, i1, htk1, hidg, hrectg⟩ |
    ⟨p1, hp1, tt1, i1, htk1, hk1, hidg, hparP1, hrectg⟩
  · -- the group box is a section frame: its own ancestor list is empty
    obtain ⟨srcg, hsrcg, hidmg, _, hparg, _⟩ := hmeta gb hgmem
    have hgpar : gb.parent = "" :=
      hparg.trans (source_parent_of_section hwf hi hsrcg hsec1 (hidmg.symm.trans hidg))
    have hancg : result.scene.layoutDump.ancestors gb.id = [] :=
      ancestors_root (hlookup gb hgmem) hgpar
    rcases origin_shape (hplaced o homem) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
      obtain ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ := hdataSec s2 j2 hsec2
      have hj : j1 ≠ j2 := by
        intro he
        have h1 : g.sections[j2]? = some s1 := by
          rw [← he]
          exact List.mem_zipIdx_iff_getElem?.mp hsec1
        have h2 : g.sections[j2]? = some s2 := List.mem_zipIdx_iff_getElem?.mp hsec2
        have hEq12 : s1 = s2 := Option.some.inj (h1.symm.trans h2)
        exact oidne (by rw [hidg, hid2, ← hEq12])
      have hran := section_ranges_disjoint hj hg1 hg2 hle1 hle2 hlt1 hlt2
      rw [hrectg, hrect2, hr1, hr2]
      rcases hran with hbd | hbd
      · exact shift_disjoint dx dy
          (journey_section_bands_disjoint c _ _ f1 l1 f2 l2 hposcol hposgap hle1 hbd)
      · exact disjoint_symm (shift_disjoint dx dy
          (journey_section_bands_disjoint c _ _ f2 l2 f1 l1 hposcol hposgap hle2 hbd))
    · obtain ⟨f1, l1, hr1, _, _, _⟩ := hdataSec s1 j1 hsec1
      rw [hrectg, hrect2, hr1, title_rect_value ht2]
      have htopval : jTop g c = t2.caption.h + c.scoreStep := by unfold jTop; simp [ht2]
      apply disjoint_symm
      apply shift_disjoint_y dx dy
      dsimp only [sectionRect]
      rw [htopval]
      omega
    · -- section frame vs task: exempt when parented to this frame, else bands differ
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      obtain ⟨srcT2, hsrcT2, _, hidT2, _, _⟩ := task_source m c g hi htk2
      have hband := task_band_cases hwf hi hids_ne hsrcO hidm2 hpar2 htk2 hid2
      rcases hband with hroot | ⟨sec, j, hsecj, hparEq, hbEq⟩
      · obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
        rw [hrectg, hrect2, task_rect_lookup' c g htk2]
        exact frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c)
          dx dy j1 ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2
          (by rw [hroot]; simp <;> omega)
      · obtain ⟨srcSec, hsrcSec, _, hidSec⟩ := section_source m c g hi hsecj
        obtain ⟨outSec, houtSec, hidOutS, hparOutS⟩ := dump_of_source hwf h hsrcSec
        have hrootSec : outSec.parent = "" :=
          hparOutS.trans (source_parent_of_section hwf hi hsrcSec hsecj hidSec)
        have hsNe : sec.id ≠ "" := fun he => hids_ne srcSec hsrcSec (hidSec.trans he)
        have hancO : result.scene.layoutDump.ancestors o.id = [sec.id] :=
          ancestors_single (hlookup o homem) hparEq hsNe
            (by rw [← hidOutS.trans hidSec]; exact hlookup outSec houtSec) hrootSec
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn1
        by_cases hEq : sec.id = gb.id
        · exact absurd hEq.symm hn1
        · have hj : j ≠ j1 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp hsecj
            have h2 := List.mem_zipIdx_iff_getElem?.mp hsec1
            rw [he] at h1
            rw [h1] at h2
            have h3 : sec = s1 := Option.some.inj h2
            exact hEq (by rw [h3, hidg])
          have hb : tt2.band ≠ (j1 : Int) := by rw [hbEq]; omega
          obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
          rw [hrectg, hrect2, task_rect_lookup' c g htk2]
          exact frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c)
            dx dy j1 ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2 hb
    · -- section frame vs people: exempt via the owner's section, else owner band differs
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      have hsb := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb] at hpar2
      rw [hparP2] at hpar2
      obtain ⟨srcT2, hsrcT2, _, hidT2, _, hparOK2⟩ := task_source m c g hi htk2
      obtain ⟨outT2, houtT2, hidOutT, hparOutT⟩ := dump_of_source hwf h hsrcT2
      have hlookT : result.scene.layoutDump.box? tt2.id = some outT2 := by
        rw [hidT2.symm.trans hidOutT.symm]
        exact hlookup outT2 houtT2
      have hownerNe : tt2.id ≠ "" := fun he => hids_ne srcT2 hsrcT2 (hidT2.trans he)
      rcases hparOK2 with hroot2 | hmem2
      · have hancO : result.scene.layoutDump.ancestors o.id = [tt2.id] :=
          ancestors_single (hlookup o homem) hpar2 hownerNe hlookT
            (hparOutT.trans hroot2)
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn1
        have hb : tt2.band = (-1 : Int) :=
          root_band hwf hi hsrcT2 hidOutT hparOutT htk2
            (hidOutT.trans hidT2) (hparOutT.trans hroot2)
        obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
        rw [hrectg, hrect2]
        exact frame_people_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c)
          dx dy j1 ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2
          (by rw [hb]; omega) (hpc tt2 i2 htk2)
      · obtain ⟨sc, hsc, hidsc⟩ := List.mem_map.mp hmem2
        obtain ⟨j2s, hj2s⟩ := List.mem_iff_getElem?.mp hsc
        have hsecO : (sc, j2s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj2s
        obtain ⟨srcSec, hsrcSec, _, hidSec⟩ := section_source m c g hi hsecO
        obtain ⟨outSec, houtSec, hidOutS, hparOutS⟩ := dump_of_source hwf h hsrcSec
        have hrootSec : outSec.parent = "" :=
          hparOutS.trans (source_parent_of_section hwf hi hsrcSec hsecO hidSec)
        have hsNe : sc.id ≠ "" := fun he => hids_ne srcSec hsrcSec (hidSec.trans he)
        have hancO : result.scene.layoutDump.ancestors o.id = [tt2.id, sc.id] :=
          ancestors_double (hlookup o homem) hpar2 hownerNe hlookT
            (hparOutT.trans hidsc.symm) hsNe
            (by rw [← hidOutS.trans hidSec]; exact hlookup outSec houtSec) hrootSec
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn1
        rcases task_band_cases hwf hi hids_ne hsrcT2 hidOutT hparOutT htk2
          (hidOutT.trans hidT2) with hb0 | ⟨sec2', j2', hsec2', hparEq2, hbEq2⟩
        · obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
          rw [hrectg, hrect2]
          exact frame_people_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c)
            dx dy j1 ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2
            (by rw [hb0]; omega) (hpc tt2 i2 htk2)
        · have hjEq : j2' = j2s :=
            zip_id_index g.sections (fun s : Card => s.id) hi.secIdsNodup hsec2' hsecO
              (by
                have e1 : sec2'.id = outT2.parent := hparEq2.symm
                exact e1.trans (hparOutT.trans hidsc.symm))
          have hbOwner : tt2.band = (j2s : Int) := by rw [hbEq2, hjEq]
          by_cases hEqg : sc.id = gb.id
          · exact absurd hEqg.symm hn1.2
          · have hj : j2s ≠ j1 := by
              intro he
              have h1 := List.mem_zipIdx_iff_getElem?.mp hsecO
              have h2 := List.mem_zipIdx_iff_getElem?.mp hsec1
              rw [he] at h1
              rw [h1] at h2
              have h3 : sc = s1 := Option.some.inj h2
              exact hEqg (by rw [h3, hidg])
            obtain ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ := hdataSec s1 j1 hsec1
            rw [hrectg, hrect2]
            exact frame_people_disjoint_of_data g c (jTop g c) (jTaskTop g c) (jTaskH g c)
              dx dy j1 ⟨f1, l1, hr1, hle1, hlt1, hg1⟩ hposcol hposgap htk2
              (by rw [hbOwner]; omega) (hpc tt2 i2 htk2)
  · -- the group box is the title card: its ancestor list is empty
    obtain ⟨srcg, hsrcg, hidmg, _, hparg, _⟩ := hmeta gb hgmem
    have hgpar : gb.parent = "" :=
      hparg.trans (source_parent_of_title hwf hi hsrcg ht1 (hidmg.symm.trans hidg))
    have hancg : result.scene.layoutDump.ancestors gb.id = [] :=
      ancestors_root (hlookup gb hgmem) hgpar
    rcases origin_shape (hplaced o homem) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · obtain ⟨f2, l2, hr2, _, _, _⟩ := hdataSec s2 j2 hsec2
      rw [hrectg, hrect2, hr2, title_rect_value ht1]
      have htopval : jTop g c = t1.caption.h + c.scoreStep := by unfold jTop; simp [ht1]
      apply shift_disjoint_y dx dy
      dsimp only [sectionRect]
      rw [htopval]
      omega
    · exfalso
      have heq : t1 = t2 := Option.some.inj (ht1.symm.trans ht2)
      exact oidne (by rw [hidg, hid2, heq])
    · rw [hrectg, hrect2, title_rect_value ht1, task_rect_lookup' c g htk2]
      have hle : t1.caption.h ≤ jTaskTop g c :=
        jTaskTop_ge_title g c (Int.le_of_lt hss) hbandHeight0 ht1
      apply shift_disjoint_y dx dy
      dsimp only [taskRect]
      omega
    · rw [hrectg, hrect2, title_rect_value ht1]
      have hle : t1.caption.h ≤ jTaskTop g c :=
        jTaskTop_ge_title g c (Int.le_of_lt hss) hbandHeight0 ht1
      have hd := title_people_disjoint c g (jTaskTop g c) (jTaskH g c) dx dy ht1 hle
        (hpc tt2 i2 htk2)
      rw [title_rect_value ht1] at hd
      exact hd
  · -- the group box is a task card
    obtain ⟨srcg, hsrcg, hidmg, _, hparg, _⟩ := hmeta gb hgmem
    obtain ⟨srcT1, hsrcT1, _, hidT1, hband1, hparOK1⟩ := task_source m c g hi htk1
    have hownerNe1 : tt1.id ≠ "" := fun he => hids_ne srcT1 hsrcT1 (hidT1.trans he)
    have hbandRoot1 : gb.parent = "" → tt1.band = (-1 : Int) :=
      root_band hwf hi hsrcg hidmg hparg htk1 hidg
    have hbandSec1 : ∀ (sec : Card) (j : Nat), (sec, j) ∈ g.sections.zipIdx →
        gb.parent = sec.id → sec.id ≠ "" → tt1.band = (j : Int) :=
      fun _ _ hs hpar hne =>
        sectioned_band hwf hi hsrcg hidmg hparg htk1 hidg hs hpar hne
    have hsameg : srcg = srcT1 :=
      source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcg hsrcT1
        (hidmg.symm.trans (hidg.trans hidT1.symm))
    have hparg' : gb.parent = srcT1.parent := hsameg ▸ hparg
    rcases origin_shape (hplaced o homem) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · -- task group vs section frame
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      have hsp2 := source_parent_of_section hwf hi hsrcO hsec2 (hidm2.symm.trans hid2)
      rcases hparOK1 with hroot1 | hmem1
      · have hb : tt1.band = (-1 : Int) := hbandRoot1 (hparg'.trans hroot1)
        obtain ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ := hdataSec s2 j2 hsec2
        rw [hrectg, hrect2, task_rect_lookup' c g htk1]
        exact disjoint_symm (frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c)
          (jTaskH g c) dx dy j2 ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ hposcol hposgap htk1
          (by rw [hb]; omega))
      · obtain ⟨sc1, hsc1, hidsc1⟩ := List.mem_map.mp hmem1
        obtain ⟨j1s, hj1s⟩ := List.mem_iff_getElem?.mp hsc1
        have hsec1z : (sc1, j1s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj1s
        obtain ⟨srcSec1, hsrcSec1, _, hidSec1⟩ := section_source m c g hi hsec1z
        obtain ⟨outSec1, houtSec1, hidOutS1, hparOutS1⟩ := dump_of_source hwf h hsrcSec1
        have hrootSec1 : outSec1.parent = "" :=
          hparOutS1.trans (source_parent_of_section hwf hi hsrcSec1 hsec1z hidSec1)
        have hsNe1 : sc1.id ≠ "" := fun he => hids_ne srcSec1 hsrcSec1 (hidSec1.trans he)
        have hancg : result.scene.layoutDump.ancestors gb.id = [sc1.id] :=
          ancestors_single (hlookup gb hgmem) (hparg'.trans hidsc1.symm) hsNe1
            (by rw [← hidOutS1.trans hidSec1]; exact hlookup outSec1 houtSec1) hrootSec1
        rw [hancg] at hn2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
        by_cases hEq : sc1.id = s2.id
        · exact (hn2 (hid2.trans hEq.symm)).elim
        · have hbandSec : tt1.band = (j1s : Int) :=
            hbandSec1 sc1 j1s hsec1z (hparg'.trans hidsc1.symm) hsNe1
          have hj : j1s ≠ j2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp hsec1z
            have h2 := List.mem_zipIdx_iff_getElem?.mp hsec2
            rw [he] at h1
            rw [h1] at h2
            have h3 : sc1 = s2 := Option.some.inj h2
            exact hEq (by rw [h3])
          have hb : tt1.band ≠ (j2 : Int) := by rw [hbandSec]; omega
          obtain ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ := hdataSec s2 j2 hsec2
          rw [hrectg, hrect2, task_rect_lookup' c g htk1]
          exact disjoint_symm (frame_task_disjoint_of_data g c (jTop g c) (jTaskTop g c)
            (jTaskH g c) dx dy j2 ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ hposcol hposgap htk1 hb)
    · rw [hrectg, hrect2, title_rect_value ht2, task_rect_lookup' c g htk1]
      have htopval : jTop g c = t2.caption.h + c.scoreStep := by unfold jTop; simp [ht2]
      apply disjoint_symm
      apply shift_disjoint_y dx dy
      dsimp only [taskRect]
      unfold jTaskTop
      rw [htopval]
      omega
    · rw [hrectg, hrect2, task_rect_lookup' c g htk1, task_rect_lookup' c g htk2]
      have hidx : i1 ≠ i2 := by
        intro he
        have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
        have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
        rw [he] at h1
        rw [h1] at h2
        have h3 : tt1 = tt2 := Option.some.inj h2
        exact oidne (by rw [hidg, hid2, h3])
      exact cards_disjoint_shifted c (jTaskTop g c) (jTaskH g c) dx dy i1 i2 hposcol hposgap hidx
    · -- task group vs people: exempt when the people card belongs to this task
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hp2
        (hidm2.symm.trans hid2)
      rw [hsb2] at hpar2
      rw [hparP2] at hpar2
      obtain ⟨srcT2, hsrcT2, _, hidT2, _, hparOK2⟩ := task_source m c g hi htk2
      obtain ⟨outT2, houtT2, hidOutT, hparOutT⟩ := dump_of_source hwf h hsrcT2
      have hlookT : result.scene.layoutDump.box? tt2.id = some outT2 := by
        rw [hidT2.symm.trans hidOutT.symm]
        exact hlookup outT2 houtT2
      have hownerNe2 : tt2.id ≠ "" := fun he => hids_ne srcT2 hsrcT2 (hidT2.trans he)
      rcases hparOK2 with hroot2 | hmem2
      · have hancO : result.scene.layoutDump.ancestors o.id = [tt2.id] :=
          ancestors_single (hlookup o homem) hpar2 hownerNe2 hlookT
            (hparOutT.trans hroot2)
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn1
        by_cases hEq : tt1.id = tt2.id
        · exact (hn1 (hidg.trans hEq)).elim
        · have hidx : i1 ≠ i2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
            have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
            rw [he] at h1
            rw [h1] at h2
            have h3 : tt1 = tt2 := Option.some.inj h2
            exact hEq (by rw [h3])
          rw [hrectg, hrect2, task_rect_lookup' c g htk1]
          exact card_people_disjoint c (jTaskTop g c) (jTaskH g c) dx dy g i1 i2 tt2
            hidx hposcol hposgap (hpc tt2 i2 htk2)
      · obtain ⟨sc, hsc, hidsc⟩ := List.mem_map.mp hmem2
        obtain ⟨j2s, hj2s⟩ := List.mem_iff_getElem?.mp hsc
        have hsecO : (sc, j2s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj2s
        obtain ⟨srcSec, hsrcSec, _, hidSec⟩ := section_source m c g hi hsecO
        obtain ⟨outSec, houtSec, hidOutS, hparOutS⟩ := dump_of_source hwf h hsrcSec
        have hrootSec : outSec.parent = "" :=
          hparOutS.trans (source_parent_of_section hwf hi hsrcSec hsecO hidSec)
        have hsNe : sc.id ≠ "" := fun he => hids_ne srcSec hsrcSec (hidSec.trans he)
        have hancO : result.scene.layoutDump.ancestors o.id = [tt2.id, sc.id] :=
          ancestors_double (hlookup o homem) hpar2 hownerNe2 hlookT
            (hparOutT.trans hidsc.symm) hsNe
            (by rw [← hidOutS.trans hidSec]; exact hlookup outSec houtSec) hrootSec
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn1
        by_cases hEq : tt1.id = tt2.id
        · exact (hn1.1 (hidg.trans hEq)).elim
        · have hidx : i1 ≠ i2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
            have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
            rw [he] at h1
            rw [h1] at h2
            have h3 : tt1 = tt2 := Option.some.inj h2
            exact hEq (by rw [h3])
          rw [hrectg, hrect2, task_rect_lookup' c g htk1]
          exact card_people_disjoint c (jTaskTop g c) (jTaskH g c) dx dy g i1 i2 tt2
            hidx hposcol hposgap (hpc tt2 i2 htk2)
  · -- the group box is a people card
    obtain ⟨srcg, hsrcg, hidmg, _, hparg, _⟩ := hmeta gb hgmem
    have hsb := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcg hp1
      (hidmg.symm.trans hidg)
    rw [hsb] at hparg
    rw [hparP1] at hparg
    obtain ⟨srcT1, hsrcT1, _, hidT1, hband1, hparOK1⟩ := task_source m c g hi htk1
    have hownerNe1 : tt1.id ≠ "" := fun he => hids_ne srcT1 hsrcT1 (hidT1.trans he)
    obtain ⟨outT1, houtT1, hidOutT1, hparOutT1⟩ := dump_of_source hwf h hsrcT1
    have hlookT1 : result.scene.layoutDump.box? tt1.id = some outT1 := by
      rw [hidT1.symm.trans hidOutT1.symm]
      exact hlookup outT1 houtT1
    rcases origin_shape (hplaced o homem) with ⟨s2, j2, hsec2, hid2, hrect2⟩ |
      ⟨t2, ht2, hid2, hrect2⟩ |
      ⟨tt2, i2, htk2, hid2, hrect2⟩ |
      ⟨p2, hp2, tt2, i2, htk2, hk2, hid2, hparP2, hrect2⟩
    · -- people group vs section frame: exempt when the owner sits in that section
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      have hsp2 := source_parent_of_section hwf hi hsrcO hsec2 (hidm2.symm.trans hid2)
      rcases hparOK1 with hroot1 | hmem1
      · have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id] :=
          ancestors_single (hlookup gb hgmem) hparg hownerNe1 hlookT1
            (hparOutT1.trans hroot1)
        rw [hancg] at hn2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
        have hb : tt1.band = (-1 : Int) :=
          root_band hwf hi hsrcT1 hidOutT1 hparOutT1 htk1
            (hidOutT1.trans hidT1) (hparOutT1.trans hroot1)
        obtain ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ := hdataSec s2 j2 hsec2
        rw [hrectg, hrect2]
        exact disjoint_symm (frame_people_disjoint_of_data g c (jTop g c) (jTaskTop g c)
          (jTaskH g c) dx dy j2 ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ hposcol hposgap htk1
          (by rw [hb]; omega) (hpc tt1 i1 htk1))
      · obtain ⟨sc1, hsc1, hidsc1⟩ := List.mem_map.mp hmem1
        obtain ⟨j1s, hj1s⟩ := List.mem_iff_getElem?.mp hsc1
        have hsec1z : (sc1, j1s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj1s
        obtain ⟨srcSec1, hsrcSec1, _, hidSec1⟩ := section_source m c g hi hsec1z
        obtain ⟨outSec1, houtSec1, hidOutS1, hparOutS1⟩ := dump_of_source hwf h hsrcSec1
        have hrootSec1 : outSec1.parent = "" :=
          hparOutS1.trans (source_parent_of_section hwf hi hsrcSec1 hsec1z hidSec1)
        have hsNe1 : sc1.id ≠ "" := fun he => hids_ne srcSec1 hsrcSec1 (hidSec1.trans he)
        have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id, sc1.id] :=
          ancestors_double (hlookup gb hgmem) hparg hownerNe1 hlookT1
            (hparOutT1.trans hidsc1.symm) hsNe1
            (by rw [← hidOutS1.trans hidSec1]; exact hlookup outSec1 houtSec1) hrootSec1
        rw [hancg] at hn2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn2
        by_cases hEq : sc1.id = s2.id
        · exact (hn2.2 (hid2.trans hEq.symm)).elim
        · have hbandOwner : tt1.band = (j1s : Int) :=
            sectioned_band hwf hi hsrcT1 hidOutT1 hparOutT1 htk1
              (hidOutT1.trans hidT1) hsec1z
              (hparOutT1.trans hidsc1.symm) hsNe1
          have hj : j1s ≠ j2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp hsec1z
            have h2 := List.mem_zipIdx_iff_getElem?.mp hsec2
            rw [he] at h1
            rw [h1] at h2
            have h3 : sc1 = s2 := Option.some.inj h2
            exact hEq (by rw [h3])
          obtain ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ := hdataSec s2 j2 hsec2
          rw [hrectg, hrect2]
          exact disjoint_symm (frame_people_disjoint_of_data g c (jTop g c) (jTaskTop g c)
            (jTaskH g c) dx dy j2 ⟨f2, l2, hr2, hle2, hlt2, hg2⟩ hposcol hposgap htk1
            (by rw [hbandOwner]; omega) (hpc tt1 i1 htk1))
    · rw [hrectg, hrect2, title_rect_value ht2]
      have hle : t2.caption.h ≤ jTaskTop g c :=
        jTaskTop_ge_title g c (Int.le_of_lt hss) hbandHeight0 ht2
      have hd := title_people_disjoint c g (jTaskTop g c) (jTaskH g c) dx dy ht2 hle
        (hpc tt1 i1 htk1)
      rw [title_rect_value ht2] at hd
      apply disjoint_symm
      exact hd
    · -- people group vs task card: exempt when this is the owner task
      obtain ⟨srcO, hsrcO, hidm2, _, hpar2, _⟩ := hmeta o homem
      obtain ⟨srcT2, hsrcT2, _, hidT2, _, hparOK2⟩ := task_source m c g hi htk2
      have hsb2 := source_id_unique m.boxes (Model.boxIds_nodup hwf) hsrcO hsrcT2
        (hidm2.symm.trans (hid2.trans hidT2.symm))
      rw [hsb2] at hpar2
      have hexempt : tt2.id = tt1.id → False := by
        intro hEq
        rcases hparOK1 with hroot1 | hmem1
        · have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id] :=
            ancestors_single (hlookup gb hgmem) hparg hownerNe1 hlookT1
              (hparOutT1.trans hroot1)
          rw [hancg] at hn2
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
          exact hn2 (hid2.trans hEq)
        · obtain ⟨sc1, hsc1, hidsc1⟩ := List.mem_map.mp hmem1
          obtain ⟨j1s, hj1s⟩ := List.mem_iff_getElem?.mp hsc1
          have hsec1z : (sc1, j1s) ∈ g.sections.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr hj1s
          obtain ⟨srcSec1, hsrcSec1, _, hidSec1⟩ := section_source m c g hi hsec1z
          obtain ⟨outSec1, houtSec1, hidOutS1, hparOutS1⟩ := dump_of_source hwf h hsrcSec1
          have hrootSec1 : outSec1.parent = "" :=
            hparOutS1.trans (source_parent_of_section hwf hi hsrcSec1 hsec1z hidSec1)
          have hsNe1 : sc1.id ≠ "" := fun he => hids_ne srcSec1 hsrcSec1 (hidSec1.trans he)
          have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id, sc1.id] :=
            ancestors_double (hlookup gb hgmem) hparg hownerNe1 hlookT1
              (hparOutT1.trans hidsc1.symm) hsNe1
              (by rw [← hidOutS1.trans hidSec1]; exact hlookup outSec1 houtSec1) hrootSec1
          rw [hancg, ← hEq] at hn2
          exact hn2 (by simp [hid2])
      rcases hparOK2 with hroot2 | hmem2
      · have hancO : result.scene.layoutDump.ancestors o.id = [] :=
          ancestors_root (hlookup o homem) (hpar2.trans hroot2)
        rw [hancO] at hn1
        simp only [List.not_mem_nil] at hn1
        by_cases hEq : tt2.id = tt1.id
        · exact (hexempt hEq).elim
        · have hidx : i1 ≠ i2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
            have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
            rw [he] at h1
            rw [h1] at h2
            have h3 : tt1 = tt2 := Option.some.inj h2
            exact hEq (by rw [h3])
          rw [hrectg, hrect2, task_rect_lookup' c g htk2]
          exact disjoint_symm (card_people_disjoint c (jTaskTop g c) (jTaskH g c) dx dy g
            i2 i1 tt1 (Ne.symm hidx) hposcol hposgap (hpc tt1 i1 htk1))
      · obtain ⟨sc, hsc, hidsc⟩ := List.mem_map.mp hmem2
        obtain ⟨j2s, hj2s⟩ := List.mem_iff_getElem?.mp hsc
        have hsecO : (sc, j2s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj2s
        obtain ⟨srcSec, hsrcSec, _, hidSec⟩ := section_source m c g hi hsecO
        obtain ⟨outSec, houtSec, hidOutS, hparOutS⟩ := dump_of_source hwf h hsrcSec
        have hrootSec : outSec.parent = "" :=
          hparOutS.trans (source_parent_of_section hwf hi hsrcSec hsecO hidSec)
        have hsNe : sc.id ≠ "" := fun he => hids_ne srcSec hsrcSec (hidSec.trans he)
        have hancO : result.scene.layoutDump.ancestors o.id = [sc.id] :=
          ancestors_single (hlookup o homem) (hpar2.trans hidsc.symm) hsNe
            (by rw [← hidOutS.trans hidSec]; exact hlookup outSec houtSec) hrootSec
        rw [hancO] at hn1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn1
        by_cases hEq : tt2.id = tt1.id
        · exact (hexempt hEq).elim
        · have hidx : i1 ≠ i2 := by
            intro he
            have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
            have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
            rw [he] at h1
            rw [h1] at h2
            have h3 : tt1 = tt2 := Option.some.inj h2
            exact hEq (by rw [h3])
          rw [hrectg, hrect2, task_rect_lookup' c g htk2]
          exact disjoint_symm (card_people_disjoint c (jTaskTop g c) (jTaskH g c) dx dy g
            i2 i1 tt1 (Ne.symm hidx) hposcol hposgap (hpc tt1 i1 htk1))
    · -- people group vs people card: same-owner pairs are mutual ancestors
      have hexemptAndSep : ∀ hidx : i1 ≠ i2,
          Disjoint (shiftRect dx dy (peopleBox c g tt1 i1))
            (shiftRect dx dy (peopleBox c g tt2 i2)) :=
        fun hidx =>
          people_people_disjoint c (jTaskTop g c) (jTaskH g c) dx dy g i1 i2 tt1 tt2 hidx
            hposcol hposgap (hpc tt1 i1 htk1) (hpc tt2 i2 htk2)
      rcases hparOK1 with hroot1 | hmem1
      · have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id] :=
          ancestors_single (hlookup gb hgmem) hparg hownerNe1 hlookT1
            (hparOutT1.trans hroot1)
        rw [hancg] at hn2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
        by_cases hidxEq : i1 = i2
        · exfalso
          have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
          have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
          rw [hidxEq] at h1
          rw [h1] at h2
          have h3 : tt1 = tt2 := Option.some.inj h2
          have hsame := people_boxes_same_task_eq h hp1 hp2 hk1 hk2
            (by rw [hparP1, hparP2, h3])
          exact oidne (by rw [hidg, hid2, hsame])
        · rw [hrectg, hrect2]
          exact hexemptAndSep (by omega)
      · obtain ⟨sc1, hsc1, hidsc1⟩ := List.mem_map.mp hmem1
        obtain ⟨j1s, hj1s⟩ := List.mem_iff_getElem?.mp hsc1
        have hsec1z : (sc1, j1s) ∈ g.sections.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hj1s
        obtain ⟨srcSec1, hsrcSec1, _, hidSec1⟩ := section_source m c g hi hsec1z
        obtain ⟨outSec1, houtSec1, hidOutS1, hparOutS1⟩ := dump_of_source hwf h hsrcSec1
        have hrootSec1 : outSec1.parent = "" :=
          hparOutS1.trans (source_parent_of_section hwf hi hsrcSec1 hsec1z hidSec1)
        have hsNe1 : sc1.id ≠ "" := fun he => hids_ne srcSec1 hsrcSec1 (hidSec1.trans he)
        have hancg : result.scene.layoutDump.ancestors gb.id = [tt1.id, sc1.id] :=
          ancestors_double (hlookup gb hgmem) hparg hownerNe1 hlookT1
            (hparOutT1.trans hidsc1.symm) hsNe1
            (by rw [← hidOutS1.trans hidSec1]; exact hlookup outSec1 houtSec1) hrootSec1
        rw [hancg] at hn2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn2
        by_cases hidxEq : i1 = i2
        · exfalso
          have h1 := List.mem_zipIdx_iff_getElem?.mp htk1
          have h2 := List.mem_zipIdx_iff_getElem?.mp htk2
          rw [hidxEq] at h1
          rw [h1] at h2
          have h3 : tt1 = tt2 := Option.some.inj h2
          have hsame := people_boxes_same_task_eq h hp1 hp2 hk1 hk2
            (by rw [hparP1, hparP2, h3])
          exact oidne (by rw [hidg, hid2, hsame])
        · rw [hrectg, hrect2]
          exact hexemptAndSep (by omega)


end Elegant.Kinds.JourneySceneFacts
