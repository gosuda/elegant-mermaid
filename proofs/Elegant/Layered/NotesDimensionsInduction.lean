import Elegant.Layered.CoordGraph
import Elegant.Layered.NotesDimensionsTransport

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

private theorem notesMapM_output_origin {α β : Type} {f : α → Except LayoutError β}
    {source : List α} {output : List β} (h : source.mapM f = .ok output)
    {value : β} (hMember : value ∈ output) :
    ∃ entry ∈ source, f entry = .ok value := by
  obtain ⟨hLength, hRuns⟩ := mapM_getElem? f source output h
  obtain ⟨i, hIndex⟩ := List.mem_iff_getElem?.mp hMember
  obtain ⟨hOutputBound, _⟩ := List.getElem?_eq_some_iff.mp hIndex
  have hSourceBound : i < source.length := hLength ▸ hOutputBound
  have hSourceLookup : source[i]? = some source[i] :=
    List.getElem?_eq_getElem hSourceBound
  obtain ⟨actual, hRun, hOutputLookup⟩ := hRuns i source[i] hSourceLookup
  have hValue : actual = value := Option.some.inj (hOutputLookup.symm.trans hIndex)
  subst actual
  exact ⟨source[i], List.getElem_mem hSourceBound, hRun⟩

/-- A successful bundle runs the recursive layout on its top subtree and the base layout
on each individual note. -/
theorem bundleLayout_part_note_runs
    {recur base : Input → Options → Except LayoutError FamilyResult}
    {inp : Input} {o : Options} {margin gap : Int} {b : Bundle} {l : BundleLayout}
    (h : bundleLayout recur base inp o margin gap b = .ok l) :
    recur (subInput inp
      (fun x => x.id == l.top.id || Compound.inside inp.boxes l.top.id x.id) l.top.id) o =
        .ok l.part ∧
      ∀ q ∈ l.notes, base (subInput inp (fun x => x.id == q.1.id) q.1.id) o = .ok q.2 := by
  unfold bundleLayout at h
  cases hTop : inp.boxes[b.target]? with
  | none =>
    rw [hTop] at h
    simp at h
  | some top =>
    rw [hTop] at h
    obtain ⟨part, hPart, h⟩ := bind_ok' h
    obtain ⟨notes, hNotes, h⟩ := bind_ok' h
    have hLayout : (⟨top, b, part, notes, _⟩ : BundleLayout) = l := Except.ok.inj h
    subst l
    refine ⟨hPart, ?_⟩
    intro q hq
    obtain ⟨a, _, hRun⟩ := notesMapM_output_origin hNotes hq
    cases hBox : inp.boxes[a.note]? with
    | none =>
      rw [hBox] at hRun
      simp at hRun
    | some box =>
      rw [hBox] at hRun
      obtain ⟨note, hNote, hRun⟩ := bind_ok' hRun
      have hPair : (box, note) = q := Except.ok.inj hRun
      subst q
      exact hNote

/-- Successful note layout preserves the dimension guarantee of every actual base call. -/
theorem layoutNotes_boxes_nonneg
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hBase : ∀ ids inp o res, base ids inp o = .ok res →
      ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds fuel inp o = .ok res) :
    ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h := by
  induction fuel generalizing inp o res with
  | zero => exact hBase exactIds inp o res h
  | succ fuel ih =>
    rcases layoutNotes_success_phases h with ⟨_, hDirect⟩ | hexecution
    · exact hBase exactIds inp o res hDirect
    · obtain ⟨e⟩ := hexecution
      refine e.boxes_nonneg (hBase _ _ _ _ e.contracted_eq) ?_
      intro p hp
      rw [e.fragments_eq] at hp
      obtain ⟨l, hl, hPlaced⟩ := placedFlatten_mem e.placed_eq hp
      obtain ⟨_, _, hLayout⟩ := notesMapM_output_origin e.layouts_eq hl
      obtain ⟨hPart, hNotes⟩ := bundleLayout_part_note_runs hLayout
      rcases placedOf_scene hPlaced with hScene | ⟨q, hq, hScene⟩
      · rw [hScene]
        exact ih hPart
      · rw [hScene]
        exact hBase _ _ _ _ (hNotes q hq)

/-- Lookups in the router's rectangle table inherit the successful note layout's bounds. -/
theorem layoutNotes_rects_lookup_nonneg
    {base : List String → Input → Options → Except LayoutError FamilyResult}
    (hBase : ∀ ids inp o res, base ids inp o = .ok res →
      ∀ b ∈ res.scene.boxes, 0 ≤ b.rect.w ∧ 0 ≤ b.rect.h)
    {exactIds : List String} {fuel : Nat} {inp : Input} {o : Options} {res : FamilyResult}
    (h : layoutNotes base exactIds fuel inp o = .ok res)
    {id : String} {rect : Rect}
    (hLookup : (notesRectsOf res.scene.boxes).lookup id = some rect) :
    0 ≤ rect.w ∧ 0 ≤ rect.h := by
  obtain ⟨before, _, hSplit, _⟩ := List.lookup_eq_some_iff.mp hLookup
  have hPair : (id, rect) ∈ notesRectsOf res.scene.boxes := by
    rw [hSplit]
    exact List.mem_append_right before List.mem_cons_self
  change (id, rect) ∈ res.scene.boxes.map (fun b => (b.id, b.rect)) at hPair
  obtain ⟨b, hb, hEntry⟩ := List.mem_map.mp hPair
  have hRect : b.rect = rect := congrArg Prod.snd hEntry
  rw [← hRect]
  exact layoutNotes_boxes_nonneg hBase h b hb

end PipelineImpl
end Layered
end Elegant
