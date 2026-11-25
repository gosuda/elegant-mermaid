import Elegant.Kinds.Usecase

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

open Elegant.Kinds.Usecase (firstText)

theorem groupTitles_filterMap_firstText (groups : List Group) :
    groupTitles groups = groups.filterMap (fun group =>
      if group.role = .group then (firstText group.items).map (fun rect => (group.owner, rect))
      else none) := by
  unfold groupTitles
  apply congrArg (fun f : Group → Option (String × Rect) => groups.filterMap f)
  funext group
  change (if group.role != .group then none else
      (firstText group.items).bind (fun rect => some (group.owner, rect))) = _
  by_cases hrole : group.role = .group
  · cases htext : firstText group.items <;> simp [hrole]
  · simp [hrole]

theorem mem_groupTitles_iff {groups : List Group} {owner : String} {rect : Rect} :
    (owner, rect) ∈ groupTitles groups ↔
      ∃ group ∈ groups, group.owner = owner ∧ group.role = .group ∧
        firstText group.items = some rect := by
  rw [groupTitles_filterMap_firstText, List.mem_filterMap]
  constructor
  · rintro ⟨group, hmem, hentry⟩
    by_cases hrole : group.role = .group
    · rw [ite_eq_left hrole] at hentry
      obtain ⟨sourceRect, htext, hp⟩ := Option.map_eq_some_iff.mp hentry
      have hrect : sourceRect = rect := congrArg Prod.snd hp
      exact ⟨group, hmem, congrArg Prod.fst hp, hrole, hrect ▸ htext⟩
    · rw [ite_eq_right hrole] at hentry
      cases hentry
  · rintro ⟨group, hmem, howner, hrole, htext⟩
    exact ⟨group, hmem, by simp [howner, hrole, htext]⟩

/-- A duplicate key selects the first group of that owner with a text primitive. -/
theorem groupTitles_find?_firstText (groups : List Group) (owner : String) :
    (groupTitles groups).find? (fun title => title.1 == owner) =
      groups.findSome? (fun group =>
        if group.role = .group ∧ group.owner = owner then
          (firstText group.items).map (fun rect => (group.owner, rect))
        else none) := by
  rw [← List.head?_filter, groupTitles_filterMap_firstText, List.filter_filterMap,
    List.head?_filterMap]
  apply congrArg (fun f : Group → Option (String × Rect) => groups.findSome? f)
  funext group
  by_cases hrole : group.role = .group
  · simp only [hrole, true_and, ↓reduceIte]
    cases firstText group.items with
    | none => simp
    | some rect => simp only [Option.map_some, Option.filter_some, beq_iff_eq]
  · simp [hrole]

theorem groupTitles_find?_eq_none_iff {groups : List Group} {owner : String} :
    (groupTitles groups).find? (fun title => title.1 == owner) = none ↔
      ∀ group ∈ groups, group.owner = owner → group.role = .group →
        firstText group.items = none := by
  rw [groupTitles_find?_firstText, List.findSome?_eq_none_iff]
  constructor
  · intro h group hmem howner hrole
    have hentry := h group hmem
    rw [ite_eq_left ⟨hrole, howner⟩] at hentry
    exact Option.map_eq_none_iff.mp hentry
  · intro h group hmem
    by_cases hkey : group.role = .group ∧ group.owner = owner
    · rw [ite_eq_left hkey, h group hmem hkey.2 hkey.1, Option.map_none]
    · exact ite_eq_right hkey

theorem groupTitles_find?_of_firstText {groups : List Group} {group : Group} {rect : Rect}
    (hmem : group ∈ groups) (hrole : group.role = .group)
    (htext : firstText group.items = some rect)
    (howner : ∀ other ∈ groups, other.owner = group.owner → other.role = .group →
      other = group) :
    (groupTitles groups).find? (fun title => title.1 == group.owner) =
      some (group.owner, rect) := by
  cases hfind : (groupTitles groups).find? (fun title => title.1 == group.owner) with
  | none =>
    have hnone := (groupTitles_find?_eq_none_iff.mp hfind) group hmem rfl hrole
    rw [htext] at hnone
    cases hnone
  | some title =>
    obtain ⟨key, found⟩ := title
    have hpred : (key == group.owner) = true :=
      List.find?_some (p := fun title : String × Rect => title.fst == group.owner) hfind
    have hkey : key = group.owner := beq_iff_eq.mp hpred
    obtain ⟨other, hother, hotherOwner, hotherRole, hotherText⟩ :=
      mem_groupTitles_iff.mp (List.mem_of_find?_eq_some hfind)
    rw [howner other hother (hotherOwner.trans hkey) hotherRole, htext] at hotherText
    rw [hkey, Option.some.inj hotherText]

theorem groupTitles_find?_shiftRect (groups : List Group) (owner : String) (dx dy : Int) :
    ((groupTitles groups).map (fun title => (title.1, shiftRect dx dy title.2))).find?
        (fun title => title.1 == owner) =
      ((groupTitles groups).find? (fun title => title.1 == owner)).map
        (fun title => (title.1, shiftRect dx dy title.2)) :=
  List.find?_map

theorem firstText_groupItems (P : Params) (box : Rect) (lines : List Measure.Line) :
    firstText (groupItems P box lines) = some (titleRect P box lines) := rfl

theorem firstText_nodeItems (P : Params) (box : Rect) (lines : List Measure.Line) :
    firstText (nodeItems P box lines) =
      some ⟨box.x, box.y + Int.tdiv (box.h - (lines.length : Int) * P.lineH) 2,
        box.w, (lines.length : Int) * P.lineH⟩ := rfl

theorem firstText_nodeItems_shiftRect (P : Params) (box : Rect) (lines : List Measure.Line)
    (dx dy : Int) :
    firstText (nodeItems P (shiftRect dx dy box) lines) =
      (firstText (nodeItems P box lines)).map (shiftRect dx dy) := by
  simp only [firstText_nodeItems, Option.map_some, shiftRect, Int.add_right_comm]

private theorem firstText_replace_rect (items : List Primitive) (rect : Rect) :
    firstText (items.map fun item => match item with
      | .text text => .text { text with rect := rect }
      | _ => item) = (firstText items).map (fun _ => rect) := by
  unfold firstText
  rw [List.findSome?_map, List.map_findSome?]
  apply congrArg (fun f : Primitive → Option Rect => items.findSome? f)
  funext item
  cases item <;> rfl

/-- The title table selects by owner for every role, but cannot create a text primitive. -/
theorem applyTitles_getElem?_firstText (titles : List (String × Rect))
    {groups : List Group} {index : Nat} {source : Group}
    (hsource : groups[index]? = some source) :
    ∃ out, (applyTitles titles groups)[index]? = some out ∧
      out.owner = source.owner ∧ out.role = source.role ∧
      firstText out.items = (firstText source.items).map (fun rect =>
        match titles.find? (fun title => title.1 == source.owner) with
        | none => rect
        | some title => title.2) := by
  simp only [applyTitles, List.getElem?_map, hsource, Option.map_some]
  cases titles.find? (fun title => title.1 == source.owner) with
  | none => exact ⟨source, rfl, rfl, rfl, by cases firstText source.items <;> rfl⟩
  | some title => exact ⟨_, rfl, rfl, rfl, firstText_replace_rect source.items title.2⟩

theorem applyTitles_firstText_source {titles : List (String × Rect)}
    {groups : List Group} {out : Group} (hout : out ∈ applyTitles titles groups) :
    ∃ source ∈ groups, out.owner = source.owner ∧ out.role = source.role ∧
      firstText out.items = (firstText source.items).map (fun rect =>
        match titles.find? (fun title => title.1 == source.owner) with
        | none => rect
        | some title => title.2) := by
  obtain ⟨index, houtIndex⟩ := List.mem_iff_getElem?.mp hout
  have hindex : index < groups.length := by
    simpa only [applyTitles, List.length_map] using (List.getElem?_eq_some_iff.mp houtIndex).1
  let source := groups[index]
  have hsource : groups[index]? = some source := List.getElem?_eq_getElem hindex
  obtain ⟨applied, happlied, howner, hrole, htext⟩ :=
    applyTitles_getElem?_firstText titles hsource
  have heq : applied = out := Option.some.inj (happlied.symm.trans houtIndex)
  exact ⟨source, List.mem_of_getElem? hsource, heq ▸ howner, heq ▸ hrole, heq ▸ htext⟩

end Elegant.Layered.PipelineImpl
