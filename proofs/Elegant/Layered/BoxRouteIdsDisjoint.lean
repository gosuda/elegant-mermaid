import Elegant.Layered.SelectFacts
import Elegant.Layered.RecursiveCallContext

set_option autoImplicit false

/-!
# Box/route id disjointness of the recursion sub-inputs

Engine-built models keep the two id namespaces apart (a flowchart whose
nodes are named `e0, e1, e2` numbers its routes `e3, e4, e5`), but
`modelWellFormed` does not state it, so it travels as an explicit input
premise. Both recursion sub-inputs preserve it: `selectInput` keeps
sublists of the input boxes and routes with the same ids, and
`parentSubInput` only appends fixed side tables, leaving boxes and routes
untouched.
-/

namespace Elegant.Layered.PipelineImpl

/-- No box id names a route id. -/
def BoxRouteIdsDisjoint (inp : Input) : Prop :=
  ∀ id ∈ inp.boxes.map (·.id), id ∉ inp.routes.map (·.id)

theorem BoxRouteIdsDisjoint.childSubInput {inp : Input} (h : BoxRouteIdsDisjoint inp)
    (group : ModelBox) : BoxRouteIdsDisjoint (childSubInput inp group) := by
  intro id hid hcon
  unfold _root_.Elegant.Layered.PipelineImpl.childSubInput at hid
  unfold _root_.Elegant.Layered.PipelineImpl.childSubInput at hcon
  rw [selectInput_box_ids] at hid
  obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hid
  have hbIn : b.id ∈ inp.boxes.map (·.id) :=
    List.mem_map.mpr ⟨b, (List.mem_filter.mp hb).1, rfl⟩
  have hnot := h b.id hbIn
  obtain ⟨r, hr, hreq⟩ := List.mem_map.mp hcon
  have hrIn : r ∈ inp.routes :=
    ((selectInput_route_mem inp _ _ r).mp hr).1
  have hmem : r.id ∈ inp.routes.map (·.id) := List.mem_map.mpr ⟨r, hrIn, rfl⟩
  rw [hreq, ← hbeq] at hmem
  exact hnot hmem

theorem BoxRouteIdsDisjoint.parentSubInput {inp : Input} (h : BoxRouteIdsDisjoint inp)
    (group : ModelBox) (P : Params) (titleLines : List Measure.Line)
    (child : FamilyResult) :
    BoxRouteIdsDisjoint (parentSubInput inp group P titleLines child) := by
  have hPB : (_root_.Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).boxes =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").boxes := rfl
  have hPR : (_root_.Elegant.Layered.PipelineImpl.parentSubInput inp group P titleLines child).routes =
      (selectInput inp (fun box => !Compound.inside inp.boxes group.id box.id) "").routes := rfl
  intro id hid hcon
  rw [hPB, selectInput_box_ids] at hid
  obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hid
  have hbIn : b.id ∈ inp.boxes.map (·.id) :=
    List.mem_map.mpr ⟨b, (List.mem_filter.mp hb).1, rfl⟩
  have hnot := h b.id hbIn
  rw [hPR] at hcon
  obtain ⟨r, hr, hreq⟩ := List.mem_map.mp hcon
  have hrIn : r ∈ inp.routes :=
    ((selectInput_route_mem inp _ _ r).mp hr).1
  have hmem : r.id ∈ inp.routes.map (·.id) := List.mem_map.mpr ⟨r, hrIn, rfl⟩
  rw [hreq, ← hbeq] at hmem
  exact hnot hmem

end Elegant.Layered.PipelineImpl
