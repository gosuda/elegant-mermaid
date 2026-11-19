import Elegant.Kinds.Common
import Elegant.Chart.Venn

set_option autoImplicit false

namespace Elegant.Kinds.Venn

def layout (m : Model) : Except LayoutFailure Layered.FamilyResult :=
  if m.boxes.any (·.exclusive) then .error (.geometry .domain)
  else if m.boxes.any (fun b => if b.id == "venn" then b.parent != "" else b.parent != "venn") then
    .error (.geometry .domain)
  else if m.boxes.any (fun b => b.role != .node) then .error (.geometry .domain)
  else if Chart.Venn.config m "width" 800 < 0 ∨ Chart.Venn.config m "height" 450 < 0 then
    .error (.geometry .domain)
  else match Chart.Venn.layout m with
    | .error e => .error (.geometry e)
    | .ok r => .ok { scene := Chart.Venn.sceneOf m r, budgetExhausted := false }

theorem successful_nonexclusive (m : Model) (s : Layered.FamilyResult)
    (h : layout m = .ok s) : m.boxes.any (·.exclusive) = false := by
  by_cases he : m.boxes.any (·.exclusive) = true
  · simp [layout, he] at h
  · exact Bool.eq_false_iff.mpr he

theorem successful_parents (m : Model) (s : Layered.FamilyResult)
    (h : layout m = .ok s) :
    m.boxes.any (fun b => if b.id == "venn" then b.parent != "" else b.parent != "venn") = false := by
  have he := successful_nonexclusive m s h
  by_cases hp : m.boxes.any (fun b =>
      if b.id == "venn" then b.parent != "" else b.parent != "venn") = true
  · simp only [layout, he, hp, Bool.false_eq_true, ite_false, ite_true] at h
    cases h
  · exact Bool.eq_false_iff.mpr hp

theorem successful_roles (m : Model) (s : Layered.FamilyResult)
    (h : layout m = .ok s) : m.boxes.any (fun b => b.role != .node) = false := by
  have he := successful_nonexclusive m s h
  have hp := successful_parents m s h
  by_cases hr : m.boxes.any (fun b => b.role != .node) = true
  · simp only [layout, he, hp, hr, Bool.false_eq_true, ite_false, ite_true] at h
    cases h
  · exact Bool.eq_false_iff.mpr hr

theorem successful_dimensions (m : Model) (s : Layered.FamilyResult)
    (h : layout m = .ok s) :
    0 ≤ Chart.Venn.config m "width" 800 ∧ 0 ≤ Chart.Venn.config m "height" 450 := by
  have he := successful_nonexclusive m s h
  have hp := successful_parents m s h
  have hr := successful_roles m s h
  by_cases hn : Chart.Venn.config m "width" 800 < 0 ∨ Chart.Venn.config m "height" 450 < 0
  · simp only [layout, he, hp, hr, Bool.false_eq_true, ite_false, hn, ite_true] at h
    cases h
  · omega

theorem successful_scene (m : Model) (s : Layered.FamilyResult)
    (h : layout m = .ok s) :
    ∃ r, Chart.Venn.layout m = .ok r ∧ s.scene = Chart.Venn.sceneOf m r := by
  have he := successful_nonexclusive m s h
  have hp := successful_parents m s h
  have hr := successful_roles m s h
  have hd := successful_dimensions m s h
  have hn : ¬ (Chart.Venn.config m "width" 800 < 0 ∨ Chart.Venn.config m "height" 450 < 0) := by
    omega
  simp only [layout, he, hp, hr, Bool.false_eq_true, ite_false, ite_eq_right hn] at h
  cases hg : Chart.Venn.layout m with
  | error e => simp only [hg] at h; cases h
  | ok r =>
    simp only [hg, Except.ok.injEq] at h
    subst s
    exact ⟨r,rfl,rfl⟩

end Elegant.Kinds.Venn
