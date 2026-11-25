import Elegant.Layered.LaneBandsRouteClausesProof
import Elegant.Layered.LaneBandsFindRouteClearProof
import Elegant.GridSimplify

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace LaneBands

private theorem frfT_orth_of_pairs : ∀ (l : List Point), (∀ a b : Point, (a, b) ∈ l.zip l.tail → a.x = b.x ∨ a.y = b.y) → Polyline.isOrthogonal l = true
  | [], _ => rfl
  | [_], _ => rfl
  | p :: q :: rest, h => by
    rw [Polyline.isOrthogonal_cons, Bool.and_eq_true]
    have hmem : (p, q) ∈ (p :: q :: rest).zip (p :: q :: rest).tail := by simp
    have hfirst : p.x = q.x ∨ p.y = q.y := h p q hmem
    have hhead : (p.x = q.x || p.y = q.y) = true := by simpa only [Bool.or_eq_true, decide_eq_true_eq] using hfirst
    refine ⟨hhead, frfT_orth_of_pairs (q :: rest) ?_⟩
    intro a b hmem2
    have heq : ((p :: q :: rest).zip (p :: q :: rest).tail) = (p, q) :: ((q :: rest).zip (q :: rest).tail) := by simp
    have hmem' : (a, b) ∈ ((p :: q :: rest).zip (p :: q :: rest).tail) := by rw [heq]; exact List.mem_cons_of_mem _ hmem2
    exact h a b hmem'

private theorem frfT_last_append (xs : List Point) (p : Point) : (xs ++ [p]).getLast? = some p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [List.cons_append, List.getLast?_cons_cons]
      exact ih

theorem findRouteOrthoPin_holds : FindRouteOrthoPin := by
  intro axis sp pin fb tb original ends obs bend pts hends hfind
  have hpair := findRoute_orthogonal axis sp pin fb tb original ends hends obs bend pts hfind
  exact frfT_orth_of_pairs pts hpair

theorem findRouteEndsPin_holds : FindRouteEndsPin := by
  intro axis sp pin fb tb original ends obs bend pts hends hfind
  obtain ⟨_, _, _, _, _, _, _, hpoly, _⟩ := findRoute_ok_node axis ends obs bend [sp.slot, 0] pts hfind
  rw [routePolyline.eq_def] at hpoly
  obtain ⟨middle, _hmap, hrest⟩ := bindOk_inv hpoly
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hrest
  subst hrest
  have hraw_head : ([ends.source] ++ middle ++ [ends.target]).head? = some ends.source := by simp
  have hassoc : ([ends.source] ++ middle ++ [ends.target]) = (([ends.source] ++ middle) ++ [ends.target]) := by rw [List.append_assoc]
  have hraw_last : ([ends.source] ++ middle ++ [ends.target]).getLast? = some ends.target := by rw [hassoc]; exact frfT_last_append ([ends.source] ++ middle) ends.target
  have hhead : (simplifyPoints ([ends.source] ++ middle ++ [ends.target])).head? = ([ends.source] ++ middle ++ [ends.target]).head? := by rw [simplifyPoints_eq_simplify]; exact (Grid.simplify_endpoints _).1
  have hlast : (simplifyPoints ([ends.source] ++ middle ++ [ends.target])).getLast? = ([ends.source] ++ middle ++ [ends.target]).getLast? := by rw [simplifyPoints_eq_simplify]; exact (Grid.simplify_endpoints _).2
  rw [hhead, hraw_head, hlast, hraw_last]
  exact ⟨rfl, rfl⟩

end LaneBands
end Layered
end Elegant
