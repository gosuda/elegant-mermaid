import Elegant.Layered.VisibilityPredecessorCost
import Elegant.Layered.VisibilityFrontierBounds

set_option autoImplicit false

namespace Elegant.Layered.Visibility

local instance : LawfulBEq Cost where
  rfl := by deriving_ReflEq_tactic
  eq_of_beq := by deriving_LawfulEq_tactic

theorem Grid.run_prev_dist_strict {g : Grid} {ends : List Point} {fuel : Nat}
    {s out : Search} {last : Vertex}
    (xUnique : g.xs.toList.Nodup) (yUnique : g.ys.toList.Nodup)
    (hf : FrontierBounds g s.frontier) (hs : PrevDistStrict s)
    (hrun : g.run ends fuel s = some (last, out)) : PrevDistStrict out := by
  induction fuel generalizing s with
  | zero => simp [Grid.run] at hrun
  | succ fuel ih =>
      unfold Grid.run at hrun
      split at hrun
      · simp at hrun
      · rename_i entry rest hpop
        obtain ⟨he, hrest⟩ := popMin_bounds hf hpop
        have hremaining : FrontierBounds g ({ s with frontier := rest } : Search).frontier :=
          hrest
        have hstrict : PrevDistStrict { s with frontier := rest } := hs
        dsimp only at hrun
        split at hrun
        · exact ih hremaining hstrict hrun
        · rename_i current hdist
          split at hrun
          · exact ih hremaining hstrict hrun
          · rename_i hmatching
            split at hrun
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              rw [← hrun.2]
              exact hstrict
            · have hcost : current = entry.cost :=
                bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hmatching)
              have hentry : ({ s with frontier := rest } : Search).dist[entry.vertex]? =
                  some entry.cost := hcost ▸ hdist
              exact ih (relax_bounds he hremaining)
                (Grid.relax_prev_dist_strict xUnique yUnique he.1 he.2 hstrict hentry).1 hrun

theorem Grid.seed_run_prev_dist_strict {g : Grid} {starts ends : List Point} {fuel : Nat}
    {seeded out : Search} {last : Vertex}
    (xUnique : g.xs.toList.Nodup) (yUnique : g.ys.toList.Nodup)
    (hseed : g.seed starts = some seeded)
    (hrun : g.run ends fuel seeded = some (last, out)) : PrevDistStrict out :=
  Grid.run_prev_dist_strict xUnique yUnique (seed_bounds hseed)
    (Grid.seed_prev_dist_strict hseed) hrun

theorem newGrid_seed_run_prev_dist_strict {obstacles : List Rect} {points starts ends : List Point}
    {bound : Option Rect} {fuel : Nat} {seeded out : Search} {last : Vertex}
    (hseed : (newGrid obstacles points bound).seed starts = some seeded)
    (hrun : (newGrid obstacles points bound).run ends fuel seeded = some (last, out)) :
    PrevDistStrict out :=
  let unique := newGrid_nodup obstacles points bound
  Grid.seed_run_prev_dist_strict unique.1 unique.2 hseed hrun

end Elegant.Layered.Visibility
