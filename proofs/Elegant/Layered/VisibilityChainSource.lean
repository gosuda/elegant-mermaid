import Elegant.Layered.VisibilitySeededRoots
import Elegant.Layered.VisibilityNonnegativeCosts
import Elegant.Layered.VisibilityPredecessorCost
import Elegant.Layered.VisibilityChainTermination

set_option autoImplicit false

namespace Elegant.Layered.Visibility

theorem Grid.chain_head_seeded {g : Grid} {starts : List Point} {s : Search} {v : Vertex}
    (hstrict : PrevDistStrict s) (hnonnegative : DistancesNonnegative s)
    (hseeded : SeededRoots g starts s) (hreached : ∃ cost : Cost, s.dist[v]? = some cost) :
    ∃ p ∈ starts, (g.chain s.prev (s.prev.size + 1) v []).head? = some p := by
  let rank (u : Vertex) : Nat := (s.dist[u]?.getD default).dist.toNat
  obtain ⟨root, hprev, ⟨cost, hdist⟩, hhead⟩ :=
    g.chain_head_root_of_rank_preserving s.prev v rank
      (fun u => ∃ cost : Cost, s.dist[u]? = some cost)
      (fun u p edge => DistancesNonnegative.rank_lt hnonnegative (hstrict u p edge))
      hreached (fun u p edge _ => by
        obtain ⟨parentCost, _, hparent, _, _⟩ := hstrict u p edge
        exact ⟨parentCost, hparent⟩)
  obtain ⟨p, hp, hvertex⟩ := hseeded root cost hdist hprev
  exact ⟨p, hp, hhead.trans (congrArg some (Grid.point_vertexAt hvertex))⟩

end Elegant.Layered.Visibility
