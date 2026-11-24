import Elegant.Layered.VisibilityPredecessorRun
import Elegant.Layered.VisibilityChainSource
import Elegant.Layered.NotesRouterEndsProof

set_option autoImplicit false

namespace Elegant.Layered.Visibility

theorem newGrid_shortest_start_mem {obstacles : List Rect} {points starts ends pts : List Point}
    {bound : Option Rect} (h : (newGrid obstacles points bound).shortest starts ends = some pts) :
    ∃ p ∈ starts, pts.head? = some p := by
  unfold Grid.shortest at h
  obtain ⟨seeded, hseed, hrest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨last, s⟩, hrun, hpath⟩ := Option.bind_eq_some_iff.mp hrest
  have hpts : compress ((newGrid obstacles points bound).chain s.prev (s.prev.size + 1) last []) =
      pts := Option.some.inj hpath
  have hstrict := newGrid_seed_run_prev_dist_strict hseed hrun
  obtain ⟨hnonnegative, hreached⟩ := Grid.seed_run_distances hseed hrun
  have hseeded := seed_run_roots hseed hrun
  obtain ⟨p, hp, hhead⟩ := Grid.chain_head_seeded hstrict hnonnegative hseeded hreached
  refine ⟨p, hp, ?_⟩
  rw [← hpts]
  exact (Elegant.Layered.PipelineImpl.nrep_compress_endpoints _).1.trans hhead

end Elegant.Layered.Visibility
