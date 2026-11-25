import Elegant.Layered.RegionActualParts
import Elegant.Layered.RegionFoundation
import Elegant.Layered.RegionRunSpec
import Elegant.Layered.RegionSubInputStepC2
import Elegant.Layered.FamilyC5B
import Elegant.Layered.FamilyC5Measured

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

open RegionImpl

/-! # Region flat C5: route endpoints attach to their boxes (`layoutRIds`).

Packet P4 of `local://region-tower-plan.md` (field 5, `flatC5`).

Mirror of the exact twin `flatC5B_layoutX_closed`
(`ExactFlatC5Closed.lean`), whose reduction (`ExactFlatC5.lean:152-160`) needs
endpoint lookup over the rewritten graph `cg'`: `rankEquivalentR` orients
semantic edges against the constraint order, so `cg'.edges` endpoints are
swapped relative to `cg.edges` while only `decl` is preserved
(`componentRunR_edges_decls_factR` below). A literal replay looking ports up
by `cg.edges[i]` is false for oriented edges; the seam below is stated over
executed routes and their input `from`/`to` boxes.

Route: `RB_layout_ids` (`RegionSubInputStepC2.lean`) gives id preservation;
`componentRunR_specR` (`RegionRunSpec.lean`) gives the ranking disjunction,
from which `rfc5_edges_decls` proves `decl` preservation; the endpoint row
stays open as the single residual `R_ExecutedC5EndpointsR`, discharged by
`flatC5B_layoutRIds`.

Truth probes (`proofs/wip/Probe/RegionFlatC5TProbe.lean`, `lake env lean`):
- two-region witness: `decls` preserved, `c5 = true`.
- two-cycle witness (`a1->c1`, `c1->a1`): one edge swapped by the ranking
  rewrite, `decls` still preserved, `c5 = true`.
 - fixed-parent input (`exactIds = ["G1"]` naming a region parent with
   children): base layout fails the validator elsewhere, `c5 = true`, and only
   the local `framedParents` premise excludes it from the flat clauses.
 Clause probe (`proofs/wip/Probe/RegionFlatC5TClauseProbe.lean`): per-route
 decisions of every `GroupEndpointInvariantMeasured` clause (source/target
 membership, endpoint presence, dump-box lookup, both `onBoundary` facts)
 are all true on all eight region inputs, including the two-cycle rewrite.
-/

 /-- Peel helper (prefixed copy: `bind_ok` is private in every module). -/
 private theorem rfc5bind_ok {α β : Type} {x : Except LayoutError α}
     {f : α → Except LayoutError β} {b : β} (h : x.bind f = .ok b) :
     ∃ a, x = .ok a ∧ f a = .ok b := by
   cases x with
   | error e => cases h
   | ok a => exact ⟨a, rfl, h⟩

/-- A mapped zip-indexed list keeps every declaration when each mapped edge
does (prefixed copy of `rrc_map_decl_of_mem`, private there). -/
private theorem rfc5_map_decl_of_mem (l : List Edge) (n : Nat)
    (f : Edge × Nat → Edge)
    (hf : ∀ q ∈ l.zipIdx n, (f q).decl = q.1.decl) :
    (((l.zipIdx n).map f).map (·.decl) = l.map (·.decl)) := by
  induction l generalizing n with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    have htail := ih (n + 1) (fun q hq => hf q (List.mem_cons_of_mem (e, n) hq))
    rw [htail]
    have hhead := hf (e, n) (by simp)
    simpa using congrArg (fun d => d :: rest.map (·.decl)) hhead

 /-- Rank rewriting preserves edge declarations (only orientations change).
 Prefixed copy of `rrc_rankEquivalentR_decls` (private to
 `RegionRunChainFacts`): the final graph is `cg` with edges mapped over
 `zipIdx`, each image either the edge or its `reverse`, both keeping `decl`. -/
 private theorem rfc5_rankEquivalentR_decls {rm : ComponentRegions}
     {cg cg' : Graph} {ranks : List Int} {budget : Bool}
     (h : rankEquivalentR rm cg = .ok (ranks, cg', budget)) :
     cg'.edges.map (·.decl) = cg.edges.map (·.decl) := by
   unfold rankEquivalentR at h
   dsimp only at h
   split at h
   · have hF : False := by
       simp only [bind, Except.bind] at h
       exact absurd h (by simp)
     exact hF.elim
   · obtain ⟨conds, _, h⟩ := rfc5bind_ok h
     obtain ⟨out1, _, h⟩ := rfc5bind_ok h
     obtain ⟨flagsAndOut, _, h⟩ := rfc5bind_ok h
     obtain ⟨ranked, _, h⟩ := rfc5bind_ok h
     have he := Except.ok.inj h
     have hmap := congrArg
       (fun q : List Int × Graph × Bool => q.2.1.edges.map (·.decl)) he
     dsimp only at hmap
     rw [← hmap]
     refine rfc5_map_decl_of_mem cg.edges 0 _ ?_
     intro q _
     split
     · rfl
     · split
       · rfl
       · exact (Edge.reverse_identity q.1).1

 /-- Rank rewriting preserves edge declarations over every region run.
 From `componentRunR_specR`: the `none` arm keeps `cg` (`cg' = cg`), the
 `some` arm goes through `rankEquivalentR`. Endpoint lookup for oriented
 edges must therefore go through the returned `cg'`, keyed by `decl`. -/
 theorem rfc5_edges_decls : componentRunR_edges_decls_factR := by
   unfold componentRunR_edges_decls_factR
   intro P exact spec inp cg cg' run labels orderOptions h
   obtain ⟨rs, ranks, rankBudget, p0, labeled, pCoord, minimum, ord,
     labelWidths, reserved, placedProper, q0, yt, ysMid,
     hRs, hRank, hRest⟩ := componentRunR_specR h
   rcases hRank with ⟨rr, _, _, _, hcg', _⟩ | ⟨rm, _, hranked⟩
   · rw [hcg']
   · exact rfc5_rankEquivalentR_decls hranked

 /-- Executed-run C5 endpoint residual: every executed region run on a
 well-formed framed-parents input attaches all scene routes to the boundary
 of their input `from`/`to` dump boxes. Well-formedness and framed parents
 are local premises after the execution binder (never a global hypothesis).
 Strictly narrower than `FlatC5B`: id preservation is proved separately
 (`RB_layout_ids`), and this quantifies over `SceneExecutionR` runs rather
 than successful `layoutRIds` calls. True on all eight region probes
 (`rrtpC5Ok`, `RegionRunTruthProbes.lean`), including the two-cycle input
 whose ranking rewrite swaps one edge orientation. -/
 def R_ExecutedC5EndpointsR (exactIds : List String)
     (idSets : List (String × List String)) : Prop :=
   ∀ {inp : Input} {o : Options} {res : FamilyResult}
     (_execution : SceneExecutionR exactIds idSets inp o res),
     WellFormed (inputModel inp o) → framedParents inp = true →
     GroupEndpointInvariantMeasured inp res.scene

 /-- Flat C5 for the region pipeline: every successful `layoutRIds` on a
 well-formed framed-parents input preserves box and route ids and attaches
 every route endpoint to its dump-box boundary. -/
 theorem flatC5B_layoutRIds (exactIds : List String)
     (idSets : List (String × List String))
     (h : R_ExecutedC5EndpointsR exactIds idSets) :
     FlatC5B (layoutRIds exactIds idSets) := by
   intro inp o res hwf hfp hb
   obtain ⟨execution⟩ := layoutRIds_sceneExecution hb
   have hids := RB_layout_ids hb
   exact ⟨hids.1, hids.2, h execution hwf hfp⟩

end PipelineImpl
end Layered
end Elegant
