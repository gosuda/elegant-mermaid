import Elegant.Layered.FlatC6LoopProof
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Exclusive loop-box border zero

`FlatC6LoopProof.LoopForeignBoxBorderZero` is the last open id fact of the
self-loop case of clause C6: an exclusive scene box whose rect is the
transported `frameRect` of a real node of an executed component run comes from
a plain node, so the candidate node at that position has `border = 0`.

Route taken: the id route. The rect equation is consumed once, inside the
residual `LoopRectPlainSource`, which turns the rect coincidence into a
model-box role fact (the run node's own source box is not a group). The rest
is pure index transport with no geometry: a non-group box index carries a
border-0 graph node (`SceneExecution.plain_graph_node`, or
`SceneExecution.fixed_candidate_node_border_zero` for fixed-size boxes, which
`measuredGraph` rewrites to node role), transported to the candidate by
`candidate_node_of_part_key`.
-/

/-- A candidate node whose model source box is not a group has `border = 0`.
Fixed-size boxes are rewritten to node role by `measuredGraph`, so the fixed
path applies; otherwise the plain graph node record applies. -/
theorem candidateBorderZeroOfNonGroup {inp : Input} {o : Options}
    {res : FamilyResult} (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate v key : Nat} {src : ModelBox}
    (hkey : comp[v]? = some key) (hsrc : inp.boxes[key]? = some src)
    (hng : src.role ≠ .group) :
    ((componentCandidate execution.graph comp candidate).nodes.getD v default).border = 0 := by
  have hv : v < comp.length := (List.getElem?_eq_some_iff.mp hkey).1
  cases hfind : inp.fixedSizes.find? (fun fixed => fixed.1 == src.id) with
  | some entry =>
    have heq : comp[v] = key := (List.getElem?_eq_some_iff.mp hkey).2
    have hsource' : inp.boxes[comp[v]]? = some src := by
      rw [heq]
      exact hsrc
    obtain ⟨node, hnode, hborder⟩ :=
      execution.fixed_candidate_node_border_zero comp candidate v hv hsource' hfind
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD v default =
        node := by
      simp only [List.getD_eq_getElem?_getD, hnode, Option.getD_some]
    rw [hget]
    exact hborder
  | none =>
    have hfalse : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false :=
      List.any_eq_false.mpr (List.find?_eq_none.mp hfind)
    have hplain : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false →
        ¬(src.role = .group ∧
          inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false) :=
      fun _ hcon => hng hcon.1
    obtain ⟨gnode, hgn, hb0, _, _⟩ :=
      execution.plain_graph_node hsrc (hplain hfalse)
    have hcand : (componentCandidate execution.graph comp candidate).nodes[v]? =
        some gnode :=
      candidate_node_of_part_key hkey hgn
    have hget : (componentCandidate execution.graph comp candidate).nodes.getD v default =
        gnode := by
      simp only [List.getD_eq_getElem?_getD, hcand, Option.getD_some]
    rw [hget]
    exact hb0

/-- Residual (rect-to-role link, the only unproved step): when the rect of an
exclusive scene box of an executed layout equals the transported `frameRect`
of a real node of an executed component run, that run node's own source box
is not a group.

Why this holds for executed layouts: candidate nodes are box nodes and
appended bottom markers only, so their borders are `-2`, `0`, or `2` (side
markers and title copies live in the proper graph, never in the candidate).
A bottom marker keeps height `0` through the executed pipeline (cf.
`bottomMarker_frame_disjoint`), so its transported frame cannot coincide with
the positive-extent rect of an exclusive plain box; a group top spans its
member and side-border hulls, strictly wider than any single member via the
cluster-border span, so it cannot coincide either. The coincident real node
is hence plain, and its source box is not a group.

FALSE AS STATED: the arbitrary-shift `q` form is refuted (a fixed group aligns
with a same-size exclusive node; see `LoopRectPlainSourceProof`); the true
real-`q` replacement is the `LoopRect*Real` family assembled by
`loopRectPlainSourceRealQ` / `loopForeignBoxBorderZeroRealQ`.
The conclusion speaks only of component membership and model-box roles (the
measured-graph index phase), with no geometry; it is pinned by the
`SceneExecution` equations (`graph_eq` for boxes to nodes, `componentRun`
success for the run, `scene_eq` for box emission). -/
def LoopRectPlainSource (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (comp : List Nat) (candidate : Nat) (run : Run),
    comp ∈ components execution.graph →
    componentRun execution.params
      (componentCandidate execution.graph comp candidate) execution.measured
      (candidateOrder candidate) = .ok run →
    ∀ {q : (List Nat × Part) × Rect} {loops : List (Nat × LoopPlacement)}
      (v : Nat) (b : Box),
      RouteImpl.IsReal run.proper v →
      b ∈ res.scene.boxes → b.exclusive = true →
      b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
        (orientRect o.direction execution.packedAcc.canvasH
          (shiftRect q.2.x q.2.y
            (shiftRect (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run execution.measured
                loops).minX)
              (0 - (placeBounds execution.params
                (componentCandidate execution.graph comp candidate) run execution.measured
                loops).minY)
              (frameRect execution.params
                (componentCandidate execution.graph comp candidate) run v)))) →
      ∃ (key : Nat) (src : ModelBox),
        comp[v]? = some key ∧ inp.boxes[key]? = some src ∧ src.role ≠ .group

end PipelineImpl
end Layered
end Elegant
