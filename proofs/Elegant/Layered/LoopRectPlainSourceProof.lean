import Elegant.Layered.LoopBoxBorderZeroProof
import Elegant.Layered.GroupWidthFacts
import Elegant.Layered.PipelineFacts

set_option autoImplicit false

namespace Elegant
namespace Layered
namespace PipelineImpl

/-!
# Plain-source cases of the loop-box rect residual, real-part form

`LoopBoxBorderZeroProof.LoopRectPlainSource` quantifies the packed part `q`
universally, but its rect equation only constrains `q.2.x` and `q.2.y`. For a
non-plain real node `v` whose frame size coincides (up to orientation swap)
with an exclusive scene box, an adversarial `q` aligns the transported frame
with that box, satisfying the equation while the role conclusion is false.

Executed witness (`proofs/wip/Probe/LoopRectPlainSourceProbe.lean`,
`falsifyFixedSame`): input with fixed group `G` (`9000x9000`, member `m`)
and fixed plain `m` (`9000x9000`, exclusive). At `comp = [0]`, candidate `0`,
`v = 0` is real, `comp[0]? = some 0`, `boxes[0]? = G` (role `group`), the
frame is `(-4500, 0, 9000, 9000)`, and with `loops = []` the choice
`q.2 = (0, 10536)` makes the transported frame equal `m`'s scene box
`(1024, 11560, 9000, 9000)` (`aligned=true` by recomputation). The equation
holds, `IsReal` holds, the box is exclusive, yet no non-group source exists.
Hence the universally quantified `LoopRectPlainSource` is false, and so are
its top and fixed cases in that form.

The consumer (`flatC6LoopCase`) only ever applies the residual at the real
packed part (`hselected`) with the real placement equation (`hpart`). The
replacement below pins `q` to that real part (`hpack`, `hselected`,
`hpart`) and pins the component to `q.1.1`, which is exactly how the
consumer instantiates it. The remaining cases are stated in this real-part
form:

* `LoopRectTopReal`: group-top frame never coincides (strict containment
  for members, foreign-span separation otherwise).
* `LoopRectFixedReal`: fixed-size border-0 frame never coincides except via
  its own box, whose source is then a node.
* `LoopRectTitleReal`: title/proxy frames beyond the candidate range never
  coincide.
* `LoopRectBottomReal`: bottom-marker frames have height `0` while exclusive
  boxes are positive.
* `LoopRectRangeDegReal`: degenerate default frames beyond the proper run
  never coincide with positive boxes.

Probed on executed layouts at candidate 0 (plain, grouped, nested,
fixed-size, self-loop inputs, plus zero-padding variants which fail to
execute): every real-`q` coincidence of a transported real-node frame with
an exclusive scene box rect happens at a `border = 0` node whose source box
has role `node`; marker frames, the fixed-size group frame, and
out-of-range frames never coincide with any exclusive scene box rect.

Proved here without further hypotheses: the unfixed plain case
(`loopRectPlain_of_unfixed`, via `nonfixed_group_graph_node`) and the
box-less border-0 case (`loopRectNoBox`, whose `boxes[key]? = none`
hypothesis contradicts the prepared-node index bound).
-/

/-- Local re-proof of the private `ComponentCoverage.componentCandidate_nodes_length`:
a candidate graph has exactly the component's nodes. -/
private theorem candidate_nodes_length (g : Graph) (comp : List Nat) (index : Nat) :
    (componentCandidate g comp index).nodes.length = comp.length := by
  rw [componentCandidate_nodes]
  simp only [componentGraph, List.length_map]

/-- Residual (real-part group-top case). -/
def LoopRectTopReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = -2 →
      False

/-- Residual (real-part fixed-size case). -/
def LoopRectFixedReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node} {key : Nat} {src : ModelBox},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = 0 →
      q.1.1[v]? = some key → inp.boxes[key]? = some src →
      inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = true →
      ∃ (key' : Nat) (src' : ModelBox),
        q.1.1[v]? = some key' ∧ inp.boxes[key']? = some src' ∧ src'.role ≠ .group

/-- Residual (real-part title case): a real node beyond the candidate range
whose proper node exists (title/side-marker copies) never satisfies the
real-part rect equation. -/
def LoopRectTitleReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none →
    run.proper.nodes[v]? ≠ none →
    False

/-- Residual (real-part bottom-marker case). -/
def LoopRectBottomReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    ∀ {node : Node},
      (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = some node →
      node.border = 2 →
      False

/-- Residual (real-part degenerate case): a real node beyond both the
candidate range and the proper run never satisfies the real-part rect
equation (its frame is degenerate while exclusive boxes are positive). -/
def LoopRectRangeDegReal (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (_hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (_hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (_hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (_hcomp : q.1.1 ∈ components execution.graph)
    (_hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box),
    RouteImpl.IsReal run.proper v →
    b ∈ res.scene.boxes → b.exclusive = true →
    b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v)))) →
    (componentCandidate execution.graph q.1.1 candidate).nodes[v]? = none →
    run.proper.nodes[v]? = none →
    False

/-- Proved plain case: a `border = 0` candidate node whose model source box
has no fixed-size entry cannot come from a group box. A group-role box
without a fixed entry is stored as a group top (`border = -2`) by
`nonfixed_group_graph_node`, contradicting `border = 0` at the same
position. The rect equation is not needed. -/
theorem loopRectPlain_of_unfixed {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate v key : Nat} {node : Node} {src : ModelBox}
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb0 : node.border = 0)
    (hkey : comp[v]? = some key)
    (hsrc : inp.boxes[key]? = some src)
    (hnf : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) = false) :
    src.role ≠ .group := by
  intro hgroup
  obtain ⟨gnode, hgn, hgborder, _⟩ := execution.nonfixed_group_graph_node hsrc hgroup hnf
  have hvalue : execution.graph.nodes.getD key default = node := by
    have h2 := hnode
    rw [componentCandidate_nodes] at h2
    have h3 : (comp.map fun k => execution.graph.nodes.getD k default)[v]? = some node := h2
    simpa only [List.getElem?_map, hkey, Option.map_some, Option.some.injEq] using h3
  have h1 : execution.graph.nodes.getD key default = gnode := by
    simp only [List.getD_eq_getElem?_getD, hgn, Option.getD_some]
  have heq : gnode = node := h1.symm.trans hvalue
  rw [heq] at hgborder
  omega

/-- Proved box-less case: a `border = 0` candidate position always has a
model source box. A border-0 prepared node below the source length carries
its box; at or beyond the source length `prepare_bottom_of_index` forces
`border = 2`. The rect equation is not needed. -/
theorem loopRectNoBox {inp : Input} {o : Options} {res : FamilyResult}
    (execution : SceneExecution inp o res)
    {comp : List Nat} {candidate v key : Nat} {node : Node}
    (hcomp : comp ∈ components execution.graph)
    (hnode : (componentCandidate execution.graph comp candidate).nodes[v]? = some node)
    (hb0 : node.border = 0)
    (hkey : comp[v]? = some key)
    (hnone : inp.boxes[key]? = none) :
    False := by
  have hbound : key < execution.graph.nodes.length := by
    obtain ⟨r, hr⟩ := mem_components_eq hcomp
    have hmem : key ∈ comp := List.mem_of_getElem? hkey
    rw [hr] at hmem
    exact List.mem_range.mp (List.mem_filter.mp hmem).1
  have hvalue : execution.graph.nodes.getD key default = node := by
    have h2 := hnode
    rw [componentCandidate_nodes] at h2
    have h3 : (comp.map fun k => execution.graph.nodes.getD k default)[v]? = some node := h2
    simpa only [List.getElem?_map, hkey, Option.map_some, Option.some.injEq] using h3
  have hgraphnode : execution.graph.nodes[key]? = some node := by
    have h1 := hvalue
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbound,
      Option.getD_some] at h1
    rw [List.getElem?_eq_getElem hbound]
    exact congrArg some h1
  obtain ⟨box, hbox, _, _⟩ := execution.plain_node_path_source hgraphnode hb0
  rw [hbox] at hnone
  cases hnone
/-- Real-part assembly: the rect-to-role link for the real packed part,
dispatched to the proved plain/box-less cases and the five real-part
residuals. The component is pinned to `q.1.1`, exactly as `flatC6LoopCase`
instantiates it. -/
theorem loopRectPlainSourceRealQ {inp : Input} {o : Options} {res : FamilyResult}
    (htop : LoopRectTopReal inp o res)
    (hfix : LoopRectFixedReal inp o res)
    (htitle : LoopRectTitleReal inp o res)
    (hbot : LoopRectBottomReal inp o res)
    (hrange : LoopRectRangeDegReal inp o res)
    (execution : SceneExecution inp o res) (candidate : Nat) (run : Run)
    (packed : Pack.State)
    (hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed)
    (c : Nat) (q : (List Nat × Part) × Rect)
    (hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q)
    {area : Int} {loops : List (Nat × LoopPlacement)}
    (hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area })
    (hcomp : q.1.1 ∈ components execution.graph)
    (hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run)
    (v : Nat) (b : Box)
    (hreal : RouteImpl.IsReal run.proper v)
    (hbmem : b ∈ res.scene.boxes) (hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v))))) :
    ∃ (key : Nat) (src : ModelBox),
      q.1.1[v]? = some key ∧ inp.boxes[key]? = some src ∧ src.role ≠ .group := by
  cases hnode : (componentCandidate execution.graph q.1.1 candidate).nodes[v]? with
  | none =>
      cases hproper : run.proper.nodes[v]? with
      | none =>
          exact False.elim (hrange execution candidate run packed hpack c q
            hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnode hproper)
      | some _ =>
          have hne : run.proper.nodes[v]? ≠ none := by simp [hproper]
          exact False.elim (htitle execution candidate run packed hpack c q
            hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnode hne)
  | some node =>
      obtain ⟨hshape, _⟩ := componentCandidate_marker_shape execution.graph_eq hnode
      rcases hshape with hb0 | hbtop | hbbot
      · have hvlen : v < (componentCandidate execution.graph q.1.1 candidate).nodes.length :=
          (List.getElem?_eq_some_iff.mp hnode).1
        have hlen := candidate_nodes_length execution.graph q.1.1 candidate
        have hvcomp : v < q.1.1.length := by omega
        obtain ⟨key, hkey⟩ : ∃ key, q.1.1[v]? = some key :=
          ⟨_, List.getElem?_eq_getElem hvcomp⟩
        cases hsrc : inp.boxes[key]? with
        | none =>
            exact False.elim (loopRectNoBox execution hcomp hnode hb0 hkey hsrc)
        | some src =>
            match hfb : inp.fixedSizes.any (fun fixed => fixed.1 == src.id) with
            | true =>
                exact hfix execution candidate run packed hpack c q
                  hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnode hb0
                  hkey hsrc hfb
            | false =>
                exact ⟨key, src, hkey, hsrc,
                  loopRectPlain_of_unfixed execution hnode hb0 hkey hsrc hfb⟩
      · exact False.elim (htop execution candidate run packed hpack c q
          hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnode hbtop)
      · exact False.elim (hbot execution candidate run packed hpack c q
          hselected hpart hcomp hrun v b hreal hbmem hexcl hrect hnode hbbot)

/-- Real-part loop-case exclusive-box fact: the form `flatC6LoopCase` needs.
Its `hbord` call site (`FlatC6LoopProof.lean`, `hborder0`) passes the real
packed part; replace that call with this theorem, supplying `packed`,
`hpack`, `hselected`, `hpart` from its context plus the five real-part
residuals. The universally quantified `LoopForeignBoxBorderZero` is false
(see the file docstring); this is its weakest true replacement that still
proves the loop case. -/
theorem loopForeignBoxBorderZeroRealQ {inp : Input} {o : Options} {res : FamilyResult}
    {execution : SceneExecution inp o res} {candidate : Nat} {run : Run}
    {packed : Pack.State}
    {hpack : Pack.pack (if o.profile == .cell then o.maxWidth else 0)
      execution.params.nodeGap 0
      (LayoutConst.component_aspect_num.get o.profile)
      (LayoutConst.component_aspect_den.get o.profile)
      (execution.componentsAcc.parts.map fun part =>
        ⟨part.2.width, part.2.height, part.2.area⟩) = .ok packed}
    {c : Nat} {q : (List Nat × Part) × Rect}
    {hselected : (execution.componentsAcc.parts.zip packed.boxes)[c]? = some q}
    {area : Int} {loops : List (Nat × LoopPlacement)}
    {hpart : q.1.2 = { placeComponent execution.params
      (componentCandidate execution.graph q.1.1 candidate) run 0 execution.measured
      loops with area := area }}
    {hcomp : q.1.1 ∈ components execution.graph}
    {hrun : componentRun execution.params
      (componentCandidate execution.graph q.1.1 candidate) execution.measured
      (candidateOrder candidate) = .ok run}
    (htop : LoopRectTopReal inp o res)
    (hfix : LoopRectFixedReal inp o res)
    (htitle : LoopRectTitleReal inp o res)
    (hbot : LoopRectBottomReal inp o res)
    (hrange : LoopRectRangeDegReal inp o res)
    {v : Nat} {b : Box}
    (hreal : RouteImpl.IsReal run.proper v)
    (hbmem : b ∈ res.scene.boxes) (hexcl : b.exclusive = true)
    (hrect : b.rect = shiftRect execution.params.canvasMargin execution.params.canvasMargin
      (orientRect o.direction execution.packedAcc.canvasH
        (shiftRect q.2.x q.2.y
          (shiftRect (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minX)
            (0 - (placeBounds execution.params
              (componentCandidate execution.graph q.1.1 candidate) run execution.measured
              loops).minY)
            (frameRect execution.params
              (componentCandidate execution.graph q.1.1 candidate) run v))))) :
    ((componentCandidate execution.graph q.1.1 candidate).nodes.getD v default).border = 0 := by
  obtain ⟨key, src, hkey, hsrc, hng⟩ :=
    loopRectPlainSourceRealQ htop hfix htitle hbot hrange
      execution candidate run packed hpack c q hselected hpart hcomp hrun v b
      hreal hbmem hexcl hrect
  exact candidateBorderZeroOfNonGroup execution hkey hsrc hng


