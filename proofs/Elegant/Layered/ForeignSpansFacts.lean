import Elegant.Layered.ForeignFrameClearance
import Elegant.Layered.FrameClearanceSeam
import Elegant.Layered.RecursiveC78
import Elegant.Layered.PipelineFacts
import Elegant.Layered.SceneBounds
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered

namespace PipelineImpl

/-- The named per-layout span premise: for every executed component run of a
successful flat `PipelineImpl.layout`, the executed frame rectangles of any two
distinct, mutually unrelated group-declaration nodes are disjoint. -/
def ForeignSpansAll (inp : Input) (o : Options) (res : FamilyResult) : Prop :=
  ∀ (execution : SceneExecution inp o res) (part : List Nat × Part),
    part ∈ execution.componentsAcc.parts →
    ∀ (candidate : Nat) (run : Run) (orderOptions : OrderOptions),
      componentRun execution.params
        (componentCandidate execution.graph part.1 candidate) execution.measured
        orderOptions = .ok run →
      ForeignSpansClear execution.params
        (componentCandidate execution.graph part.1 candidate) run

/-- A part of the executed accumulator is a component of the measured graph. -/
theorem part_component_mem {g : Graph} {componentsAcc : Acc}
    (hparts : componentsAcc.parts.map (·.1) = components g)
    {part : List Nat × Part} (hpart : part ∈ componentsAcc.parts) :
    part.1 ∈ components g := by
  rw [← hparts]
  exact List.mem_map_of_mem hpart

set_option maxHeartbeats 2000000 in
/-- The flat foreign-frame clause `FlatC8a` follows from the inside-rank
bracket closure (via `frameClearanceSeam_holds`) and the executed span premise:
`layout_c8a` consumes `FrameClearance` per run through the seam and
`ForeignSpansClear` through `ForeignSpansAll`. -/
theorem flatC8a_of_spans (hspans : ∀ (inp : Input) (o : Options)
      (res : FamilyResult), ForeignSpansAll inp o res)
    (hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      BracketInsidePremises inp o res) : FlatC8a := by
  intro inp o res hwf hfp h
  apply layout_c8a h hwf hfp
  intro execution part hpart
  have hmap : execution.componentsAcc.parts.map (·.1) = components execution.graph := by
    have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = [] := rfl
    exact (actual_components_parts_geometry (P := execution.params) (inp := inp)
      (o := o) (g := execution.graph) (labels := execution.measured) hempty
      execution.components_eq).1
  have hcomp : part.1 ∈ components execution.graph :=
    part_component_mem hmap hpart
  refine fun candidate run orderOptions hrun =>
    ⟨frameClearanceSeam_holds (hbracket inp o res)
      execution part.1 candidate run orderOptions hcomp hrun,
     hspans inp o res execution part hpart candidate run orderOptions hrun⟩

/-! ### Executed foreign spans of one component run -/

/-- Member rects of one group declaration: the vertical hull input of `frameRect`. -/
def groupMemberRects (_cg : Graph) (run : Run) (decl : Nat) : List Rect :=
  run.proper.nodes.zipIdx.filterMap fun q =>
    if q.1.node.clusterPath.contains decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none

/-- Border-marker rects of one group declaration: the horizontal hull input of
`frameRect`. -/
def groupBorderRects (_cg : Graph) (run : Run) (decl : Nat) : List Rect :=
  run.proper.nodes.zipIdx.filterMap fun q =>
    if (q.1.node.border == -1 || q.1.node.border == 1) &&
        q.1.node.clusterPath.getLast? == some decl then
      some (Labels.rectAt run.proper run.xs run.ys q.2)
    else none

/-- The executed frame rectangle of a group-declaration node is the bounding box
of its border markers horizontally and of its member nodes vertically. -/
theorem frameRect_group_span {P : Params} {cg : Graph} {run : Run} {u : Nat}
    {uNode : Node} (hu : cg.nodes[u]? = some uNode) (hgroup : uNode.border = -2) :
    frameRect P cg run u =
      ⟨(boundsOf (groupBorderRects cg run uNode.decl) []).minX,
        (boundsOf (groupMemberRects cg run uNode.decl) []).minY,
        (boundsOf (groupBorderRects cg run uNode.decl) []).right -
          (boundsOf (groupBorderRects cg run uNode.decl) []).minX,
        (boundsOf (groupMemberRects cg run uNode.decl) []).bottom -
          (boundsOf (groupMemberRects cg run uNode.decl) []).minY⟩ := by
  have hget : cg.nodes.getD u default = uNode := by
    rw [List.getD_eq_getElem?_getD, hu]
    rfl
  unfold frameRect groupMemberRects groupBorderRects
  simp only [hget, hgroup, show ((-2 : Int) != -2) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]

/-- Hull-separated frames are disjoint: either the border hulls separate on `x`
or the member hulls separate on `y`. -/
theorem frameRect_disjoint_of_hulls
    {P : Params} {cg : Graph} {run : Run} {u w : Nat} {uNode wNode : Node}
    (hu : cg.nodes[u]? = some uNode) (hgroupU : uNode.border = -2)
    (hw : cg.nodes[w]? = some wNode) (hgroupW : wNode.border = -2)
    (hsep : (boundsOf (groupBorderRects cg run uNode.decl) []).right ≤
          (boundsOf (groupBorderRects cg run wNode.decl) []).minX ∨
        (boundsOf (groupBorderRects cg run wNode.decl) []).right ≤
          (boundsOf (groupBorderRects cg run uNode.decl) []).minX ∨
        (boundsOf (groupMemberRects cg run uNode.decl) []).bottom ≤
          (boundsOf (groupMemberRects cg run wNode.decl) []).minY ∨
        (boundsOf (groupMemberRects cg run wNode.decl) []).bottom ≤
          (boundsOf (groupMemberRects cg run uNode.decl) []).minY) :
    Disjoint (frameRect P cg run u) (frameRect P cg run w) := by
  rw [frameRect_group_span hu hgroupU, frameRect_group_span hw hgroupW]
  unfold Disjoint Rect.meetsInterior
  dsimp only
  rcases hsep with h | h | h | h <;> omega

/-- A group declaration with no border markers has a zero-width frame, so its
frame cannot meet any interior. -/
theorem frameRect_disjoint_of_hull_empty
    {P : Params} {cg : Graph} {run : Run} {u w : Nat} {wNode : Node}
    (hw : cg.nodes[w]? = some wNode) (hgroupW : wNode.border = -2)
    (hempty : groupBorderRects cg run wNode.decl = []) :
    Disjoint (frameRect P cg run u) (frameRect P cg run w) := by
  rw [frameRect_group_span hw hgroupW, hempty]
  unfold Disjoint Rect.meetsInterior
  simp only [boundsOf, List.foldl_nil]
  omega

/-- The `x`-right edge of a rect hull is bounded by any upper bound of its
members (and by zero, the fold's identity). -/
theorem boundsOf_right_le_of_all {rects : List Rect} {hi : Int}
    (hzero : 0 ≤ hi) (hall : ∀ r ∈ rects, r.x + r.w ≤ hi) :
    (boundsOf rects []).right ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      initial.right ≤ hi →
      (∀ r ∈ remaining, r.x + r.w ≤ hi) →
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).right ≤ hi := by
    intro remaining
    induction remaining with
    | nil => intro initial hinit _; exact hinit
    | cons first rest ih =>
      intro initial hinit hrest
      simp only [List.foldl_cons]
      exact ih _ (Int.max_le.mpr ⟨hinit, hrest first (by simp)⟩)
        (fun r hr => hrest r (List.mem_cons_of_mem _ hr))
  cases rects with
  | nil => simpa [boundsOf] using hzero
  | cons first rest =>
    change ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).right ≤ hi
    exact preserve _ _ hzero hall

/-- The `x`-left edge of a nonempty rect hull is above any lower bound of its
members. -/
theorem boundsOf_minX_ge_of_all {rects : List Rect} {lo : Int}
    (hne : rects ≠ []) (hall : ∀ r ∈ rects, lo ≤ r.x) :
    lo ≤ (boundsOf rects []).minX := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minX →
      (∀ r ∈ remaining, lo ≤ r.x) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minX := by
    intro remaining
    induction remaining with
    | nil => intro initial hinit _; exact hinit
    | cons first rest ih =>
      intro initial hinit hrest
      simp only [List.foldl_cons]
      exact ih _ (Int.le_min.mpr ⟨hinit, hrest first (by simp)⟩)
        (fun r hr => hrest r (List.mem_cons_of_mem _ hr))
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minX
    exact preserve _ _ (hall first (by simp)) hall

/-- The `y`-bottom of a rect hull is bounded by any upper bound of its members
(and by zero, the fold's identity). -/
theorem boundsOf_bottom_le_of_all {rects : List Rect} {hi : Int}
    (hzero : 0 ≤ hi) (hall : ∀ r ∈ rects, r.y + r.h ≤ hi) :
    (boundsOf rects []).bottom ≤ hi := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      initial.bottom ≤ hi →
      (∀ r ∈ remaining, r.y + r.h ≤ hi) →
      (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).bottom ≤ hi := by
    intro remaining
    induction remaining with
    | nil => intro initial hinit _; exact hinit
    | cons first rest ih =>
      intro initial hinit hrest
      simp only [List.foldl_cons]
      exact ih _ (Int.max_le.mpr ⟨hinit, hrest first (by simp)⟩)
        (fun r hr => hrest r (List.mem_cons_of_mem _ hr))
  cases rects with
  | nil => simpa [boundsOf] using hzero
  | cons first rest =>
    change ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).bottom ≤ hi
    exact preserve _ _ hzero hall

/-- The `y`-top of a nonempty rect hull is above any lower bound of its members. -/
theorem boundsOf_minY_ge_of_all {rects : List Rect} {lo : Int}
    (hne : rects ≠ []) (hall : ∀ r ∈ rects, lo ≤ r.y) :
    lo ≤ (boundsOf rects []).minY := by
  have preserve : ∀ (remaining : List Rect) (initial : Bounds),
      lo ≤ initial.minY →
      (∀ r ∈ remaining, lo ≤ r.y) →
      lo ≤ (remaining.foldl
        (fun b r => ⟨min b.minX r.x, min b.minY r.y,
          max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩) initial).minY := by
    intro remaining
    induction remaining with
    | nil => intro initial hinit _; exact hinit
    | cons first rest ih =>
      intro initial hinit hrest
      simp only [List.foldl_cons]
      exact ih _ (Int.le_min.mpr ⟨hinit, hrest first (by simp)⟩)
        (fun r hr => hrest r (List.mem_cons_of_mem _ hr))
  cases rects with
  | nil => exact absurd rfl hne
  | cons first rest =>
    change lo ≤ ((first :: rest).foldl
      (fun b r => ⟨min b.minX r.x, min b.minY r.y,
        max b.right (r.x + r.w), max b.bottom (r.y + r.h)⟩)
      (⟨first.x, first.y, 0, 0⟩ : Bounds)).minY
    exact preserve _ _ (hall first (by simp)) hall

/-- Open seam for the executed foreign-span clause (group-vs-group half):
the hulls of two unrelated group declarations of one executed run separate
either on `x` through the border-marker hulls or on `y` through the member hulls.

Proof obligations, in dependency order:
1. `border_chain_aligned` — the horizontal pass keeps every border marker of one
   group declaration at a common x-span, so `groupBorderRects` of one declaration
   is a set of equal x-intervals.  This is the executed `BorderChainUps`
   alignment content (`borderChainBlock_of_ups` reduces it to the single named
   hypothesis `BorderChainUps`).
2. Pairwise separation at every layer where both groups carry markers follows
   from `cluster_all_pairs_separated` (side markers are non-proxy).
3. Disjoint member rank ranges give (via `rankAxis_node_in_band` and
   `rankAxis_bands_disjoint` applied to the frame's member hull bounds) the `y`
   alternative; overlapping ranges force shared marker ranks and then (1)+(2)
   give an `x` alternative. -/
def ForeignBorderSpansSeparated : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border = -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
        uNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
          wNode.decl) []).minX ∨
      (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
        wNode.decl) []).right ≤
        (boundsOf (groupBorderRects (componentCandidate graph comp candidate) run
          uNode.decl) []).minX ∨
      (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
        uNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
          wNode.decl) []).minY ∨
      (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
        wNode.decl) []).bottom ≤
        (boundsOf (groupMemberRects (componentCandidate graph comp candidate) run
          uNode.decl) []).minY

/-- Open seam for the foreign-span clause against a non-group witness `w`: a
plain node, a title marker, or a bottom proxy of an unrelated group.

Proof obligations:
* plain `w` whose rank lies outside the group's member-rank range: the frame's
  vertical hull is confined to the member rank bands (`rankAxis_node_in_band`,
  `rankAxis_bands_disjoint`, `proxyYs_getD` as in
  `componentRun_positions_disjoint`), so the y-intervals separate.
* plain `w` inside the range: the group carries border markers at `w`'s rank
  (`coordinateGraph_rank_pair`), `w` sits outside that rank's bracket
  positions, and the chain alignment (`border_chain_aligned`) transports the
  per-rank separation to the whole hull.
* title marker `w`: its rect lies within its owner group's border hull, which
  is span-separated from `u`'s hull by `foreign_border_spans_separated`.
* bottom proxy `w` (`border = 2`): `frameRect` reduces to the proxy's
  `nodeRect`, whose x-interval is its owner's marker span
  (`componentRun_proxy_border_extrema`), again span-separated. -/
def ForeignNonGroupSpansClear : Prop :=
  ∀ {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph},
    measuredGraph P inp o lines = .ok graph →
    ∀ {comp : List Nat}, comp ∈ components graph →
    ∀ {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
      {orderOptions : OrderOptions},
    componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run →
    ∀ {u w : Nat} {uNode wNode : Node},
    (componentCandidate graph comp candidate).nodes[u]? = some uNode →
    (componentCandidate graph comp candidate).nodes[w]? = some wNode →
    uNode.border = -2 → wNode.border ≠ -2 →
    uNode.decl ≠ wNode.decl →
    wNode.clusterPath.contains uNode.decl = false →
    uNode.clusterPath.contains wNode.decl = false →
    Disjoint (frameRect P (componentCandidate graph comp candidate) run u)
      (frameRect P (componentCandidate graph comp candidate) run w)

/-- The executed foreign-span clause of one successful component run, from the
two open seams. -/
theorem foreignSpansClear_of_run
    (hgroups : ForeignBorderSpansSeparated) (hothers : ForeignNonGroupSpansClear)
    {P : Params} {inp : Input} {o : Options}
    {lines : List (List Measure.Line)} {graph : Graph}
    (hgraph : measuredGraph P inp o lines = .ok graph)
    {comp : List Nat} (hcomp : comp ∈ components graph)
    {candidate : Nat} {run : Run} {labels : List MeasuredLabel}
    {orderOptions : OrderOptions}
    (hrun : componentRun P (componentCandidate graph comp candidate) labels
      orderOptions = .ok run) :
    ForeignSpansClear P (componentCandidate graph comp candidate) run := by
  intro u w uNode wNode hu hw hgroupU hne hpathW hpathU
  by_cases hgroupW : wNode.border = -2
  · exact frameRect_disjoint_of_hulls hu hgroupU hw hgroupW
      (hgroups hgraph hcomp hrun hu hw hgroupU
        hgroupW hne hpathW hpathU)
  · exact hothers hgraph hcomp hrun hu hw hgroupU
      hgroupW hne hpathW hpathU

/-- The named per-layout span premise from the per-run theorem. -/
theorem foreignSpansAll_of_run
    (hclear : ∀ (P : Params) (inp : Input) (o : Options)
        (lines : List (List Measure.Line)) (graph : Graph) (comp : List Nat),
        measuredGraph P inp o lines = .ok graph → comp ∈ components graph →
        ∀ (candidate : Nat) (run : Run) (labels : List MeasuredLabel)
          (orderOptions : OrderOptions),
          componentRun P (componentCandidate graph comp candidate) labels
            orderOptions = .ok run →
          ForeignSpansClear P (componentCandidate graph comp candidate) run) :
    ∀ (inp : Input) (o : Options) (res : FamilyResult), ForeignSpansAll inp o res := by
  intro inp o res execution part hpart candidate run orderOptions hrun
  have hmap : execution.componentsAcc.parts.map (·.1) = components execution.graph := by
    have hempty : (⟨0, 0, 0, Array.replicate inp.boxes.length default,
        Array.replicate inp.routes.length [], Array.replicate inp.labels.length default,
        false, [], []⟩ : Acc).parts = [] := rfl
    exact (actual_components_parts_geometry (P := execution.params) (inp := inp)
      (o := o) (g := execution.graph) (labels := execution.measured) hempty
      execution.components_eq).1
  have hcomp := part_component_mem hmap hpart
  have hper := hclear execution.params inp o execution.lines execution.graph part.1
    execution.graph_eq hcomp
  exact hper candidate run execution.measured orderOptions hrun

/-- `FlatC8a` composes from the bracket seam and the two open foreign-span
seams alone: the group-vs-group hull separation
(`ForeignBorderSpansSeparated`) and the non-group witness clause
(`ForeignNonGroupSpansClear`). -/
theorem flatC8a_of_span_seams
    (hgroups : ForeignBorderSpansSeparated) (hothers : ForeignNonGroupSpansClear)
    (hbracket : ∀ (inp : Input) (o : Options) (res : FamilyResult),
      BracketInsidePremises inp o res) : FlatC8a :=
  flatC8a_of_spans
    (foreignSpansAll_of_run (fun _ _ _ _ _ _ hgraph hcomp _ _ _ _ hrun =>
      foreignSpansClear_of_run hgroups hothers hgraph hcomp hrun))
    hbracket

end PipelineImpl

end Elegant.Layered
