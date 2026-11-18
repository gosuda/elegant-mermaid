import Elegant.Layered.LabelsC7
import Elegant.Layered.PipelineFacts
import Elegant.Layered.Coords
import ElegantGeometry.Disjoint

set_option autoImplicit false

namespace Elegant.Layered

open PipelineImpl

/-! Run-local half of flat-layered clause 7: the placed rect of a measured
route label misses the `RouteImpl.boxRect` of every real node outside the
edge's run scope.

The file reduces `RunLocalLabelClearance` to three geometry facts about
executed runs, one per `labelEnvelope` branch (forward label node, self-loop
footprint, reversed lane), each proved from the executed coordinate and
reservation lemmas. -/

/-! ## Rectangle separation primitives -/

/-- Two rectangles whose x-projections are separated (touching allowed) do not
share an interior point. -/
theorem not_meetsInterior_of_right_le {a b : Rect} (h : a.x + a.w ≤ b.x) :
    ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-- The mirror form: `b` lies entirely left of `a`. -/
theorem not_meetsInterior_of_left_le {a b : Rect} (h : b.x + b.w ≤ a.x) :
    ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-- Two rectangles whose y-projections are separated do not share an interior
point. -/
theorem not_meetsInterior_of_below {a b : Rect} (h : a.y + a.h ≤ b.y) :
    ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-- The mirror form: `b` lies entirely above `a`. -/
theorem not_meetsInterior_of_above {a b : Rect} (h : b.y + b.h ≤ a.y) :
    ¬ a.meetsInterior b := by
  unfold Rect.meetsInterior
  omega

/-! ## Forward branch: same-layer horizontal separation -/

/-- The left edge of a forward label envelope is the node centre shifted left by
half the node width and then by the measured gutter. -/
theorem textRectAt_left (p : Proper) (xs ys : List Int) (u : Nat)
    (gutter : Int) :
    (Labels.textRectAt p xs ys u gutter).x =
      RouteImpl.xAt xs u - Int.fdiv (RouteImpl.nodeW p u) 2 + gutter :=
  rfl

/-- The left edge of a node box is the node centre shifted left by half the node
width. -/
theorem boxRect_left (p : Proper) (xs ys : List Int) (v : Nat) :
    (RouteImpl.boxRect p xs ys v).x =
      RouteImpl.xAt xs v - Int.fdiv (RouteImpl.nodeW p v) 2 :=
  rfl

/-- The top edge of a node box is the node's rank coordinate. -/
theorem boxRect_top (p : Proper) (xs ys : List Int) (v : Nat) :
    (RouteImpl.boxRect p xs ys v).y = RouteImpl.yAt ys v :=
  rfl

/-- The width of a node box is the executed node width. -/
theorem boxRect_w (p : Proper) (xs ys : List Int) (v : Nat) :
    (RouteImpl.boxRect p xs ys v).w = RouteImpl.nodeW p v :=
  rfl

/-- The height of a node box is the executed node height. -/
theorem boxRect_h (p : Proper) (xs ys : List Int) (v : Nat) :
    (RouteImpl.boxRect p xs ys v).h = RouteImpl.nodeH p v :=
  rfl

/-- The vertical position of a forward label envelope is the label node's rank
coordinate. -/
theorem textRectAt_y (p : Proper) (xs ys : List Int) (u : Nat) (gutter : Int) :
    (Labels.textRectAt p xs ys u gutter).y = RouteImpl.yAt ys u :=
  rfl

/-- `Int.fdiv` by the literal `2` is the `omega`-native floored division. -/
theorem fdiv2_ediv (a : Int) : Int.fdiv a 2 = a / 2 :=
  Int.fdiv_eq_ediv_of_nonneg a (show (0 : Int) ≤ 2 by decide)

/-- **Forward branch, left–right order.** A stack entry placed at a forward label
envelope stays left of the box of a node that follows it in the same layer,
given the executed rank separation bound (`coordSep` is dominated by the centre
distance) and the reserved label width. The one-unit parity slack of the label
node width is absorbed by the strictly positive node gap. -/
theorem forward_stack_left_le_box
    {p : Proper} {xs ys : List Int} {u v : Nat} {gutter gap : Int}
    {r : Rect}
    (hg : 1 ≤ gap)
    (hwr : r.w ≤ RouteImpl.nodeW p u - gutter)
    (hx : r.x = (Labels.textRectAt p xs ys u gutter).x)
    (hsep : RouteImpl.coordSep gap p u v ≤
      RouteImpl.xAt xs v - RouteImpl.xAt xs u) :
    r.x + r.w ≤ (RouteImpl.boxRect p xs ys v).x := by
  rw [textRectAt_left] at hx
  rw [boxRect_left]
  rw [hx]
  unfold RouteImpl.coordSep at hsep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)] at hsep ⊢
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)] at hsep
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by decide)]
  omega

/-! ## Vertical separation across ranks -/

/-- The rank-axis layer height agrees with the route layer height. -/
theorem layerHeight_eq_route (p : Proper) (l : List Nat) :
    CoordsImpl.layerHeight p l = RouteImpl.layerHeight p l := rfl

/-- A node in a strictly earlier rank band ends above every node of a later
rank band. -/
theorem rank_band_above
    {p : Proper} {layers : List (List Nat)} {ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k < k')
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + CoordsImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u ∧
      RouteImpl.yAt ys u + RouteImpl.nodeH p u ≤
        top.getD k 0 + RouteImpl.layerHeight p l)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v) :
    RouteImpl.yAt ys u + RouteImpl.nodeH p u ≤ RouteImpl.yAt ys v := by
  have hb := htop k k' l l' hlt hk hk'
  rw [layerHeight_eq_route] at hb
  omega

/-- A node in a strictly later rank band starts below every node of an earlier
rank band. -/
theorem rank_band_below
    {p : Proper} {layers : List (List Nat)} {ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k' < k)
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + CoordsImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v ∧
      RouteImpl.yAt ys v + RouteImpl.nodeH p v ≤
        top.getD k' 0 + CoordsImpl.layerHeight p l') :
    RouteImpl.yAt ys v + RouteImpl.nodeH p v ≤ RouteImpl.yAt ys u := by
  have hb := htop k' k l' l hlt hk' hk
  rw [layerHeight_eq_route] at hb hbandV
  omega

/-! ## Branch theorems

Each theorem below is the geometric half of one `labelEnvelope` branch: it
converts the executed placement identity of the label rect plus the executed
coordinate separation (from `CoordsImpl.cluster_all_pairs_separated`,
`CoordsImpl.rankAxis_bands_disjoint` / `RouteImpl.CoordFacts.node_in_band`, or
`RouteImpl.plannedLane_right_strict`) into the clause-7 conclusion. -/

/-- **Forward branch, label node first in its layer.** -/
theorem forward_branch_clear_left
    {p : Proper} {xs ys : List Int} {u v : Nat} {gutter gap : Int} {r : Rect}
    (hg : 1 ≤ gap)
    (hrx : r.x = (Labels.textRectAt p xs ys u gutter).x)
    (hrw : r.w ≤ RouteImpl.nodeW p u - gutter)
    (hsep : RouteImpl.coordSep gap p u v ≤
      RouteImpl.xAt xs v - RouteImpl.xAt xs u) :
    ¬ r.meetsInterior (RouteImpl.boxRect p xs ys v) :=
  not_meetsInterior_of_right_le (forward_stack_left_le_box hg hrw hrx hsep)

/-- **Forward branch, foreign node first in its layer.** The label's left edge
stays right of the foreign box, using the measured gutter the envelope adds on
the left of the label-carrying node. -/
theorem forward_branch_clear_right
    {p : Proper} {xs ys : List Int} {u v : Nat} {gutter gap : Int} {r : Rect}
    (hg : 1 ≤ gap) (hgut : 0 ≤ gutter)
    (hrx : r.x = (Labels.textRectAt p xs ys u gutter).x)
    (hsep : RouteImpl.coordSep gap p v u ≤
      RouteImpl.xAt xs u - RouteImpl.xAt xs v) :
    ¬ r.meetsInterior (RouteImpl.boxRect p xs ys v) := by
  apply not_meetsInterior_of_left_le
  rw [hrx, boxRect_left, boxRect_w, textRectAt_left]
  unfold RouteImpl.coordSep at hsep
  simp only [fdiv2_ediv] at hsep ⊢
  omega

/-- **Forward branch, label node in an earlier rank band.** -/
theorem forward_branch_clear_rank
    {p : Proper} {layers : List (List Nat)} {xs ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat} {gutter : Int} {r : Rect}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k < k')
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + CoordsImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u ∧
      RouteImpl.yAt ys u + RouteImpl.nodeH p u ≤
        top.getD k 0 + RouteImpl.layerHeight p l)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v)
    (hry : r.y = (Labels.textRectAt p xs ys u gutter).y)
    (hrh : r.h ≤ RouteImpl.nodeH p u) :
    ¬ r.meetsInterior (RouteImpl.boxRect p xs ys v) := by
  apply not_meetsInterior_of_below
  have hle := rank_band_above hk hk' hlt htop hbandU hbandV
  show r.y + r.h ≤ (RouteImpl.boxRect p xs ys v).y
  rw [hry, textRectAt_y, boxRect_top]
  omega

/-- **Forward branch, foreign node in an earlier rank band.** -/
theorem forward_branch_clear_rank_right
    {p : Proper} {layers : List (List Nat)} {xs ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat} {gutter : Int} {r : Rect}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k' < k)
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + CoordsImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v ∧
      RouteImpl.yAt ys v + RouteImpl.nodeH p v ≤
        top.getD k' 0 + CoordsImpl.layerHeight p l')
    (hry : r.y = (Labels.textRectAt p xs ys u gutter).y) :
    ¬ r.meetsInterior (RouteImpl.boxRect p xs ys v) := by
  apply not_meetsInterior_of_above
  have hle := rank_band_below hk hk' hlt htop hbandU hbandV
  show (RouteImpl.boxRect p xs ys v).y + (RouteImpl.boxRect p xs ys v).h ≤ r.y
  rw [boxRect_top, boxRect_h, hry, textRectAt_y]
  omega

/-- **Reversed branch.** A reversed edge's label sits in its planned lane, which
`RouteImpl.plannedLane_right_strict` places strictly right of the foot of every
node of the run, so the label clears the box of every node of that run. -/
theorem reversed_branch_clear
    {p : Proper} {xs ys : List Int} {v : Nat} {lane slot : Int} {r : Rect}
    (hx : r.x = lane + slot) (hslot : 0 ≤ slot)
    (hge : RouteImpl.laneRight p xs + slot ≤ lane)
    (hv : v < p.nodes.length) :
    ¬ r.meetsInterior (RouteImpl.boxRect p xs ys v) := by
  apply not_meetsInterior_of_left_le
  have hb := RouteImpl.laneRight_bound p xs hv
  rw [hx, boxRect_left, boxRect_w]
  simp only [fdiv2_ediv] at hb ⊢
  omega

/-! ## Self-loop branch -/

/-- A rect contained in an envelope that misses a box's interior itself misses
that interior. -/
theorem not_meetsInterior_of_contained {env r box : Rect}
    (hcont : env.Contained r) (hclear : ¬ env.meetsInterior box) :
    ¬ r.meetsInterior box := by
  intro hm
  apply hclear
  unfold Rect.Contained at hcont
  unfold Rect.meetsInterior at hm ⊢
  omega

/-- Purely coordinate-separation fact for the executed self-loop branch: the
label envelope of the self-loop edge misses the foreign box.  Discharged from
the loop footprint bounds (`loopFootprint`, `loops_result_footprint` in
Layered/FlatC6Loops.lean) plus the executed frame clearance of the run. -/
def LoopFootprintSeparation (_P : PipelineImpl.Params) (_cg : Graph)
    (_run : PipelineImpl.Run) (_labels : List PipelineImpl.MeasuredLabel)
    (_k : Nat) (_e : Edge) (env : Rect) (v : Nat) : Prop :=
  ¬ env.meetsInterior (RouteImpl.boxRect _run.proper _run.xs _run.ys v)

/-- **Self-loop branch.** Every stack rect inside the executed self-loop label
envelope clears a foreign box whenever the envelope does. -/
theorem loop_branch_clear
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {k : Nat} {e : Edge}
    {env : Rect} {v : Nat} {r : Rect}
    (_hk : cg.edges[k]? = some e) (hloop : e.tail = e.head)
    (henv : labelEnvelope P cg run labels k e = some env)
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hr : r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)))
    (hsep : LoopFootprintSeparation P cg run labels k e env v) :
    ¬ r.meetsInterior (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  obtain ⟨hw, hh⟩ := labelEnvelope_loop_size hloop henv
  have hsizes : ∀ s ∈ (routeLabels labels e.decl).map (fun l => (l.width, l.height)),
      0 ≤ s.1 ∧ 0 ≤ s.2 := by
    intro s hs
    obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
    exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
      (hlab l (List.mem_filter.mp hlm).1).2.1⟩
  have hwr : Labels.stackWidth
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤ env.w := by
    rw [hw, stackSize_width_eq]
    exact Int.le_refl _
  have hhr : Labels.stackHeight cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)) ≤ env.h := by
    rw [hh, stackSize_height_eq]
    exact Int.le_refl _
  obtain ⟨_, _, hcont⟩ :=
    Labels.stackRects_contained env cg.slot hslot hsizes hwr hhr r hr
  exact not_meetsInterior_of_contained hcont hsep

/-- Axis-aligned coordinate separation of two rectangles: disjoint
x-projections (either side) or disjoint y-projections.  A pure coordinate
fact about the executed `run.xs`/`run.ys`-derived boxes, never the
`meetsInterior` goal itself. -/
def RectAxisSeparated (a b : Rect) : Prop :=
  a.x + a.w ≤ b.x ∨ b.x + b.w ≤ a.x ∨ a.y + a.h ≤ b.y ∨ b.y + b.h ≤ a.y

/-- **Run-local label clearance.** For an executed run, a measured label's
placed rect `r` inside its `labelEnvelope` misses the `boxRect` of a real
node `v` outside the edge's scope.  The proof splits three ways on the
executed edge form — self-loop, forward, reversed — and each branch
consumes only its own coordinate-separation hypothesis:

* self-loop: `LoopFootprintSeparation` (the envelope misses the box),
  discharged from `loopFootprint`/`loops_result_footprint` plus frame
  clearance;
* forward: `RectAxisSeparated r box`, the coordSep/band separation of the
  label-carrying dummy node from `v`;
* reversed: the foreign box ends left of the label rect, the
  `plannedLane_right_strict` lane bound transported through the envelope. -/
theorem runLocalLabelClearance
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {labels : List PipelineImpl.MeasuredLabel} {k : Nat} {e : Edge}
    {env : Rect} {v : Nat} {r : Rect}
    (hk : cg.edges[k]? = some e)
    (henv : labelEnvelope P cg run labels k e = some env)
    (hslot : 0 ≤ cg.slot)
    (hlab : ∀ l ∈ labels, 0 ≤ l.width ∧ 0 ≤ l.height ∧ 0 ≤ l.gutter)
    (hr : r ∈ Labels.stackRects env.x env.y cg.slot
      ((routeLabels labels e.decl).map fun l => (l.width, l.height)))
    (hsep_loop : e.tail = e.head →
      LoopFootprintSeparation P cg run labels k e env v)
    (hsep_forward : e.tail ≠ e.head → e.reversed = false →
      RectAxisSeparated r (RouteImpl.boxRect run.proper run.xs run.ys v))
    (hsep_reversed : e.tail ≠ e.head → e.reversed = true →
      (RouteImpl.boxRect run.proper run.xs run.ys v).x +
        (RouteImpl.boxRect run.proper run.xs run.ys v).w ≤ r.x) :
    ¬ r.meetsInterior (RouteImpl.boxRect run.proper run.xs run.ys v) := by
  by_cases hloop : e.tail = e.head
  · exact loop_branch_clear hk hloop henv hslot hlab hr (hsep_loop hloop)
  · cases hrev : e.reversed
    · -- forward branch (`e.reversed = false`): axis-separated rectangles
      -- miss interiors.
      rcases hsep_forward hloop hrev with h | h | h | h
      · exact not_meetsInterior_of_right_le h
      · exact not_meetsInterior_of_left_le h
      · exact not_meetsInterior_of_below h
      · exact not_meetsInterior_of_above h
    · -- reversed branch: every node box ends left of the label rect.
      apply not_meetsInterior_of_left_le
      exact hsep_reversed hloop hrev

/-! ## Placed-label pairing -/

/-- A measured label on an edge is one of the measured labels. -/
theorem mem_measured_of_mem_routeLabels
    {labels : List PipelineImpl.MeasuredLabel} {edge : Nat}
    {l : PipelineImpl.MeasuredLabel}
    (hl : l ∈ routeLabels labels edge) : l ∈ labels :=
  (List.mem_filter.mp hl).1

/-- `headD` of a list whose members all equal `a`, with `a` present. -/
theorem headD_eq_of_all {α : Type} [DecidableEq α] (ts : List α) (d a : α)
    (hmem : a ∈ ts) (hall : ∀ x ∈ ts, x = a) : ts.headD d = a := by
  cases ts with
  | nil => exact absurd hmem (by simp)
  | cons b t =>
    have hb : b = a := hall b (by simp)
    rw [hb]
    rfl

/-- The rect `routeLabelRect` pairs with `l` when the executed pairing places
`(l.index, rect)` and no other placed pair carries that index. -/
theorem routeLabelRect_eq
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {measured : List PipelineImpl.MeasuredLabel}
    {l : PipelineImpl.MeasuredLabel} {rect : Rect}
    (hmem : (l.index, rect) ∈ placedLabels P cg run measured)
    (huniq : ∀ q ∈ placedLabels P cg run measured, q.1 = l.index → q.2 = rect) :
    routeLabelRect P cg run measured l = rect := by
  unfold routeLabelRect
  have hfilter_mem : (l.index, rect) ∈
      (placedLabels P cg run measured).filter (fun q => q.1 == l.index) := by
    apply List.mem_filter.mpr
    exact ⟨hmem, by simp⟩
  have hfilter_all : ∀ q ∈ (placedLabels P cg run measured).filter
      (fun q => q.1 == l.index), q = (l.index, rect) := by
    intro q hq
    obtain ⟨hqm, hcond⟩ := List.mem_filter.mp hq
    obtain ⟨qi, ri⟩ := q
    have h1 : qi = l.index := by simpa using hcond
    have h2 : ri = rect := huniq ⟨qi, ri⟩ hqm h1
    exact by rw [h1, h2]
  rw [headD_eq_of_all _ (l.index, ⟨0, 0, 0, 0⟩) (l.index, rect) hfilter_mem
    hfilter_all]

/-- The executed pairing places the stack rect found for a measured label. -/
theorem placedLabels_pair_mem
    {P : PipelineImpl.Params} {cg : Graph} {run : PipelineImpl.Run}
    {measured : List PipelineImpl.MeasuredLabel}
    {l₀ : PipelineImpl.MeasuredLabel} {edge : Nat} {e : Edge} {env : Rect}
    {rect : Rect}
    (hmem0 : l₀ ∈ measured)
    (hfind : cg.edges.findIdx? (fun x => x.decl == l₀.edge) = some edge)
    (he : cg.edges[edge]? = some e)
    (henv : labelEnvelope P cg run measured edge e = some env)
    (hfind2 : ((routeLabels measured e.decl).zip
        (Labels.stackRects env.x env.y cg.slot
          ((routeLabels measured e.decl).map fun q => (q.width, q.height)))).find?
        (fun q => q.1.index == l₀.index) = some (l₀, rect)) :
    (l₀.index, rect) ∈ placedLabels P cg run measured := by
  unfold placedLabels
  apply List.mem_filterMap.mpr
  refine ⟨l₀, hmem0, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨edge, hfind, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨e, he, ?_⟩
  apply Option.bind_eq_some_iff.mpr
  refine ⟨env, henv, ?_⟩
  dsimp only
  rw [hfind2]
  rfl

/-! ## Executed-form branch lemmas -/

/-- A box of height zero has an empty interior, so no rect meets it. -/
theorem not_meetsInterior_of_box_zero_h {a b : Rect} (hh : b.h = 0) :
    ¬ a.meetsInterior b := by
  intro hm
  unfold Rect.meetsInterior at hm
  rw [hh] at hm
  omega

/-- **Forward branch, label node in an earlier rank band, stack-rect form.**
The stack rect is vertically inside the label envelope, whose height is the
label-carrying node's height. -/
theorem forward_stack_clear_rank
    {p : Proper} {layers : List (List Nat)} {ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat} {env r : Rect}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k < k')
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + RouteImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u ∧
      RouteImpl.yAt ys u + RouteImpl.nodeH p u ≤
        top.getD k 0 + RouteImpl.layerHeight p l)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v)
    (henvy : env.y = RouteImpl.yAt ys u)
    (henvh : env.h = RouteImpl.nodeH p u)
    (hry : env.y ≤ r.y ∧ r.y + r.h ≤ env.y + env.h) :
    ¬ r.meetsInterior (RouteImpl.boxRect p ys ys v) := by
  apply not_meetsInterior_of_below
  have hb := htop k k' l l' hlt hk hk'
  have hvy : (RouteImpl.boxRect p ys ys v).y = RouteImpl.yAt ys v := rfl
  show r.y + r.h ≤ (RouteImpl.boxRect p ys ys v).y
  rw [hvy]
  omega

/-- **Forward branch, foreign node in an earlier rank band, stack-rect form.** -/
theorem forward_stack_clear_rank_right
    {p : Proper} {layers : List (List Nat)} {ys top : List Int}
    {k k' : Nat} {l l' : List Nat} {u v : Nat} {env r : Rect}
    (hk : layers[k]? = some l) (hk' : layers[k']? = some l')
    (hlt : k' < k)
    (htop : ∀ r r' (lr lr' : List Nat), r < r' → layers[r]? = some lr →
      layers[r']? = some lr' →
      top.getD r 0 + RouteImpl.layerHeight p lr ≤ top.getD r' 0)
    (hbandU : top.getD k 0 ≤ RouteImpl.yAt ys u)
    (hbandV : top.getD k' 0 ≤ RouteImpl.yAt ys v ∧
      RouteImpl.yAt ys v + RouteImpl.nodeH p v ≤
        top.getD k' 0 + RouteImpl.layerHeight p l')
    (henvy : env.y = RouteImpl.yAt ys u)
    (_henvh : env.h = RouteImpl.nodeH p u)
    (hry : env.y ≤ r.y ∧ r.y + r.h ≤ env.y + env.h) :
    ¬ r.meetsInterior (RouteImpl.boxRect p ys ys v) := by
  apply not_meetsInterior_of_above
  have hb := htop k' k l' l hlt hk' hk
  have hvy : (RouteImpl.boxRect p ys ys v).y = RouteImpl.yAt ys v := rfl
  have hvh : (RouteImpl.boxRect p ys ys v).h = RouteImpl.nodeH p v := rfl
  show (RouteImpl.boxRect p ys ys v).y +
      (RouteImpl.boxRect p ys ys v).h ≤ r.y
  omega

end Elegant.Layered
