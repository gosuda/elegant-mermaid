 import Elegant.Layered.Pipeline
 import Elegant.Layered.LabelsC7RunLocal
 import Elegant.Layered.ForeignNonGroupSpansProof
 import Elegant.Layered.ForeignBorderSpansProof
 import Elegant.Layered.RunLocalSeparationsProof
 import Elegant.Layered.LabelRunBridgeFacts
 import Elegant.Layered.ForeignSpansFacts
 import Elegant.Layered.PipelineFacts
 import Elegant.Layered.SceneBounds
 import Elegant.Layered.GroupWidthFacts
 import Elegant.Layered.Labels
 import Elegant.Layered.ForeignBorderAnchorsProof
 import Elegant.Layered.SideMarkerPathsProof

set_option autoImplicit false

namespace Elegant.Layered.PipelineImpl

/-! # Run-level route-label clearance, by node kind at each in-bounds position

`RouteRunClearInlined` is the inlined (equation-free) form of the route-label
conjunct of `ExecutedPartFrameCores`: every placed route label of one executed
component run misses every in-bounds frame position or lies strictly inside
it. The bound `pos < cg.nodes.length` is load-bearing: at `pos =
cg.nodes.length` `frameRect` reads default nodes and can coincide exactly with
a placed label (see `wip/Probe/PartRouteRunClear.lean`: every in-bounds pair
clears while the out-of-bounds default rects coincide with placed labels).

For an in-bounds `pos`, `frameRect` branches on the kind of component node
there. Let `nd` be that node:

* group frame containing the label dummy (`nd.border = -2`, group decl in the
  dummy's cluster path): the label is strictly inside, via `StrictDummyFrame`
  (the strict dummy counterpart of the proved non-strict
  `frameRect_member_contained`, upgraded with the padding gap; the member form
  is being proved in `StrictMemberFrame.lean`) and `RouteLabelInDummy`.
* group frame not containing it: disjoint, via `SeamsImplyForeign` applied to
  the six named span seams, composed with the inside result for the label's
  own group (`ForeignFramesDisjoint`).
* non-group position: `frameRect` returns the node's own rect (`nodeRect`),
  transported to `RouteImpl.boxRect`. A real proper node outside the edge's
  scope is `RouteLabelRealClear`; a zero-height box meets nothing
  (`not_meetsInterior_of_box_zero_h`); the remaining proper shapes (a nonzero
  dummy, or a real node failing the scope check) are `RouteLabelLeftoverPair`.
* non-forward edges (self-loops, reversed lanes) are `RouteNonforwardLabelClear`.

 `SeamsImplyForeign` takes the three open seam defs (`BracketMarkersAtRank`,
 `ForeignClusterRankSpans`, `ForeignBorderChainXAligned`) as hypotheses by
 their existing names; the other two historical seams are closed
 (`plainClearOfSideMarker'`, `foreignBorderLayerOrder'`) and the marker-span
 alignment is derived (`sideMarkerSpanAligned'`); no parallel seam is introduced.

Residual evidence (`wip/Probe/PartRouteRunClear.lean`, 8 inputs × 4
profiles, 5 candidates each, 1020 in-bounds pairs, 0 violations):
`StrictDummyFrame`: no counterexamples, positive holds on group inputs;
`RouteLabelInDummy`: placed labels contained in their dummies on all inputs
(all edges single-labeled); `ForeignFramesDisjoint`: holds on the sibling-pair
input; `RouteLabelRealClear`: holds on all scope-ok real pairs;
`RouteLabelForeignClear`: holds on all outside pairs; `RouteNonforwardLabelClear`:
holds on the self-loop inputs (no reversed-lane instances on the probe
inputs); `RouteLabelDummyPair`/`RouteLabelScopeFail` sides of
`RouteLabelLeftoverPair`: vacuous on the probe (no in-bounds nonzero dummy,
every scope-failing in-bounds pair has height zero and is handled by the
zero-height case). -/

/-! ## Local glue (proved) -/

/-- Shrinking the inner rectangle preserves strict-inside. -/
private theorem inner_strict_of_sub {o m l : Rect}
    (h : o.StrictInside m) (hs : m.Contained l) : o.StrictInside l := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- Strict-inside implies containment. -/
private theorem strict_to_contained {o l : Rect}
    (h : o.StrictInside l) : o.Contained l := by
  unfold Rect.StrictInside Rect.Contained at *
  omega

/-- `Disjoint` is symmetric. -/
 private theorem disjoint_symm' {a b : Rect} (h : Disjoint a b) : Disjoint b a :=
   fun hm => h ((Rect.meetsInterior_comm _ _).mpr hm)

/-- Containment transports disjointness to the sub-rectangle. -/
private theorem sub_disjoint {f l g : Rect}
    (hsub : f.Contained l) (hdis : Disjoint f g) : Disjoint l g := by
  unfold Disjoint Rect.meetsInterior Rect.Contained at *
  omega

/-- A `findIdx?` hit carries its element and predicate. Copy of the helper in
`Elegant/Chart/TreemapC8bKernelsProof.lean` (which keeps it private). -/
private theorem findIdxHitElem {α : Type} {l : List α} (p : α → Bool) (j : Nat)
    (h : l.findIdx? p = some j) : ∃ x, l[j]? = some x ∧ p x = true := by
  induction l generalizing j with
  | nil => rw [List.findIdx?_nil] at h; exact absurd h (by simp)
  | cons y ys ih =>
    rw [List.findIdx?_cons] at h
    cases hp : p y with
    | true =>
      simp only [hp, ↓reduceIte, Option.some.injEq] at h
      cases j with
      | zero => exact ⟨y, rfl, hp⟩
      | succ j' => exact absurd h (by simp)
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      cases j with
      | zero => exact absurd h (by simp)
      | succ j' =>
        cases hv : ys.findIdx? p with
        | none => rw [hv] at h; simp at h
        | some k =>
          rw [hv, Option.map_some, Option.some.injEq] at h
          have hjk : j' = k := by omega
          obtain ⟨x, hx, hpx⟩ := ih k hv
          exact ⟨x, by simp only [hjk]; simpa using hx, hpx⟩
 /-- `nodeRect` is `RouteImpl.boxRect` at the same index, under a proper lookup. -/
 private theorem nodeRect_eq_boxRect {cg : Graph} {run : Run} {pos : Nat} {pn : ProperNode}
     (hlook : run.proper.nodes[pos]? = some pn) :
     nodeRect cg run pos = RouteImpl.boxRect run.proper run.xs run.ys pos := by
   have hget : run.proper.nodes.getD pos default = pn := by
     rw [List.getD_eq_getElem?_getD, hlook, Option.getD_some]
   have hw : RouteImpl.nodeW run.proper pos = pn.node.w := by
     unfold RouteImpl.nodeW
     simp only [hlook]
   have hh : RouteImpl.nodeH run.proper pos = pn.node.h := by
     unfold RouteImpl.nodeH
     simp only [hlook]
   unfold nodeRect RouteImpl.boxRect RouteImpl.xAt RouteImpl.yAt
   rw [hget, hw, hh]

 private theorem frameRect_eq_nodeRect_of_plain {P : Params} {cg : Graph}
     {run : Run} {pos : Nat} {nd : Node} (hnd : cg.nodes[pos]? = some nd)
     (hplain : nd.border ≠ -2) :
     frameRect P cg run pos = nodeRect cg run pos := by
   have hget : cg.nodes.getD pos default = nd := by
     rw [List.getD_eq_getElem?_getD, hnd, Option.getD_some]
   have hb : ((cg.nodes.getD pos default).border != -2) = true := by
     rw [hget]
     simp only [bne_iff_ne]
     exact hplain
   unfold frameRect
   dsimp only
   rw [ite_eq_left hb]

 /-! ## Membership inversion (proved) -/


 /-- Membership in `placedLabels` unpacks to the source label, its edge, and
 the envelope equation. -/
 theorem placed_mem_unpack {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {rect : Rect}
     (hmem : (k, rect) ∈ placedLabels P cg run labels) :
     ∃ l₀ edge e, l₀ ∈ labels ∧ l₀.index = k ∧
       cg.edges.findIdx? (fun x => x.decl == l₀.edge) = some edge ∧
       cg.edges[edge]? = some e ∧ e.decl = l₀.edge := by
   unfold placedLabels at hmem
   obtain ⟨l₀, hmem0, hsome⟩ := List.mem_filterMap.mp hmem
   cases hfind : cg.edges.findIdx? (fun x => x.decl == l₀.edge) with
   | none => simp [hfind] at hsome
   | some edge' =>
     simp [hfind] at hsome
     cases hget : cg.edges[edge']? with
     | none => simp [hget] at hsome
     | some e' =>
       simp [hget] at hsome
       cases henv : labelEnvelope P cg run labels edge' e' with
       | none => simp [henv] at hsome
       | some env' =>
         simp [henv] at hsome
         cases hfp : List.find? (fun q => q.1.index == l₀.index)
             ((routeLabels labels e'.decl).zip
               (Labels.stackRects env'.x env'.y cg.slot
                 ((routeLabels labels e'.decl).map fun q => (q.width, q.height)))) with
         | none => rw [hfp] at hsome; simp at hsome
         | some pr =>
           simp [hfp] at hsome
           have hk : l₀.index = k := hsome.1
           obtain ⟨x, hx, hpx⟩ := findIdxHitElem _ _ hfind
           have hee : e' = x := Option.some.inj (hget.symm.trans hx)
           have hdecl : e'.decl = l₀.edge := by
             have hpx2 : (x.decl == l₀.edge) = true := hpx
             rw [← hee] at hpx2
             exact beq_iff_eq.mp hpx2
           exact ⟨l₀, edge', e', hmem0, hk, hfind, hget, hdecl⟩

 /-! ## The inlined conclusion -/

 /-- Run-level route-label clearance, equation-free form. -/
 def RouteRunClearInlined (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect), (k, rect) ∈ placedLabels P cg run labels →
     ∀ (pos : Nat), pos < cg.nodes.length →
       Disjoint (frameRect P cg run pos) rect ∨
         (frameRect P cg run pos).StrictInside rect

 /-! ## Run-level residuals (named hypotheses) -/

 /-- Strict dummy frame: every dummy proper node whose cluster path carries a
 group declaration lies strictly inside that group's frame. This is the dummy
 counterpart of the proved non-strict `frameRect_member_contained`, upgraded
 with the padding gap; the member form is being proved in
 `StrictMemberFrameProof.lean`. Probe: `h1dummyBad = 0` on all inputs
 (`h1dummyOk > 0` wherever groups and label dummies occur). -/
 def StrictDummyFrame (P : Params) (cg : Graph) (run : Run) : Prop :=
   ∀ (gpos : Nat) (gn : Node), cg.nodes[gpos]? = some gn → gn.border = -2 →
     ∀ (d : Nat) (nd : ProperNode), nd.dummy = true →
       gn.decl ∈ nd.node.clusterPath →
       (frameRect P cg run gpos).StrictInside (Labels.rectAt run.proper run.xs run.ys d)

 /-- Placed label inside its dummy, single-label forward edges. Probe: `sub`
 holds on every placed label of every run (all probe edges are single-labeled;
 `multi = 0` everywhere); `strictSub` never holds. The `hne`/`hrev` premises
 are load-bearing: a reversed edge with `span ≥ 2` gets a resized chain dummy
 while its label sits in the planned lane, refuting containment. -/
 def RouteLabelInDummy (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     e.tail ≠ e.head → e.reversed = false →
     ∀ (d : Nat) (nd : ProperNode), nd.dummy = true →
       run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d) →
       (Labels.rectAt run.proper run.xs run.ys d).Contained rect

 /-- Foreign frame disjointness: frames of mutually unrelated groups are
 pairwise disjoint. Probe: `h3viol = 0` everywhere, `h3ok = 5` per
 sibling-pair config. -/
 def ForeignFramesDisjoint (P : Params) (cg : Graph) (run : Run) : Prop :=
   ∀ (g1 g2 : Nat) (n1 n2 : Node),
     cg.nodes[g1]? = some n1 → cg.nodes[g2]? = some n2 →
     n1.border = -2 → n2.border = -2 → n1.decl ≠ n2.decl →
     n1.clusterPath.contains n2.decl = false →
     n2.clusterPath.contains n1.decl = false →
     Disjoint (frameRect P cg run g1) (frameRect P cg run g2)

 /-- Seam discharge contract: the three open span seams imply foreign-frame
 disjointness. -/
 def SeamsImplyForeign (P : Params) (cg : Graph) (run : Run) : Prop :=
   BracketMarkersAtRank → ForeignClusterRankSpans → ForeignBorderChainXAligned →
   ForeignFramesDisjoint P cg run

 /-- Real node outside the edge scope: a placed label misses the box of every
 real proper node whose declaration lies outside both endpoint cluster paths.
 This is the placed-form of `LabelsC7.RunLocalLabelClearance`. Probe: `scokV
 = 0` on all scope-ok real pairs. -/
 def RouteLabelRealClear (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     ∀ (v : Nat) (pn : ProperNode), run.proper.nodes[v]? = some pn →
     RouteImpl.IsReal run.proper v →
     RouteImpl.nodeDecl run.proper v ∉ ((cg.nodes[e.tail]?).map (fun n => n.clusterPath)).getD [] →
     RouteImpl.nodeDecl run.proper v ∉ ((cg.nodes[e.head]?).map (fun n => n.clusterPath)).getD [] →
     Disjoint (RouteImpl.boxRect run.proper run.xs run.ys v) rect

 /-- Outside label vs foreign frame: a placed label whose dummy path avoids a
 group declaration misses that group's frame. The `hne`/`hrev` premises are
 load-bearing (as in `RouteLabelInDummy`): the argument routes through the
 label dummy, which only carries forward labels. Probe: `outV = 0` on all
 outside pairs. -/
 def RouteLabelForeignClear (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   BracketMarkersAtRank → ForeignClusterRankSpans → ForeignBorderChainXAligned →
   SeamsImplyForeign P cg run →
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     e.tail ≠ e.head → e.reversed = false →
     ∀ (d : Nat) (nd : ProperNode), nd.dummy = true →
       run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d) →
     ∀ (gpos : Nat) (gn : Node), cg.nodes[gpos]? = some gn → gn.border = -2 →
       gn.decl ∉ nd.node.clusterPath →
       Disjoint (frameRect P cg run gpos) rect

 /-- Non-forward labels: placed labels of self-loops and reversed lanes clear
 every in-bounds frame. Probe: all self-loop in-bounds pairs clear; no
 reversed-lane instances on the probe inputs. -/
 def RouteNonforwardLabelClear (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     (e.tail = e.head ∨ e.reversed = true) →
     ∀ (pos : Nat), pos < cg.nodes.length →
       Disjoint (frameRect P cg run pos) rect ∨ (frameRect P cg run pos).StrictInside rect

 /-- Leftover proper shapes: a placed label against an in-bounds frame whose
 proper node is a nonzero dummy, or a real node failing the scope check.
 Probe: vacuous — `dpos = 0` everywhere, and every scope-failing in-bounds
 pair has height zero (handled by the zero case). -/
 def RouteLabelLeftoverPair (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     ∀ (pos : Nat), pos < cg.nodes.length →
     ∀ (pn : ProperNode), run.proper.nodes[pos]? = some pn →
       ((pn.dummy = true ∧ RouteImpl.nodeH run.proper pos ≠ 0) ∨
         (RouteImpl.IsReal run.proper pos ∧
           ¬(RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.tail]?).map (fun n => n.clusterPath)).getD [] ∧
             RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.head]?).map (fun n => n.clusterPath)).getD []))) →
       Disjoint (frameRect P cg run pos) rect ∨ (frameRect P cg run pos).StrictInside rect

 /-! ## Case lemmas (proved from the hypotheses) -/

 /-- (a) Group frame containing the label dummy: strictly inside. -/
 theorem case_group_inside {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {rect : Rect}
     {l₀ : MeasuredLabel} {edge : Nat} {e : Edge}
     (hmem : (k, rect) ∈ placedLabels P cg run labels)
     (hmem0 : l₀ ∈ labels) (hidx : l₀.index = k)
     (hedge : cg.edges[edge]? = some e) (hdecl : e.decl = l₀.edge)
     (hne : e.tail ≠ e.head) (hrev : e.reversed = false)
     {gpos : Nat} {gn : Node} (hg : cg.nodes[gpos]? = some gn)
     (hgrp : gn.border = -2)
     {d : Nat} {nd : ProperNode} (hdummy : nd.dummy = true)
     (hfindd : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d))
     (hpath : gn.decl ∈ nd.node.clusterPath)
     (h1 : StrictDummyFrame P cg run)
     (h2 : RouteLabelInDummy P cg run labels) :
     (frameRect P cg run gpos).StrictInside rect := by
   have hS := h1 gpos gn hg hgrp d nd hdummy hpath
   have hC := h2 k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev d nd hdummy hfindd
   exact inner_strict_of_sub hS hC

 /-- (b) Group frame not containing the label dummy: disjoint, via the
 label's own group frame and the seam-implied foreign-frame disjointness. -/
 theorem case_group_foreign {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {rect : Rect}
     {l₀ : MeasuredLabel} {edge : Nat} {e : Edge}
     (hmem : (k, rect) ∈ placedLabels P cg run labels)
     (hmem0 : l₀ ∈ labels) (hidx : l₀.index = k)
     (hedge : cg.edges[edge]? = some e) (hdecl : e.decl = l₀.edge)
     (hTail : e.tail ≠ e.head) (hRev : e.reversed = false)
     {d : Nat} {nd : ProperNode} (hdummy : nd.dummy = true)
     (hfindd : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (nd, d))
     {g1pos : Nat} {g1n : Node} (hg1 : cg.nodes[g1pos]? = some g1n)
     (hgrp1 : g1n.border = -2) (hpath1 : g1n.decl ∈ nd.node.clusterPath)
     {gpos : Nat} {gn : Node} (hg2 : cg.nodes[gpos]? = some gn)
     (hgrp2 : gn.border = -2)
     (hunrel1 : g1n.clusterPath.contains gn.decl = false)
     (hunrel2 : gn.clusterPath.contains g1n.decl = false)
     (hne : g1n.decl ≠ gn.decl)
     (h1 : StrictDummyFrame P cg run)
     (h2 : RouteLabelInDummy P cg run labels)
     (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
     (hxalign : ForeignBorderChainXAligned)
     (himp : SeamsImplyForeign P cg run) :
     Disjoint (frameRect P cg run gpos) rect := by
   have hinside : (frameRect P cg run g1pos).StrictInside rect :=
     case_group_inside hmem hmem0 hidx hedge hdecl hTail hRev hg1 hgrp1 hdummy hfindd hpath1 h1 h2
   have hff := himp hbracket hrank hxalign
   have hdis : Disjoint (frameRect P cg run g1pos) (frameRect P cg run gpos) :=
     hff g1pos gpos g1n gn hg1 hg2 hgrp1 hgrp2 hne hunrel1 hunrel2
   have hsub : (frameRect P cg run g1pos).Contained rect :=
     strict_to_contained hinside
   exact disjoint_symm' (sub_disjoint hsub hdis)

 /-- (c, real) Non-group position with a real proper node outside the edge
 scope: disjoint. -/
 theorem case_plain_real {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel} {k : Nat} {rect : Rect}
     {l₀ : MeasuredLabel} {edge : Nat} {e : Edge}
     (hmem : (k, rect) ∈ placedLabels P cg run labels)
     (hmem0 : l₀ ∈ labels) (hidx : l₀.index = k)
     (hedge : cg.edges[edge]? = some e) (hdecl : e.decl = l₀.edge)
     {pos : Nat}
     {nd : Node} (hnd : cg.nodes[pos]? = some nd) (hplain : nd.border ≠ -2)
     {pn : ProperNode} (hlook : run.proper.nodes[pos]? = some pn)
     (hI : RouteImpl.IsReal run.proper pos)
     (hsc1 : RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.tail]?).map (fun n => n.clusterPath)).getD [])
     (hsc2 : RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.head]?).map (fun n => n.clusterPath)).getD [])
     (hReal : RouteLabelRealClear P cg run labels) :
     Disjoint (frameRect P cg run pos) rect := by
   have hfr : frameRect P cg run pos = nodeRect cg run pos :=
     frameRect_eq_nodeRect_of_plain hnd hplain
   have hbr : nodeRect cg run pos = RouteImpl.boxRect run.proper run.xs run.ys pos :=
     nodeRect_eq_boxRect hlook
   have hD := hReal k rect l₀ edge e hmem hmem0 hidx hedge hdecl pos pn hlook hI hsc1 hsc2
   rw [hfr, hbr]
   exact hD

 /-- (c, zero) Non-group position whose proper box has height zero: every
 rect misses it. -/
 theorem case_plain_zero {P : Params} {cg : Graph} {run : Run}
     {pos : Nat} {nd : Node} (hnd : cg.nodes[pos]? = some nd)
     (hplain : nd.border ≠ -2)
     {pn : ProperNode} (hlook : run.proper.nodes[pos]? = some pn)
     (hh : RouteImpl.nodeH run.proper pos = 0) :
     ∀ rect, Disjoint (frameRect P cg run pos) rect := by
   intro rect
   have hfr : frameRect P cg run pos = nodeRect cg run pos :=
     frameRect_eq_nodeRect_of_plain hnd hplain
   have hbr : nodeRect cg run pos = RouteImpl.boxRect run.proper run.xs run.ys pos :=
     nodeRect_eq_boxRect hlook
   have hh0 : (RouteImpl.boxRect run.proper run.xs run.ys pos).h = 0 := hh
   have hD : Disjoint rect (frameRect P cg run pos) := by
     rw [hfr, hbr]
     exact not_meetsInterior_of_box_zero_h hh0
   exact disjoint_symm' hD

 /-! ## Main dispatch -/

 /-- The inlined route-label clearance for an executed run, by case analysis
 on the node kind at each in-bounds position. No single-label premise: the
 placed-label argument uses `stackRects_contained` for every stack rect. The
 dummy-existence premise is conditional on the edge carrying a label (only
 placed edges need dummies; unlabeled span-one edges have none). -/
 theorem route_run_clear_inlined {P : Params} {cg : Graph} {run : Run}
     {labels : List MeasuredLabel}
     (hdummy_ex : ∀ (edge : Nat) (e : Edge), cg.edges[edge]? = some e →
       e.tail ≠ e.head → e.reversed = false →
       (∃ l, l ∈ labels ∧ l.edge = e.decl) →
       ∃ ndd d, ndd.dummy = true ∧ run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (ndd, d))
     (h1 : StrictDummyFrame P cg run)
     (h2 : RouteLabelInDummy P cg run labels)
     (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
     (hxalign : ForeignBorderChainXAligned)
     (himp : SeamsImplyForeign P cg run)
     (hReal : RouteLabelRealClear P cg run labels)
     (hforeign : RouteLabelForeignClear P cg run labels)
     (hloop : RouteNonforwardLabelClear P cg run labels)
     (hleftover : RouteLabelLeftoverPair P cg run labels) :
     RouteRunClearInlined P cg run labels := by
   intro k rect hmem pos hpos
   obtain ⟨l₀, edge, e, hmem0, hidx, hfind, he, hdecl⟩ :=
     placed_mem_unpack hmem
   have hne : cg.nodes[pos]? ≠ none := by
     intro h
     rw [List.getElem?_eq_none_iff] at h
     omega
   obtain ⟨nd, hnd⟩ := Option.ne_none_iff_exists'.mp hne
   by_cases hgrp : nd.border = -2
   · -- group frame at `pos`
     by_cases hfw : e.tail = e.head ∨ e.reversed = true
     · exact hloop k rect l₀ edge e hmem hmem0 hidx he hdecl hfw pos hpos
     · have hne : e.tail ≠ e.head := fun h => hfw (Or.inl h)
       have hnr : e.reversed = false := by
         cases hr : e.reversed with
         | true => rw [hr] at hfw; simp at hfw
         | false => rfl
       obtain ⟨ndd, d, hddummy, hdfind⟩ := hdummy_ex edge e he hne hnr ⟨l₀, hmem0, hdecl.symm⟩
       by_cases hpc : nd.decl ∈ ndd.node.clusterPath
       · have hS := case_group_inside hmem hmem0 hidx he hdecl hne hnr hnd hgrp hddummy hdfind hpc h1 h2
         exact Or.inr hS
       · have hD := hforeign hbracket hrank hxalign himp k rect l₀ edge e hmem hmem0 hidx he hdecl hne hnr d ndd hddummy hdfind pos nd hnd hgrp hpc
         exact Or.inl hD
   · -- non-group position: the node's own rect
     by_cases hfw : e.tail = e.head ∨ e.reversed = true
     · exact hloop k rect l₀ edge e hmem hmem0 hidx he hdecl hfw pos hpos
     · have hne : e.tail ≠ e.head := fun h => hfw (Or.inl h)
       have hnr : e.reversed = false := by
         cases hr : e.reversed with
         | true => rw [hr] at hfw; simp at hfw
         | false => rfl
       cases hpp : run.proper.nodes[pos]? with
       | none =>
         have hget : run.proper.nodes.getD pos default = default := by
           simp only [List.getD_eq_getElem?_getD, hpp, Option.getD_none]
         have hfr : frameRect P cg run pos = nodeRect cg run pos :=
           frameRect_eq_nodeRect_of_plain hnd hgrp
         have hh0 : (nodeRect cg run pos).h = 0 := by
           unfold nodeRect
           rw [hget]
           show (default : ProperNode).node.h = 0
           rfl
         have hD : Disjoint rect (frameRect P cg run pos) := by
           rw [hfr]
           exact not_meetsInterior_of_box_zero_h hh0
         exact Or.inl (disjoint_symm' hD)
       | some pn =>
         by_cases hh0 : RouteImpl.nodeH run.proper pos = 0
         · exact Or.inl (case_plain_zero hnd hgrp hpp hh0 rect)
         · by_cases hreal : pn.dummy = false
           · have hI : RouteImpl.IsReal run.proper pos := fun nd' hnd' => by
               rw [hpp] at hnd'
               have heq : nd' = pn := Option.some.inj hnd'.symm
               rw [heq]
               exact hreal
             by_cases hsc : (RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.tail]?).map (fun n => n.clusterPath)).getD [] ∧ RouteImpl.nodeDecl run.proper pos ∉ ((cg.nodes[e.head]?).map (fun n => n.clusterPath)).getD [])
             · have hD := case_plain_real hmem hmem0 hidx he hdecl hnd hgrp hpp hI hsc.1 hsc.2 hReal
               exact Or.inl hD
             · exact hleftover k rect l₀ edge e hmem hmem0 hidx he hdecl pos hpos pn hpp (Or.inr ⟨hI, hsc⟩)
           · have hdt : pn.dummy = true := by
               cases hd : pn.dummy with
               | true => rfl
               | false => exact absurd hd hreal
             exact hleftover k rect l₀ edge e hmem hmem0 hidx he hdecl pos hpos pn hpp (Or.inl ⟨hdt, hh0⟩)


 /-! ## Executed discharge: from probe residuals to proved facts -/

 /-- New single-case residual (the only one kept): self-loop placed labels
 against in-bounds group frames. Probe (`wip/Probe/PartRouteRunClear.lean`):
 self-loop inputs (`selfSolo`, `selfGrouped`) contribute 45 in-bounds pairs
 across 4 profiles, 0 violations; no reversed-lane instances on the probe.
 Exact missing lemma: `loopFootprint_group_hull_clear` — the loop footprint
 at the loop node stays disjoint from a foreign (or member) group hull in the
 x-separated, y-overlapping, hull-right sub-case. The y-separated and
 hull-left sub-cases, and the loop-on-the-group-node case, are proved inline
 from `loop_envelope_contained` and the footprint shape
 (`footprint = ⟨F.x + F.w, F.y, extent, F.h⟩`); only the hull-right x-extent
 bound is open. -/
 def LoopLabelGroupClear (P : Params) (cg : Graph) (run : Run)
     (labels : List MeasuredLabel) : Prop :=
   ∀ (k : Nat) (rect : Rect) (l₀ : MeasuredLabel) (edge : Nat) (e : Edge),
     (k, rect) ∈ placedLabels P cg run labels → l₀ ∈ labels → l₀.index = k →
     cg.edges[edge]? = some e → e.decl = l₀.edge →
     e.tail = e.head →
     ∀ (pos : Nat), pos < cg.nodes.length →
     ∀ (gn : Node), cg.nodes[pos]? = some gn → gn.border = -2 →
       Disjoint (frameRect P cg run pos) rect ∨ (frameRect P cg run pos).StrictInside rect

 /-- Executed `RouteLabelInDummy` (forward edges only): every placed label lies
 in its dummy rect. No single-label premise (`stackRects_contained` covers every
 stack rect; the probe's `multi = 0` is not needed). The dummy record and size
 come from `forward_anchor_full`; the envelope equation from
 `forward_envelope_eq`. The `hne`/`hrev` premises are load-bearing: a reversed
 edge with `span ≥ 2` gets a resized chain dummy, so the `find?` premise can
 succeed while the lane-placed rect lies right of every node box
 (`RouteImpl.plannedLane_right_strict`), refuting containment. -/
 theorem routeLabelInDummy_of_run {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run) :
     RouteLabelInDummy execution.params
       (componentCandidate execution.graph comp candidate) run execution.measured := by
   intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl hne hrev d nd _hdummy hfindd
   have hnd := measureLabels_index_nodup execution.measured_eq
   obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
     placedLabels_pair_inv hnd hmem
   have hml : ml = l₀ :=
     measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
   have hdecl' : e'.decl = ml.edge := by
     obtain ⟨x, hx, hpx⟩ := findIdxHitElem _ _ hfind
     have hee : e' = x := Option.some.inj (he'.symm.trans hx)
     have hpx2 : (x.decl == ml.edge) = true := hpx
     rw [← hee] at hpx2
     exact beq_iff_eq.mp hpx2
   subst hml
   have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
   have hdecls :=
     componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
   have heq : edge = edge' := by
     have hmap : ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge]? =
         ((componentCandidate execution.graph comp candidate).edges.map Edge.decl)[edge']? := by
       simp only [List.getElem?_map, hedge, he', Option.map_some]
       exact congrArg some hdd
     have hlen : edge <
         ((componentCandidate execution.graph comp candidate).edges.map Edge.decl).length := by
       simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
     exact (hdecls.getElem?_inj hlen).mp hmap
   subst heq
   have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
   have hne' : e'.tail ≠ e'.head := by
     intro hcon
     rw [← hEE] at hcon
     exact hne hcon
   have hrev' : e'.reversed = false := by
     rw [← hEE]
     exact hrev
   rw [hEE] at hfindd
   obtain ⟨first, q, hfirst, hqfind, hqenv⟩ := forward_envelope_eq hne' hrev' henv
   obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, _hdummyA, _hborderA, hwA, hhA⟩ :=
     forward_anchor_full hrun he' hne' hfirst
   rw [labelAnchorIndex_eq] at hanchor
   have hu : q.2 = aindex := by
     rw [hqfind] at hanchor
     exact Option.some.inj hanchor
   have hqq : q = (nd, d) := Option.some.inj (hqfind.symm.trans hfindd)
   have hq2 : q.2 = d := congrArg Prod.snd hqq
   have hq1a : q.1 = nd := congrArg Prod.fst hqq
   have hmemq : run.proper.nodes[q.2]? = some q.1 :=
     List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hqfind)
   have hnodeA' : run.proper.nodes[q.2]? = some and := by
     rw [hu]
     exact hnodeA
   have hq1b : q.1 = and := Option.some.inj (hmemq.symm.trans hnodeA')
   have hndand : nd = and := hq1a.symm.trans hq1b
   have hlab := execution.measured_nonneg
   have hfm : first ∈ routeLabels execution.measured e'.decl := by
     cases hrfl : routeLabels execution.measured e'.decl with
     | nil => simp [hrfl] at hfirst
     | cons hd tl =>
       have heq2 : hd = first := by
         have h2 := hfirst
         rw [hrfl] at h2
         simpa using h2
       subst heq2
       exact List.mem_cons_self
   have hg0 : 0 ≤ first.gutter := (hlab first (List.mem_filter.mp hfm).1).2.2
   have hsizes : ∀ s ∈ (routeLabels execution.measured e'.decl).map
       fun l => (l.width, l.height), 0 ≤ s.1 ∧ 0 ≤ s.2 := by
     intro s hs
     obtain ⟨l, hlm, rfl⟩ := List.mem_map.mp hs
     exact ⟨(hlab l (List.mem_filter.mp hlm).1).1,
       (hlab l (List.mem_filter.mp hlm).1).2.1⟩
   have hslot := componentRun_slot_nonneg hrun
   have hmemd : run.proper.nodes[d]? = some nd := by
     rw [← hq2, ← hq1a]
     exact hmemq
   have hWd : RouteImpl.nodeW run.proper d = nd.node.w := by
     unfold RouteImpl.nodeW
     rw [hmemd]
   have hHd : RouteImpl.nodeH run.proper d = nd.node.h := by
     unfold RouteImpl.nodeH
     rw [hmemd]
   have he2 : env = Labels.textRectAt run.proper run.xs run.ys d first.gutter := by
     rw [hqenv, hq2]
   have henvW : env.w = nd.node.w - first.gutter := by
     simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
   have henvH : env.h = nd.node.h := by
     simp only [he2, Labels.textRectAt, Labels.rectAt, Labels.labelRect, hWd, hHd]
   have hmemstk : rect ∈ Labels.stackRects env.x env.y
       ((componentCandidate execution.graph comp candidate).slot)
       ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) := by
     have hmstk := List.mem_of_find?_eq_some hfindstk
     have hzip := (List.of_mem_zip hmstk).2
     rw [← hrfl] at hzip
     exact hzip
   have hw : Labels.stackWidth
       ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.w := by
     have hwA' : Labels.stackWidth
         ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤
         and.node.w - first.gutter := by
       rw [stackSize_width_eq] at hwA
       omega
     rw [henvW, hndand]
     exact hwA'
   have hh : Labels.stackHeight
       ((componentCandidate execution.graph comp candidate).slot)
       ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) ≤ env.h := by
     rw [henvH, hndand, hhA, stackSize_height_eq]
     exact Int.le_refl _
   obtain ⟨_, _, hcont⟩ := Labels.stackRects_contained env
       ((componentCandidate execution.graph comp candidate).slot) hslot hsizes hw hh
       rect hmemstk
   have hsub : (Labels.rectAt run.proper run.xs run.ys d).Contained env := by
     have hex : env.x = (Labels.rectAt run.proper run.xs run.ys d).x + first.gutter := by
       rw [he2]
       rfl
     have hey : env.y = (Labels.rectAt run.proper run.xs run.ys d).y := by
       rw [he2]
       rfl
     have how : (Labels.rectAt run.proper run.xs run.ys d).w = nd.node.w := by
       unfold Labels.rectAt Labels.labelRect
       exact hWd
     have hoh : (Labels.rectAt run.proper run.xs run.ys d).h = nd.node.h := by
       unfold Labels.rectAt Labels.labelRect
       exact hHd
     unfold Rect.Contained
     omega
   exact Rect.Contained.trans hsub hcont

 /-- Executed `RouteLabelRealClear`: a placed label misses the box of every
 real proper node outside the edge's endpoint cluster paths. Each edge form
 uses its own proved separation (`runLocalForwardSeparation`,
 `runLocalReversedSeparation`, `runLocalLoopSeparation` via `hfoot`) through
 `runLocalLabelClearance`/`loop_branch_clear`; the scope premises are unused
 by the forward proof, so scope-ok endpoint boxes are covered too. -/
 theorem routeLabelRealClear_of_run {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (comp : List Nat) (candidate : Nat) (run : Run)
     (orderOptions : OrderOptions) (cg : Graph)
     (hcomp : comp ∈ components execution.graph)
     (hcg : cg = componentCandidate execution.graph comp candidate)
     (hrun : componentRun execution.params cg execution.measured orderOptions = .ok run)
     (hfoot : RunLocalLoopFootprint inp o res) :
     RouteLabelRealClear execution.params cg run execution.measured := by
   intro k rect l₀ edge e hmem hmem0 hidx hedge hdecl v pn hlook hI hsc1 hsc2
   have hnd := measureLabels_index_nodup execution.measured_eq
   obtain ⟨ml, edge', e', env, _rect', hmlmem, hmlidx, hfind, he', henv, hfindstk, hrfl⟩ :=
     placedLabels_pair_inv hnd hmem
   have hml : ml = l₀ :=
     measured_eq_of_index_eq _ hnd ml l₀ hmlmem hmem0 (hmlidx.trans hidx.symm)
   have hdecl' : e'.decl = ml.edge := by
     obtain ⟨x, hx, hpx⟩ := findIdxHitElem _ _ hfind
     have hee : e' = x := Option.some.inj (he'.symm.trans hx)
     have hpx2 : (x.decl == ml.edge) = true := hpx
     rw [← hee] at hpx2
     exact beq_iff_eq.mp hpx2
   subst hml
   have hdd : e.decl = e'.decl := hdecl.trans hdecl'.symm
   have hdecls : (cg.edges.map Edge.decl).Nodup := by
     rw [hcg]
     exact componentCandidate_decls_nodup_of_measuredGraph execution.graph_eq comp candidate
   have heq : edge = edge' := by
     have hmap : (cg.edges.map Edge.decl)[edge]? = (cg.edges.map Edge.decl)[edge']? := by
       simp only [List.getElem?_map, hedge, he', Option.map_some]
       exact congrArg some hdd
     have hlen : edge < (cg.edges.map Edge.decl).length := by
       simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp hedge).1
     exact (hdecls.getElem?_inj hlen).mp hmap
   subst heq
   have hEE : e = e' := Option.some.inj (hedge.symm.trans he')
   have hsc1' : RouteImpl.nodeDecl run.proper v ∉
       ((cg.nodes[e'.tail]?).map (fun n => n.clusterPath)).getD [] := by
     rw [← hEE]
     exact hsc1
   have hsc2' : RouteImpl.nodeDecl run.proper v ∉
       ((cg.nodes[e'.head]?).map (fun n => n.clusterPath)).getD [] := by
     rw [← hEE]
     exact hsc2
   have hv : v < run.proper.nodes.length := (List.getElem?_eq_some_iff.mp hlook).1
   have hmemstk : rect ∈ Labels.stackRects env.x env.y cg.slot
       ((routeLabels execution.measured e'.decl).map fun l => (l.width, l.height)) := by
     have hmstk := List.mem_of_find?_eq_some hfindstk
     have hzip := (List.of_mem_zip hmstk).2
     rw [← hrfl] at hzip
     exact hzip
   have hslot := componentRun_slot_nonneg hrun
   have hlab := execution.measured_nonneg
   by_cases hloop : e'.tail = e'.head
   · have hsep := runLocalLoopSeparation _ _ _ hfoot execution comp candidate run
       orderOptions cg edge e' env v hcomp hcg hrun he' hloop henv hv hI hsc1' hsc2'
     have hclear := loop_branch_clear he' hloop henv hslot hlab hmemstk hsep
     unfold Disjoint
     rw [Rect.meetsInterior_comm]
     exact hclear
   · by_cases hrev : e'.reversed = true
     · have hle := runLocalReversedSeparation _ _ _ execution comp candidate run
         orderOptions cg edge e' env v rect hcomp hcg hrun he' hloop hrev henv hv
         hI hsc1' hsc2' hmemstk
       unfold Disjoint Rect.meetsInterior
       omega
     · have hrev' : e'.reversed = false := by
         cases hr : e'.reversed with
         | true => exact absurd hr hrev
         | false => rfl
       have hsep := runLocalForwardSeparation _ _ _ execution comp candidate run
           orderOptions cg edge e' env v rect hcomp hcg hrun he' hloop hrev' henv
           hv hI hsc1' hsc2' hmemstk
       have hdis := RectAxisSeparated_of_not_meetsInterior hsep
       unfold Disjoint
       rw [Rect.meetsInterior_comm]
       exact hdis

 /-- Executed `SeamsImplyForeign`/`ForeignFramesDisjoint`: the open span seams
 imply foreign-frame disjointness on the executed run. The group half
 (`ForeignClusterRankSpans`, `ForeignBorderChainXAligned`) plus the closed
 `foreignBorderLayerOrder'` give `ForeignBorderSpansSeparated`; the marker
 half (`BracketMarkersAtRank`, `SideMarkerSpanAligned`) plus the closed
 `plainClearOfSideMarker'` give `ForeignNonGroupSpansClear`;
 `foreignSpansClear_of_run` composes them into `ForeignSpansClear`, which
 specializes to `ForeignFramesDisjoint` (the group-vs-group case). -/
 theorem foreignFramesDisjoint_of_run {inp : Input} {o : Options} {res : FamilyResult}
     (execution : SceneExecution inp o res)
     (hwf : WellFormed (inputModel inp o)) (hfp : framedParents inp = true)
     {comp : List Nat} (hcomp : comp ∈ components execution.graph)
     {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
     (hrun : componentRun execution.params
       (componentCandidate execution.graph comp candidate) execution.measured
       orderOptions = .ok run)
     (hbracket : BracketMarkersAtRank)
     (hrank : ForeignClusterRankSpans) (hxalign : ForeignBorderChainXAligned) :
     ForeignFramesDisjoint execution.params
       (componentCandidate execution.graph comp candidate) run := by
   have hgraph := execution.graph_eq
   have hlines : execution.lines.length = inp.boxes.length :=
     boxLines_length execution.lines_eq
   have hgroups : ForeignBorderSpansSeparated :=
     foreignBorderSpansSeparated hrank foreignBorderLayerOrder' hxalign
   have halign : SideMarkerSpanAligned := sideMarkerSpanAligned' hxalign
   have hothers : ForeignNonGroupSpansClear :=
     foreignNonGroupSpansClear hbracket plainClearOfSideMarker' halign
   have hclear := foreignSpansClear_of_run hgroups hothers hgraph hlines hwf hfp hcomp hrun
   intro g1 g2 n1 n2 hg1 hg2 hgrp1 hgrp2 hne hu1 hu2
   exact hclear g1 g2 n1 n2 hg1 hg2 hgrp1 hne hu2 hu1

 /-- Labeled-edge dummy existence on executed runs: every forward edge carrying
 a label has its mid-rank anchor dummy. The labeled edge has a head label
 (the witness list entry), hence an anchor by `forward_anchor_full`, which is
 the `find?` witness by `labelAnchorIndex_eq`. -/
 theorem dummy_ex_labeled_of_run {inp : Input} {o : Options} {res : FamilyResult}
   (execution : SceneExecution inp o res)
   {comp : List Nat} (_hcomp : comp ∈ components execution.graph)
   {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
   (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
     execution.measured orderOptions = .ok run) :
   ∀ (edge : Nat) (e : Edge),
     (componentCandidate execution.graph comp candidate).edges[edge]? = some e →
       e.tail ≠ e.head → e.reversed = false →
       (∃ l, l ∈ execution.measured ∧ l.edge = e.decl) →
       ∃ ndd d, ndd.dummy = true ∧ run.proper.nodes.zipIdx.find?
         (fun q => q.1.edge == some edge && rk run.proper.rank q.2 ==
           rk run.proper.rank e.tail + Int.fdiv
             (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) = some (ndd, d) := by
   intro edge e he hne _hrev ⟨l, hlm, hledge⟩
   have hbe : (l.edge == e.decl) = true := by simp [hledge]
   have hmem_f : l ∈ routeLabels execution.measured e.decl :=
     List.mem_filter.mpr ⟨hlm, hbe⟩
   obtain ⟨first, hfirst⟩ : ∃ first, (routeLabels execution.measured e.decl).head? = some first := by
     cases hcon : routeLabels execution.measured e.decl with
     | nil => rw [hcon] at hmem_f; simp at hmem_f
     | cons f r => exact ⟨f, rfl⟩
   obtain ⟨aindex, and, hanchor, hnodeA, _hedgeA, hdummyA, _hborderA, _hwA, _hhA⟩ :=
     forward_anchor_full hrun he hne hfirst
   rw [labelAnchorIndex_eq] at hanchor
   cases hfq : run.proper.nodes.zipIdx.find? (fun q => q.1.edge == some edge && rk run.proper.rank q.2 == rk run.proper.rank e.tail + Int.fdiv (rk run.proper.rank e.head - rk run.proper.rank e.tail) 2) with
   | none => rw [hfq] at hanchor; simp at hanchor
   | some q =>
     obtain ⟨qd, d⟩ := q
     have hd_eq : d = aindex := Option.some.inj (by rw [hfq] at hanchor; simpa using hanchor)
     have hmemq : run.proper.nodes[d]? = some qd :=
       List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hfq)
     have hqd : qd = and := by
       rw [hd_eq] at hmemq
       exact Option.some.inj (hmemq.symm.trans hnodeA)
     have hqdum : qd.dummy = true := by rw [hqd]; exact hdummyA
     exact ⟨qd, d, hqdum, rfl⟩

 /-- Executed run clearance from the inlined dispatch and the discharged
 `of_run` lemmas. Dummy existence is proved (`dummy_ex_labeled_of_run`); every
 still-open residual is an explicit hypothesis: `StrictDummyFrame`, the three open
 span seams, `RouteLabelForeignClear`, `RouteNonforwardLabelClear`,
 `RouteLabelLeftoverPair`, and `RunLocalLoopFootprint` (for the real-node
 case). -/
 theorem route_run_clear_executed {inp : Input} {o : Options} {res : FamilyResult}
   (execution : SceneExecution inp o res) (hwf : WellFormed (inputModel inp o))
   (hframed : framedParents inp = true)
   {comp : List Nat} (hcomp : comp ∈ components execution.graph)
   {candidate : Nat} {run : Run} {orderOptions : OrderOptions}
   (hrun : componentRun execution.params (componentCandidate execution.graph comp candidate)
     execution.measured orderOptions = .ok run)
   (hstrict : StrictDummyFrame execution.params
     (componentCandidate execution.graph comp candidate) run)
   (hbracket : BracketMarkersAtRank) (hrank : ForeignClusterRankSpans)
   (hxalign : ForeignBorderChainXAligned)
   (hforeign : RouteLabelForeignClear execution.params
     (componentCandidate execution.graph comp candidate) run execution.measured)
   (hloop : RouteNonforwardLabelClear execution.params
     (componentCandidate execution.graph comp candidate) run execution.measured)
   (hleftover : RouteLabelLeftoverPair execution.params
     (componentCandidate execution.graph comp candidate) run execution.measured)
   (hfoot : RunLocalLoopFootprint inp o res) :
   RouteRunClearInlined execution.params
     (componentCandidate execution.graph comp candidate) run execution.measured := by
   have h2 := routeLabelInDummy_of_run execution hcomp hrun
   have hReal := routeLabelRealClear_of_run execution comp candidate run orderOptions
     (componentCandidate execution.graph comp candidate) hcomp rfl hrun hfoot
   have himp : SeamsImplyForeign execution.params
       (componentCandidate execution.graph comp candidate) run :=
     fun hb' hr' hx' =>
       foreignFramesDisjoint_of_run execution hwf hframed hcomp hrun hb' hr' hx'
   have hdummy := dummy_ex_labeled_of_run execution hcomp hrun
   exact route_run_clear_inlined hdummy hstrict h2 hbracket hrank hxalign
     himp hReal hforeign hloop hleftover

 end Elegant.Layered.PipelineImpl