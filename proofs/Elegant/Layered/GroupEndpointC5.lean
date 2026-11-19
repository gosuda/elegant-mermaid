import Elegant.Layered.RouteProxyStart
import Elegant.Layered.ExecutedPortsFacts

set_option autoImplicit false

/-! ### Group endpoint attachment (C5, parent/route attachment)

The route-attachment statement for group endpoints is the same statement as
`componentRun_ordinary_route_attachment` without the `hsource`/`htarget`
plainness premises: an endpoint whose graph node carries `border = -2` attaches
to the *frame* `frameRect P cg run v` rather than to the proxy's own
`boxRect`.  The transported `frameRect` then replaces the plain rectangle in
the `onBoundary` conclusions.

The facts that statement needs are proved in `RouteProxyStart`:

* `componentRun_group_proxy_ys_eq_top` — the routed `ys` of a group top proxy
  is its layer top `run.top[k]`, so the stored port point of a group endpoint
  has vertical coordinate `frameRect.y` once the frame top is known;
* `frameRect_top_eq_of_members` — the frame top equals that routed `ys` as
  soon as every member of the cluster is routed at or below the top proxy;
* `componentRun_group_frame_x_contains_port` — the proxy port span is a
  sub-interval of the frame's horizontal hull, using
  `componentRun_proxy_interval` and `proxySpan_endpoint_sources` over the
  `border = -1` side records that also enter `frameRect`;
* `componentRun_group_frame_boundary` — composition of the three, giving
  `Validator.onBoundary ⟨px, run.ys.getD v 0⟩ (frameRect P cg run v)`.

Two obligations remain before the attachment theorem itself can be stated
without extra hypotheses:

1. *Member routing bound* (`hlow` in `componentRun_group_frame_boundary`):
   every proper node whose `clusterPath` contains the group declaration is
   routed with `run.ys.getD v 0 ≤ run.ys.getD u 0`.  For a component-candidate
   graph this decomposes into
   `ranked_compound_member_interval` (plain members), `ranked_compound_child_interval`
   plus a fuel induction over `clusterPath` length (nested groups, in the style
   of `componentRun_group_top_lt_bottom`), the constant/side ranks introduced by
   `titleReservations`/`addClusterBorders`, and the chain-position ranks of
   `componentRun_labeled_chain_rank_positions` for label dummies; each case then
   transfers the rank bound to a `ys` bound through `proxyYs`, `rankAxis_node_in_band`
   and `top_mono`.
2. *Endpoint shape transfers*: for a `border = -2` graph node `v`, the
   coordinate node's `border`/`clusterPath.getLast?` facts (`hborder`,
   `howner`) and its `frameKind`, plus `pc_frame_flat` for the proxy's zero
   height, so that both `pieceStart` forms (top attach, and the reversed
   bottom attach `ys + nodeH`) collapse to `⟨px, run.ys.getD v 0⟩` on the frame
   top.

With those in hand the attachment proof mirrors
`componentRun_ordinary_route_attachment`: `route_endpoints_on_ports` gives the
four endpoint forms, plain endpoints rewrite through
`plain_frame_eq_boxRect` (re-derived locally, since it is private), group
endpoints apply `componentRun_group_frame_boundary`, and
`onBoundary_shift`/`onBoundary_orient` transport each conclusion.
-/

namespace Elegant.Layered.PipelineImpl

/-- Re-derivation of the private `plain_frame_eq_boxRect`: a graph node that is
not a group has `frameRect = boxRect`. -/
theorem plain_frame_eq_boxRect' (P : Params) (cg : Graph) (run : Run)
    (v : Nat) (hv : v < run.proper.nodes.length)
    (hplain : (cg.nodes.getD v default).border ≠ -2) :
    frameRect P cg run v = boxRect run.proper run.xs run.ys v := by
  have hb : ((cg.nodes.getD v default).border != -2) = true := by
    simp only [bne_iff_ne]
    exact hplain
  unfold frameRect
  dsimp only
  rw [ite_eq_left hb]
  simp only [nodeRect,
    boxRect, RouteImpl.xAt, RouteImpl.yAt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv,
    Option.getD_some, RouteImpl.nodeW, RouteImpl.nodeH]

end Elegant.Layered.PipelineImpl
