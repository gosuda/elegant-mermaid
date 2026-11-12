# Ports and orthogonal routing

This file defines the ports, the orthogonal routing with slot assignment, the reversed-edge lanes, the self-loops, the route labels, and the corners of the layered family.

## Ports

- routing-01: Ports MUST belong to the triple (node, side, neighbour). [just lean-parity]
    A node has top ports for its distinct upper neighbours and bottom ports for its distinct lower neighbours.
- routing-02: Each chain edge MUST leave its source through a bottom port and enter its target through a top port. [just lean-parity]
- routing-03: Port `i` of `k` on a side (0-indexed in port order) MUST sit at `x = L + floor_div((i + 1) * w, k + 1)`. [just lean-parity]
    `L` is the left border and `w` the width of the node.
- routing-04: The port count `k` MUST be known after the ordering phase, so the size phase can size the node, and port positions MUST be set after the cross-axis coordinate phase. [just lean-parity]
- routing-05: Port order on a side MUST be the neighbour's `x`, then the neighbour's `decl`. [just lean-parity]
- routing-06: A label node MUST have one top port and one bottom port, both at its left border `x - floor_div(w, 2)`. [just lean-parity]
- routing-07: Edges that share a triple MUST share a trunk: they use one segment in the routing phase. [just lean-parity]
- routing-08: A layered kind MUST use top and bottom ports only. [just lean-parity]
    Grid kinds place side ports by the Architecture rules of spec/layout/grid.md.

## Label chains

- routing-09: The chain route of a label node MUST run along the box's left border, so it does not cross the label text. [just lean-parity]

## Orthogonal routing

- routing-10: In a layered kind, between rank `r` and rank `r + 1`, each chain edge MUST be one route: a stub from its source bottom port down to the slot line of its segment, one horizontal run on that line, and a stub from the line down to its target top port. [just lean-parity]
- routing-11: The slot line of slot index `s` in `0 .. S_r - 1` MUST be `ys(s) = rank_top[r] + H_r + slot * (s + 1) + floor_div(slot, 2)`. [just lean-parity]
    Every slot line lies above `rank_top[r + 1]`, because `floor_div(slot, 2) < rank_gap` in both profiles.
- routing-12: The stub length MUST be the distance from the port to its slot line, and it MUST be at least `slot`. [just lean-parity]
    `ys(0) - (rank_top[r] + H_r)` is at least `slot`.
- routing-13: A segment MUST be a horizontal run from `x_src` (source port) to `x_tgt` (target port), with the interval `[min(x_src, x_tgt), max(x_src, x_tgt)]`. [just lean-parity]
    A segment with `x_src = x_tgt` is straight. A straight segment takes no slot and conflicts with nothing.
- routing-14: Two non-straight segments in one channel MUST count as conflicting exactly when their closed intervals intersect and they do not share a trunk (same source triple and same target triple). [just lean-parity]
- routing-15: A conflict arc MUST point from `a` to `b` when `(x_src(a), decl(a))` is lexicographically lower than `(x_src(b), decl(b))`, and the arc means `slot(a) < slot(b)`. [just lean-parity]
    No cycle guard runs. A segment's `decl` is the lowest `decl` of its edges. Arcs run in the total order `(x_src, decl)` on segments, so they form no cycle.
- routing-16: Slot numbering MUST use Kahn's algorithm, taking the ready segment with the lowest `decl` first. [just lean-parity]
    A segment with no predecessor gets slot 0. Any other segment gets `1 + max slot(predecessor)`.
- routing-17: `S_r` MUST be `max slot + 1` over the non-straight segments of the channel, or 0 when there are none. [just lean-parity]
- routing-18: Edges that share a trunk MUST use one segment, one slot, and one drawn line. [just lean-parity]
- routing-19: In the vector profile, a corner between segments of lengths `l1` and `l2` MUST have the radius `min(corner_radius, floor_div(min(l1, l2), 2))`. [just go-check]
- routing-20: In the cell profile, corners MUST be square and drawn with box-drawing glyphs. [just lean-parity]
    Every slot is one cell wide.

## Reversed-edge lanes

- routing-21: A reversed edge of a layered kind MUST be drawn from its original source `s` to its original target `t` as one route of six points: `(px_s, s.y)`, `(px_s, cs)`, `(lane, cs)`, `(lane, ct)`, `(px_t, ct)`, `(px_t, t.y + t.h)`. [just lean-parity]
    `px_s` is the top port of `s` and `px_t` the bottom port of `t` on this edge's chain. The forward chain runs from `t` to `s`, so `rank[s] - rank[t] >= 1`, or `>= 2` when the edge is labelled (the rank phase). Hence `s` is never in rank 0, `t` is never in the last rank, and `s` and `t` never share a rank.
- routing-22: `cs` MUST be a slot line of gap `rank[s] - 1`, the gap below rank `rank[s] - 1` and above the rank of `s`, and `ct` MUST be a slot line of gap `rank[t]`, the gap below the rank of `t`. [just lean-parity]
    The run from `px_s` to the lane is one routing segment of gap `rank[s] - 1`. The run from `px_t` to the lane is one routing segment of gap `rank[t]`. Each segment has `x_src` at its port and `x_tgt` at the lane.
- routing-23: When `rank[s] = rank[t] + 1`, both runs MUST lie in one gap, and they MUST conflict there, because both reach the lane, so `cs` and `ct` MUST differ. [just lean-parity]
- routing-24: Lanes MUST lie on the trailing side (internal right), beyond every node. [just lean-parity]
    They do not lie beyond the top or bottom rank, because a route there would cross the interior ranks.
- routing-25: `R` MUST be `max over every node v of the component's proper graph (real, dummy, label, and border nodes) of (xr_v + E_v)`, where `E_v` is the loop extent (0 for a node without loops). [just lean-parity]
    No loop of `v` reaches past `xr_v + E_v`. Here `xr_v = x_v - floor_div(w_v, 2) + w_v` is the right border of node `v`, where `x_v` is its centre.
- routing-26: `max_lw` MUST be the widest label among the reversed edges of the component, or 0 when none is labelled, and the lane of the `i`-th reversed edge of the component in declaration order (0-based) MUST be `lane_i = R + slot + i * (2 * slot + max_lw)`. [just lean-parity]
    A label box of width `max_lw`, with one `slot` of clearance on each side, fits between lane `i` and lane `i + 1`.
- routing-27: A labelled reversed edge MUST have its label box centred at `(lane_i + slot + floor_div(lw_i, 2), floor_div(ct + cs, 2))`, right of its lane, so the lane line does not cross the text. [just lean-parity]
    The box ends one `slot` before lane `i + 1`, and `lw_i` is the label width of the size phase. Its label node stays in its chain for ordering and separation, and the chain nodes of a reversed edge are not drawn.
- routing-28: A reversed run MUST share no trunk, because its far end is its own lane. [just lean-parity]
- routing-29: The routing phase MUST route no chain edge of a reversed edge, and its two runs MUST take part in the slot numbering in their place. [just lean-parity]
- routing-30: The component bounding box MUST include every lane and every reversed label box, so the last lane's label lies inside the canvas. [just lean-parity]

## Self-loops

- routing-31: For node `v` with `K` loops, loop `k` (0-based, in declaration order at `v`) MUST use `loop_band = max(2 * slot, tallest label height among the loops of v)`. [just lean-parity]
- routing-32: Loop `k` MUST have `b_k = y_v + k * loop_band`, ports `ya_k = b_k + floor_div(loop_band, 2) - slot` and `yb_k = b_k + floor_div(loop_band, 2) + slot`, and the four points `(xr_v, ya_k)`, `(xr_v + slot * (k + 1), ya_k)`, `(xr_v + slot * (k + 1), yb_k)`, and `(xr_v, yb_k)`. [just lean-parity]
- routing-33: If the loop has a label, its left border MUST be at `xr_v + slot * (k + 2)` and its vertical centre MUST be at `b_k + floor_div(loop_band, 2)`. [just lean-parity]
- routing-34: The loop extent MUST be `E_v = sum over k of (slot * (k + 2) + lw_k)`, where `lw_k` is the label width of loop `k` (0 without a label). [just lean-parity]
    The size phase uses `E_v` in `wsep` (spec/layout/layered.md).
- routing-35: A node with `K` self-loops MUST satisfy `h = max(h, 2 * K * loop_band)`. [just lean-parity]
    The height rule keeps every loop band above `yc_v = y_v + floor_div(h_v, 2)`, the vertical centre of `v`.

## Tie-breaks

- routing-36: The routing phases MUST break ties by this table. [just lean-parity]
    |Phase|Deterministic rule|
    |---|---|
    |Port order|neighbour `x`, then neighbour declaration index|
    |Slot assignment|number slots in topological order of the conflict arcs, lowest declaration index first; the arcs form no cycle, so no cycle removal runs|
    |Slot arc|a conflict arc points from `a` to `b` when `(x_src(a), decl(a))` is lower than `(x_src(b), decl(b))`; the arc means `slot(a) < slot(b)`|
    |Reversed lanes|lane index follows declaration order of the reversed edges|
    |Self-loops|loop index follows declaration order at the node|
