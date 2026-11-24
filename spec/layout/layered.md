# Layered layout family

This file defines the layered layout family: its conventions, its pipeline phases, its deterministic tie-breaks, its constants, its files, and its proofs.

## Conventions

- layered-01: All layered arithmetic MUST be integer. [just lean-parity]
    Intermediate values are `int64` with checked operations. A coordinate outside `int32`, or an intermediate outside `int64`, returns `ErrOverflow` in all three implementations.
- layered-02: Every operand of `floor_div` in the layered phases MUST be non-negative unless the rule states otherwise. [just lean-parity]
    `floor_div(a, b)` is the kernel floor division of spec/geometry-kernel.md; it rounds toward negative infinity for `b > 0`.
- layered-03: The internal orientation MUST be `TB`. [just lean-parity]
    The rank axis is `y`; rank 0 has the smallest `y`. The cross axis is `x`, which grows in declaration order. A node has top `y` and centre `x`. Its box covers `[x - floor_div(w, 2), x - floor_div(w, 2) + w)` horizontally.
- layered-04: `pos[v]` MUST be the index of `v` in its rank, and `decl[v]` MUST be the declaration index of `v`. [just lean-parity]
    A dummy or label node takes the index of its edge. A border node takes the index of its cluster. Every tie falls back to the lowest `decl`, unless the rule names another tie-break.
- layered-05: The pipeline MUST build the compound graph of real nodes, edges, and clusters linked by parent. [just lean-parity]
- layered-06: Every named layered constant MUST be a key of `spec/data/layout-constants.json`. [just gen-check]
    A `vector` value is in units (1/64 px), which is 64 times the px value. A `cell` value is in cells.
- layered-07: The layered constants MUST have these values. [just gen-check]
    |Key|Vector (units)|Cell (cells)|Used in|
    |---|---|---|---|
    |`node_pad_x`|768 (12 px)|1|step 1|
    |`node_pad_y`|512 (8 px)|0|step 1|
    |`node_border`|0|1|step 1|
    |`line_h`|1280 (20 px)|1|steps 1, 11|
    |`node_min_w`|2048 (32 px)|3|step 1|
    |`node_min_h`|1280 (20 px)|3|step 1|
    |`port_gap`|512 (8 px)|1|step 1|
    |`node_gap`|1536 (24 px)|2|steps 7, 12|
    |`rank_gap`|3072 (48 px)|3|steps 8, 9|
    |`slot`|768 (12 px)|1|steps 1, 4, 9, 10|
    |`cluster_border_w`|512 (8 px)|1|steps 1, 7|
    |`cluster_pad`|1024 (16 px)|1|steps 7, 11|
    |`canvas_margin`|1024 (16 px)|1|step 12|
    |`corner_radius`|512 (8 px)|0 (square corners)|step 9|
    |`component_aspect_num`|16|2|step 12|
    |`component_aspect_den`|9|1|step 12|
    |`sweep_max`|24|24|step 5|
    |`sweep_stall`|4|4|step 5|
    |`pivot_factor`|50|50|step 3|
    |`portfolio_max`|5|5|portfolio|
    |`portfolio_replace_num`|97|97|portfolio|
    |`portfolio_replace_den`|100|100|portfolio|
    Derived values, not keys: `loop_band`, `wsep`, `E_v`, `rank_top`, `H_r`, `g_r`, `G_r`, `S_r`, `lane_i`. `max_width` and `thoroughness` are options, not constants.

## Direction

- layered-08: A direction `LR`, `RL`, or `BT` MUST be an axis mapping applied to sizes before layout and to coordinates after it. [just lean-parity]
    `TD` is `TB`. An absent direction is `TB`. Let `H` be the internal canvas height after the packing phase and before the margin. The map from an internal box `(x, y, w, h)` to the output box is:
    - `TB`: `(x, y, w, h)`. Internal sizes equal output sizes.
    - `BT`: `(x, H - y - h, w, h)`. Internal sizes equal output sizes.
    - `LR`: `(y, x, h, w)`. Internal sizes are `(h, w)` of the output size.
    - `RL`: `(H - y - h, x, h, w)`. Internal sizes are `(h, w)` of the output size.
    Routes, labels, loops, and lanes take the same map point by point. The internal right side is the trailing side. It is the output bottom for `LR` and `RL`.

## Node size

- layered-09: A node with text MUST take its size from measurement and its port count. [just lean-parity]
    `w0 = textW + 2 * node_pad_x + 2 * node_border` and `h0 = lines * line_h + 2 * node_pad_y + 2 * node_border`. `textW` and `lines` come from measurement.
    `k` is the larger of the number of distinct top neighbours and the number of distinct bottom neighbours; it is the port count of spec/layout/routing.md.
    `w = max(w0, (k + 1) * port_gap, node_min_w)` and `h = max(h0, node_min_h)`.
    Each candidate MUST first measure intrinsic text and minimum sizes, apply the direction's size swap, and reserve loops. After semantic-edge normalization, it MUST compute `k` from distinct proper-chain neighbours on each side and apply the port-width term to the internal cross-axis width. It MUST exclude ranking-only constraints and self-loops from this count. Fixed independent group frames MUST retain their fixed sizes. Final rectangles and routing MUST use the resulting proper-node dimensions, not stale intrinsic widths.
- layered-10: A dummy node MUST have `w = slot` and `h = 0`. [just lean-parity]
    Left and right border nodes have `w = cluster_border_w` and `h = 0`. Top and bottom border nodes have `w = 0` and `h = 0`.
    Each cluster MUST reserve its measured title at rank `rank[T_C]` with a routing-free synthetic item. Its width MUST be the measured title width. Its height MUST be `max(1, title_lines) * line_h + cluster_pad`. It MUST NOT appear as a model box or dump label. The title text MUST start at `frame_top + cluster_pad` and MUST retain every measured line.
    The title rectangle MUST remain private layout metadata until scene assembly. `LR` and `RL` MUST swap its measured dimensions before layout. Direction and origin maps MUST transform it with the other label rectangles. The scene MUST emit upright text in that mapped rectangle, on the leading-side reservation rather than moving it to the output top.
- layered-11: A label node MUST reserve its measured text and a route gutter, with no border, port term, or minimum size. [just lean-parity]
    After the direction's size swap, let `textW` and `textH` be the internal cross-axis and rank-axis text extents. `gutter` MUST be `slot` in the cell profile and 0 in the vector profile. The node MUST have `w = textW + gutter`, `h = textH`, and `wsep = w`. Its actual text rectangle MUST start at `node_left + gutter`, with width `textW` and height `textH`. The label width `lw` used by loop and lane placement MUST remain the measured text width, without this graph reservation.
    Distinct labels owned by one route MUST share one reservation node. In original label order, its internal text width MUST be the largest individual cross-axis width, and its internal text height MUST be the sum of individual rank-axis heights plus `slot` between consecutive labels. Actual label rectangles MUST start at the shared text left edge and successive prefix heights plus slot gaps. Every original label ID, text, and global dump position MUST remain unchanged. Loop and reversed-edge side labels MUST use the same aggregate stack without the midpoint gutter.
- layered-12: The separation width of a node MUST be `wsep = w + 2 * E`, where `E` is the loop extent of spec/layout/routing.md (0 without loops). [just lean-parity]
    Only the cross-axis coordinate phase reads `wsep`.

## Cycle breaking

- layered-13: The cycle phase MUST set self-loops aside. A graph without protected cluster constraints MUST use depth-first search, with roots and out-edges in declaration order, and reverse an edge when its target is on the DFS stack. [just lean-parity]
    For a compound graph, the phase MUST start with the immutable synthetic constraint DAG and insert semantic edges once in declaration order. It MUST reverse `u -> v` exactly when the current graph has a path `v -> u`. An inserted edge MUST NOT change direction again. Synthetic constraints MUST NOT reverse. The same protected insertion rule MUST constrain the greedy portfolio candidate. This bounded compound case takes `O(edges * (nodes + edges))`; the model limits MUST apply before it runs.
    The cycle rule MUST depend on the constraints in the current component. A cluster in another component MUST NOT disable depth-first cycle breaking.
    A reversed edge MUST retain its original endpoints for drawing. The routing phase MUST place self-loops under spec/layout/routing.md.

## Ranking

- layered-14: The rank phase MUST rank each connected component of the ranking graph separately. [just lean-parity]
    The component phase orders the components. The ranking graph holds the real nodes, the edges without self-loops, and the border edges below.
- layered-15: The minimum length of an edge MUST be 2 when the edge carries a label, else 1. [just lean-parity]
    Every edge has weight 1. The cost is `sum over edges (rank[head] - rank[tail])`.
- layered-16: Each cluster MUST contribute a top border node `T_C` and a bottom border node `B_C` to the ranking graph. [just lean-parity]
    For each real node `v` in `C`, including nodes of descendant clusters, the phase MUST add `T_C -> v` and `v -> B_C`, each with minimum length 1. For each direct child cluster `D`, it MUST add `T_C -> T_D` and `B_D -> B_C`, each with minimum length 1. An empty cluster MUST add `T_C -> B_C` with minimum length 1. These structural constraints MUST remain directed and MUST preserve nested title bands and bottom padding.
    A group endpoint MUST use a per-route-end proxy that aliases `T_C` or `B_C` without adding a model or output box. A source group containing its distinct target MUST use `T_C`; every other source group MUST use `B_C`. A target group containing its distinct source MUST use `B_C`; every other target group MUST use `T_C`. Containment MUST include every descendant depth. A same-group route MUST use a frame self-loop, not a rank constraint between its borders. The first point of a route whose source group contains its distinct target MUST lie on the top edge of that group frame, at the rank top of `T_C`, even when region placement has given `T_C` a title height; the bottom port of `T_C` MUST NOT be the first point.
- layered-17: The rank phase MUST start from the longest-path ranks, pivot by the network simplex rules, and restart the scan after each pivot. [just lean-parity]
    The tie-break table below fixes the initial ranking, the feasible tree, the leaving edge, and the entering edge.
- layered-18: Pivoting MUST stop when no cut value is negative, or after `pivot_factor * nodes` pivots. [just lean-parity]
    `nodes` is the node count of the component's ranking graph, border nodes included. On reaching the cap, the current ranks stay, and they are feasible.
- layered-19: A capped ranking MUST emit `layout/budget-exhausted` (info). [just go-check]
- layered-20: The rank phase MUST subtract the minimum rank so the smallest rank is 0, and MUST NOT run a balance step. [just lean-parity]

## Dummy and label nodes

- layered-21: A semantic edge with span `s = rank[head] - rank[tail] >= 1` MUST get one dummy node at each of its `s - 1` intermediate ranks. [just lean-parity]
    The phase MUST use the semantic edge's endpoints after cycle breaking. Ranking-only hierarchy and containment constraints MUST disappear after ranking and MUST NOT produce normalized dummy chains. Left and right ordering-border chains MUST be constructed separately for ordering and alignment, and MUST NOT consume routing ports or channel slots or appear as drawn routes or metric items.
- layered-22: A labelled edge MUST get one label node at rank `rank[tail] + floor_div(s, 2)`, which replaces the dummy at that rank. [just lean-parity]
    The rule is the same for every span. For `s = 2` it is the middle rank.
- layered-23: A label node MUST take part in ordering and crossing counts like any other node. [just lean-parity]
    The reserved label node MUST be centred on its `x`. The actual text rectangle MUST follow layered-11. The chain route MUST run along the reservation's left boundary, so its cell column remains outside the text.

## Ordering

- layered-24: The initial order MUST sort each rank by `decl`; it is candidate 1 of the portfolio. [just lean-parity]
- layered-25: Sweep 1 MUST run downward and sweep 2 MUST run upward, and sweeps MUST alternate. [just lean-parity]
    Sweep 1 runs ranks 1 to the last rank, in order. Each rank is reordered by barycentre against the rank above, which is fixed. Sweep 2 runs upward against the rank below.
- layered-26: One sweep MUST be one barycentre pass over all ranks in its direction, then one transpose pass over all ranks. [just lean-parity]
- layered-27: The order phase MUST count crossings over all adjacent rank pairs with the accumulator tree after each sweep, as `int64`. [just lean-parity]
    A sweep improves when its count is strictly lower than the best count so far. A sweep that improves replaces the best order, and every sweep starts from the best order so far.
- layered-28: The sweep loop MUST stop after `sweep_max` sweeps, or after `sweep_stall` consecutive sweeps without improvement, and MUST return the best order. [just lean-parity]
- layered-29: Reaching `sweep_max` MUST emit `layout/budget-exhausted` (info). [just go-check]
- layered-30: Two edges `(a, b)` and `(c, d)` between adjacent ranks MUST count as crossing exactly when `(pos[a] - pos[c]) * (pos[b] - pos[d]) < 0`. [just lean-parity]
    `a` and `c` are in the upper rank and `b` and `d` are in the lower rank. Equal positions never cross, so edges that share an endpoint never cross.
- layered-31: The barycentre key MUST be the rational `S / C`, compared as `S1 * C2` against `S2 * C1` with no division. [just lean-parity]
    `S` is the sum of the positions of the node's neighbours in the fixed rank, and `C` is their count. A node with `C = 0` has key `pos / 1`. The phase sorts ascending by key. Ties keep the current order.
- layered-32: The median key of candidate 4 MUST be the element at index `floor_div(d - 1, 2)` of the neighbour positions sorted ascending. [just lean-parity]
    A node with `d = 0` has key `pos`.
- layered-33: A transpose scan MUST swap an adjacent pair only when both nodes have the same innermost cluster and the swap gives strictly fewer crossings in the two adjacent rank pairs. [just lean-parity]
    The scan runs left to right inside a rank. Full scans repeat until one scan swaps nothing. Each swap lowers the total count by at least one, so the loop ends.
- layered-34: The block of a cluster in a rank MUST hold its left border, its members in that rank, and its right border. [just lean-parity]
    A rank in the span with no member gives a block of the two borders only.
- layered-35: A block key MUST be the rational `S / C` over the block's edges to the fixed rank. [just lean-parity]
    `S` is the sum of the neighbour positions over all edges from the block's members to the fixed rank, border nodes included, and `C` is the number of those edges. A block with no such edge takes `S` as the sum of its members' positions and `C` as their count. A block key and a loose node key `S2 / C2` compare as `S1 * C2` against `S2 * C1` in `int64`.
- layered-36: The phase MUST sort inside each parent block, and the blocks and loose nodes of the parent MUST sort ascending by key. [just lean-parity]
    The tie value of a block is the lowest `decl` among its members, and the tie value of a loose node is its own `decl`. A tie goes to the smaller tie value. A block is never split and never interleaved with another block.
    After that sort, the phase MUST apply the sibling cluster order rule below to the initial order of every candidate and to the result of every sweep. For the initial order, the rule MUST run on the declaration seed and on the requested seed, after both seeds are constrained into cluster blocks and before the two are compared. For a sweep, the rule MUST run after the transpose pass and before the crossing count of layered-27. The best-order rule and the seed comparison MUST compare the orders that the rule returns. The rule reads only the order that it receives.
    Sibling cluster order rule. Siblings are the direct child clusters of one parent, and the parent is a cluster or the root. The span of a cluster `C` is the ranks `rank[T_C]` to `rank[B_C]`, both included. For each rank `r` of the span, `lb(C, r)` is the left border node of `C` at rank `r`. `p(v)` is `pos[v]` in the order that the rule receives. Two siblings share a rank when that rank is in both spans. Cluster `decl` values are distinct.
    1. Precedence. Let `A` and `B` be siblings that share at least one rank. Let `nA` be the number of shared ranks `r` with `p(lb(A, r)) < p(lb(B, r))`, and let `nB` be the number of shared ranks `r` with `p(lb(A, r)) > p(lb(B, r))`. `A` precedes `B` when `nA > nB`, or when `nA = nB` and `decl[A] < decl[B]`. Otherwise `B` precedes `A`. Siblings that share no rank have no precedence.
    2. Key. The key of a cluster `C` is the rational `S / N`. `S` is the sum of `p(lb(C, r))` over the whole span of `C`, and `N` is the number of ranks in the span. Key `S1 / N1` is smaller than key `S2 / N2` when `S1 * N2 < S2 * N1`, computed in `int64` with no division. Equal keys compare by `decl`, the smaller `decl` first.
    3. Selection. The phase MUST build one sibling order for each parent with Kahn's algorithm. A sibling is ready when it is not taken and every sibling that precedes it is taken. The phase MUST take the ready sibling with the smallest key. When no sibling is ready, the precedences hold a cycle, and the phase MUST take the sibling with the smallest key among all siblings that are not taken. The k-th sibling taken, counting from 0, has sibling index `k`.
    4. Placement. The phase MUST run the placement on each rank, with the whole rank as the node list and the root as the parent. A node lies inside a cluster `D` when its `parent` is `D` or a descendant of `D`. The placement of a node list `N` for a parent `P` has four parts. (a) Cut `N` into items in list order. A node that lies inside no child cluster of `P` is one loose item. A maximal run of consecutive nodes that lie inside the same child cluster `D` of `P` is one block item of `D`. (b) Replace the node list of each block item of `D` by the placement of that list for the parent `D`. (c) Let the slots be the indices of the block items in the item list, in ascending order. Sort the block items ascending by the sibling index of their clusters. Put the k-th block item of the sorted list into the k-th slot. Loose items keep their indices. (d) The result is the node lists of the items, in item order.
    A block moves as a whole, so no block is split. When the moved blocks differ in length, the positions of the nodes after them change. One sibling index applies to every rank, so two siblings keep one relative order on every rank where both are present.
- layered-110: The phase MUST choose its tie rule once for the whole graph, and MUST NOT choose it for each rank. [just lean-parity]
    A graph with at least one cluster, and every graph with the median key, MUST sort each rank by layered-36: the blocks and loose nodes of the root sort ascending by key, a tie goes to the smaller tie value, and a tie of tie values keeps the current order. This includes a rank in which no node lies inside a cluster. Only a graph with no cluster and the barycentre key MUST use layered-31, where ties keep the current order.

## Cross-axis coordinates

- layered-37: The separation between neighbours `L` and `R` in one rank MUST be `sep = floor_div(wsep_L, 2) + floor_div(wsep_R, 2) + gap`. [just lean-parity]
    `gap` MUST be `cluster_pad` between a left or right border node and a member of the same cluster block. Otherwise it MUST be 0 between a zero-width top or bottom anchor and its own title reservation, and `node_gap` for every other pair. This zero-gap exception MUST NOT apply to arbitrary real-node neighbours. The ordinary box gap is at least `gap - 1`; a zero-width anchor has no interior.
- layered-38: The coordinate phase MUST mark type-1 conflicts before the four passes. [just lean-parity]
    A border-chain segment is a proper edge `(u, v)` where `u` and `v` are both left border nodes, or both right border nodes, of one cluster `C`, at the consecutive ranks `r` and `r + 1` of the span of `C`. These edges are the ordering-border chains of layered-21. The marking rule has three parts, in this priority order.
    1. A border-chain segment MUST never be marked.
    2. Any other segment, inner or non-inner, that crosses a border-chain segment MUST be marked. Let `s = (a, b)` be the other segment and `t = (c, d)` a border-chain segment between the same two adjacent ranks, with `a` and `c` in the upper rank and `b` and `d` in the lower rank. Then `s` crosses `t` iff `(pos[a] - pos[c]) * (pos[b] - pos[d]) < 0`. This is the crossing rule of layered-30.
    3. Every segment that parts 1 and 2 leave undecided follows the type-1 rule: the phase MUST mark each non-inner segment that crosses an inner segment. An inner segment joins two chain nodes (dummy or label). A non-inner segment is any segment that is not inner, so at least one of its endpoints is an original node. A border-chain segment is non-inner, and part 1 exempts it. Let `e = (a, b)` be a non-inner segment and `f = (c, d)` an inner segment between the same two adjacent ranks, with `a` and `c` in the upper rank and `b` and `d` in the lower rank. Then `e` crosses `f` iff `(pos[a] - pos[c]) * (pos[b] - pos[d]) < 0`. This is the crossing rule of the ordering phase, applied to one non-inner and one inner segment.
    Equal positions never cross, so segments that share an endpoint are never marked. The marks use the positions after the ordering phase, and the passes do not change them. An alignment that uses a marked segment is rejected.
- layered-39: The coordinate phase MUST run four passes in this fixed order: up-left, up-right, down-left, down-right. [just lean-parity]
    Up passes align each node with its upper neighbours and process ranks top to bottom. Down passes use lower neighbours and process ranks bottom to top. Left passes process nodes left to right, right passes right to left. Node order within a rank is cross-axis order.
- layered-40: The medians of a node with `d` neighbours sorted by `pos` MUST be at indices `floor_div(d - 1, 2)` and `floor_div(d, 2)`. [just lean-parity]
    Left passes try the lower median first. Right passes try the upper median first. The first median that gives a valid alignment wins. A node with `d = 0` forms its own block and aligns with no neighbour.
- layered-41: The up-left pass MUST run steps C1 to C4, and the other passes MUST map onto it by step C5. [just lean-parity]
    The steps are the corrected algorithm 3 of Brandes and Köpf 2001, as fixed by Brandes, Walter, Zink 2020 (arXiv:2008.01252). Step C3 places each block relative to its class sink, and step C4 adds the class shifts after all blocks are placed. `node(i, p)` is the node at position `p` of rank `i`, and `len(i)` is the number of nodes in rank `i`.
- layered-42: Step C1 MUST build the alignment blocks with these rules. [just lean-parity]
    Start each pass with `root[v] = v` and `align[v] = v` for every node `v`. Process ranks top to bottom. Set `r = -1` before each rank. Process the nodes of a rank by increasing `pos`. For a node `v`, sort its upper neighbours by `pos` (`x` is not known yet) and try the medians of the median rule in their order. A median `w` links to `v` when `align[v] = v`, the segment `(w, v)` is not type-1 marked, and `pos[w] > r`. A link sets `align[w] = v`, `align[v] = root[w]`, `root[v] = root[w]`, and `r = pos[w]`. A node links at most once, so the first valid median wins. Each alignment block is a cycle: `root[v]` is its top node, `align` leads down the block, and the bottom node has `align` equal to the root. A node that never links is a block of one node with `align[v] = v`.
- layered-43: Step C2 MUST set the initial values. [just lean-parity]
    For every node `v`, set `sink[v] = v`, `shift[v] = unset`, and `x[v] = unset`. `unset` is not a number, and `min(unset, s) = s` for every number `s`. A value is read only after it is set. Every `+`, `-`, `max`, and `min` in C3 to C5 is checked `int64` arithmetic. An overflow returns the overflow error of the conventions.
- layered-44: Step C3 MUST place blocks with an explicit stack and no recursion. [just lean-parity]
    A frame is `(v, w)`, where `v` is a block root and `w` is a cursor, a node of that block. Visit the roots in rank order, top to bottom and left to right. For a root `r` with `x[r]` unset, set `x[r] = 0` and push `(r, r)`. While the stack is not empty, take the top frame `(v, w)` and run one iteration. (a) If `pos[w] > 0`, let `u = root[pred(w)]`, where `pred(w)` is `node(i, pos[w] - 1)` in the rank `i` of `w`. If `x[u]` is unset, set `x[u] = 0`, push `(u, u)`, and leave the frame unchanged. (b) Otherwise, if `pos[w] > 0`, with `u` as in (a), set `g = sep(pred(w), w)`. If `sink[v] = v`, set `sink[v] = sink[u]`. If `sink[v] = sink[u]`, set `x[v] = max(x[v], x[u] + g)`. (c) Otherwise, or after (b), set `w = align[w]`. If `w` is not `v`, keep the frame with the new cursor. If `w = v`, set `x[m] = x[v]` and `sink[m] = sink[v]` for every other node `m` of the block, then pop the frame. A block is never read while it is on the stack, because the block graph is acyclic (erratum, Section 2). Fuel is `2 * n`, where `n` counts every node, including dummy, label, and border nodes. Each iteration of (a), or of (b) and (c), spends one unit. There are at most `n` pushes, one per root, and exactly `n` cursor steps, one per node, so the loop ends within the fuel. The bound is structural, like the feasible-tree bound of the rank phase, and no cap constant applies.
- layered-45: Step C4 MUST add the class offsets after every block is placed. [just lean-parity]
    A class is the set of nodes with one `sink`. A sink `s` has `sink[s] = s`, and C3 makes every sink the node at position 0 of its rank. (a) For each rank `i` and each `p` with `1 <= p < len(i)`, let `a = node(i, p - 1)` and `b = node(i, p)`. If `sink[a] != sink[b]`, append `(a, b)` to the list `N[j]`, where `j` is the rank of `sink[b]`. The rank of `sink[b]` is less than the rank of `sink[a]` (erratum, Lemma 1). (b) For each rank `i` from top to bottom: if `node(i, 0)` is a sink and `shift[node(i, 0)]` is unset, set it to 0. Then, for each `(a, b)` in `N[i]` in any order, set `shift[sink[a]] = min(shift[sink[a]], shift[sink[b]] + x[b] - (x[a] + sep(a, b)))`. Each shift read here is final, because every update targets a lower rank. (c) For every node `v`, set `x[v] = x[v] + shift[sink[v]]`. The result of the pass is `x`.
- layered-46: Step C5 MUST derive the other three passes from the up-left pass. [just lean-parity]
    Right passes run C1 to C4 on mirrored ranks, where `pos' = len(i) - 1 - pos` replaces `pos`, so the right neighbour takes the role of the left one. Then each result `x` is replaced by `-x` (checked). Down passes run C1 to C4 with the rank order reversed, so rank `i` is read as rank `last - i` and the lower neighbour takes the role of the upper one; their results are not negated. Down-right passes do both. Since `sep(a, b) = sep(b, a)`, the mirrored runs use the same separations. The values of C3 and C4 do not depend on the order in which ranks and nodes are visited, but implementations MUST use the orders of C1 and C3, so that Go, Rust, and Lean run the same steps.
- layered-47: Each pass result MUST shift so its minimum is 0. [just lean-parity]
- layered-48: The balance MUST align the four layouts to the narrowest one. [just lean-parity]
    The narrowest pass result has the least `max - min`. Ties go to the earlier pass in the order of the pass rule. Left-pass results shift so their minimum equals the narrowest minimum. Right-pass results shift so their maximum equals the narrowest maximum. Then all four results shift by one common constant so the smallest value over all nodes is 0. For each node, the coordinate is `floor_div(second smallest + third smallest, 2)` of its four values. All `floor_div` operands here are non-negative.
- layered-49: The output `x` MUST be the centre of each node. [just lean-parity]

## Rank-axis coordinates

- layered-50: `H_r` MUST be the largest `h` among the nodes of rank `r`, or 0 when the rank has none. [just lean-parity]
    Border, dummy, and loop heights enter through `h`.
- layered-51: The gap below rank `r` MUST be `G_r = g_r + slot * S_r`, where `S_r` is the slot count of spec/layout/routing.md, `g_r = ceil_div(rank_gap, 2)` when rank `r` or rank `r + 1` is a label rank, and `g_r = rank_gap` otherwise. [just lean-parity]
    `rank_top[0] = 0` and `rank_top[r + 1] = rank_top[r] + H_r + G_r`. A label rank is a non-empty rank whose nodes are all dummy nodes of edge chains, and at least one of them is the label node of its chain. A real node and every border node (cluster top, bottom, left, right, and title) are not dummy nodes, so a rank that holds one of them is not a label rank. In the cell profile `rank_gap` is 3 and `ceil_div(3, 2)` is 2 rows.
    Hard-constraint side conditions: `ceil_div(rank_gap, 2) >= 1` because `rank_gap >= 1`, so every `G_r` is at least 1 and the rank bands stay disjoint. Every slot line stays above `rank_top[r + 1]` because `floor_div(slot, 2) < ceil_div(rank_gap, 2)` in both profiles: 6 px is less than 24 px in the vector profile, and 0 is less than 2 in the cell profile. The slot line formula of routing-11 and the stub bound of routing-12 therefore stay unchanged.
- layered-52: A node's top MUST be `y = rank_top[r] + floor_div(H_r - h, 2)`, so its bottom is `y + h`. [just lean-parity]
    Structural cluster anchors MUST be exceptions to node centering: `T_C.y = rank_top[rank[T_C]]` and `B_C.y = rank_top[rank[B_C]] + H_rank[B_C]`. These anchors MUST be the frame's top and bottom. The strict hierarchy ranks and the existing rank gap MUST preserve title and bottom clearance without a separate title stack.

## Ports and routes

- layered-53: A layered layout MUST set port positions, chain routes, slot numbers, corners, reversed-edge lanes, self-loops, and route labels by spec/layout/routing.md. [just lean-parity]

## Subgraph direction

- layered-54: The pipeline MUST lay out a subgraph `S` with its own `direction` before its parent is ranked. [just lean-parity]
    `S` has crossing edges when some edge has exactly one endpoint among its proper descendants. The boundary identity `S` MUST NOT count as inside. A route from `S` to its descendant therefore crosses its boundary. A route from `S` to an external box MUST stay parent-owned, as MUST a self-loop on `S`. Recursive child layout MUST NOT emit the root frame or these parent-owned routes a second time.
- layered-55: A subgraph with no crossing edges MUST be laid out with its own direction, using the whole pipeline, and the parent MUST see it as a fixed-size node. [just lean-parity]
    Its size is the output bounding box of that layout, plus `cluster_pad` on the left, right, and bottom, plus `cluster_pad + max(1, title_lines) * line_h` on top for the title. The child layout MUST apply no `canvas_margin`. The frame and the title MUST be built in the internal orientation of the child's own direction and then mapped by that direction, so the title sits on the child's leading side. The parent MUST read the mapped frame in the parent's internal orientation, so the size is swapped when the parent is `LR` or `RL`.
- layered-56: A subgraph with crossing edges MUST ignore the `direction` and become an ordinary cluster in the parent's orientation. [just lean-parity]
- layered-57: An ignored subgraph direction MUST emit `flowchart/subgraph-direction-ignored` (warning, no fix). [just go-check]
    The span is the `direction` statement. The message is `subgraph direction is ignored because an edge crosses its boundary`. The registry row is in `spec/data/diagnostics/flowchart.json`. Only `render` and `layout` run layout, so only they print this code, to stderr.
- layered-58: A subgraph without a `direction` MUST be an ordinary cluster of the rank phase. [just lean-parity]

## Components and packing

- layered-59: The pipeline MUST lay out each connected component of the ranking graph on its own internal canvas. [just lean-parity]
    A component box is the bounding box of all node boxes, cluster frames, routes, labels, lanes, and loop extents of one component. `comp_w` and `comp_h` are its width and height. The pipeline translates each component so that its component box starts at (0, 0).
- layered-60: The components MUST be ordered by the lowest `decl` of their members. [just lean-parity]
- layered-61: The target width MUST be `T = max_width` when `max_width > 0`. Otherwise `T` MUST be the candidate with the smallest packed area `W * H` among `T_0 = isqrt(floor_div(S * component_aspect_num, component_aspect_den))` and, for `k` from 1 to `n`, `T_k = comp_w_1 + ... + comp_w_k + (k - 1) * node_gap`, where `n` is the component count and `comp_w_i` is the width of the component at pack position `i`. [just lean-parity]
    `S` is the sum of `width * height` over every item box of every component (`int64`). Each item box counts once: each node box, cluster frame, label box, loop extent, and the bounding box of each route (a reversed route's box covers its lane). The component box does not count. `isqrt(n)` is the largest `r` with `r * r <= n`.
    The packed area of a candidate is `W * H` of the bounding box that the row rule of layered-62 gives for that candidate. `W` is the widest row without its trailing gap, and `H` is the top of the last row plus its height. The product is an `int64` and a product above `int64` is the overflow error. The candidates are tried in the order `T_0`, `T_1`, ..., `T_n`, and a later candidate replaces the best only when its packed area is strictly smaller. A tie therefore keeps the earlier candidate, so it keeps `T_0`. A layout with one component has one candidate.
    A forward route-label stack MUST contribute its full reservation envelope once, including the cell gutter, instead of its individual text rectangles. A reversed or loop label stack MUST contribute its aggregate side envelope once, without counting hidden normalized nodes. Each owning node or frame MUST contribute one loop reservation of width `E_v` and height `K * loop_band`. Embedded fixed-child geometry MUST be expanded before this accounting, with every model item and semantic title counted once.
- layered-62: The pack phase MUST place components left to right with `node_gap` between them. [just lean-parity]
    `row_w` is the total width of the components in the current row, with the gaps between them. A component starts a new row when the row is not empty and `row_w + node_gap + comp_w > T`. Rows stack top to bottom with `node_gap` between them. The same row rule evaluates every candidate of layered-61.
- layered-63: The origin phase MUST translate so that the smallest `x` and the smallest `y` over all boxes, routes, labels, and lanes are 0. [just lean-parity]
    It then applies the direction map and adds `canvas_margin` to every coordinate. The canvas is the bounding box size plus `2 * canvas_margin` in each axis.

## Tie-breaks

- layered-64: The layered phases MUST follow this table, and both implementations MUST follow the table, not the papers, where they differ. [just lean-parity]
    |Phase|Deterministic rule|
    |---|---|
    |Cycle breaking|DFS roots and out-edges in declaration order; reverse an edge when its target is on the DFS stack|
    |Initial ranking|longest path, nodes in declaration order|
    |Feasible tree|grow from the lowest-`decl` node; scan tree nodes in `decl` order and their edges in declaration order; add the first tight edge; when none exists, shift the tree by the minimum slack of an edge that leaves it, lowest declaration index on ties|
    |Leaving edge|the tree edge with a negative cut value that has the lowest declaration index|
    |Entering edge|minimum slack among edges that cross the cut in the required direction, lowest declaration index on ties|
    |Simplex end|stop when no cut value is negative; after `pivot_factor * nodes` pivots keep the current feasible ranks and emit `layout/budget-exhausted`; subtract the minimum rank; no balance step|
    |Barycentre order|ties keep the current order; a node with no neighbour in the fixed layer keeps its position index|
    |Barycentre key|compare `S / C` by `S1 * C2` against `S2 * C1`; no division|
    |Cluster block order|blocks sort by block key inside their parent block; ties go to the lowest member declaration index; a block is never split|
    |Sibling cluster order|majority over the shared ranks of the left-border order, ties to the lower cluster `decl`; Kahn selection by (mean left-border position, `decl`); on a cycle take the smallest key; blocks move to the block slots they already occupy, and loose nodes stay in place|
    |Transpose|scan adjacent pairs left to right; swap only on strictly fewer crossings and only inside one innermost cluster; repeat until one full scan swaps nothing|
    |Best order|a new order replaces the best only on strictly fewer crossings|
    |Brandes-Köpf|alignments in the order up-left, up-right, down-left, down-right; with two medians try the lower first in left passes and the upper first in right passes|
    |Balance|align the four layouts to the narrowest one; the coordinate is `floor_div(second smallest + third smallest, 2)`|
    |Components|lowest member declaration index|
    |Portfolio|candidates in the order (1) to (5); ties keep the incumbent|
    The port, slot, lane, and self-loop tie-breaks are in spec/layout/routing.md.

## Bounds and fuel

- layered-65: At the limits of 2000 nodes and 5000 edges, the phases MUST stay within these bounds. [just proofs]
    Ranking runs at most `pivot_factor * nodes` pivots. Ordering runs at most `sweep_max` sweeps of `O(edges * log nodes)`. Coordinates and routing are linear in nodes plus dummy nodes. The portfolio multiplies the total by `thoroughness`, at most `portfolio_max`.
- layered-66: Every iterative phase MUST take a `fuel` argument, decrement it each iteration, and return its current state at zero as a normal return, never an error. [just lean-parity]
    Go, Rust, and Lean stop at the same iteration. Where a rule emits `layout/budget-exhausted` (info) on a cap, the Lean function returns the same diagnostic in its result, and `geomcheck layout` writes it to stderr as Go and Rust do. `lean-parity` compares stdout and the exit status only, so it does not compare the diagnostic.
- layered-67: The network simplex fuel MUST be `pivot_factor * nodes`, with `pivot_factor` = 50. [just lean-parity]
    Each applied pivot lowers the cost, so a capped run still satisfies `simplex_cost_le_init`.
- layered-68: The layer sweep fuel MUST be `sweep_max` = 24, and the loop MUST also stop after `sweep_stall` = 4 sweeps without improvement. [just lean-parity]
- layered-69: The transpose fuel MUST be `c0 + 1` per transpose call, where `c0` is the crossing count of the layer with its fixed neighbour layers when the call starts. [just lean-parity]
    This is the only fuel that depends on the input. Each pass that swaps lowers that count by at least 1, so a clean pass ends the loop before the fuel is spent.
- layered-70: The portfolio fuel MUST be `min(thoroughness, portfolio_max)`, with `portfolio_max` = 5. [just lean-parity]
- layered-71: Cycle breaking MUST recurse on the DFS over unvisited nodes, and feasible-tree growth MUST take at most `nodes - 1` steps, one node per step. [just lean-parity]
- layered-72: `sweep_max`, `sweep_stall`, `pivot_factor`, and `portfolio_max` MUST be keys of `spec/data/layout-constants.json`. [just gen-check]

## Portfolio

- layered-73: With thoroughness `t` (1 to 5, default 3), the portfolio MUST lay out `min(t, portfolio_max)` candidates for each component and keep the best. [just lean-parity]
- layered-74: The candidates MUST run in this fixed order with these rules. [just lean-parity]
    1. Declaration order start, with the depth-first cycle breaking of the cycle phase.
    2. Breadth-first start order on the normalized proper graph, including real, dummy, label, and border nodes, with the same cycle breaking as candidate 1. The root MUST be the lowest-`decl` node with no incoming edge, or the lowest-`decl` node overall when none exists. A queue MUST visit out-edges in declaration order. Each rank's initial order MUST be the search discovery order. When the queue empties, the next root MUST be the lowest-`decl` unvisited proper node. Equal declarations MUST retain stable proper-node construction order.
    3. Greedy feedback-arc cycle breaking (Eades, Lin, Smyth 1993, integer form). Repeatedly remove the lowest-`decl` remaining sink into the right list, or, when no sink exists, the lowest-`decl` remaining source into the left list. When neither exists, remove the node with the largest `outdeg - indeg` among the remaining nodes, lowest `decl` on ties. The order is the left list followed by the reversed right list. An edge is reversed when its tail follows its head in this order. The rank phase runs again on the new graph, and the rest of the pipeline follows.
    4. Median weights (the median key of the ordering phase) in place of barycentre, from the declaration order start.
    5. Reversed start order: each rank's initial order is reversed.
    For candidates 2 and 5, ordering MUST first constrain both the declaration seed and the requested seed into cluster blocks. Both seeds MUST then pass the sibling cluster order rule of layered-36, before they are compared. The declaration seed MUST remain the ordering incumbent unless the requested seed has strictly fewer crossings. Sweeps MUST start from that incumbent. This rule preserves the declaration-order bound of `order_crossings_le_init`.
- layered-75: Candidate 1 MUST be the incumbent, and a later candidate MUST replace it only when `portfolio_replace_den * cost_new < portfolio_replace_num * cost_incumbent`. [just lean-parity]
    The composite score is the soft cost of the candidate's component layout, as spec/quality-metrics.md defines it. The comparison is `100 * cost_new < 97 * cost_incumbent`. Ties keep the incumbent.
    Scoring MUST use the fully expanded candidate component, including independent child nodes, routes, labels, and groups. Synthetic graph items MUST NOT count as model items. Child contributions MUST remain in every cost term and denominator even when unchanged across candidates, because the replacement threshold applies to total cost.
- layered-76: Both profiles MUST use this pipeline. [just lean-parity]
    Under the cell profile the spacing constants are in cells, every slot is one cell wide, and every route is drawn with box-drawing glyphs. Under the vector profile the SVG back end draws the orthogonal route with rounded corners by default and maps upstream `curve` values to path commands over the same points. The corner rule is in spec/layout/routing.md.

## Files

- layered-77: Each phase MUST be one file, most files MUST hold one entry function, and shared types MUST live in `graph` with no entry function. [just build]
    `coords.go` and `route.go` hold two each. Go files live in `internal/layout/layered/`. Rust files live in `crates/elegant-mermaid/src/layout/layered/`, with `mod.rs` as the module root. Lean files live in `proofs/Elegant/Layered/`. The files are `graph`, `cycles`, `rank`, `normalize`, `labels`, `order`, `coords`, `route`, `loops`, `pack`, `portfolio`, and `pipeline`.
- layered-78: The Go entries MUST have these signatures. [just build]
    - `cycles.go`: `func BreakCycles(g *Graph) (reversed []bool, err error)` (the cycle phase)
    - `rank.go`: `func Rank(g *Graph) (rank []int32, err error)`; `g` is one component (the rank phase)
    - `normalize.go`: `func Normalize(g *Graph, rank []int32) (*Proper, error)` (the dummy phase)
    - `labels.go`: `func AddLabelNodes(p *Proper) error` (the label phase)
    - `order.go`: `func Order(p *Proper, opts OrderOptions) ([][]int32, error)` (the ordering phase)
    - `coords.go`: `func CrossCoords(p *Proper, layers [][]int32) ([]int32, error)` and `func RankCoords(p *Proper, layers [][]int32, r *Routing) (y []int32, rankTop []int32, err error)`, where `y[v]` is the top of node `v` and `rankTop[r]` is the top of rank `r` (the coordinate phases; the rank-axis phase needs the slot counts of the routing phase, so this file holds two entry functions)
    - `route.go`: `func Route(p *Proper, layers [][]int32, x []int32) (*Routing, error)` numbers the channel segments of the routing phase, including the reversed runs, and sets each lane `x` and `R`; it needs no `y`. Its second entry is `func RoutePoints(p *Proper, layers [][]int32, x []int32, y []int32, rankTop []int32, r *Routing) (routes []EdgeRoute, labels []Box, err error)`, where `EdgeRoute` holds the original edge index and its points (Go cannot name a type and a function `Route` in one package); it turns the routing into the points of every route, using `x`, `y`, and `rankTop` from `RankCoords`; it returns the stub-run-stub routes, the six-point routes, and the label boxes of labelled reversed edges; the rank heights `H_r` come from `p` and `layers`
    - `loops.go`: `func Loops(g *Graph, boxes []Box) ([]EdgeRoute, error)` (the self-loop phase)
    - `pack.go`: `func Pack(parts []Layout, opts PackOptions) (Layout, error)` (the packing phase)
    - `portfolio.go`: `func Portfolio(g *Graph, thoroughness int) (Layout, error)` (the portfolio)
    - `pipeline.go`: `func LayoutFamily(in Input, opts Options) (Scene, error)` (the size, subgraph, and origin phases)
    Lean entries are `breakCycles`, `rank`, `normalize`, `addLabelNodes`, `order`, `crossCoords`, `rankCoords`, `route`, `routePoints`, `loops`, `pack`, `portfolio`, and `layoutFamily`, in modules `Cycles`, `Rank`, `Normalize`, `Labels`, `Order`, `Coords`, `Route`, `Loops`, `Pack`, `Portfolio`, and `Pipeline`. Rust entries use the same names in snake case.
- layered-79: Each file added by the label, loop, pack, and portfolio phases MUST have one unit test on a fixed small graph. [just go-check]

## Oracles

- layered-80: The ranking oracle MUST find the minimum cost by search: for graphs of at most 5 nodes, a search over every rank vector with values in `0 .. 2 * (n - 1)` finds the minimum cost, and the simplex cost MUST equal that minimum when no budget diagnostic is emitted. [just go-check]
    The random graphs are built in the test by the rules of `tools/randgraph`, as the test set of this item states. Test set: the first 100 layered cases of `tools/randgraph` in case index order from 0 to 1999 that have at most 5 nodes. The test fails when fewer than 100 cases qualify. Cost is the sum over edges of (rank of head minus rank of tail).
- layered-81: The crossings oracle MUST hold: a naive count over all edge pairs of each adjacent rank pair, with the crossing rule of the ordering phase, equals the accumulator-tree count on the same order. [just go-check]
    Test set: 200 random layer pairs.
- layered-82: The coordinates oracle MUST hold: a naive in-test Brandes-Köpf, a direct transcription of the rules of the cross-axis phase (alignments, medians, erratum compaction, balance), reproduces the production coordinates exactly on seeded random graphs. [just go-check]
    Test set: the layered cases with case index 0 to 199 of `tools/randgraph`, built in the test by the same draws and not read from `corpus/.cache/random/`. The output also keeps the layer order and every minimum separation.

## Theorems

- layered-83: The proof `breakCycles_acyclic` in `proofs/Elegant/Layered/Cycles.lean` MUST hold. [just proofs]
    Statement: `forall g, Acyclic (Layered.breakCycles g)`, where `Acyclic` means no directed cycle.
    Proof approach: induction on DFS steps; each reversed edge closes a path on the DFS stack, and every other edge follows finish order.
- layered-84: The proof `breakCycles_edges_perm` in `proofs/Elegant/Layered/Cycles.lean` MUST hold. [just proofs]
    Statement: `(Layered.breakCycles g).edges` is a `List.Perm` of `g.edges` with exactly the DFS back edges reversed.
    Proof approach: induction on DFS steps; each edge is emitted once.
- layered-85: The proof `rank_feasible` in `proofs/Elegant/Layered/Rank.lean` MUST hold. [just proofs]
    Statement: `Layered.rank g = .ok r -> forall e in g.edges, r e.head - r e.tail >= minLen e`.
    Proof approach: invariant; the longest-path start is feasible, and each pivot keeps tree edges tight and all edges feasible.
- layered-86: The proof `simplex_cost_le_init` in `proofs/Elegant/Layered/Rank.lean` MUST hold. [just proofs]
    Statement: `Layered.rank g = .ok r -> cost r <= cost (Layered.feasibleRank g)`, where `feasibleRank` is the ranking after the feasible tree is built and `initRank` stays the longest-path ranking; the bound against `initRank` does not hold after feasible-tree construction when an edge has minimum length 2.
    Proof approach: each applied pivot has a negative cut value and lowers the cost; the pivot fuel bounds the loop.
- layered-87: The proof `normalize_proper` in `proofs/Elegant/Layered/Normalize.lean` MUST hold. [just proofs]
    Statement: `forall e in (Layered.normalize g).edges, span e = 1`.
    Proof approach: induction over edges; a span-k edge becomes k unit edges through k - 1 dummy nodes.
- layered-88: The proof `order_perm` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: `forall i, (Layered.order g).layers[i]` is a `List.Perm` of `(Layered.initOrder g).layers[i]`.
    Proof approach: sweeps and transposes only permute within a layer; `List.Perm` is closed under adjacent swaps and sorting.
    The proof MUST include `siblingNormalise_perm`: the sibling cluster order rule returns a `List.Perm` of each layer that it receives.
- layered-89: The proof `order_crossings_le_init` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: `crossCount (Layered.order g) <= crossCount (Layered.initOrder g)`.
    Proof approach: best-so-far tracking; the result is the minimum over the candidates, and the initial order is the first candidate.
    `Layered.initOrder` MUST include the sibling cluster order rule of layered-36, so that the initial order is the declaration order after cluster blocking and sibling normalisation.
- layered-90: The proof `transpose_crossings_le` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: `crossCount (Layered.transpose L) <= crossCount L`.
    Proof approach: a swap is applied only when it strictly lowers the local count, and the local change of an adjacent swap is exact.
- layered-91: The proof `crossCount_eq_naive` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: `Layered.crossCount L = naiveCrossCount L`, counting edge pairs with `(pos a - pos c) * (pos b - pos d) < 0`.
    Proof approach: accumulator-tree sums rewritten with `inversions_eq_crossings` and a sort lemma.
- layered-92: The proof `order_clusters_contiguous` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: `forall c, i < j < k, L[i] in c and L[k] in c -> L[j] in c`.
    Proof approach: induction over the cluster tree; recursive sorting places each child cluster as one run.
    The proof MUST include `siblingNormalise_contiguous`: the sibling cluster order rule keeps every cluster as one run, because it moves only whole blocks.
- layered-93: The proof `coords_order_preserved` in `proofs/Elegant/Layered/Coords.lean` MUST hold. [just proofs]
    Statement: `forall L i, x (L[i]) <= x (L[i+1])`.
    Proof approach: within a class, step C3 only raises `x`; the class shifts of step C4 move whole classes and may be negative, and the order follows from `coords_separated` because every `sep` is positive.
- layered-94: The proof `coords_separated` in `proofs/Elegant/Layered/Coords.lean` MUST hold. [just proofs]
    Statement: `forall L i, x (L[i+1]) - x (L[i]) >= sep (L[i], L[i+1])`, where `sep (L, R) = floor_div (wsep L) 2 + floor_div (wsep R) 2 + gap` and `gap` is the gap of the separation rule.
    Proof approach: step C3 enforces the gap for adjacent nodes of one class at every placement, and step C4 (b) enforces it for adjacent nodes of different classes; induction over the layer.
    The proof MUST include `rawPass_separated`: a raw pass that returns a result satisfies the separation rule; the coordinate functions MUST NOT hold a runtime separation check.
- layered-95: The proof `balance_separated` in `proofs/Elegant/Layered/Coords.lean` MUST hold. [just proofs]
    Statement: `forall L i, bal (L[i+1]) - bal (L[i]) >= sep`, where `bal v = floor_div (s2 + s3) 2` and `s2`, `s3` are the second and third smallest of the four alignment values of `v`.
    Proof approach: the four separated families dominate componentwise; order statistics are monotone, so `s2` and `s3` each rise by at least `sep`.
- layered-96: The proof `rankAxis_bands_disjoint` in `proofs/Elegant/Layered/Coords.lean` MUST hold. [just proofs]
    Statement: `forall r < r', the rank-axis intervals [y_r, y_r + h_r] and [y_r', y_r' + h_r'] share no interior point`.
    Proof approach: induction on the rank index, using the gap formula with `gap >= 0`.
- layered-97: The proof `route_orthogonal` in `proofs/Elegant/Layered/Route.lean` MUST hold. [just proofs]
    Statement: `forall r, Polyline.isOrthogonal (Layered.route r).points`.
    Proof approach: each route is port stubs, channel runs, and for reversed edges one lane, all axis-aligned; induction over the segment list.
- layered-98: The proof `route_endpoints_on_ports` in `proofs/Elegant/Layered/Route.lean` MUST hold. [just proofs]
    Statement: `(Layered.route r).points.head? = some (port r.fromId) and (Layered.route r).points.getLast? = some (port r.toId)`.
    Proof approach: route construction starts and ends with the port stub.
- layered-99: The proof `route_avoids_nodes` in `proofs/Elegant/Layered/Route.lean` MUST hold. [just proofs]
    Statement: `forall r, forall exclusive b with b.id not in Scope r, Polyline.hitsRect (Layered.route r).points b.rect = .ok false`.
    Proof approach: channels lie in the gaps between rank bands, lanes lie right of `R`, which bounds every box, and stubs lie in the endpoint's band, so no route reaches an exclusive box outside `Scope r`.
- layered-100: The proof `slots_separate_overlapping_segments` in `proofs/Elegant/Layered/Route.lean` MUST hold. [just proofs]
    Statement: `forall s, t in one channel with intersecting closed projections and different trunks, Layered.slot s != Layered.slot t`.
    Proof approach: slots are a topological numbering of an acyclic conflict graph; overlapping pairs are oriented and get distinct numbers.
- layered-101: The proof `labels_disjoint` in `proofs/Elegant/Layered/Labels.lean` MUST hold. [just proofs]
    Statement: `forall l != l', intersects (label l).rect (label l').rect = .ok false`.
    Proof approach: labels are placed by a compact sweep and `Rect.placeAfter`; induction over the label list.
- layered-102: The proof `loops_outside_node` in `proofs/Elegant/Layered/Loops.lean` MUST hold. [just proofs]
    Statement: `forall n, Polyline.hitsRect (Layered.loop n).points n.rect = .ok false`.
    Proof approach: loop points sit outside the node on the trailing side; each loop segment passes the separating-axis test against the node.
- layered-103: The proof `pack_components_disjoint` in `proofs/Elegant/Layered/Pack.lean` MUST hold. [just proofs]
    Statement: `forall i != j, intersects (box i) (box j) = .ok false` for the boxes of `Layered.pack`.
    Proof approach: each row is a compact sweep (`compact_pairwise_disjoint`); rows are stacked with `placeAfter_disjoint`.
- layered-104: The proof `portfolio_cost_le_default` in `proofs/Elegant/Layered/Portfolio.lean` MUST hold. [just proofs]
    Statement: `softCost (Layered.portfolio g t) <= softCost (Layered.candidate g 1)`.
    Proof approach: the incumbent changes only when `100 * new < 97 * incumbent`; induction over candidates up to the fuel.
- layered-105: The proof `layered_valid` in `proofs/Elegant/Layered/Pipeline.lean` MUST hold. [just proofs]
    Statement: `forall m, WellFormed m -> WithinLimits m -> Layered.layoutFamily m = .ok s -> Validator.check (toDump s) = true`.
    Proof approach: one phase theorem per validator clause; canvas and parent containment from `crossCoords` and `rankCoords`; exclusive siblings from `coords_separated`, `balance_separated`, and `rankAxis_bands_disjoint`; orthogonality, ports, and route clearance from `route_orthogonal`, `route_endpoints_on_ports`, and `route_avoids_nodes`; label clearance because label boxes lie in inter-rank gaps or beside loops; frame clearance from `layered_frame_clearance_admitted`.
- layered-106: The proof `order_siblings_consistent` in `proofs/Elegant/Layered/Order.lean` MUST hold. [just proofs]
    Statement: for every order that the sibling cluster order rule returns, all siblings `A` and `B`, and all ranks `r` and `r'` that both siblings share, `pos (lb A r) < pos (lb B r)` implies `pos (lb A r') < pos (lb B r')`.
    Proof approach: the placement sorts the blocks of every rank by one sibling index per parent, so two blocks keep the order of their indices on every rank where both are present; induction over the cluster tree.
- layered-107: The proof `border_chain_straight_executed` in `proofs/Elegant/Layered/BorderStraightExecuted.lean` MUST hold. [just proofs]
    Statement: for every executed component run of a well-formed input with framed parents, and every cluster declaration `C`, all border nodes of one side of `C` have equal cross-axis coordinates, so `x (lb C r) = x (lb C r')` and `x (rb C r) = x (rb C r')` for all ranks `r` and `r'` of the span of `C`, where `lb` and `rb` are the left and right border nodes of `C`.
    Proof approach: under the sibling cluster order rule and the marking rule of layered-38, each border chain is one alignment block in each of the four passes, so the four pass values of a chain node are equal, and the balance returns that common value. The coordinate-phase lemma `border_chain_straight` in `proofs/Elegant/Layered/FrameEnvelope.lean` states this under the premise that each pass aligns the chain into one block. The executed theorem discharges that premise.
- layered-108: The proof `layered_frame_clearance_admitted` in `proofs/Elegant/Layered/FrameClearanceProof.lean` MUST hold. [just proofs]
    Statement: `forall inp o res, admit inp (Layered.layoutFamily inp o) = .ok res -> C8 res.scene.layoutDump`, where `C8` is the predicate of clause `frame-clearance` in spec/layout-dump.md. The companion `layered_frame_clearance_of_fixed_fit` replaces the admission premise with `InputFixedFit inp o`.
    Proof approach: `C8a` follows from `layered_foreign_boxes_clear`, which applies the recursive C8a lift to every nesting level of the executed result. `C8b` follows from the recursive C8b lift and the fixed-fit premise that admission guarantees. Within one level, a non-member lies outside the block of a cluster (`order_clusters_contiguous`) and is separated from its border nodes by the separation rule (`cluster_all_pairs_separated`); `border_chain_straight_executed` makes the frame edges equal to the border edges of every rank; outside the span, the rank bands are disjoint (`rankAxis_bands_disjoint`); sibling frames are separated at every shared rank, with one order from `order_siblings_consistent`.
- layered-109: A subgraph that layered-55 lays out as a fixed-size node MUST be a real node of its parent cluster in the rank phase. [just go-check: TestNestedDirectionSubgraphIsRankedMemberOfParentCluster]
    For the fixed-size node `F` in the parent cluster `C`, the rank phase MUST add `T_C -> F` and `F -> B_C`, each with minimum length 1. It MUST NOT treat `F` as a child cluster of `C`, and it MUST NOT add border nodes for `F`.
    The output box of `F` MUST keep the parent `C`. Its frame MUST lie inside the frame of `C` and MUST start below the title band of `C`. This rule MUST apply at every depth of nesting.
