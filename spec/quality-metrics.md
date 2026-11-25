# Quality metrics

This file defines the hard constraints beyond the validator, the metric formulas, the metric output, the dagre and ELK baselines, and the quality gates.

## Hard constraints

- quality-metrics-01: Every layout MUST satisfy the eight `HardConstraints` clauses of `spec/layout-dump.md`. [just validate]
    The cell-profile rules of this file are outside `HardConstraints`.
- quality-metrics-02: No label MUST be truncated. [just quality]
    A label is truncated when a back end cannot write all of its grapheme clusters. The vector profile never truncates a label, because vector labels are never clipped. In the cell profile, a label is truncated when the label placement rule of `spec/render-cells.md` cannot write one of its clusters.
- quality-metrics-03: Under the cell profile, no two routes MUST share a cell except at a declared junction, along a shared trunk segment (the trunk rule of spec/layout/routing.md, and grid routes that run on one gutter line), or at a crossing drawn as `┼`. [just quality]
    A route conflict is a cell that two routes enter on the same axis (both horizontal there or both vertical there) when the two routes share no trunk and share no endpoint box. Two routes that share an endpoint box meet at a declared junction. Two routes that enter one cell on different axes cross, and the cell renderer draws `┼`. The cell renderer returns the count of route conflicts, and the rule holds when that count is 0. A dump input has no cell rendering, so the rule holds for it.
- quality-metrics-04: `hard_ok` MUST be true exactly when a scene passes `HardConstraints`, both rules above, and the unwritten-cluster count is 0. [just quality]
    The cell renderer returns the count of unwritten clusters. For a model input, `--metrics` runs the cell renderer on the same model and takes that count.

## Dump elements

- quality-metrics-05: A real node MUST be a dump box with role `node`, and a group MUST be a dump box with role `group`; a label MUST be an entry of `labels`, and its `owner` MUST be the route id. [just parity]
    A dump holds model boxes only, so layered dummy nodes never count.
- quality-metrics-06: A route MUST be its `points` list, and consecutive equal points MUST be removed before any measure. [just parity]
    A segment is two consecutive points of one route. A route with fewer than two points has no segments.

## Soft cost

- quality-metrics-07: The `nodes` term `N` MUST be the number of real nodes. [just parity]
- quality-metrics-08: The `mean_node_extent` term `M` MUST be `max(1, floor_div(S, max(1, N)))`, where `S` is the sum over real nodes of `floor_div(w + h, 2)` with `w` and `h` in units. [just parity]
- quality-metrics-09: The `crossings` term `C` MUST be the number of unordered pairs of segments from two different routes that cross properly. [just parity]
    Their open segments meet in exactly one point, and that point is interior to both. Touching at an endpoint and collinear overlap do not count. Only routes count; layered dummy chains do not. Let `cross(u, v) = u.x * v.y - u.y * v.x` and let `o(a, b, p)` be the sign of `cross(b - a, p - a)`. A pair of segments `[a1, a2]` and `[b1, b2]` counts when `o(a1, a2, b1) * o(a1, a2, b2) = -1` and `o(b1, b2, a1) * o(b1, b2, a2) = -1`. Multiply the signs only, never the raw cross products.
- quality-metrics-10: The `bends` term `B` MUST be the number of interior points `p[i]` of a route (`0 < i <` last index) where `d1 = p[i] - p[i-1]` and `d2 = p[i+1] - p[i]` satisfy `cross(d1, d2) != 0 or dot(d1, d2) < 0`. [just parity]
    A straight continuation is not a bend. A reversal is a bend.
- quality-metrics-11: The `against_flow_edges` term `A` MUST be the number of routes whose target lies before their source on the rank axis, as drawn. [just parity]
    Let `c(box)` be twice the centre of a box on the rank axis: `x0 + x1` for LR and RL, `y0 + y1` for TB and BT. Let `s` be `+1` for TB and LR and `-1` for BT and RL. A route counts when `s * (c(to) - c(from)) < 0`. The endpoints `from` and `to` may be real nodes or groups. A self-loop never counts. The rule reads the drawing only, so the cycle breaking inside an engine does not change it.
- quality-metrics-12: The `total_route_length` term `T` MUST be the sum over all segments of all routes of `isqrt(dx * dx + dy * dy)`, with `dx` and `dy` in units and `isqrt` the kernel floor square root. [just parity]
    Orthogonal segments give exact lengths.
- quality-metrics-13: The `canvas_area` term `K` MUST be `W * H`, where `W` and `H` are the width and height of the bounding box of all real node boxes, group boxes, label boxes, and route points. [just parity]
    The bounding box has no margin. A dump with no node box, group box, label box, and route point has `W = 0` and `H = 0`, so `K = 0`.
- quality-metrics-14: The composite score MUST be `soft_cost = 10 * C + 2 * B + 5 * A + floor_div(T, M) + floor_div(K, M * M * max(1, N))`. [just parity]
    All terms are integers and not negative, so each `floor_div` is the floor of its exact quotient. `N`, `S`, and `M` depend only on the model boxes, so ours and both baselines share them for one fixture.
- quality-metrics-15: Our layouts and both baseline dumps MUST go through the same metric code on the same kind of dump. [just quality]
- quality-metrics-16: Every metric MUST be unchanged by a translation, so margins and paddings never change a term. [just go-check]
- quality-metrics-17: An overflow in any metric step MUST raise the kernel overflow error (`LayoutError`). [just go-check]

## Metric output

- quality-metrics-18: `emd layout --metrics` MUST print one line of UTF-8 JSON, with keys in this order, no spaces, and a final LF. [just parity]
    `{"schema":1,"hard_ok":true,"nodes":N,"mean_node_extent":M,"crossings":C,"bends":B,"against_flow_edges":A,"total_route_length":T,"canvas_area":K,"soft_cost":S}`
    The metrics score the vector profile. Coordinates, lengths, and sizes are integers in units of 1/64 px. `canvas_area` is in units squared.
- quality-metrics-19: `hard_ok` MUST be `true` or `false`, and every other value MUST be an integer. [just parity]
    `just parity` compares these bytes between Go and Rust.
- quality-metrics-20: `emd layout --metrics` MUST always score the vector profile. [just go-check]
- quality-metrics-21: `--profile cell` with `--metrics` MUST exit 2 with the message `--metrics needs --profile vector`. [just go-check]
- quality-metrics-22: The hidden form `emd layout --metrics --dump FILE` MUST read one canonical layout dump of any origin and print the same line. [just quality]
    A dump has no model, so this form takes the count of unwritten clusters as 0. It is not in help.

## Baselines

- quality-metrics-23: The quality baselines MUST be `elkjs` 0.12.1 (ELK Layered) and `@dagrejs/dagre` 3.1.3. [just quality]
    ELK Layered is upstream Mermaid's default layout (`layout: elk`). Dagre is the opt-in classic layout. Upstream pins `elkjs` `^0.12.0` and `dagre-d3-es` 7.0.14; this project does not use `dagre-d3-es`.
- quality-metrics-24: `tools/upstream-oracle/baseline.mjs` MUST run these steps for each path in `corpus/quality-corpus.txt`. [just quality]
    1. Read our vector dump from `emd layout --profile vector FILE`. Take the box ids, `parent` links, node and group sizes, route `from` and `to`, and the label `owner`, `w`, and `h`.
    2. Run dagre and ELK with the parameters below. Use the same node and label sizes as ours.
    3. Write two canonical layout dumps: `corpus/.cache/quality/<path>.dagre.json` and `corpus/.cache/quality/<path>.elk.json`, where `<path>` is the corpus path.
- quality-metrics-25: Baseline spacing MUST come from the vector values of `spec/data/layout-constants.json`, with sizes in px = units / 64 and all unlisted options at the engine default. [just quality]
    Spacing comes from the vector values of `spec/data/layout-constants.json`: `vector.node_gap` = 24 px, `vector.rank_gap` = 48 px, and `vector.slot` = 12 px. Sizes pass in px = units / 64, which is exact in binary floating point. Padding and margins are 0 in both engines. Every option that is not listed keeps the engine's default. Mermaid's `elk.layered` defaults are not used except where listed.
- quality-metrics-26: The dagre baseline MUST use these graph options. [just quality]
    |Option|Value|
    |---|---|
    |`rankdir`|`TB`, `BT`, `LR`, or `RL`, the fixture direction (`TD` is `TB`)|
    |`nodesep`|`vector.node_gap` = 24|
    |`ranksep`|`vector.rank_gap` = 48|
    |`edgesep`|`vector.slot` = 12|
    |`marginx`, `marginy`|0|
    |`compound`|`true`; each group is a compound parent, with `setParent`|
    |`acyclicer`|unset (dagre 3.1.3 then breaks cycles by depth-first search; `greedy` is the only other value)|
    |`ranker`|unset (dagre default, network simplex)|
    Dagre 3.1.3 cannot rank an edge that ends at a compound parent. An edge endpoint that is a group MUST be replaced, for dagre only, by the first real node among the group's descendants in declaration order. A group with no real descendant MUST be passed to dagre as an ordinary node with our measured size and no children. The dump keeps the original `from` and `to` ids. A fixture for which an engine still throws fails `just quality`, and the message names the fixture and the engine.
- quality-metrics-27: The ELK baseline MUST use these Layered options, with edge routing orthogonal and model order on. [just quality]
    Upstream Mermaid defaults `forceNodeModelOrder` to false and `considerModelOrder` to `NODES_AND_EDGES`; here both are on.
    The table applies at the root. Nested graphs MUST repeat the same options except the two model-order options, which MUST remain root-only. ELK 0.12.1 does not initialize the model-order indices needed when those options are repeated on nested graphs. Spacing, direction, and padding therefore remain identical at every depth without invoking that invalid nested ordering pass.
    |Option|Value|
    |---|---|
    |`elk.algorithm`|`layered`|
    |`elk.direction`|`DOWN`, `UP`, `RIGHT`, or `LEFT` for `TB`, `BT`, `LR`, or `RL`|
    |`elk.spacing.nodeNode`|24|
    |`elk.layered.spacing.nodeNodeBetweenLayers`|48|
    |`elk.spacing.edgeEdge`|12|
    |`elk.layered.spacing.edgeEdgeBetweenLayers`|12|
    |`elk.layered.spacing.edgeNodeBetweenLayers`|12|
    |`elk.padding`|`[top=0,left=0,bottom=0,right=0]`|
    |`elk.edgeRouting`|`ORTHOGONAL`|
    |`elk.layered.crossingMinimization.forceNodeModelOrder`|`true` (the id `org.eclipse.elk.layered.crossingMinimization.forceNodeModelOrder` is present in elkjs 0.12.1)|
    |`elk.layered.considerModelOrder.strategy`|`NODES_AND_EDGES`|
    |`elk.layered.nodePlacement.bk.fixedAlignment`|`BALANCED`|
    |`elk.hierarchyHandling`|`INCLUDE_CHILDREN`; all edges are listed at the root|
    |`elk.edgeLabels.inline`|`true`|
    |`elk.edgeLabels.placement`|`CENTER`|
- quality-metrics-28: No subgraph `direction` MUST be passed to either baseline. [just quality]
- quality-metrics-29: Node text MUST stay inside the node box, and neither baseline MUST get node labels. [just quality]
    An edge label is passed with our measured `w` and `h`. Dagre gets `width`, `height`, and `labelpos: 'c'` on the edge, with the edge name set to the route id. ELK gets a label child with the label id, `text`, `width`, and `height`, and the listed inline and placement options on that label. ELK ignores a label without `text`, and the root options do not set an individual label's placement. Dagre returns the label centre as the edge `x` and `y` when `labelpos` is `c` (dagre 3.1.3 shifts `x` by half the label width only for `l` and `r`). ELK returns the label top-left relative to its edge's container; the adapter adds that container's absolute position before rounding, as it does for route points.
- quality-metrics-30: Every coordinate or size that a baseline returns in px, `v`, MUST become the integer `r(64 * v)`, where `r(u) = sign(u) * floor(abs(u) + 0.5)` rounds half away from zero on the IEEE double `u`. [just quality]
    The product `64 * v` is exact.
- quality-metrics-31: A real node box MUST keep our `w` and `h`. [just quality]
    Dagre gives the centre, so `left = r(64 * x) - floor_div(w, 2)` and `top = r(64 * y) - floor_div(h, 2)`. ELK gives the top-left, so `left = r(64 * x)` and `top = r(64 * y)`.
- quality-metrics-32: A group box MUST take `w = r(64 * width)` and `h = r(64 * height)` from the engine output, and its position MUST follow the same rule as a node. [just quality]
- quality-metrics-33: ELK positions MUST be made absolute before rounding: ELK reports positions relative to the parent, so the `x` and `y` of every ancestor are added before rounding. [just quality]
    `tools/upstream-oracle/baseline.mjs` MUST assert this on one nested fixture: a child placed at `(0, 0)` inside a group that is not at the origin gets the group's position.
- quality-metrics-34: Baseline routes MUST be scored as returned. [just quality]
    A dagre route is its `points` list, as returned. An ELK route is, for each section in order, `startPoint`, then `bendPoints`, then `endPoint`. A point equal to the previous point is dropped. Routes are scored as returned. They are not clipped, rerouted, or given extra endpoints. Baseline `hard_ok` is reported and not gated.

## Quality gates

- quality-metrics-35: The fixture set `F` MUST be the set of rows of `corpus/verdicts.json` with `accept` true and `kind` one of `flowchart`, `class`, `state`, `er`, `requirement`, `usecase`, `c4`, `agentflow`, or `swimlane` (the layered family; `flowchart` alone until the other eight layered kinds exist, then all nine). [just quality]
- quality-metrics-36: `corpus/quality-corpus.txt` MUST list the paths of `F`, byte-wise sorted, one per line, with a final LF, and `just quality` MUST recompute that file and fail when the committed file differs. [just quality]
- quality-metrics-37: `N_F` MUST be the size of `F`, every sum MUST run over `F`, and the gates MUST use integer comparisons only. [just quality]
- quality-metrics-38: Gate 1 MUST hold: `hard_ok` is `true` for every fixture of ours. [just quality]
- quality-metrics-39: Gate 2 MUST hold: `sum C(ours) <= sum C(dagre)` and `sum C(ours) <= sum C(ELK)`. [just quality]
- quality-metrics-40: Gate 3 MUST hold: `sum soft_cost(ours) <= sum soft_cost(dagre)` and `sum soft_cost(ours) <= sum soft_cost(ELK)`. [just quality]
- quality-metrics-41: Gate 4 MUST hold: per fixture, with `best = min(soft_cost(dagre), soft_cost(ELK))`, a fixture is an exception when `100 * soft_cost(ours) > 120 * best`, and with `e` exceptions the gate passes when `20 * e <= N_F`. [just quality]
    This is exactly "at most 5 percent".
- quality-metrics-42: `corpus/quality-exceptions.json` MUST be one line of UTF-8 JSON, with no spaces and a final LF, in this format. [just quality]
    `{"schema":1,"fixtures":N_F,"exceptions":[{"path":P,"best":B,"best_soft_cost":V,"ours":{"crossings":C,"soft_cost":S},"dagre":{"crossings":C,"soft_cost":S},"elk":{"crossings":C,"soft_cost":S}}]}`
    `best` is `dagre` or `elk`, whichever baseline has the lower soft cost. A tie gives `dagre`. `exceptions` is sorted byte-wise by `path`. An empty list is `[]`. Only the parent writes this file, as it writes `corpus/divergences.json`.
- quality-metrics-43: `just quality` MUST regenerate the expected bytes of `corpus/quality-exceptions.json` and compare them, and it MUST print one row per fixture, with the crossings and soft cost of each layout and the exception flag, then the verdict of each gate. [just quality]
