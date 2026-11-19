# Swimlane grammar

This file defines the `swimlane` kind. All source spans are half-open byte ranges.

## Authority

Authority readings: `.references/mermaid/packages/mermaid/src/diagrams/swimlanes/detector.ts:7-15`; `swimlanesDiagram.ts:1-11`; `styles.ts:1-28`; `swimlanesDiagram.spec.ts:20-66,69-133` in that directory; `.references/mermaid/packages/mermaid/src/diagrams/flowchart/flowDiagram.ts:1-35`; `parser/flow.jison:9-284,300-650` and `flowDb.ts:156-268,419-424,1090-1325` in the flowchart directory; `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:2381-2432`. These are behavioral sources, not text templates.

## Scope and header

- swimlane-01: The implementation MUST use the flowchart language defined by `spec/grammar/flowchart.md`, with only the changes in this file. The upstream factory connects `flowParser`, a new `FlowDB`, and `flowRenderer-v3-unified`; the swimlane definition replaces only the style function. [just oracle]
- swimlane-02: Detection MUST select kind `swimlane`, family `layered`, and upstream alias `swimlane` for the case-sensitive header `swimlane-beta`, using detection-05 through detection-16 of `spec/detection.md`. [just gen-check]
- swimlane-03: The parser MUST replace the header alternatives of flowchart-007 with `swimlane-beta` only; header direction and its normalization MUST follow flowchart-008 through flowchart-014, including the accepted `BR` fallback. Other diagram headers MUST NOT enter this grammar. [just oracle]
- swimlane-04: Preprocessing and spans MUST follow flowchart-005 and flowchart-006. Shared preprocessing, source, limit, and interaction diagnostics MUST retain their common registry ownership and MUST NOT acquire a swimlane prefix. [just parity]

## Lexer

- swimlane-05: The lexer MUST use the modes, entry and exit conditions, and first-match order of flowchart-015 through flowchart-033, with the INITIAL header match for `swimlane-beta` at authority line 117 returning `GRAPH` and entering `dir` on the first header. It MUST NOT add a lane-specific token or mode. [just parity]

The inherited mode table and lexical tables are normative by reference: INITIAL rules in authority order; direction mode rules; text, ellipseText, and trapText rules; string, markdown-string, edge-text, and interaction rules; and shape-data rules. In particular, the wildcard bracket rules precede later general text rules, and unreachable modes remain unreachable. A lexer MUST NOT select a later rule merely because its match is longer.

## Grammar

- swimlane-06: The parser MUST use the following EBNF substitution, with all imported productions and SP rules defined by flowchart-034 and flowchart-035; it MUST NOT backtrack over consumed tokens. [just parity]

```ebnf
swimlane-document = swimlane-header, { statement | SP }, [ EOF ];
swimlane-header   = SWIMLANE, [ SP, direction ], header-end;
SWIMLANE          = "swimlane-beta"; (* token kind GRAPH *)
statement         = vertex-statement, separator
                  | style-statement, separator
                  | class-def-statement, separator
                  | class-statement, separator
                  | link-style-statement, separator
                  | click-statement, separator
                  | subgraph-statement
                  | direction-statement, separator
                  | acc-title, separator
                  | acc-descr, separator
                  | acc-descr-block, separator;
```

- swimlane-07: Every statement alternative above MUST have exactly the forms of flowchart-036 through flowchart-048: bare and shaped nodes; typed shape data; node class shorthand; ampersand groups and link chains; optional link ids and labels; style, classDef, class, and linkStyle including interpolation; callback and href click actions with their permitted tooltips and targets; all three subgraph headers; nested bodies; direction; accessible title; and single-line or block accessible description. [just oracle]
- swimlane-08: Empty lanes, repeated node mentions, nested subgraphs, cross-lane edges, self-loops, nodes outside lanes, and diagrams without subgraphs MUST NOT be rejected solely for those properties. A separate `lane` statement, a phase declaration, or a second orthogonal lane hierarchy MUST NOT be added to the grammar. An unsupported statement MUST use the recovery rules below. [just oracle]

## Statement boundary and AST

- swimlane-09: Statement boundaries and recovery MUST follow flowchart-049 through flowchart-052: skip to a semicolon or physical line end outside strings, balanced shape delimiters, pipe labels, and shape-data blocks at bracket depth zero. Recovery MUST NOT create a node, route, or group. [just go-check]
- swimlane-10: AST nodes and their spans MUST follow flowchart-053 through flowchart-056, without replacing upstream production names by lane-specific names. [just parity]

The imported PascalCase node names are `Start`, `GraphConfig`, `Document`, `Line`, `VertexStatement`, `Node`, `StyledVertex`, `Vertex`, `Link`, `LinkStatement`, `ArrowText`, `EdgeText`, `ShapeData`, `Subgraph`, `StyleStatement`, `ClassDefStatement`, `ClassStatement`, `LinkStyleStatement`, `ClickStatement`, `NumList`, `StylesOpt`, `Style`, `Direction`, `AccTitle`, `AccDescr`, `AccDescrBlock`, `IdString`, `Text`, `TextNoTags`, and `AlphaNum`. Start covers the input; GraphConfig covers the header through its direction; Subgraph includes its closing end. Other nodes cover first through last token, without a trailing separator. Quoted values exclude delimiters from content but include them in spans.

## Model and lanes

- swimlane-11: Model resolution MUST follow flowchart-057 through flowchart-089 for declaration order, implicit nodes, labels and shapes, links, styles, classes, interaction metadata, accessibility, subgraph ids, membership deduplication, and resolved direction; references to diagnostic codes MUST use the ownership rule in swimlane-18. [just parity]
- swimlane-12: Each top-level subgraph MUST become one lane cluster. A nested subgraph MUST remain a plain group inside its containing lane, not a second lane band. Its descendant nodes MUST belong to that top-level lane for band placement. [just parity]
- swimlane-13: A node mentioned by multiple top-level lanes MUST remain in the first lane that claims it under inherited membership resolution, including a claim through a nested group. A later lane left empty only by removal of duplicate claims MUST be omitted; an explicitly empty lane MUST remain. Nested groups and duplicate claims MUST NOT become parser errors. [just oracle]
- swimlane-14: Lane declaration order MUST be the order of the first top-level subgraph openings, not FlowDB's completion order or the order of its returned node list. Repeated ids MUST merge under flowchart-078. Unassigned nodes MUST remain ordinary root-level nodes and MUST NOT create an implicit named lane. [just parity]

## Project layout decision

- swimlane-15: A lane MUST be a cluster pinned to one cross-axis band. Lane bands MUST be consecutive in declaration order with no gap. The cross axis MUST be x for TB and BT and y for LR and RL. [just validate]
- swimlane-16: Lane thickness MUST equal content thickness plus title band plus twice the sum of padding and routing gutter, measured on the cross axis. Content thickness MUST be `hi - lo`, where `lo` is the least cross-axis start and `hi` is the greatest cross-axis end over every box of the lane and over every point of every route with both ends in the lane, taken from the layered layout before any band is moved. [just validate]
    A box of the lane is the lane's own frame box and every box below it at any depth, nested group frames and nodes included. A route has both ends in the lane when each end is a box of the lane. A route label does not count. The lane's own frame box is always a member, so an empty lane is not zero thickness: its content thickness is the cross-axis extent of its own frame box in the layered layout. Content thickness is 0 only when the layered layout holds no box of the lane and no such route.
- swimlane-17: The title band MUST use `line_h` (1280 vector units, 20 px, or 1 cell); padding MUST use `cluster_pad` (1024 vector units, 16 px, or 1 cell); routing gutter MUST use `slot` (768 vector units, 12 px, or 1 cell). These rules are project decisions, not claims about the unavailable upstream layout implementation. [just validate]

## Diagnostics

- swimlane-18: The diagnostic suffixes and trigger, span, and precedence rules of flowchart-090 through flowchart-095 MUST apply under the `swimlane/` prefix. Every such kind-specific row MUST live in `spec/data/diagnostics/swimlane.json`; inherited lint-only predicates of flowchart-096 MUST NOT become syntax errors. Shared diagnostics MUST remain in their shared registries. [just gen-check]
- swimlane-19: The registry MUST contain exactly the following kind-specific codes, all error severity except the stated warning: `swimlane/unexpected-token`, `swimlane/unknown-statement`, `swimlane/unterminated`, `swimlane/unclosed-node-bracket`, `swimlane/subgraph-direction-ignored` (warning), `swimlane/arrow-invalid`, `swimlane/link-unsupported-marker`, `swimlane/label-double-in-double`, `swimlane/label-double-in-single`, `swimlane/label-escaped-quote`, `swimlane/label-quote-in-unquoted`, `swimlane/label-parens-unquoted`, `swimlane/dir-invalid`, `swimlane/dir-kw-invalid`, `swimlane/link-missing`, `swimlane/meta-unsupported`, `swimlane/end-without-subgraph`, `swimlane/node-mixed-brackets`, `swimlane/node-empty`, `swimlane/quote-unclosed`, `swimlane/class-malformed`, `swimlane/linkstyle-multiline`, `swimlane/linkstyle-range-not-supported`, `swimlane/click-call-extra-text`, `swimlane/linkstyle-id-unknown`, and `swimlane/typed-shape-unsupported`. [just gen-check]
- swimlane-20: The unexpected-token message MUST be `unexpected TOKEN, expected one of: LIST`, where TOKEN is source text and LIST is accepted token-kind names sorted bytewise and joined by `, `. Unknown-statement MUST span its first token through its statement boundary. Unterminated MUST span its opener through EOF. A more specific named diagnostic MUST replace a generic unterminated diagnostic for the same failure. [just parity]
- swimlane-21: An out-of-range linkStyle index and an invalid typed shape MUST become model errors, not exceptions. A subgraph direction ignored because an edge crosses its boundary MUST produce the warning only during layout, never during check or lint. The accepted BR header MUST NOT produce dir-invalid. [just oracle]

## Configuration and readings

- swimlane-22: The seven properties of SwimlaneDiagramConfig MUST have rows in `spec/data/config-keys/swimlane.json`. Theme and look MUST be honoured; layout, lineHops, ignoreCrossLaneEdges, optimizeRanksByCrossings, and automaticLaneOrdering MUST be accepted and ignored. Inherited base properties MUST use the common registry; shared flowchart properties MUST use the flowchart registry, not duplicate rows under swimlane. [just gen-check]
- swimlane-23: The implementation MUST preserve accepted syntax when upstream logs a warning for duplicate lane membership or a nested group. The upstream test's returned order of an explicitly empty lane before an earlier nonempty lane MUST NOT override the declaration-order band rule of this project. [just oracle]
- swimlane-24: When the diagram has at least one lane, the node boxes with no parent MUST share one band after the last lane. Let `start` be the least cross-axis start of the lane frame boxes plus the sum of all lane thicknesses, and `clear` the sum of padding and routing gutter. The band thickness MUST be `hi - lo`, taken by the content rule of swimlane-16 over those node boxes, with no title band and no `2 * clear`. The band MUST move by `start + clear - lo` on the cross axis. Swimlane-16 does not apply to this band. [just validate]
- swimlane-25: After band pinning, the layout MUST rebuild each route whose endpoints belong to different bands, including the unnamed root-node band of swimlane-24. It MUST retain the original endpoint positions translated by their bands and extend each endpoint outward on the rank axis by `slot`. The outward direction MUST be positive when twice the endpoint rank coordinate is at least twice its box's rank start plus its rank length, and negative otherwise. Each unrelated exclusive node box MUST remain an obstacle; endpoint boxes MUST be excluded only as permitted by route-clearance in `spec/quality-metrics.md`. [just validate]
- swimlane-26: The router MUST search the orthogonal grid formed by the two extended endpoints and each obstacle's near and far coordinates, offset outward by `slot`, sorted and deduplicated on each axis. Transitions MUST join adjacent grid vertices without meeting an obstacle's open interior. Each vertex MUST have four arrival-direction states in the order `+cross`, `-cross`, `+rank`, `-rank`; an immediate direction reversal MUST NOT be allowed. A transition MUST cost its Manhattan length plus `rank_gap` when its direction changes. The final approach MUST include the same turn cost. A* priority MUST be accumulated cost plus Manhattan distance to the extended target, with ties by cross-major, rank-minor vertex index, then direction index. Equal-cost alternatives MUST retain the earlier path; equal-cost completed routes MUST retain the earlier arrival. [just parity]
- swimlane-27: If the offset grid supplies no clear complete route, the router MUST repeat the search on exact obstacle boundaries. A returned route MUST include both fixed endpoint stubs and pass the complete open-interior clearance check; failure of both searches MUST return the geometry domain error, not a broken route. The exact-edge grid admits a free orthogonal path when both extended endpoints are outside every obstacle interior and the fixed stubs are clear. The router MUST remove consecutive duplicate and collinear points and update the dump route and its edge-group geometry together. With `C` cross coordinates and `R` rank coordinates, the search MUST be structurally bounded by `S = 4CR` directional states, with at most four transitions and `O(B)` obstacle work per expanded state for `B` obstacles. Go and Rust use heap queue operations costing `O(log S)`; the Lean reference sorts its queue at each expansion, costing `O(S log S)`. The router MUST NOT introduce a configurable search cap or search budget diagnostic. [just lean-parity]
- swimlane-28: As the last layout step, after the canvas grows, the layout MUST re-attach each route end whose endpoint box is a lane frame. For that frame let `S` and `F` be its cross-axis start and end, let `lo` be `S` plus the frame's layered cross-axis start plus its band shift minus its band start, and let `hi` be `lo` plus the frame's layered cross-axis length. An end whose cross coordinate equals `hi` MUST move to `F`; otherwise an end whose cross coordinate equals `lo` MUST move to `S`; its rank coordinate MUST NOT change. A route with a moved end MUST consist of the moved first end, the route's points, and the moved last end, with consecutive duplicate and collinear points removed as in swimlane-27. Its edge-group polylines MUST take the new points, and each marker at an old end MUST move to the new end and point from the adjacent point toward it, the larger absolute coordinate difference choosing the axis and x winning ties. Other routes, nodes, frames, labels, and the canvas MUST NOT change. [just validate]
