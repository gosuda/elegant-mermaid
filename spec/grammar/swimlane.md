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
- swimlane-16: Lane thickness MUST equal content thickness plus title band plus twice the sum of padding and routing gutter. Content thickness MUST be the cross-axis extent of the bounding box of the lane's member node boxes and routes with both ends in that lane, measured after its layout. Empty-lane content thickness MUST be zero. [just validate]
- swimlane-17: The title band MUST use `line_h` (1280 vector units, 20 px, or 1 cell); padding MUST use `cluster_pad` (1024 vector units, 16 px, or 1 cell); routing gutter MUST use `slot` (768 vector units, 12 px, or 1 cell). These rules are project decisions, not claims about the unavailable upstream layout implementation. [just validate]

## Diagnostics

- swimlane-18: The diagnostic suffixes and trigger, span, and precedence rules of flowchart-090 through flowchart-095 MUST apply under the `swimlane/` prefix. Every such kind-specific row MUST live in `spec/data/diagnostics/swimlane.json`; inherited lint-only predicates of flowchart-096 MUST NOT become syntax errors. Shared diagnostics MUST remain in their shared registries. [just gen-check]
- swimlane-19: The registry MUST contain exactly the following kind-specific codes, all error severity except the stated warning: `swimlane/unexpected-token`, `swimlane/unknown-statement`, `swimlane/unterminated`, `swimlane/unclosed-node-bracket`, `swimlane/subgraph-direction-ignored` (warning), `swimlane/arrow-invalid`, `swimlane/link-unsupported-marker`, `swimlane/label-double-in-double`, `swimlane/label-double-in-single`, `swimlane/label-escaped-quote`, `swimlane/label-quote-in-unquoted`, `swimlane/label-parens-unquoted`, `swimlane/dir-invalid`, `swimlane/dir-kw-invalid`, `swimlane/link-missing`, `swimlane/meta-unsupported`, `swimlane/end-without-subgraph`, `swimlane/node-mixed-brackets`, `swimlane/node-empty`, `swimlane/quote-unclosed`, `swimlane/class-malformed`, `swimlane/linkstyle-multiline`, `swimlane/linkstyle-range-not-supported`, `swimlane/click-call-extra-text`, `swimlane/linkstyle-id-unknown`, and `swimlane/typed-shape-unsupported`. [just gen-check]
- swimlane-20: The unexpected-token message MUST be `unexpected TOKEN, expected one of: LIST`, where TOKEN is source text and LIST is accepted token-kind names sorted bytewise and joined by `, `. Unknown-statement MUST span its first token through its statement boundary. Unterminated MUST span its opener through EOF. A more specific named diagnostic MUST replace a generic unterminated diagnostic for the same failure. [just parity]
- swimlane-21: An out-of-range linkStyle index and an invalid typed shape MUST become model errors, not exceptions. A subgraph direction ignored because an edge crosses its boundary MUST produce the warning only during layout, never during check or lint. The accepted BR header MUST NOT produce dir-invalid. [just oracle]

## Configuration and readings

- swimlane-22: The seven properties of SwimlaneDiagramConfig MUST have rows in `spec/data/config-keys/swimlane.json`. Theme and look MUST be honoured; layout, lineHops, ignoreCrossLaneEdges, optimizeRanksByCrossings, and automaticLaneOrdering MUST be accepted and ignored. Inherited base properties MUST use the common registry; shared flowchart properties MUST use the flowchart registry, not duplicate rows under swimlane. [just gen-check]
- swimlane-23: The implementation MUST preserve accepted syntax when upstream logs a warning for duplicate lane membership or a nested group. The upstream test's returned order of an explicitly empty lane before an earlier nonempty lane MUST NOT override the declaration-order band rule of this project. [just oracle]
