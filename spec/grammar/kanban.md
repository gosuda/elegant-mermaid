# Kanban grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `kanban` kind.

## Scope

- kanban-01: The implementation MUST use `kanban.jison:6-162` in `.references/mermaid/packages/mermaid/src/diagrams/kanban/parser/` as its grammar authority, and `kanbanDb.ts:15-195,202-214` in the parent directory as its resolution authority. [just oracle]
- kanban-02: The config authority MUST be `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:476-529,1257-1272`; layout MUST remain in `spec/layout/grid.md`. [just gen-check]
- kanban-03: The language MUST include column declarations, card declarations, indentation, delimiter labels, metadata, icon decorations, class decorations, and empty or comment lines; it MUST NOT infer edges from node text. [just oracle]

## Header forms

- kanban-04: Detection MUST accept only the case-sensitive header `kanban`, with the boundary rule of `spec/detection.md`; the body lexer MUST use ASCII case-insensitive literal matching, as the authority's lexer option requires. [just oracle]

## Lexer modes

- kanban-05: The lexer MUST keep the exclusive mode names `NODE`, `NSTR`, `NSTR2`, `ICON`, `CLASS`, `shapeData`, `shapeDataStr`, and `shapeDataEndBracket`; the last mode has no entry rule or active rule. [just parity]
- kanban-06: The lexer MUST choose the first matching rule in the following source order, within the active mode; `INITIAL` means an unqualified rule. [just parity]

| Authority line | Mode | Match | Result |
|---|---|---|---|
|24|INITIAL|`@{`|Push `shapeData`; emit empty-valued `SHAPE_DATA`.|
|27|shapeData|`"`|Push `shapeDataStr`; emit `SHAPE_DATA`, including the quote.|
|32|shapeDataStr|`"`|Pop; emit `SHAPE_DATA`, including the quote.|
|35|shapeDataStr|one or more bytes other than `"`|Emit `SHAPE_DATA`; replace each LF and following whitespace with `<br/>` in its value.|
|40|shapeData|one or more bytes other than `}`, `^`, or `"`|Emit `SHAPE_DATA`.|
|44|shapeData|`}`|Pop; emit nothing.|
|48|INITIAL|whitespace, then `%%`, then text to line end|Emit `SPACELINE`.|
|50|INITIAL|`kanban`|Emit `KANBAN`.|
|51|INITIAL|`:::`|Enter `CLASS`; emit nothing.|
|52|CLASS|one or more non-line-end characters|Pop; emit `CLASS`.|
|53|CLASS|LF|Pop; emit nothing.|
|55|INITIAL|`::icon(`|Enter `ICON`; emit nothing.|
|56|INITIAL|one or more whitespace characters followed by LF|Emit `SPACELINE`.|
|57|INITIAL|one or more LF|Emit `NL`.|
|58|ICON|one or more characters other than `)`|Emit `ICON`.|
|59|ICON|`)`|Pop; emit nothing.|
|60-67|INITIAL|`-)`, `(-`, `))`, `)`, `((`, `{{`, `(`, `[` in that order|Enter `NODE`; emit `NODE_DSTART`.|
|68|INITIAL|one or more whitespace characters|Emit `SPACELIST`.|
|70|INITIAL|one or more characters other than `(`, `[`, LF, `)`, `{`, `}`, `@`|Emit `NODE_ID`.|
|71|INITIAL|end of input|Emit `EOF`.|
|72|NODE|double quote followed by backtick|Enter `NSTR2`; emit nothing.|
|73|NSTR2|one or more characters other than backtick or double quote|Emit `NODE_DESCR`.|
|74|NSTR2|backtick followed by double quote|Pop; emit nothing.|
|75|NODE|double quote|Enter `NSTR`; emit nothing.|
|76|NSTR|one or more characters other than double quote|Emit `NODE_DESCR`.|
|77|NSTR|double quote|Pop; emit nothing.|
|78-85|NODE|`))`, `)`, `]`, `}}`, `(-`, `-)`, `((`, `(` in that order|Pop; emit `NODE_DEND`.|
|86|NODE|one or more characters other than `)`, `]`, `(`, `}`|Emit `NODE_DESCR`.|
|87|NODE|the authority fallback `.+(?!\(\()`|Emit `NODE_DESCR`.|

- kanban-07: Token spans MUST index original source bytes, including discarded delimiters; transformed metadata values MUST retain the source spans of their contributing tokens. Shared preprocessing and line-ending rules MUST follow `spec/preprocessing.md`. [just parity]
- kanban-08: A `NODE_ID` MUST retain its full token text, including trailing spaces; neither ids nor unquoted descriptions MUST receive an additional trim pass. A delimiter pair MUST be accepted by the token grammar rather than checked against a balanced-pair table. [just oracle]

## Grammar

- kanban-09: The parser MUST implement the following EBNF with the authority production names; token values used by actions MUST remain available. [just parity]

```ebnf
start = mindMap | spaceLines, mindMap ;
spaceLines = SPACELINE, { SPACELINE | NL } ;
mindMap = KANBAN, [ NL ], document ;
stop = (NL | EOF | SPACELINE), { NL | EOF } ;
document = statement, stop, { statement, stop } ;
statement = SPACELIST, node, [ shapeData ]
          | SPACELIST, ICON | SPACELIST, CLASS
          | SPACELINE | node, [ shapeData ] | ICON | CLASS | SPACELIST ;
node = nodeWithId | nodeWithoutId ;
nodeWithoutId = NODE_DSTART, NODE_DESCR, NODE_DEND ;
nodeWithId = NODE_ID, [ NODE_DSTART, NODE_DESCR, NODE_DEND ] ;
shapeData = SHAPE_DATA, { SHAPE_DATA } ;
```

- kanban-10: The parser MUST NOT combine multiple `NODE_DESCR` tokens into one label where the production accepts only one; an empty delimiter label has no matching node production. [just oracle]

## Statement boundary

- kanban-11: Recovery MUST stop at the next physical line ending outside a label, icon, or metadata mode; a semicolon MUST remain ordinary node text rather than a statement separator. [just go-check]
- kanban-12: An unrecognised statement MUST NOT create a node; an error inside a recognised statement MUST report its offending token and resume at the boundary. End of input in an open mode MUST report an unterminated construct. [just go-check]

## Abstract syntax tree

- kanban-13: AST nodes MUST use the production names `Start`, `SpaceLines`, `MindMap`, `Stop`, `Document`, `Statement`, `Node`, `NodeWithoutId`, `NodeWithId`, and `ShapeData` in PascalCase; each span MUST cover its first through last source token. [just parity]

| Node | Data and span detail |
|---|---|
|Start, MindMap|Header and document; include the header keyword.|
|SpaceLines, Stop|Separator tokens and their complete source spans.|
|Document|Statements in source order, including their separator nodes.|
|Statement|Indent token or level zero; node and optional metadata, decoration, or whitespace; exclude the trailing Stop from its span.|
|Node, NodeWithId|Id token; optional delimiters and description; include closing delimiter when present.|
|NodeWithoutId|Description used for both id and label; include both delimiters.|
|ShapeData|Concatenated token values and original metadata span, from `@{` through `}`.|

- kanban-14: Tokens MUST borrow source text; the model MUST keep declaration, indentation, delimiter, decoration, and metadata spans for diagnostics. [just parity]

## Semantic resolution

- kanban-15: Resolution MUST append nodes in declaration order without id deduplication. Each node MUST store `id`, `level`, `label`, `width`, `padding`, and initial `isGroup=false`. Its id and initial label MUST use the shared static text sanitisation; an empty sanitised id MUST become `kbnN`, with one shared counter starting at zero and incremented only on generated ids. [just parity]
- kanban-16: An unshaped node MUST use its id text as its description and type zero. A node without an explicit id MUST use its description as its id. Type MUST be rect for `[`, rounded rect for `(` closed by `)`, cloud for other `(` endings or opening `)`, circle for `((`, bang for `))`, hexagon for `{{`, and default for every other opener. [just oracle]
- kanban-17: The stored width MUST come from `mindmap.maxNodeWidth` or its upstream default. Stored padding MUST come from `mindmap.padding` or its upstream default, doubled for rounded rect, rect, and hexagon types. These stored fields MUST NOT define new layout rules here. [just parity]
- kanban-18: A node's level MUST equal the character count of its leading `SPACELIST`, or zero when absent; each TAB MUST count as one character, not an indentation stop. [just oracle]
- kanban-19: The first node MUST define the section level and MUST become a section. Before each later insertion, resolution MUST scan all existing nodes backwards: remember the first node at the first node's level as the latest section, and reject if any existing node has a lower level than the first node. [just oracle]
- kanban-20: A new node at the latest section's level MUST become a new section. Every other level MUST select that latest section as parent, including a smaller level. Deeper indentation MUST NOT create nested cards or select the nearest shallower card. A below-section-level node MUST be inserted as a card first; the next node insertion MUST reject it through the preceding scan. An input that ends immediately after that card MUST retain it. [just oracle]
- kanban-21: The resolved model MUST retain sections in insertion order and cards with their selected `parentId`. The data projection MUST visit each section, then all nodes whose `parentId` equals that section id in declaration order; repeated section ids therefore select the same matching cards. Edges MUST be empty. [just parity]
- kanban-22: Metadata MUST concatenate `SHAPE_DATA` values without the outer `@{` and `}`. If the result has no LF, the reader MUST surround it with flow-map braces and line endings; otherwise it MUST append one LF and read it as block YAML, using the upstream JSON-schema scalar rules. Invalid YAML or a value whose property access fails MUST reject the declaration. [just oracle]
- kanban-23: Metadata MUST read only `shape`, `label`, `icon`, `assigned`, `ticket`, and `priority`; unknown keys MUST have no effect. A truthy `shape` MUST reject when it is not lowercase or contains `_`; a non-string truthy shape MUST reject. The subsequent `shape == kanbanItem` assignment MUST remain unreachable because that spelling fails the lowercase check. Other lowercase shape names MUST be ignored. [just oracle]
- kanban-24: Truthy metadata `label` MUST replace the label without a second sanitisation pass; truthy `icon`, `assigned`, and `ticket` MUST be converted with JavaScript-compatible `toString`; truthy `priority` MUST keep its parsed value without validation. Falsy values, including zero, false, null, and an empty string, MUST leave the field unset or unchanged. [just oracle]
- kanban-25: An icon or class decoration MUST modify the last inserted node, with shared sanitisation, and MUST reject when no node exists. A later decoration MUST replace its field; decoration indentation MUST NOT select a different target. [just oracle]
- kanban-26: The projected section MUST expose id, sanitised label, markdown label type, group flag, ticket, level, shape `kanbanSection`, and configured look. A projected card MUST expose id, parent id, sanitised label, markdown label type, non-group flag, ticket, priority, assigned, icon, level, shape `kanbanItem`, radii 5, and left text alignment; stored class decorations, width, and padding MUST NOT be silently promoted into this projection. [just parity]

## Diagnostics

- kanban-27: Each rejection MUST use the following registry; database exceptions MUST become diagnostics rather than a panic. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
|`kanban/unexpected-token`|error|Token cannot continue a recognised production.|Offending token.|`unexpected TOKEN, expected one of: LIST`|
|`kanban/unknown-statement`|error|No statement starts with this token.|Statement through its boundary, excluding separator.|`unknown statement TOKEN`|
|`kanban/unterminated`|error|Input ends inside a label, icon, or metadata construct.|Opening delimiter through input end.|`unterminated TOKEN`|
|`kanban/items-without-section`|error|The pre-insertion scan finds a stored level below the first node's level.|The earlier below-level declaration's indentation, or its first token at level zero.|`items without section detected at LABEL`|
|`kanban/malformed-metadata`|error|Metadata YAML fails, or metadata property access/conversion fails.|Metadata construct.|`invalid node metadata`|
|`kanban/invalid-shape`|error|Truthy shape is not a lowercase string without underscores.|Shape value.|`invalid shape SHAPE; shape names must be lowercase without underscores`|
|`kanban/decoration-without-node`|error|Icon or class decoration precedes every node.|Decoration construct.|`decoration requires a preceding node`|

- kanban-28: `TOKEN` MUST be the original token text; `LIST` MUST hold accepted token-kind names in ascending byte order joined by `, `. Named model checks MUST NOT duplicate a generic parser diagnostic for the same failure. [just parity]

## Upstream readings

| Reading | Authority fact | Resolution here |
|---|---|---|
|`kanban.jison:126-162`|The production names still refer to mind maps.|Keep those AST names; do not rename `MindMap` to a new production.|
|`kanbanDb.ts:25-48,157-164`|Parent selection uses the first level and latest section, not a nesting stack.|All non-section levels attach to one column; the lower-level error is delayed until the next insertion.|
|`kanbanDb.ts:118-154`|The lowercase shape check precedes the mixed-case accepted shape spelling.|Reject `kanbanItem`; ignore other lowercase shapes.|
|`kanbanDb.ts:54-96,202-214`|The exported projection omits some stored decorations and sizing fields.|Keep stored fields separately from the projected section/card data.|

- kanban-29: An authority-versus-corpus disagreement MUST follow the upstream oracle verdict and MUST record the concrete reading in this section; no layout heuristic MUST change syntax acceptance. [just oracle]
