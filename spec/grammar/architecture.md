# Architecture grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `architecture` kind.

## Scope

- architecture-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/architecture/architecture.langium:1-57`, with `arch.langium:1-2` and `../common/common.langium:6-34` for imported rules. [just oracle]
- architecture-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/architecture/architectureParser.ts:8-17` and `architectureDb.ts:75-282`; token conversion MUST follow `.references/mermaid/packages/parser/src/language/architecture/valueConverter.ts:11-28`. [just parity]
- architecture-03: Shared preprocessing and source-position rules MUST run first; spans MUST index repaired source bytes with exclusive ends. [just parity]

## Header forms

- architecture-04: The parser MUST accept `architecture-beta` and the repository alias `architecture`, case-sensitive, with the boundary in `spec/detection.md` and `spec/data/kinds.json`. [just oracle]
- architecture-05: Body keywords and port letters MUST match case-sensitively. [just oracle]

## Lexer modes

- architecture-06: The lexer MUST use one `INITIAL` mode; it MUST NOT introduce stateful string or title modes. [just parity]

### Lexical rules in first-match order

- architecture-07: The lexer MUST test grammar literals before terminals, with a keyword-to-ID boundary check, then test local terminals, imported common terminals, and imported architecture terminals in the order below; the first matching rule MUST win. [just parity]

| Order | Pattern or token | Action |
|---|---|---|
| literals | `architecture-beta`, `group`, `service`, `junction`, `in`, `align`, `row`, `column`, `:`, `--`, `-` | Emit literal token; prefer `--` to its `-` prefix. |
| architecture:55 | `ARROW_DIRECTION`: `L`, `R`, `T`, `B` | Emit a port letter; an ID beginning with that letter remains an ID. |
| architecture:56 | `ARROW_GROUP`: literal `{group}` | Emit boundary modifier. |
| architecture:57 | `ARROW_INTO`: `<` or `>` | Emit arrow flag. |
| common:12 | `BOOLEAN`: `true` or `false` | Emit boolean terminal; no architecture production consumes it. |
| common:14 | `ACC_DESCR`: leading horizontal space, `accDescr`, then colon text up to comment or line end, or whitespace and brace text through the next `}` | Emit common description token. |
| common:15 | `ACC_TITLE`: leading horizontal space, `accTitle`, optional horizontal space, colon, text up to comment or line end | Emit common accessible title token. |
| common:16 | `TITLE`: leading horizontal space, `title`, then optional horizontal-space-prefixed line text | Emit diagram title token. |
| common:18-20 | `FLOAT`, `INT`, `NUMBER`: decimal digits with a required fractional part for FLOAT; INT is zero or a nonzero digit followed by digits, not followed by a dot | Emit numeric terminal; no architecture production consumes it. |
| common:22 | `STRING`: matching single or double quotes, with backslash followed by any character as an escape | Emit string token. |
| common:27 | `ID`: ASCII word character followed optionally by word characters or hyphens, ending with a word character | Emit identifier; a single word character is valid. |
| common:29 | `NEWLINE`: LF or CRLF | Emit line end; shared preprocessing also recognizes lone CR. |
| common:31 | `WHITESPACE`: one or more spaces or tabs | Hide. |
| common:32-34 | `YAML`, `DIRECTIVE`, `SINGLE_LINE_COMMENT` | Shared preprocessing owns these hidden forms. |
| arch:1 | `ARCH_ICON`: `(`, one or more ASCII word characters, hyphens, or colons, `)` | Emit icon token. |
| arch:2 | `ARCH_TITLE`: `[`, either a complete quoted string or one or more characters other than brackets and line ends, `]` | Emit title token. |

- architecture-08: A title token MUST retain its delimiters in its span; its value MUST remove the outer brackets, trim whitespace, remove matching outer quotes, replace escaped single and double quotes with those quotes, and trim again. [just parity]
- architecture-09: An icon value MUST remove parentheses and trim whitespace; a service STRING icon MUST use the shared string conversion and MUST remain distinct from an ARCH_ICON value. [just parity]

## Grammar

- architecture-10: The parser MUST implement the following EBNF without backtracking over consumed tokens. [just parity]

```ebnf
Architecture = NEWLINE*, header, (NEWLINE | TitleAndAccessibilities | Statement)* ;
header = 'architecture-beta' | 'architecture' ;
Statement = Group | Service | Junction | Edge | Alignment ;
Group = 'group', ID, ARCH_ICON?, ARCH_TITLE?, ('in', ID)?, EOL ;
Service = 'service', ID, (STRING | ARCH_ICON)?, ARCH_TITLE?, ('in', ID)?, EOL ;
Junction = 'junction', ID, ('in', ID)?, EOL ;
Edge = ID, ARROW_GROUP?, Arrow, ID, ARROW_GROUP?, EOL ;
Arrow = LeftPort, ARROW_INTO?, ('--' | '-', ARCH_TITLE, '-'), ARROW_INTO?, RightPort ;
LeftPort = ':', ARROW_DIRECTION ;
RightPort = ARROW_DIRECTION, ':' ;
Alignment = 'align', ('row' | 'column'), ID, ID, ID*, EOL ;
TitleAndAccessibilities = ((ACC_DESCR | ACC_TITLE | TITLE), EOL)+ ;
EOL = NEWLINE+ | EOF ;
```

- architecture-11: Both arrow flag positions MUST accept either `<` or `>`; each flag MUST resolve to presence, not to a second direction enum. [just oracle]
- architecture-12: The parser MUST allow an empty body, repeated edges, self-edges, and metadata between statements; it MUST NOT create implicit endpoint nodes. [just oracle]

## Statement boundary

- architecture-13: Recovery MUST stop at the next physical line end outside complete quoted, bracketed, or parenthesized tokens, or at EOF; a semicolon MUST NOT terminate a statement. [just go-check]
- architecture-14: A statement with an unknown initial token MUST raise `architecture/unknown-statement` and MUST NOT create a model element; a recognized statement with invalid continuation MUST raise `architecture/unexpected-token`. [just oracle]
- architecture-15: EOF inside a string, icon, bracketed title, or brace description MUST raise `architecture/unterminated`, with the span from the opening delimiter through EOF. [just go-check]

## Abstract syntax tree

- architecture-16: AST nodes MUST use the authority production names below and MUST span their first through last content token, excluding trailing EOL; the root MUST span the complete parsed document. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| `Architecture` | groups, services, junctions, edges, alignments, common metadata | Complete document. |
| `Group` | id, optional icon, title, in | `group` through final field. |
| `Service` | id, optional iconText or icon, title, in | `service` through final field. |
| `Junction` | id, optional in | `junction` through final field. |
| `Edge` | lhsId, lhsGroup, lhsDir, lhsInto, title, rhsInto, rhsDir, rhsId, rhsGroup | First endpoint through last modifier or endpoint. |
| `Alignment` | direction, ordered members | `align` through last member. |
| `TitleAndAccessibilities` | ordered metadata tokens | First metadata token through last value. |

`Statement`, `Arrow`, `LeftPort`, and `RightPort` are authority fragments. They contribute fields and token spans, not independent model elements.

- architecture-17: The AST MUST retain identifier, parent, port, modifier, and member spans for diagnostics; token text MUST borrow source bytes. [just parity]

## Semantic resolution

- architecture-18: Resolution MUST populate common metadata first, then all groups in group declaration order, then all services, then all junctions, then all edges, then all alignment hints; it MUST NOT validate these lists in interleaved source order. Common metadata MUST use the shared converter: trim single-line values and collapse repeated spaces or tabs; for brace descriptions, trim each line, collapse repeated horizontal whitespace, and collapse repeated line-ending characters to one LF. [just oracle]
- architecture-19: Groups and nodes MUST share one registered-id namespace; a repeated id MUST raise `architecture/duplicate-id` at the later processed id, with the first id as a related span. [just oracle]
- architecture-20: A parent MUST differ from the child id, exist when that child is processed, and name a group; violations MUST raise `architecture/self-parent`, `architecture/parent-not-found`, or `architecture/parent-not-group`, respectively. [just oracle]
- architecture-21: A group MUST store id, icon, title, and optional parent unchanged after value conversion; a service MUST store id, type `service`, icon, iconText, title, parent, and an initially empty edge list; a junction MUST store id, type `junction`, parent, and an initially empty edge list. [just parity]
- architecture-22: An edge MUST retain both endpoint ids, both side letters, both arrow-presence flags, both group-presence flags, and its optional title; `{group}` MUST NOT replace an endpoint id with a group id. [just parity]
- architecture-23: Each endpoint MUST name an existing node; an unknown id MUST raise `architecture/endpoint-not-found`; a group id used directly MUST raise `architecture/endpoint-not-node`, because the database dereferences the node before it stores the edge. [just oracle]
- architecture-24: A group modifier MUST raise `architecture/group-boundary-not-crossed` when both endpoint parents exist and are equal; a modifier on an ungrouped endpoint or an edge with only one grouped endpoint MUST remain accepted. [just oracle]
- architecture-25: Each accepted edge MUST append once to the diagram edge list and once to each endpoint edge list; a self-edge MUST append twice to that node's list. [just parity]
- architecture-26: An alignment MUST contain at least two members, each an existing service or junction, with no repeated id; it MUST retain direction and member order as a layout hint without adding an edge. [just oracle]
- architecture-27: Group and node insertion order MUST remain stable; layout placement and routing MUST remain owned by `spec/layout/grid.md`, not by this grammar. [just parity]

## Diagnostics

- architecture-28: Rejections MUST use the codes below with severity error; a failed database operation MUST NOT add its element. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `architecture/unexpected-token` | error | Token has no valid continuation | Offending token, zero-width at EOF | `unexpected TOKEN, expected one of: LIST` |
| `architecture/unknown-statement` | error | Unknown statement start | First token through recovery boundary, excluding line end | `unknown statement TOKEN` |
| `architecture/unterminated` | error | Open delimiter at EOF | Opening delimiter through EOF | `unterminated TOKEN` |
| `architecture/duplicate-id` | error | Id already registered | Later processed id | `id ID is already in use` |
| `architecture/self-parent` | error | Parent equals child | Parent id | `element ID cannot contain itself` |
| `architecture/parent-not-found` | error | Parent not registered | Parent id | `parent ID does not exist` |
| `architecture/parent-not-group` | error | Parent is a node | Parent id | `parent ID is not a group` |
| `architecture/invalid-direction` | error | Side outside L/R/T/B | Invalid side token | `invalid edge direction TOKEN; expected L, R, T, B` |
| `architecture/endpoint-not-found` | error | Endpoint absent | Endpoint id | `edge endpoint ID does not exist` |
| `architecture/endpoint-not-node` | error | Endpoint names a group directly | Endpoint id | `edge endpoint ID is not a service or junction` |
| `architecture/group-boundary-not-crossed` | error | Modifier between two nodes with the same defined parent | Offending modifier; left before right | `endpoint ID has a group modifier but the edge stays in one group` |
| `architecture/align-too-few-members` | error | Fewer than two alignment members | Alignment statement | `alignment requires at least two members` |
| `architecture/align-member-not-node` | error | Alignment member absent or a group | Member id | `alignment member ID is not a service or junction` |
| `architecture/align-duplicate-member` | error | Repeated alignment member | Repeated member id | `alignment lists ID more than once` |

- architecture-29: LIST MUST contain valid token-kind names sorted bytewise and joined by `, `; TOKEN MUST use source text; invalid port letters and too-short alignments MUST use their named diagnostics instead of the generic continuation diagnostic. [just parity]

## Upstream readings

| Reading | Authority fact | Resolution here |
|---|---|---|
| architecture.langium:35-52 | Groups, services, junctions, edges, and alignments are separate lists. | Keep every statement form, including align. |
| architectureParser.ts:10-16 | Population is grouped by element type. | Forward references to later services work; forward references to later groups from groups do not. |
| architectureDb.ts:214-226 | Endpoint existence permits group ids, but the next operation dereferences nodes. | Reject direct group endpoints with a typed diagnostic instead of a runtime exception. |
| architectureDb.ts:227-255 | Modifiers test equal defined parents; edges attach at both ends. | Preserve modifiers and duplicate self-edge incidence. |
| architecture/valueConverter.ts:13-14 | ARCH_TEXT_ICON converter branch exists, but no grammar rule reaches it. | Do not add a text-icon syntax beyond service STRING. |
| config.schema.yaml:476-525,1132-1204 | Architecture inherits base keys and adds layout parameters. | Classify all keys in the companion registry. |

- architecture-30: The Go and Rust parsers MUST produce the same ordered semantic records and diagnostics; corpus verdicts MUST decide any conflict between this reading and upstream acceptance. [just parity]
