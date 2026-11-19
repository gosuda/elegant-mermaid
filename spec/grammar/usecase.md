# Usecase grammar

This file fixes lexical rules, grammar, abstract syntax, resolution, and diagnostics for `usecase`.

## Scope

- usecase-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/usecase/parser/usecase.tokens.ts:13-121,124-410` and `usecase.parser.ts:137-663,668-701`; semantic authorities MUST be `usecase.visitor.ts:137-880`, `usecaseModelBuilder.ts:280-1049`, and `../usecaseDb.ts:213-277,324-520`, relative to that parser directory. [just oracle]
- usecase-02: The parser MUST cover all reachable authority productions, including JSON nodes, notes, metadata, styles, and accessibility; it MUST NOT accept PlantUML syntax by analogy. [just oracle]
- usecase-03: Shared preprocessing MUST run first; spans MUST index repaired UTF-8 source bytes with exclusive ends. [just parity]

## Header forms

- usecase-04: The header MUST be `usecase-beta`, case-sensitive, followed by a line end or EOF; shared detection MUST enforce its keyword boundary. [just oracle]
- usecase-05: Body keywords MUST be case-sensitive except `include` and `extend`, which MUST use ASCII case folding; keyword `longer_alt` MUST preserve longer identifiers. [just parity]

## Lexer modes

- usecase-06: The lexer MUST retain the authority mode names and take the first matching rule in each ordered list below; abstract categories MUST NOT consume text. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| `defaultMode` | source start | push of another mode |
| `jsonBody` | `JSON_DECLARATION_START` | object or unclosed-object token pops |
| `stereotype` | `<<` | `>>` or unclosed text pops |

### Lexical rules in first-match order

- usecase-07: `defaultMode` MUST use this order from `usecase.tokens.ts:323-390`, not token-definition order. [just parity]

| Order | Token | Match or action |
|---|---|---|
| 1–2 | LABEL_TEXT, WORD | abstract categories; WORD belongs to LABEL_TEXT |
| 3 | HWS | one or more SP or HT; skip |
| 4 | MARKDOWN_STRING | double quote then backtick, through first backtick then double quote; may cross lines |
| 5 | UNCLOSED_MARKDOWN_STRING | same opener through EOF |
| 6 | COMMENT | `%%` through line end, only after indentation at line start |
| 7 | NEWLINE | CRLF, LF, or CR |
| 8 | ACC_DESCR_BLOCK | line-initial `accDescr` plus optional HWS and `{`, through first `}` |
| 9–10 | ACC_TITLE_LINE, ACC_DESCR_LINE | line-initial `accTitle` or `accDescr`, optional HWS, colon, remaining line |
| 11 | JSON_DECLARATION_START | `json` HWS+ ASCII word HWS* `@` HWS* before `{`; push jsonBody |
| 12–31 | USECASE, ACTOR, SYSTEM_BOUNDARY, END, DIRECTION, TD, TB, BT, LR, RL, NOTE, FOR, JSON, CLASS_DEF, CLASS, STYLE, INCLUDE, EXTEND, TRUE, FALSE | keywords in this displayed order; USECASE is `usecase-beta`, SYSTEM_BOUNDARY is `systemBoundary`, CLASS_DEF is `classDef`; all belong to WORD |
| next | GENERALIZATION, DEPENDENCY_ARROW, STEREOTYPE_START | `--\|>`, `..>`, `<<`; last pushes stereotype |
| next | CLASS_SEPARATOR | `:::` |
| next | FORWARD_SOLID, BACKWARD_SOLID | two or more hyphens then `>`; `<` then two or more hyphens |
| next | FORWARD_CIRCLE, BACKWARD_CIRCLE, FORWARD_CROSS, BACKWARD_CROSS | `--o`, `o--`, `--x`, `x--` |
| next | MARKERLESS_SOLID | two or more hyphens |
| next | METADATA_START, AT, LBRACE, RBRACE, LBRACKET, RBRACKET, LPAREN, RPAREN, COMMA, COLON | `@{`, `@`, `{`, `}`, `[`, `]`, `(`, `)`, `,`, `:` |
| next | HASH_COLOR | `#` followed by one or more hexadecimal digits |
| next | PLAIN_STRING | single- or double-quoted text, without line ends or its closing quote; no escape processing |
| next | CSS_IDENTIFIER | `--` then ASCII letter or underscore then word/hyphen characters; or ASCII word with at least one hyphen-separated word suffix |
| next | IDENTIFIER | ASCII letters, digits, underscore, one or more; NUMBER is its longer alternative |
| next | NUMBER | digits with optional decimal fraction, or dot then digits; optional ASCII-letter unit suffix |
| next | CSS_ESCAPED_COMMA, DASH, DOT, PERCENT | backslash-comma, `-`, `.`, `%` |
| next | CSS_PUNCTUATION | one of `! # $ & * + / = ? ^ _ \| ~` |
| next | LABEL_PUNCTUATION | semicolon, angle bracket, backslash, or backtick |
| last | LABEL_SYMBOL | nonempty run outside printable ASCII, SP, HT, CR, LF |

- usecase-08: LABEL_TEXT MUST include WORD, NUMBER, AT, COMMA, COLON, HASH_COLOR, CSS_IDENTIFIER, CSS_ESCAPED_COMMA, DASH, DOT, PERCENT, CSS_PUNCTUATION, LABEL_PUNCTUATION, and LABEL_SYMBOL; delimiters and operators MUST NOT belong to it. [just parity]
- usecase-09: `jsonBody` MUST try JSON_OBJECT_LITERAL before UNCLOSED_JSON_OBJECT_LITERAL; the first MUST scan balanced braces while ignoring braces in double-quoted JSON strings and respecting backslash escapes. [just parity]
- usecase-10: `stereotype` MUST try STEREOTYPE_END, STEREOTYPE_TEXT, then UNCLOSED_STEREOTYPE_TEXT; text MUST end before `>>`, MUST contain non-whitespace text, and MUST NOT cross a line end. [just parity]
- usecase-11: Unquoted labels MUST preserve source bytes between their first and last token, including skipped internal whitespace; quoted labels MUST remove only their delimiters. [just parity]

## Grammar

- usecase-12: The parser MUST use the EBNF below; names MUST follow the authority productions and token names MUST refer to the ordered lexer above. [just parity]

```ebnf
start = USECASE, lineEnd, { line } ;
line = blankLine | commentLine | statement ;
lineEnd = NEWLINE | EOF ;
blankLine = NEWLINE ;
commentLine = COMMENT, lineEnd ;
statement = accTitleStatement | accDescrStatement | directionStatement
 | actorStatement | systemBoundaryStatement | noteStatement | jsonStatement
 | classDefStatement | classStatement | styleStatement
 | metadataAssignmentStatement | entityStatement ;
accTitleStatement = ACC_TITLE_LINE, lineEnd ;
accDescrStatement = (ACC_DESCR_LINE | ACC_DESCR_BLOCK), lineEnd ;
actorStatement = ACTOR, actorItem, [ (COMMA, actorItem, { COMMA, actorItem }) | relationTail ], lineEnd ;
actorDeclarationOnly = ACTOR, actorItem, { COMMA, actorItem }, lineEnd ;
actorItem = actorName, [ metadata ], [ stereotype ], [ classSuffix ] ;
actorName = IDENTIFIER, [ LPAREN, nodeLabel, RPAREN ] | PLAIN_STRING | MARKDOWN_STRING ;
entityStatement = entityName, [ relationTail ], lineEnd ;
entityName = (IDENTIFIER, [ LPAREN, nodeLabel, RPAREN | LBRACKET, nodeLabel, RBRACKET ]
 | PLAIN_STRING | MARKDOWN_STRING), [ useCaseMetadata ], [ stereotype ], [ classSuffix ] ;
nodeLabel = PLAIN_STRING | MARKDOWN_STRING | LABEL_TEXT, { LABEL_TEXT } ;
useCaseMetadata = metadata ;
relationTail = [ IDENTIFIER, AT ], arrow, entityName ;
arrow = semanticRelation | forwardSolidOperator | backwardSolidOperator
 | markerlessSolidOperator | forwardCircleOperator | backwardCircleOperator
 | forwardCrossOperator | backwardCrossOperator ;
forwardSolidOperator = FORWARD_SOLID ;
backwardSolidOperator = BACKWARD_SOLID, [ edgeLabel, MARKERLESS_SOLID ] ;
markerlessSolidOperator = MARKERLESS_SOLID,
 [ edgeLabel, (FORWARD_SOLID | MARKERLESS_SOLID | FORWARD_CIRCLE | FORWARD_CROSS) ] ;
forwardCircleOperator = FORWARD_CIRCLE ;
backwardCircleOperator = BACKWARD_CIRCLE, [ edgeLabel, MARKERLESS_SOLID ] ;
forwardCrossOperator = FORWARD_CROSS ;
backwardCrossOperator = BACKWARD_CROSS, [ edgeLabel, MARKERLESS_SOLID ] ;
edgeLabel = PLAIN_STRING | MARKDOWN_STRING | LABEL_TEXT, { LABEL_TEXT } ;
semanticRelation = DEPENDENCY_ARROW, COLON, (INCLUDE | EXTEND) | GENERALIZATION ;
metadata = METADATA_START, { NEWLINE },
 [ metadataProperty, { metadataSeparator, metadataProperty }, [ COMMA ], { NEWLINE } ], RBRACE ;
metadataProperty = (IDENTIFIER | PLAIN_STRING), COLON, (IDENTIFIER | PLAIN_STRING | TRUE | FALSE) ;
metadataSeparator = COMMA, { NEWLINE } | NEWLINE, { NEWLINE }, [ COMMA ], { NEWLINE } ;
systemBoundaryStatement = SYSTEM_BOUNDARY, systemBoundaryName, [ metadata ], [ classSuffix ],
 lineEnd, systemBoundaryContent, END, lineEnd ;
systemBoundaryName = IDENTIFIER, [ LPAREN, nodeLabel, RPAREN | LBRACKET, nodeLabel, RBRACKET ]
 | PLAIN_STRING | MARKDOWN_STRING ;
systemBoundaryContent = { blankLine | commentLine | boundaryElement } ;
boundaryElement = actorDeclarationOnly | entityName, lineEnd ;
metadataAssignmentStatement = metadataAssignmentTarget, metadata, lineEnd ;
metadataAssignmentTarget = IDENTIFIER | PLAIN_STRING | MARKDOWN_STRING ;
noteStatement = NOTE, FOR, IDENTIFIER, nodeLabel, lineEnd ;
stereotype = STEREOTYPE_START, STEREOTYPE_TEXT, STEREOTYPE_END ;
classSuffix = CLASS_SEPARATOR, IDENTIFIER, { COMMA, IDENTIFIER } ;
jsonStatement = JSON_DECLARATION_START, JSON_OBJECT_LITERAL, [ classSuffix ], lineEnd ;
directionStatement = DIRECTION, (TD | TB | BT | LR | RL), lineEnd ;
classDefStatement = CLASS_DEF, IDENTIFIER, { COMMA, IDENTIFIER }, styles, lineEnd ;
classStatement = CLASS, IDENTIFIER, { COMMA, IDENTIFIER }, IDENTIFIER, { COMMA, IDENTIFIER }, lineEnd ;
styleStatement = STYLE, IDENTIFIER, styles, lineEnd ;
styles = styleValue, { COMMA, styleValue } ;
styleValue = (WORD | CSS_IDENTIFIER | MARKERLESS_SOLID, WORD), COLON, styleComponent, { styleComponent } ;
styleComponent = WORD | PLAIN_STRING | NUMBER | HASH_COLOR | CSS_IDENTIFIER | CSS_ESCAPED_COMMA
 | DASH | DOT | PERCENT | CSS_PUNCTUATION | COLON | LPAREN | RPAREN
 | LBRACKET | RBRACKET | LBRACE | RBRACE | AT | MARKERLESS_SOLID ;
```

- usecase-13: Metadata-assignment lookahead MUST select a bare identifier or quoted name immediately followed by METADATA_START before entityStatement; this form MUST NOT declare a new node. [just oracle]
- usecase-14: An optional embedded association label MUST be read only when a right operator follows a nonempty contiguous sequence of label tokens; the opening markerless operator MUST be exactly `--`, and a labeled backward-solid opener MUST be exactly `<--`. [just oracle]
- usecase-15: A boundary body MUST contain only actor declarations, entity declarations, blank lines, and comments; relations, nested boundaries, direction, notes, JSON, and style statements MUST remain top-level. [just oracle]
- usecase-16: The identifiers `allowmixing`, `newpage`, `package`, `rectangle`, and `skinparam` at statement start MUST be rejected with ASCII case folding; a semicolon MUST NOT terminate a statement. [just oracle]

## Statement boundary

- usecase-17: Recovery MUST stop at the next physical line end outside a markdown string, JSON object, metadata object, or accessibility block, or before the current boundary's `end`; recovery MUST leave that `end` for its owner. [just go-check]
- usecase-18: An unknown statement MUST span from its first token to that boundary, excluding the separator; it MUST NOT create a node. [just parity]
- usecase-19: EOF inside a string, stereotype, metadata, JSON object, accessibility block, or system boundary MUST produce `usecase/unterminated` from the opening token through EOF; a parser MUST emit only that diagnostic for the unfinished construct. [just parity]

## Abstract syntax tree

- usecase-20: Each concrete production above MUST have a PascalCase AST node with its production name; each node MUST retain its ordered child nodes and source tokens, with a span from first token start through last token end, excluding its final lineEnd. [just parity]

| Nodes | Required payload and extra spans |
|---|---|
| Start, Line, Statement, LineEnd, BlankLine, CommentLine | header, ordered alternatives, separator or comment token |
| AccTitleStatement, AccDescrStatement, DirectionStatement | value and content span |
| ActorStatement, ActorDeclarationOnly, ActorItem, ActorName | ordered declarations, id, label, metadata, stereotype, classes, optional relation |
| EntityStatement, EntityName, NodeLabel, UseCaseMetadata | id, label kind, delimiter kind, suffixes, optional relation; id and label-content spans |
| RelationTail, Arrow, SemanticRelation, ForwardSolidOperator, BackwardSolidOperator, MarkerlessSolidOperator, ForwardCircleOperator, BackwardCircleOperator, ForwardCrossOperator, BackwardCrossOperator, EdgeLabel | endpoint, optional edge id, arrow tokens, optional label; separate endpoint, id, and label spans |
| Metadata, MetadataProperty, MetadataSeparator, MetadataAssignmentStatement, MetadataAssignmentTarget | ordered properties, raw key/value tokens and separate key/value-content spans |
| SystemBoundaryStatement, SystemBoundaryName, SystemBoundaryContent, BoundaryElement | boundary id, title, members, metadata, classes, closing-token span |
| NoteStatement, Stereotype, ClassSuffix, JsonStatement | target and label; stereotype content; class token spans; JSON id and ordered object |
| ClassDefStatement, ClassStatement, StyleStatement, Styles, StyleValue, StyleComponent | target/class lists, ordered style components and source spans |

- usecase-21: Tokens MUST borrow source bytes; quoted-content spans MUST exclude quotes, markdown-content spans MUST exclude both delimiter pairs, and node spans MUST retain those delimiters. [just parity]

## Semantic resolution

- usecase-22: Resolution MUST collect explicit declarations and explicit edge ids in source order before resolving references; forward references MUST be valid, and undeclared relation endpoints MUST become ellipse use cases. [just oracle]
- usecase-23: Node order MUST follow first source occurrence, including relation references; relationship order MUST follow declaration order, and anonymous relationship ids MUST be `edge-N` with zero-based anonymous-only numbering. [just parity]
- usecase-24: A quoted name MUST derive its id by replacing each character outside ASCII letters, digits, and underscore with `_`; repeated generated-id declarations MUST be rejected even when their labels agree. [just parity]
- usecase-25: Bare top-level entities MUST declare ellipse use cases; parenthesized labels MUST select ellipses and bracket labels MUST select rectangles; actor declarations MUST select actors with captions. [just oracle]
- usecase-26: Repeated explicit declarations MUST merge classes without duplicates only when kind, label text, label kind, shape, parent boundary, stereotype, and declaration metadata agree; conflicting declarations MUST report `usecase/declaration-conflict` with a related first-declaration span. [just oracle]
- usecase-27: Boundaries MUST become clusters with ordered unique members; their label delimiters MUST NOT select their geometry, and their type MUST default to `rect`. [just parity]
- usecase-28: Actor metadata MUST accept `type` equal to `normal`, `hollow`, or `awesome`, string `icon`, and boolean `business`; use-case metadata MUST accept only boolean `business`; boundary metadata MUST accept only `type` equal to `rect` or `package`. [just oracle]
- usecase-29: Standalone metadata MUST resolve an existing symbol after declaration collection and MUST replace the specified fields in statement order; explicit-edge metadata MUST accept boolean `animate` and `animation` equal to `fast` or `slow`, with animation enabling animate; JSON-node metadata MUST be invalid. [just oracle]
- usecase-30: An actor MUST NOT combine a nonempty icon with hollow or awesome type; a business actor MUST use normal or hollow geometry; a rectangular use case MUST NOT be business. [just oracle]
- usecase-31: Associations MUST accept `-->`, `<--`, `--`, `--o`, `o--`, `--x`, and `x--`; longer solid hyphen runs MUST set minimum length to max(1, hyphen count minus 1), and circle/cross forms MUST set it to 1. [just parity]
- usecase-32: Embedded association labels MUST use `-- LABEL -->`, `-- LABEL --`, `-- LABEL --o`, `-- LABEL --x`, `<-- LABEL --`, `o-- LABEL --`, or `x-- LABEL --`; backward markers MUST remain at the source endpoint without swapping source declaration order. [just oracle]
- usecase-33: `..>:include` and `..>:extend` MUST create directed semantic relationships with normalized lowercase labels and minimum length 1; both endpoints MUST be use cases. [just oracle]
- usecase-34: `--|>` MUST create generalization toward its target with minimum length 1; both endpoints MUST be actors or both MUST be use cases. [just oracle]
- usecase-35: Boundary and edge symbols MUST NOT be relationship endpoints; JSON endpoints MUST permit only forward-point, backward-point, or markerless solid association; a bare endpoint reference with `:::` MUST be rejected unless it also declares the node. [just oracle]
- usecase-36: JSON nodes MUST parse one strict JSON object and preserve object property order at every depth; notes MUST target an existing actor or use case and MUST use ordered ids `note-N`. [just oracle]
- usecase-37: Class definitions MUST replace prior definitions of the same name; class assignments MUST append unique classes, and direct styles MUST append in source order; unresolved or anonymous class/style targets MUST be rejected. [just parity]
- usecase-38: Stereotypes MUST retain trimmed text; accessibility statements MUST set the title or description with later values winning; the last direction MUST win, `TD` MUST normalize to `TB`, and an absent direction MUST be `TB`. [just parity]
- usecase-39: Text MUST wrap at `usecase.wrapping_width` 120 px / 15 cells; ellipse width MUST be at least `usecase.min_node_width` 120 px / 15 cells; actor glyphs with captions MUST have no minimum width. [just parity]
- usecase-40: `usecase.node_spacing` 50 px, `usecase.rank_spacing` 50 px, and `usecase.diagram_padding` 20 px MUST replace layered `node_gap`, `rank_gap`, and `canvas_margin`; under the cell profile they MUST take those Layered keys' cell values, as specified in `spec/layout/layered.md`. [just parity]

## Diagnostics

- usecase-41: Every rejection MUST emit the error-severity code below; message placeholders MUST use source text, and model exceptions MUST become diagnostics instead of panics. [just oracle]

| Code | Message template | Trigger and span |
|---|---|---|
| `usecase/unexpected-token` | unexpected TOKEN, expected one of: LIST | invalid token in a known production; offending token |
| `usecase/unknown-statement` | unknown statement TOKEN | unsupported statement; first token through recovery boundary |
| `usecase/unterminated` | unterminated TOKEN | unfinished construct at EOF; opener through EOF |
| `usecase/declaration-conflict` | conflicting declaration of ID: REASON | kind, generated-id, label, shape, parent, stereotype, metadata conflict, or duplicate JSON/edge id; later declaration or property, with related earlier span |
| `usecase/invalid-metadata` | invalid metadata KEY for KIND ID | unsupported key or value; property key through value |
| `usecase/unresolved-target` | unresolved KIND target ID | metadata, note, parent, class, or style target missing, anonymous, or wrong kind; target token |
| `usecase/invalid-actor` | invalid actor ID: REASON | incompatible icon/type/business; actor declaration |
| `usecase/invalid-business-usecase` | rectangular use case ID cannot be business | business rectangle; declaration |
| `usecase/invalid-relationship` | invalid TYPE relationship: REASON | forbidden endpoint kinds or JSON marker; whole relation, with related offending declaration when available |
| `usecase/reference-class-suffix` | endpoint ID uses classes without a declaration | bare endpoint with class suffix; endpoint |
| `usecase/invalid-json` | invalid JSON object: REASON | invalid strict JSON; first offending token, or zero-width EOF |

- usecase-42: LIST MUST contain expected token-kind names sorted bytewise and joined by `, `; diagnostics MUST retain emission order after span and code sorting. [just parity]

## Upstream readings

- usecase-43: Implementations MUST use the decisions below where broad documentation differs from executable productions. [just oracle]

| Reading | Decision |
|---|---|
| Parser boundaryElement only admits declarations | Boundaries are not recursively nested and cannot contain relationships. |
| Metadata lookahead precedes entity statements | `A@{business:true}` updates A; it does not implicitly declare A. |
| Lexer arrays differ from definition order | The mode arrays determine precedence; identifier longer alternatives still apply. |
| `classStatement` has two adjacent identifier lists | The first whitespace-separated gap divides target ids from class ids; commas remain within each list. |
| Generic upstream thrown errors have no stable codes | The diagnostic table groups validation failures by their failed invariant; REASON states the specific conflict. |
| Upstream token offsets count JavaScript code units | This implementation converts all source locations to UTF-8 byte spans. |
| Config schema `UsecaseDiagramConfig:2956-3069` includes font and color controls | Only plan-read layout, look, and theme keys are honoured; remaining keys are accepted and ignored. |
- usecase-44: Go and Rust MUST resolve identical ordered model elements and relations under both metric profiles; syntax acceptance MUST NOT depend on profile. [just parity]
