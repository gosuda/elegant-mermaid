# Wardley grammar

This file fixes syntax, source spans, model resolution, and diagnostics for `wardley`.

## Scope

- wardley-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/wardley/wardley.langium:4-154`; imported terminals and metadata MUST follow `common/common.langium:6-34`. [just oracle]
- wardley-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/wardley/wardleyParser.ts:8-226`, `wardleyDb.ts:16-125`, and `wardleyBuilder.ts:92-207`, subject to the decisions below. [just oracle]
- wardley-03: Shared preprocessing and repaired-source byte positions MUST apply before parsing; configuration MUST use `config.schema.yaml:476-525,3101-3153`. [just parity]

## Header forms

- wardley-04: The header MUST be `wardley-beta`, matched with ASCII case folding and the keyword boundary of `spec/detection.md`; body keywords MUST remain case-sensitive. [just oracle]

## Lexer modes

- wardley-05: The lexer MUST use one default mode; the authority defines no named mode or mode transition. [just parity]

### Lexical rules in first-match order

- wardley-06: The lexer MUST apply local terminals before imported terminals, in the order below; punctuation literals MUST remain distinct tokens. [just parity]

| Order | Terminal | Recognition |
|---|---|---|
| local 109 | WARDLEY_NUMBER | unsigned digits, period, unsigned digits; integers do not match |
| local 111 | ARROW | `->` |
| local 112 | LINK_PORT | `+<>`, `+>`, `+<` |
| local 113 | LINK_ARROW | `-->`, `-.->`, `>`, or `+'text'` followed by `<>`, `<`, or `>`; text excludes single quote |
| local 114 | LINK_LABEL | semicolon followed by one or more non-line-end bytes |
| local 115 | STRATEGY | `build`, `buy`, `outsource`, `market` |
| local 118-131 | keyword terminals | `wardley-beta`, `size`, `evolution`, `anchor`, `component`, `label`, `inertia`, `evolve`, `pipeline`, `note`, `annotations`, `annotation`, `accelerator`, `deaccelerator`, in that order |
| local 143 | NAME_WITH_SPACES | ASCII letter followed by letters, digits, underscore, parentheses, ampersand, or hyphen not before `>`; additional space/tab-separated groups start with a letter or `(`; initial `title` plus whitespace, `accTitle`, and `accDescr` are excluded |
| local 154 | WS | hidden spaces and tabs |
| imported 12 | BOOLEAN | `true`, `false` |
| imported 14-16 | ACC_DESCR, ACC_TITLE, TITLE | shared accessibility and title tokens, in that order; description permits a brace body |
| imported 18-20 | FLOAT, INT, NUMBER | decimal; zero or nonzero-leading integer not before a period; their numeric union |
| imported 22 | STRING | single- or double-quoted text; backslash escapes the following character |
| imported 27 | ID | word character, then optional word/hyphen run ending in a word character |
| imported 29 | NEWLINE | physical line end under the shared CR/LF rule |
| imported 31-34 | WHITESPACE, YAML, DIRECTIVE, SINGLE_LINE_COMMENT | hidden horizontal whitespace and shared preprocessing constructs |

- wardley-07: STRING values MUST exclude their quote delimiters and decode escaped characters as the shared Langium string converter does; their spans MUST include both quotes. [just parity]
- wardley-08: Lexical keyword prefixes MUST follow the authority token priority rather than treating every unquoted phrase as one name; a quoted name MUST remain available when an unquoted name conflicts with a keyword. [just oracle]

## Grammar

- wardley-09: The parser MUST accept the following productions without backtracking over consumed tokens; `name` means STRING, ID, or NAME_WITH_SPACES and `EOL` means one or more physical line ends or EOF. [just parity]

```ebnf
Wardley = { NEWLINE }, KW_WARDLEY, { NEWLINE | TitleAndAccessibilities | Statement } ;
Statement = Size | Evolution | Anchor | Component | Link | Evolve | Pipeline
          | Note | Annotations | Annotation | Accelerator | Deaccelerator ;
Size = 'size', '[', INT, ',', INT, ']', EOL ;
Evolution = 'evolution', EvolutionStage, ARROW, EvolutionStage,
            { ARROW, EvolutionStage }, EOL ;
EvolutionStage = name, [ '@', WARDLEY_NUMBER ], [ '/', name ] ;
Anchor = 'anchor', name, '[', WARDLEY_NUMBER, ',', WARDLEY_NUMBER, ']', EOL ;
Component = 'component', name, '[', WARDLEY_NUMBER, ',', WARDLEY_NUMBER, ']',
            [ Label ], [ Decorator ], [ 'inertia' | '(', 'inertia', ')' ], EOL ;
Label = 'label', '[', [ '-' ], INT, ',', [ '-' ], INT, ']' ;
Decorator = '(', STRATEGY, ')' ;
Link = name, [ LINK_PORT ], [ LINK_ARROW | ARROW ], name, [ LINK_PORT ],
       [ LINK_LABEL ], EOL ;
Evolve = 'evolve', name, WARDLEY_NUMBER, EOL ;
Pipeline = 'pipeline', name, '{', NEWLINE, { NEWLINE },
           PipelineComponent, { PipelineComponent }, '}', EOL ;
PipelineComponent = 'component', name, '[', WARDLEY_NUMBER, ']', [ Label ], EOL ;
Note = 'note', STRING, '[', WARDLEY_NUMBER, ',', WARDLEY_NUMBER, ']', EOL ;
Annotations = 'annotations', '[', CoordinateValue, ',', CoordinateValue, ']', EOL ;
Annotation = 'annotation', INT, ',', '[', CoordinateValue, ',', CoordinateValue, ']', STRING, EOL ;
CoordinateValue = WARDLEY_NUMBER | INT ;
Accelerator = 'accelerator', name, '[', WARDLEY_NUMBER, ',', WARDLEY_NUMBER, ']', EOL ;
Deaccelerator = 'deaccelerator', name, '[', WARDLEY_NUMBER, ',', WARDLEY_NUMBER, ']', EOL ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE), EOL,
                         { (ACC_DESCR | ACC_TITLE | TITLE), EOL } ;
```

- wardley-10: Coordinates that require WARDLEY_NUMBER MUST reject an integer spelling; only CoordinateValue MUST accept both spellings. [just oracle]
- wardley-11: Pipeline bodies MUST contain at least one PipelineComponent and MUST NOT admit nested pipelines, notes, or general statements. [just oracle]

## Statement boundary

- wardley-12: Recovery MUST stop at the next physical line end outside STRING or an accessibility brace body, or before the enclosing pipeline close. [just go-check]
- wardley-13: A semicolon MUST start LINK_LABEL rather than terminate a statement; a pipeline opener MUST be followed by at least one line end. [just oracle]
- wardley-14: Unknown statements MUST produce no model element; EOF inside a string, bracket, decorator, pipeline, or accessibility brace body MUST produce the unterminated diagnostic. [just go-check]

## Abstract syntax tree

- wardley-15: AST node names MUST use upstream production names in PascalCase; each node span MUST cover its first through last token and MUST exclude its trailing EOL. [just parity]

| Node | Fields and span |
|---|---|
| Wardley | header, metadata, optional size/evolution, ordered lists of each statement family; complete document span |
| Size | width, height; keyword through closing bracket |
| Evolution | stages; keyword through final stage |
| EvolutionStage | name, optional boundary and secondName; first through final stage token |
| Anchor | name, visibility, evolution; complete statement |
| Component | name, visibility, evolution, optional label/decorator/inertia; complete statement |
| Label | signed offsetX and offsetY; label keyword through closing bracket |
| Decorator | strategy; both parentheses included |
| Link | from, fromPort, arrow, to, toPort, linkLabel; complete statement |
| Evolve | component, target; complete statement |
| Pipeline | parent, components; keyword through closing brace |
| PipelineComponent | name, evolution, optional label; complete statement |
| Note | text, visibility, evolution; complete statement |
| Annotations | x, y; complete statement |
| Annotation | number, x, y, text; complete statement |
| Accelerator, Deaccelerator | name, x, y; complete statement |

- wardley-16: Statement and TitleAndAccessibilities MUST remain fragments, and CoordinateValue MUST remain a scalar rule rather than create synthetic AST nodes; tokens MUST borrow source text and retain individual value spans. [just parity]

## Semantic resolution

- wardley-17: Repeated Size and Evolution MUST keep the last value; metadata MUST use the shared title and accessibility resolver. [just parity]
- wardley-18: Resolution MUST process anchors, components, notes, pipelines, links, evolves, annotation-box declarations, annotations, accelerators, and deaccelerators in that order, preserving declaration order within each family as upstream does. [just oracle]
- wardley-19: Coordinate normalization MUST multiply values at most 1 by 100 and leave larger values unchanged; it MUST reject a normalized value outside 0 through 100 before layout. [just oracle]
- wardley-20: Numeric values MUST use checked integer thousandths and round fractional excess digits half away from zero; the model MUST store x as normalized evolution and y as normalized visibility. [just parity]
- wardley-21: The adapter MUST clamp stored component coordinates to 0 through 100000 thousandths before projection; plot dimensions, padding, label placement, and centre-to-centre links MUST follow `spec/layout/charts.md`, not upstream floating-point geometry. [just lean-parity]
- wardley-22: Anchor and component ids MUST be their resolved names; a later declaration MUST replace the same id without moving its first insertion position and MUST keep an earlier class or label offset when the later value is absent. [just oracle]
- wardley-23: Components MUST retain signed label offsets, inertia, and source strategy; evolution stages MUST trim names and join a dual name with ` / `, and MUST retain only explicitly supplied boundaries in order. [just parity]
- wardley-24: A pipeline parent MUST name an existing node with coordinates after all top-level anchors and components resolve; each child MUST use id `PARENT_CHILD`, its own normalized evolution, and the parent's visibility. [just oracle]
- wardley-25: A pipeline MUST mark its parent and children; a repeated pipeline for the same parent MUST replace its membership list, while already inserted child nodes remain in their first insertion positions. [just oracle]
- wardley-26: Link endpoints MUST resolve by exact id first, then by the first matching node label, and otherwise remain unresolved names; missing endpoints MUST NOT become implicit nodes or parser errors. [just oracle]
- wardley-27: Links MUST retain declaration order; flow MUST take the source port first, then target port, then a flow arrow; `+>` means forward, `+<` backward, and `+<>` bidirectional. [just parity]
- wardley-28: A quoted flow-arrow label MUST override a semicolon label, including an empty quoted label; the semicolon label MUST retain its terminal text; `-.->` MUST mark a dashed link. [just oracle]
- wardley-29: Evolve MUST create or replace a trend only when its target component exists with visibility; an unknown target MUST have no effect and MUST NOT validate its unused numeric target. [just oracle]
- wardley-30: Only the first Annotations statement MUST set the annotation-box position; annotations, notes, accelerators, and deaccelerators MUST append without deduplication. [just oracle]
- wardley-31: Annotation and accelerator coordinate pairs MUST follow upstream's toCoordinates argument order: the first value supplies visibility and the second evolution, despite their AST field names x and y. [just oracle]
- wardley-32: The kind configuration registry MUST honour width, height, padding, theme, and look; other schema keys MUST be accepted and ignored because the plan does not read them. [just gen-check]

## Diagnostics

- wardley-33: Parser and model failures MUST use the following registry; a named failure MUST replace the generic unterminated code when both describe the same failure. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `wardley/unexpected-token` | error | token fits no current production | offending token | `unexpected TOKEN, expected one of: LIST` |
| `wardley/unknown-statement` | error | first token starts no statement | first token through recovery boundary, excluding line end | `unknown statement TOKEN` |
| `wardley/unterminated` | error | EOF inside an open delimiter | opening delimiter through EOF | `unterminated TOKEN` |
| `wardley/coordinate-out-of-range` | error | used coordinate normalizes outside 0 through 100 | numeric literal | `CONTEXT must be between 0-1 (decimal) or 0-100 (percentage). Received: VALUE` |
| `wardley/pipeline-parent-unknown` | error | pipeline parent is absent or has no visibility | parent name token | `Pipeline "NAME" must reference an existing component with coordinates.` |
| `wardley/missing-coordinates` | error | resolved node lacks either coordinate | originating declaration name | `Node "NAME" is missing coordinates` |

- wardley-34: TOKEN MUST be source text and LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `; diagnostic help MUST be empty and fixes MUST be absent. [just parity]
- wardley-35: Duplicate names, unresolved links, missing evolve targets, and unvalidated stage boundaries MUST NOT become extra syntax errors. [just oracle]

## Upstream readings

| Reading | Authority fact | Decision |
|---|---|---|
| Header case | detector folds case but the local header terminal is lowercase | accept folded header by the shared detection contract; keep body keyword case |
| Decimal-only coordinates | most productions use WARDLEY_NUMBER, not CoordinateValue | retain the restriction, including size's separate integer syntax |
| Coordinate range versus clamp | parser throws for out-of-range used coordinates; plan clamps projected coordinates | keep parser rejection, then apply plan clamp at the model-to-layout boundary |
| Declaration order | parser populates one AST collection at a time | retain upstream phase order and deterministic first insertion order within nodes |
| Unresolved references | links retain names; unknown evolve targets are skipped | do not invent unknown-node errors |
| Missing-coordinate exception | builder checks it, although ordinary declarations supply both values | retain the named defensive model diagnostic without rejecting valid statements |
| Config namespace | schema and database use `wardley-beta` | map that upstream block to registry kind `wardley` |

- wardley-36: Go and Rust MUST resolve identical ordered model elements under both metric profiles; no renderer-only check MUST silently extend parser rejection. [just parity]
