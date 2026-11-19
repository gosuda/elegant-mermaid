# Mindmap grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `mindmap` kind.

## Scope

- mindmap-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/mindmap/parser/mindmap.jison`, with `mindmapDb.ts` for semantic resolution. [just oracle]
- mindmap-02: The parser MUST accept node statements, icon decorations, class decorations, blank statements, and comment lines; it MUST NOT interpret edges, subgraphs, or semicolons as separate statements. [just oracle]
- mindmap-03: Shared preprocessing MUST run before this grammar without changing source offsets. [just parity]

## Header forms

- mindmap-04: Detection MUST match `mindmap` case-sensitively with the shared keyword boundary; after detection, the lexer MUST apply the authority's case-insensitive option. [just oracle]
- mindmap-05: The header MUST precede a non-empty document; a document MAY contain only a blank statement. [just oracle]

## Lexer modes

- mindmap-06: The lexer MUST declare the exclusive modes below and MUST restore the previous mode when it pops. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| INITIAL | Start | A mode opener |
| NODE | A shape opener | A shape closer |
| NSTR | `"` in NODE | `"` |
| NSTR2 | `"` followed by a backtick in NODE | A backtick followed by `"` |
| ICON | `::icon(` | `)` |
| CLASS | `:::` | Non-empty line content or LF |

### Lexical rules in first-match order

Order is the authority line number. Unqualified rules apply only in INITIAL. Each row is one rule. `push` saves the current mode. The comment rows in the authority are not active rules.

- mindmap-07: Within each mode, the lexer MUST apply this source order and MUST NOT prefer a longer match from a later rule. [just parity]

| Order | Pattern and modes | Action |
|---|---|---|
| 21 | INITIAL `\s*%%.*` | Emit SPACELINE |
| 23 | INITIAL `mindmap`, case-insensitive | Emit MINDMAP |
| 24 | INITIAL `:::` | Push CLASS; emit nothing |
| 25 | CLASS `.+` | Pop; emit CLASS |
| 26 | CLASS LF | Pop; emit nothing |
| 28 | INITIAL `::icon(`, case-insensitive | Push ICON; emit nothing |
| 29 | INITIAL `[\s]+[\n]` | Emit SPACELINE |
| 30 | INITIAL `[\n]+` | Emit NL |
| 31 | ICON one or more characters other than `)` | Emit ICON |
| 32 | ICON `)` | Pop; emit nothing |
| 33 | INITIAL `-)` | Push NODE; emit NODE_DSTART |
| 34 | INITIAL `(-` | Push NODE; emit NODE_DSTART |
| 35 | INITIAL `))` | Push NODE; emit NODE_DSTART |
| 36 | INITIAL `)` | Push NODE; emit NODE_DSTART |
| 37 | INITIAL `((` | Push NODE; emit NODE_DSTART |
| 38 | INITIAL `{{` | Push NODE; emit NODE_DSTART |
| 39 | INITIAL `(` | Push NODE; emit NODE_DSTART |
| 40 | INITIAL `[` | Push NODE; emit NODE_DSTART |
| 41 | INITIAL one or more `\s` characters | Emit SPACELIST |
| 43 | INITIAL one or more characters outside `(`, `[`, LF, `)`, `{`, `}` | Emit NODE_ID |
| 44 | INITIAL end of input | Emit EOF |
| 45 | NODE `"` then backtick | Push NSTR2; emit nothing |
| 46 | NSTR2 one or more characters other than backtick and `"` | Emit NODE_DESCR |
| 47 | NSTR2 backtick then `"` | Pop; emit nothing |
| 48 | NODE `"` | Push NSTR; emit nothing |
| 49 | NSTR one or more characters other than `"` | Emit NODE_DESCR |
| 50 | NSTR `"` | Pop; emit nothing |
| 51 | NODE `))` | Pop; emit NODE_DEND |
| 52 | NODE `)` | Pop; emit NODE_DEND |
| 53 | NODE `]` | Pop; emit NODE_DEND |
| 54 | NODE `}}` | Pop; emit NODE_DEND |
| 55 | NODE `(-` | Pop; emit NODE_DEND |
| 56 | NODE `-)` | Pop; emit NODE_DEND |
| 57 | NODE `((` | Pop; emit NODE_DEND |
| 58 | NODE `(` | Pop; emit NODE_DEND |
| 59 | NODE one or more characters outside `)`, `]`, `(`, `}` | Emit NODE_DESCR |
| 60 | NODE `.+(?!\(\()` | Emit NODE_DESCR |

- mindmap-08: Token values MUST exclude mode delimiters that emit no token; token spans MUST retain those delimiters through their enclosing AST node. [just parity]
- mindmap-09: The scanner MUST retain NODE_ID whitespace after its first non-whitespace character; it MUST NOT split that token at embedded spaces, colons, or a semicolon. [just oracle]
- mindmap-10: Quoted and Markdown descriptions MUST use the lexical exclusions above, without backslash escapes; an empty quoted description MUST NOT invent a NODE_DESCR token. [just oracle]
- mindmap-11: Description and ICON content MAY include line ends where their lexical rules permit them; CLASS content MUST end before a line end. [just oracle]

## Grammar

- mindmap-12: The parser MUST use the following EBNF with the terminal meanings above; production names MUST retain the authority names. [just parity]

```ebnf
start = mindMap | spaceLines, mindMap ;
spaceLines = SPACELINE, { SPACELINE | NL } ;
mindMap = MINDMAP, [ NL ], document ;
stop = ( NL | EOF | SPACELINE ), { NL | EOF } ;
document = statement, stop, { statement, stop } ;
statement = SPACELIST, node
          | SPACELIST, ICON
          | SPACELIST, CLASS
          | SPACELINE
          | node | ICON | CLASS | SPACELIST ;
node = nodeWithId | nodeWithoutId ;
nodeWithoutId = NODE_DSTART, NODE_DESCR, NODE_DEND ;
nodeWithId = NODE_ID
           | NODE_ID, NODE_DSTART, NODE_DESCR, NODE_DEND ;
```

- mindmap-13: Shape delimiters MUST follow lexical acceptance, not a balanced-pair grammar; resolution MUST select a shape with the table below. [just oracle]
- mindmap-14: A decoration MUST be a statement of its own; inline `:::class` or `::icon(...)` inside a NODE_ID token MUST remain node text. [just oracle]

## Statement boundary

- mindmap-15: Recovery MUST stop after the next physical line end outside NODE, NSTR, NSTR2, and ICON, or at end of input. [just go-check]
- mindmap-16: A malformed statement MUST NOT create a model node; recovery MUST reset the lexer to INITIAL at the boundary. [just parity]
- mindmap-17: End of input inside a shape, quoted description, Markdown description, or icon MUST produce the unterminated diagnostic, with the opening delimiter through end of input as its span. [just parity]
- mindmap-18: A blank CLASS line MUST produce no decoration; a non-empty CLASS token without a preceding node MUST use the decoration-target diagnostic. [just oracle]

## Abstract syntax tree

- mindmap-19: AST nodes MUST take authority production names in PascalCase and MUST use these fields and spans. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | Leading SpaceLines, MindMap | First source token through document end |
| SpaceLines | Blank and comment tokens | First through last included separator |
| MindMap | Header, Document | Header through document end |
| Document | Ordered Statement and Stop pairs | First statement through final stop |
| Statement | Indentation, Node or decoration or blank token | First indentation byte through final content token; exclude stop |
| Stop | Separator tokens | All consumed separator bytes; EOF is zero-width |
| Node | NodeWithId or NodeWithoutId | Selected child's span |
| NodeWithId | Id, optional opening delimiter, description, closing delimiter, description kind | Id start through final delimiter, or id end |
| NodeWithoutId | Opening delimiter, description, closing delimiter, description kind | Opening delimiter through closing delimiter |

- mindmap-20: Tokens MUST borrow source text; shape, description, decoration, indentation, and id spans MUST remain available to diagnostics. [just parity]
- mindmap-21: A decoration MUST remain a Statement variant rather than an invented grammar production; its span MUST include `:::` or `::icon(` and the icon's closing `)`. [just parity]

## Semantic resolution

- mindmap-22: Resolution MUST visit statements in declaration order and MUST keep an ordered list of successfully inserted nodes. [just parity]
- mindmap-23: A node's raw indentation MUST equal the length of its leading SPACELIST token; each space and each tab MUST count as one, without tab-stop expansion. [just oracle]
- mindmap-24: The first inserted node MUST set the base indentation and MUST have normalized level zero; each later node MUST have level `raw indentation - base indentation`. [just oracle]
- mindmap-25: A later node MUST take the most recently inserted node whose normalized level is strictly smaller as its parent; equal levels MUST be skipped and indentation jumps MUST be accepted. [just oracle]
- mindmap-26: A later node with no such parent MUST raise the second-root diagnostic and MUST NOT enter the ordered list. [just oracle]
- mindmap-27: A bare NODE_ID MUST supply both the source id and the description; a shaped node with an id MUST use NODE_ID for its source id and NODE_DESCR for its description; a shaped node without an id MUST use NODE_DESCR for both. [just parity]
- mindmap-28: Each insertion MUST receive a distinct declaration index even when its source id repeats; repeated source ids MUST NOT merge nodes or produce a duplicate-id error. [just oracle]
- mindmap-29: Shape resolution MUST use the opener and closer below; an unlisted opener MUST give the default shape. [just parity]

| Opener | Closer condition | Shape |
|---|---|---|
| `[` | Any accepted NODE_DEND | Square |
| `(` | `)` | Rounded |
| `(` | Any other accepted NODE_DEND | Cloud |
| `((` | Any accepted NODE_DEND | Circle |
| `)` | Any accepted NODE_DEND | Cloud |
| `))` | Any accepted NODE_DEND | Bang |
| `{{` | Any accepted NODE_DEND | Hexagon |
| `(-`, `-)`, or no opener | Any accepted closer, or none for a bare id | Default |

- mindmap-30: A description enclosed by double quote and backtick delimiters MUST retain Markdown-string status for the shared styled-run reader; ordinary quoted and unquoted descriptions MUST retain their own source spans. [just parity]
- mindmap-31: Model labels MUST use the shared text and entity rules instead of copying upstream HTML sanitization; source ids and descriptions MUST remain separate model fields. [just parity]
- mindmap-32: An ICON or CLASS statement MUST decorate the last successfully inserted node, regardless of the decoration line's indentation; a later non-empty decoration of the same kind MUST replace the earlier value. [just oracle]
- mindmap-33: Icon and class values MUST retain the content returned by their lexer mode; class content MUST NOT become additional nodes or change the current parent. [just parity]
- mindmap-34: Children of the root MUST alternate sides in declaration order: child index i MUST go right when i is even and left when i is odd; each deeper node MUST inherit its root child's side. [just lean-parity]
- mindmap-35: A missing root caused by blank statements alone MUST yield an empty mindmap model, not an invented node. [just oracle]

## Diagnostics

- mindmap-36: Syntax rejection and failed database checks MUST use exactly the rows below; they MUST NOT panic. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `mindmap/unexpected-token` | error | Parser | A token does not fit the current production | Offending token | `unexpected TOKEN, expected one of: LIST` |
| `mindmap/unknown-statement` | error | Parser | No statement form accepts the statement | First token through the recovery boundary, excluding its separator | `unknown statement TOKEN` |
| `mindmap/unterminated` | error | Lexer or parser | Input ends inside a required delimiter | Opening delimiter through end of input | `unterminated TOKEN` |
| `mindmap/second-root` | error | Model | A later node has no preceding lower-level parent | Rejected node, excluding indentation | `node DESCRIPTION has no parent; only one root is allowed` |
| `mindmap/decoration-target-missing` | error | Model | A non-empty decoration precedes every node | Complete decoration | `decoration has no preceding node` |

- mindmap-37: TOKEN MUST be source token text; LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; DESCRIPTION MUST be the rejected node's resolved description. [just parity]
- mindmap-38: Each diagnostic MUST have empty help and no fix; a delimiter failure MUST emit unterminated instead of an additional unexpected-token diagnostic at EOF. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| `mindmap.jison:21-60` | Exclusive modes have unusual overlapping rules | Preserve source precedence, including permissive shape closers |
| `mindmap.jison:100-107` | Indentation passes token length; decorations ignore it | Count tabs as one and attach decorations to the last insertion |
| `mindmapDb.ts:61-85,111-123` | Parent lookup scans backward for a strictly lower level | Normalize against the first node, not a fixed indentation step |
| `mindmapDb.ts:126-143` | Shape mapping is opener-led and accepts mismatched pairs | Keep that mapping; `(-` and `-)` give default |
| `mindmapDb.ts:153-165` | Decoration before a node accesses an absent value | Report decoration-target-missing rather than exposing a runtime exception |
| `mindmap.jison:45-50,117-125` | Markdown quotes are lexed but their status is lost by database arguments | Preserve the status in the AST for the shared label reader |
| `mindmapDb.ts:99-109` | Source ids are distinct from generated numeric insertion ids | Retain repeated source ids as separate nodes |

- mindmap-39: The parser MUST retain permissive authority behavior even when conventional mindmap examples use stricter delimiter pairs; it MUST NOT add an indentation-step or matching-delimiter check. [just oracle]
- mindmap-40: Go and Rust MUST produce the same ordered tree, labels, shapes, and decorations under both metric profiles. [just parity]
