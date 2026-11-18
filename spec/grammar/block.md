# Block grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `block` kind.

## Scope

- block-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/block/parser/block.jison`, with `blockDB.ts` for resolution. [just oracle]
- block-02: The parser MUST accept node declarations, column settings, spaces, composites, block arrows, edge chains, class definitions, class applications, and direct styles. [just oracle]
- block-03: Geometry MUST follow `spec/layout/grid.md`; this grammar MUST NOT choose coordinates. [just parity]

## Header forms

- block-04: The first header MUST be `block-beta` or `block`, case-sensitive, with the boundary in `spec/detection.md`. [just oracle]
- block-05: A later `block` or `block-beta` token MUST open an anonymous composite; `block:` MUST open a named composite. [just oracle]

## Lexer modes

- block-06: The lexer MUST declare the exclusive modes below with their exact authority names. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| INITIAL | source start | end of source |
| acc_title | accTitle colon | value token |
| acc_descr | accDescr colon | value token |
| acc_descr_multiline | accDescr opening brace | closing brace |
| string | double quote | double quote |
| space | no active rule | unreachable |
| md_string | double quote then backtick | backtick then double quote |
| NODE | shape opener | shape closer |
| BLOCK_ARROW | `<[` | direction-list close through ARROW_DIR |
| ARROW_DIR | `]>` and opening parenthesis | closing parenthesis |
| LLABEL | incomplete edge prefix | closing edge token |
| CLASS | class keyword and whitespace | id-list token |
| CLASS_STYLE | CLASS id list | remainder of line |
| CLASSDEF | classDef keyword and whitespace | class-id token |
| CLASSDEFID | CLASSDEF id | remainder of line |
| STYLE_STMNT | style keyword and whitespace | id-list token |
| STYLE_DEFINITION | STYLE_STMNT id list | remainder of line |

### Lexical rules in first-match order

Order is the authority line number. Unqualified rules apply only in INITIAL. Quoted patterns denote literal bytes. A push saves the current mode. A pop restores it. Repeated and shadowed rules remain in the table.

- block-07: Within each mode, the lexer MUST take the first matching rule below, not a longer match from a later rule. [just parity]

| Order | Pattern and modes | Action |
|---|---|---|
| 39–41 | `block-beta`; `block:`; `block` | BLOCK_DIAGRAM_KEY; id-block; BLOCK_DIAGRAM_KEY |
| 44–47 | whitespace run; LF run; INITIAL CRLF or LF | skip; skip; NL (shadowed) |
| 48–49 | `columns` whitespace `auto`; `columns` whitespace decimal digits | COLUMNS with value -1 or digit text |
| 50–52 | INITIAL quote-backtick; md_string bytes other than backtick or quote; md_string backtick-quote | push md_string; MD_STR; pop |
| 53–55 | INITIAL quote; string quote; string zero or more non-quote bytes | push string; pop; STR |
| 56–60 | `space:` digits; `space`; `default`; `linkStyle`; `interpolate` | SPACE_BLOCK with digit text; SPACE_BLOCK with 1; DEFAULT; LINKSTYLE; INTERPOLATE |
| 62–65 | `classDef` whitespace; CLASSDEF `DEFAULT` whitespace; CLASSDEF word characters then whitespace; CLASSDEFID non-LF remainder | push CLASSDEF and emit classDef; switch to CLASSDEFID and emit DEFAULT_CLASSDEF_ID or CLASSDEF_ID; pop and emit CLASSDEF_STYLEOPTS |
| 67–69 | `class` whitespace; CLASS word-character ids separated by comma and optional whitespace; CLASS_STYLE non-LF remainder | push CLASS and emit class; switch to CLASS_STYLE and emit CLASSENTITY_IDS; pop and emit STYLECLASS |
| 71–73 | `style` whitespace; STYLE_STMNT same id-list pattern; STYLE_DEFINITION non-LF remainder | push STYLE_STMNT and emit style; switch to STYLE_DEFINITION and emit STYLE_ENTITY_IDS; pop and emit STYLE_DEFINITION_DATA |
| 75–81 | accTitle whitespace colon whitespace; acc_title non-LF remainder; accDescr whitespace colon whitespace; acc_descr non-LF remainder; accDescr whitespace opening brace whitespace; acc_descr_multiline close brace; acc_descr_multiline non-close-brace run | push and emit acc_title; pop and emit acc_title_value; push and emit acc_descr; pop and emit acc_descr_value; push multiline; pop; acc_descr_multiline_value |
| 82 | `end` word boundary and optional whitespace | end |
| 85–101 | NODE closers in order: `(((`, `)))`, `))`, `}}`, `}`, `(-`, `-)`, `((`, `]]`, `(`, `])`, `\]`, `/]`, `)]`, `)`, `]>`, `]` | pop and emit NODE_DEND |
| 104–122 | INITIAL openers in order: `-)`, `(-`, `))`, `)`, `(((`, `((`, `{{`, `{`, `>`, `([`, `(`, `[[`, `[|`, `[(`, `)))`, `[\`, `[/`, `[\`, `[` | push NODE and emit NODE_DSTART |
| 124 | `<[` | push BLOCK_ARROW and emit BLOCK_ARROW_START |
| 126 | nonempty run excluding parentheses, brackets, LF, hyphen, braces, whitespace, angle brackets, colon, equals | NODE_ID |
| 127 | end of source | EOF |
| 130–137 | BLOCK_ARROW quote-backtick; NODE quote-backtick; md_string non-backtick/non-quote run; md_string backtick-quote; NODE quote; BLOCK_ARROW quote; string non-quote run; string quote | push md_string; push md_string; NODE_DESCR (shadowed by 51); pop; push string; push string; NODE_DESCR (shadowed by 55); pop |
| 139 | BLOCK_ARROW `]>` optional whitespace `(` | push ARROW_DIR |
| 140–146 | ARROW_DIR optional comma and whitespace followed by `right`, `left`, `x`, `y`, `up`, `down`, each with optional whitespace; then `)` optional whitespace | DIR without comma/outer whitespace; pop twice and emit BLOCK_ARROW_END |
| 149–152 | optional whitespace, optional x/o/<, at least two hyphens then -/x/o/>; same with equals; optional x/o/< then optional hyphen then dots then hyphen then optional x/o/>; at least three tildes | LINK; each pattern permits surrounding whitespace |
| 153–155 | optional whitespace and optional x/o/< followed by `--`, `==`, or `-.`, with optional whitespace | push LLABEL and emit START_LINK |
| 156–157 | LLABEL quote-backtick; LLABEL quote | push md_string; push string and emit LINK_LABEL |
| 158–160 | LLABEL solid, thick, dotted complete-link patterns of 149–151 | pop and emit LINK |
| 161 | colon and decimal digits | SIZE with digits only |

- block-08: Shared preprocessing MUST remove comments and directives without changing source spans; physical line endings MUST follow `spec/preprocessing.md`. [just parity]
- block-09: STR MUST retain all interior bytes, including line endings; quotes MUST NOT be part of its value. [just parity]
- block-10: The reserved but unconsumed tokens MD_STR, NODE_DESCR, DEFAULT_CLASSDEF_ID, LINKSTYLE, INTERPOLATE, and accessibility tokens MUST NOT create extra statement forms. [just oracle]

## Grammar

- block-11: The parser MUST use this EBNF; production names MUST retain the authority names. [just parity]

```ebnf
start = BLOCK_DIAGRAM_KEY, document, EOF ;
document = statement, { statement } ;
statement = nodeStatement | columnsStatement | SPACE_BLOCK | blockStatement
          | classDefStatement | cssClassStatement | styleStatement ;
nodeStatement = node, [ SIZE ], { link, node } ;
link = LINK | START_LINK, LINK_LABEL, STR, LINK ;
columnsStatement = COLUMNS ;
blockStatement = "id-block", nodeStatement, document, "end"
               | BLOCK_DIAGRAM_KEY, document, "end" ;
node = NODE_ID, [ nodeShapeNLabel ] ;
nodeShapeNLabel = NODE_DSTART, STR, NODE_DEND
                | BLOCK_ARROW_START, STR, dirList, BLOCK_ARROW_END ;
dirList = DIR, { DIR } ;
classDefStatement = "classDef", (CLASSDEF_ID | DEFAULT), CLASSDEF_STYLEOPTS ;
cssClassStatement = "class", CLASSENTITY_IDS, STYLECLASS ;
styleStatement = "style", STYLE_ENTITY_IDS, STYLE_DEFINITION_DATA ;
```

- block-12: A SIZE MUST occur only on the initial node of a nodeStatement; a target with SIZE MUST start another statement rather than extend that edge chain. [just oracle]
- block-13: Shape and arrow labels MUST be double-quoted STR values; a STR token MUST hold at least one character, so an empty quoted label MUST raise block/unexpected-token. [just oracle]
- block-14: A composite body and the root document MUST each contain at least one statement. [just oracle]
- block-15: The unused authority productions `spaceLines`, `separator`, and `stop` MUST NOT add separators to document. [just oracle]

## Statement boundary

- block-16: Successful statements MUST end when their production is complete; whitespace MUST permit several statements on one physical line. [just oracle]
- block-17: Error recovery MUST skip to the next physical line end outside quoted text, or stop before the enclosing composite's `end`. [just go-check]
- block-18: Recovery MUST preserve the enclosing `end` for its blockStatement and MUST NOT create a node from skipped text. [just go-check]
- block-19: End of source inside a quote, shape, direction list, or composite MUST produce the unterminated diagnostic with the opening-token-to-source-end span. [just go-check]

## Abstract syntax tree

- block-20: AST nodes MUST use the authority production names in PascalCase and MUST carry half-open byte spans from first token through last token. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | header, Document | header through last statement; exclude EOF |
| Document | ordered Statement list | first through last child |
| Statement | selected production or space count/token | selected child's span |
| NodeStatement | initial Node, optional size, ordered Link/Node pairs | first node through last size or target |
| Link | source spelling, label, endpoint-marker and line data | first prefix through closing LINK |
| ColumnsStatement | integer or auto | entire COLUMNS token |
| BlockStatement | optional identifying NodeStatement, Document | block keyword through end keyword |
| Node | id, optional NodeShapeNLabel | id through optional shape close |
| NodeShapeNLabel | opener, STR, closer, optional DirList | opener through closer, including arrow directions |
| DirList | ordered direction tokens | first through last DIR |
| ClassDefStatement | class id, style text | keyword through style remainder |
| CssClassStatement | target ids, class text | keyword through class remainder |
| StyleStatement | target ids, style text | keyword through style remainder |

- block-21: Tokens MUST borrow source bytes; the model MUST retain id, width, columns, label, and style-target spans. [just parity]
- block-22: A trailing line ending or whitespace consumed by a keyword MUST NOT extend its semantic id or delimiter span. [just parity]

## Semantic resolution

- block-23: Resolution MUST visit statements in declaration order and MUST retain first insertion order for model nodes, groups, and edges. [just parity]
- block-24: Each composite MUST hold its own columns value; absent columns and `columns auto` MUST resolve to -1. [just parity]
- block-25: Each columnsStatement MUST replace the enclosing composite's columns setting; the last setting MUST win. [just oracle]
- block-26: Decimal column counts and width spans MUST retain zero as accepted syntax; no positivity error MUST be invented. [just oracle]
- block-27: A node without SIZE MUST have widthInColumns 1; an explicit SIZE MUST set that value from its decimal digits. [just parity]
- block-28: Shape delimiter pairs MUST resolve by the following table; every other lexically accepted pair MUST resolve to `na`, not a new shape. [just oracle]

| Pair | Model type |
|---|---|
| `[]` | square |
| `()` | round |
| `(())` | circle |
| `>]` | rect_left_inv_arrow |
| `{}` | diamond |
| `{{}}` | hexagon |
| `([])` | stadium |
| `[[]]` | subroutine |
| `[()]` | cylinder |
| `((()))` | doublecircle |
| `[//]` | lean_right |
| `[\\]` | lean_left |
| `[/\]` | trapezoid |
| `[\/]` | inv_trapezoid |
| `<[]>` | block_arrow |

- block-29: A plain id MUST resolve to type `na`; its absent or empty label MUST resolve to the id. [just oracle]
- block-30: A later declaration of an existing id MUST update its type when the new type is not `na` and MUST update its label when the new label differs from the id; it MUST NOT add another child position. [just oracle]
- block-31: A composite MUST use its explicit id when present and MUST keep an empty default label; its children MUST resolve recursively. [just parity]
- block-32: Anonymous composites and spaces MUST receive deterministic generated ids in declaration order; generation MUST avoid explicit ids and MUST NOT use upstream randomness. [just parity]
- block-33: `space` MUST contribute one empty slot; `space:N` MUST contribute N empty slots in declaration order, and zero MUST contribute none. [just oracle]
- block-34: Block arrows MUST retain the direction list in source order; directions MUST be `right`, `left`, `x`, `y`, `up`, or `down`; repeated directions MUST remain accepted. [just oracle]
- block-35: Each adjacent pair in an edge chain MUST create one edge with the optional link label; repeated edges MUST remain distinct in declaration order. [just parity]
- block-36: Edge markers MUST use the first and last non-whitespace characters: x means cross, o means circle, and the respective angle bracket means point; an absent start marker MUST resolve to open and an absent end marker MUST resolve to none. [just parity]
- block-37: An edge spelling containing `==` MUST be thick; a spelling containing `.-` MUST be dotted; every other edge MUST be normal and solid. [just parity]
- block-38: Tilde links MUST remain accepted as links; this grammar MUST NOT infer invisibility from a helper that the block database does not call. [just oracle]
- block-39: A classDef MUST append comma-separated trimmed attributes to the named class; text attributes containing `color` MUST also receive the database's text-paint conversion. [just oracle]
- block-40: A class application MUST append its trimmed class text to each comma-separated target; an unknown target MUST create an `na` lookup entry without a child position. [just oracle]
- block-41: A direct style MUST replace the target's styles with comma-separated attributes; a nonempty style for an unknown target MUST raise style-target-unknown. [just oracle]
- block-42: A direct-style id list MUST be looked up as one trimmed database key, not split; an empty style remainder MUST have no effect. [just oracle]
- block-43: A width larger than the first columns setting in its scope MUST raise width-exceeds-columns as a warning when that setting is positive; later column settings MUST NOT change that check's reference value. [just oracle]
- block-44: Labels MUST use the shared label-resolution rules; style text MUST NOT undergo label entity decoding. [just parity]

## Diagnostics

- block-45: Rejected syntax and enforced database checks MUST use exactly the following rows. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| block/unexpected-token | error | parser | token cannot continue a known production | offending token | unexpected TOKEN, expected one of: LIST |
| block/unknown-statement | error | parser | no statement production accepts the first token | first token through recovery boundary, excluding boundary | unknown statement TOKEN |
| block/unterminated | error | parser | EOF inside an open construct | opening delimiter or block keyword through EOF | unterminated TOKEN |
| block/style-target-unknown | error | model | nonempty direct style names no existing key | complete target-id token | style references unknown block ID |
| block/width-exceeds-columns | warning | model | width exceeds the first scope column setting and that setting is positive | SIZE token | block ID width WIDTH exceeds configured column width COLUMNS |

- block-46: TOKEN MUST be source text; LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `. [just parity]
- block-47: A syntax failure MUST produce only the most specific applicable row; invalid direction names and missing required values MUST use unexpected-token. [just parity]
- block-48: Shared depth and source-limit diagnostics MUST remain owned by the shared registry and MUST NOT acquire block-prefixed aliases. [just gen-check]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| block.jison:44–47 | whitespace consumes newlines before NL | statement completion, not newline, separates valid statements |
| block.jison:51,132 | MD_STR wins over later NODE_DESCR; neither is a shape-label production | backtick labels remain rejected rather than silently converted to STR |
| block.jison:63,275 | lexer returns DEFAULT_CLASSDEF_ID but parser expects DEFAULT | no special default-class production is added |
| block.jison:222–236 | recursive edge action reads an array as a node on longer chains | intended adjacent-pair chain is preserved; undefined-id artifacts are not modeled |
| block.jison:245 | named composite accepts a NodeStatement, not only an id | header syntax remains NodeStatement; its initial node identifies the composite |
| blockDB.ts:108–140 | first columns setting controls warning; last controls stored columns | both orders remain explicit |
| blockDB.ts:155–188 | duplicate id updates type/label but not child placement | first placement wins |
| blockDB.ts:61–65 | direct style dereferences a possibly absent key | typed model error replaces exception |
| blockDB.ts:211–247 | unmatched delimiter pairs map to na | no invented delimiter-mismatch error |
| blockDB.ts:299–303 | generated ids use random text | deterministic collision-free ids replace randomness |

- block-49: Unreachable lexer helpers MUST NOT expand the accepted language; oracle disagreements MUST be reported before a grammar change. [just oracle]
- block-50: Go and Rust MUST resolve the same ordered model and diagnostics under both metric profiles. [just parity]
