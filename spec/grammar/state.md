# State grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `state` kind.

## Scope

- state-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/state/parser/stateDiagram.jison`, with `stateDb.ts` for semantic resolution. [just oracle]
- state-02: The parser MUST cover every reachable statement alternative of the authority. [just oracle]
- state-03: Shared preprocessing and source-position rules MUST run before this grammar; all spans MUST use repaired-source byte offsets with exclusive ends. [just parity]

## Header forms

- state-04: The first header MUST be `stateDiagram` or `stateDiagram-v2`, matched case-sensitively with the shared keyword boundary. [just oracle]
- state-05: Body keyword matching MUST use ASCII case folding, as required by the authority's case-insensitive lexer option. [just parity]
- state-06: An absent direction MUST resolve to `TB`. [just parity]

## Lexer modes

- state-07: The lexer MUST declare each mode below with the authority's exact name; an unused mode MUST remain unreachable. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| `INITIAL` | source start | mode transition |
| `ID` | no rule | none |
| `STATE` | state keyword | stereotype, newline, or opening brace |
| `FORK_STATE` | no rule | none |
| `STATE_STRING` | quote in STATE | closing quote |
| `STATE_ID` | AS in STATE | id token |
| `ALIAS` | no rule | none |
| `SCALE` | scale keyword | width suffix |
| `acc_title` | accTitle colon | value |
| `acc_descr` | accDescr colon | value |
| `acc_descr_multiline` | accDescr brace | closing brace |
| `CLASSDEF` | classDef keyword | class id |
| `CLASSDEFID` | class id | style options |
| `CLASS` | class keyword | entity ids |
| `CLASS_STYLE` | entity ids | class name |
| `STYLE` | style keyword | target ids |
| `STYLE_IDS` | no rule | none |
| `STYLEDEF_STYLES` | style target ids | style options |
| `STYLEDEF_STYLEOPTS` | no rule | none |
| `NOTE` | note keyword | position or quote |
| `NOTE_ID` | note position | target id |
| `NOTE_TEXT` | note target id | inline or block text |
| `FLOATING_NOTE` | quote in NOTE | AS |
| `FLOATING_NOTE_ID` | AS in FLOATING_NOTE | id |
| `struct` | opening composite brace | closing brace |
| `LINE` | no rule | none |

### Lexical rules in first-match order

Order is the authority line number. Unqualified rules apply in INITIAL. Mode lists restrict rules to those modes. `push` saves the previous mode; `pop` restores it. Pattern descriptions denote the authority regular expression, not a new token grammar.

- state-08: Within each mode, the lexer MUST use the following source order and MUST NOT select a longer match from a later rule. [just parity]

| Order | Pattern and modes | Action |
|---|---|---|
| 69 | click | CLICK |
| 70 | href | HREF |
| 71 | double quote, zero or more non-quotes, double quote | STRING |
| 73 | default | DEFAULT |
| 75–78 | any line prefix, direction, whitespace, TB / BT / RL / LR, remaining non-LF bytes | direction_tb / direction_bt / direction_rl / direction_lr, in that order |
| 80 | one or more LF | NL |
| 81 | one or more whitespace bytes | skip |
| 82 | ID, STATE, struct, LINE: whitespace other than LF | skip |
| 83 | INITIAL, ID, STATE, struct, LINE: hash through line end | skip |
| 84 | same modes: percent-percent not followed by opening brace, through line end | skip |
| 85–87 | scale plus whitespace; SCALE: digits; SCALE: whitespace then width | push SCALE and return scale; WIDTH; pop |
| 89–90 | accTitle, optional whitespace, colon, optional whitespace; acc_title: remainder of line | enter acc_title and return acc_title; pop and return acc_title_value |
| 91–92 | accDescr colon form; acc_descr: remainder of line | enter acc_descr and return acc_descr; pop and return acc_descr_value |
| 93–95 | accDescr brace form; acc_descr_multiline: closing brace; non-closing-brace bytes | enter mode; pop; acc_descr_multiline_value |
| 97 | INITIAL, struct: classDef plus whitespace | push CLASSDEF, classDef |
| 98–99 | CLASSDEF: DEFAULT plus whitespace; word characters plus whitespace | replace mode with CLASSDEFID, DEFAULT_CLASSDEF_ID / CLASSDEF_ID |
| 100 | CLASSDEFID: remainder of line | pop, CLASSDEF_STYLEOPTS |
| 102 | INITIAL, struct: class plus whitespace | push CLASS, class |
| 103 | CLASS: word ids separated by comma and optional whitespace | replace mode with CLASS_STYLE, CLASSENTITY_IDS |
| 104 | CLASS_STYLE: remainder of line | pop, STYLECLASS |
| 106 | INITIAL, struct: style plus whitespace | push STYLE, style |
| 107 | STYLE: word characters or commas, then whitespace | replace mode with STYLEDEF_STYLES, STYLE_IDS |
| 108 | STYLEDEF_STYLES: remainder of line | pop, STYLEDEF_STYLEOPTS |
| 110–112 | repeated scale rules, identical to 85–87 | retain their order; earlier rules win |
| 114 | INITIAL, struct: state plus whitespace | push STATE, no token |
| 116–121 | STATE: line prefix then <<fork>>, <<join>>, <<choice>>, [[fork]], [[join]], [[choice]], in that order | pop; trim prefix as FORK / JOIN / CHOICE |
| 123–126 | struct: direction patterns of 75–78 | direction token |
| 128 | STATE: double quote | push STATE_STRING |
| 129 | STATE: optional whitespace, as, whitespace | push STATE_ID, AS |
| 130 | STATE_ID: bytes other than LF or opening brace | processId, pop, ID |
| 131–132 | STATE_STRING: double quote; non-quote bytes | pop; STATE_DESCR |
| 133 | STATE: word, whitespace, word, any suffix through opening brace | reject multiword state name |
| 134–135 | STATE: bytes other than LF, whitespace, opening brace; LF | COMPOSIT_STATE; pop |
| 136 | INITIAL, STATE: opening brace | pop, push struct, STRUCT_START |
| 137–138 | struct: closing brace; LF | pop, STRUCT_STOP; skip |
| 140 | INITIAL, struct: note plus whitespace | enter NOTE, note |
| 141–143 | NOTE: left of; right of; double quote | replace with NOTE_ID and return left_of / right_of; replace with FLOATING_NOTE |
| 144–146 | FLOATING_NOTE: optional whitespace then as then optional whitespace; quote; non-quote bytes | replace with FLOATING_NOTE_ID and return AS; skip; NOTE_TEXT |
| 147 | FLOATING_NOTE_ID: remainder of line | processId, pop, ID |
| 148 | NOTE_ID: optional whitespace then bytes other than colon, LF, whitespace, hyphen | processId, replace with NOTE_TEXT, ID |
| 149 | NOTE_TEXT: optional whitespace then colon then non-colon, non-LF, non-semicolon bytes | pop, trim colon and surrounding whitespace, NOTE_TEXT |
| 150 | NOTE_TEXT: shortest text through newline, optional whitespace, end note | pop, remove terminator and trim, NOTE_TEXT |
| 152–153 | stateDiagram plus whitespace; stateDiagram-v2 plus whitespace | SD |
| 155 | hide empty description | HIDE_EMPTY |
| 157 | INITIAL, struct: [*] | EDGE_STATE |
| 158 | INITIAL, struct: bytes other than colon, LF, whitespace, hyphen, opening brace | processId, ID |
| 160 | INITIAL, struct: optional whitespace then colon, followed by non-colon, non-LF, non-semicolon bytes or colon paired with such a byte | trim, DESCR |
| 162–164 | INITIAL, struct: -->; struct: --; INITIAL, struct: ::: | arrow; CONCURRENT; STYLE_SEPARATOR |
| 165 | EOF | terminal boundary |
| 166 | any remaining character | INVALID |

- state-09: processId MUST split a token before its first `%%`, return the prefix, and leave the suffix for comment handling; an empty prefix MUST produce no token. [just parity]
- state-10: Delimiters and consumed whitespace MUST remain in token spans even when token values are trimmed. [just parity]
- state-11: Quoted state descriptions and block notes MUST retain internal line ends; the shared line-ending rule MUST treat LF, CRLF, and lone CR alike. [just parity]
- state-12: Word literals MUST use the authority's word boundary; no escape syntax MUST be added to quoted strings. [just oracle]

## Grammar

- state-13: The parser MUST use the following EBNF; terminal names MUST have the meanings of the lexer table. [just parity]

```ebnf
start = { SPACE | NL }, SD, document ;
document = { line } ;
line = [ SPACE ], statement | NL ;
statement = classDefStatement | styleStatement | cssClassStatement
          | idStatement, [ DESCR | '-->', idStatement, [ DESCR ] ]
          | HIDE_EMPTY | scale, WIDTH | COMPOSIT_STATE
          | COMPOSIT_STATE, STRUCT_START, document, STRUCT_STOP
          | STATE_DESCR, AS, ID, [ STRUCT_START, document, STRUCT_STOP ]
          | FORK | JOIN | CHOICE | CONCURRENT
          | note, notePosition, ID, NOTE_TEXT
          | note, NOTE_TEXT, AS, ID | direction
          | acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value
          | CLICK, idStatement, STRING, STRING, NL
          | CLICK, idStatement, HREF, STRING, NL ;
classDefStatement = classDef, ( CLASSDEF_ID | DEFAULT ), CLASSDEF_STYLEOPTS ;
styleStatement = style, STYLE_IDS, STYLEDEF_STYLEOPTS ;
cssClassStatement = class, CLASSENTITY_IDS, STYLECLASS ;
direction = direction_tb | direction_bt | direction_rl | direction_lr ;
idStatement = ( ID | EDGE_STATE ), [ STYLE_SEPARATOR, ID ] ;
notePosition = left_of | right_of ;
eol = NL | ';' ;
```

- state-14: The unreachable `eol` production MUST NOT make semicolon a general statement separator. [just oracle]
- state-15: The parser MUST reject a second arrow in one transition statement; it MUST NOT invent transition chaining. [just oracle]
- state-16: A bare COMPOSIT_STATE MUST be accepted without creating a resolved state, because that alternative has no state-object action. [just oracle]

## Statement boundary

- state-17: Recovery MUST stop at the next physical line end outside a quoted value, block note, or accessibility block, or before the enclosing composite's closing brace. [just go-check]
- state-18: Recovery MUST retain the enclosing scope and MUST NOT resolve a rejected statement. [just go-check]
- state-19: EOF inside a quote, composite, block note, or accessibility block MUST report the unterminated diagnostic from its opening delimiter through EOF. [just go-check]
- state-20: Composite nesting MUST stop before level 65 using the shared nesting-limit diagnostic. [just go-check]

## Abstract syntax tree

- state-21: AST nodes MUST use upstream production names in PascalCase and MUST carry the first-token-to-last-token span, without a trailing line separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| `Start` | header, Document | header through EOF |
| `Document` | ordered Line children | first through last child; empty span at body start when empty |
| `Line` | optional Statement | statement span; line-end span when empty |
| `Statement` | selected alternative, description, endpoints, body, stereotype, note, link, or accessibility value | complete alternative, including state keyword and quote delimiters consumed without tokens |
| `ClassDefStatement` | id, raw ordered style components | keyword through style options |
| `StyleStatement` | ordered target ids, raw style components | keyword through style options |
| `CssClassStatement` | ordered target ids, class name | keyword through class name |
| `Direction` | TB, BT, RL, or LR | complete greedy direction token |
| `IdStatement` | id, optional CSS class | id through CSS class |
| `NotePosition` | left_of or right_of | position words |
| `Eol` | separator | unreachable; no node is constructed |

- state-22: Tokens MUST borrow source text; the model MUST retain state-id, description, transition, directive, note, and delimiter spans. [just parity]

## Semantic resolution

- state-23: Resolution MUST traverse statements in declaration order and MUST preserve first insertion order for states and transitions. [just parity]
- state-24: A bare IdStatement, a description assignment, or a transition endpoint MUST create an absent ordinary state in its scope. [just oracle]
- state-25: Repeated declarations MUST reuse the existing state and append nonempty trimmed descriptions; the first description MUST be its label and later descriptions MUST be body rows. [just parity]
- state-26: A later body MUST attach to an existing state only when it has no body; a later declaration MUST NOT replace an established state type. [just parity]
- state-27: A quoted alias without a body MUST split its ID token at colons: the first segment MUST be the id and the second segment MUST append a description after the quoted label; later segments MUST have no effect. [just oracle]
- state-28: A quoted alias with a body MUST retain its full trimmed ID token as its id and MUST use the quoted value as its label. [just oracle]
- state-29: A composite MUST become a group cluster whose direct children name it as parent; its title band and padding MUST follow `spec/layout/layered.md`. [just validate]
- state-30: A composite with more than one nonempty description row MUST raise the group-description diagnostic below. [just oracle]
- state-31: Each root or composite scope MUST have at most one start node `<scope>_start` and one end node `<scope>_end`; the root scope name MUST be `root`. [just parity]
- state-32: A transition source `[*]` MUST create or reuse that scope's start node; a transition target `[*]` MUST create or reuse its end node. [just parity]
- state-33: A standalone `[*]` MUST resolve as the scope's start node, because standalone state translation uses the source-side interpretation. [just oracle]
- state-34: A start node MUST be a fixed 14 px circle using `state.start_size`, or one cell with symbol `disc`; an end node MUST be a fixed 14 px circle using `state.end_size`, with a 5 px inner circle using `state.end_inner_size`, or one cell with symbol `bullseye` and no inner circle. [just parity]
- state-35: Start and end nodes MUST be ordinary layered nodes; neither MUST force a rank. [just validate]
- state-36: A transition MUST retain its endpoint order and its optional trimmed colon-free label; duplicate transitions MUST remain separate records in declaration order. [just parity]
- state-37: Fork and join declarations MUST create bar-shaped nodes; choice declarations MUST create diamond-shaped nodes; both angle-bracket and square-bracket stereotype forms MUST resolve alike. [just parity]
- state-38: A `--` divider inside a composite MUST split its body into ordered concurrent regions; empty leading, middle, and trailing regions MUST remain representable and MUST NOT create phantom ordinary states. [just parity]
- state-39: Concurrent-region ids MUST use deterministic divider declaration indices rather than a random or process-global id; each region MUST remain inside its composite and its separator MUST use a dashed rule. [just parity]
- state-59: A concurrent-region separator MUST stop at the bounding envelope of its two adjacent region bodies, clipped to the parent's inset bounds. A vertical separator MUST use that envelope's top and bottom; a horizontal separator MUST use its left and right. Its other coordinate MUST remain the midpoint of the gap between the regions. A negative inset, nonpositive region extent, inverted clipped bounds, or midpoint outside that envelope MUST return the geometry domain error; coordinate overflow MUST return the geometry overflow error. The rule MUST preserve the parent title band. [just go-check: TestStateSeparatorStopsAtChildEnvelope]
- state-40: An attached note MUST create an absent target state, retain left or right placement, and replace that state's preceding note; note text MUST be trimmed and drawn in note style. [just oracle]
- state-60: Under the cell profile, attachment routing MUST reserve every nonempty label and title obstacle with one additional cell on each side before searching its visibility grid. The existing open-interior visibility test MUST NOT admit a path through a text cell. Vector text obstacles MUST keep their measured bounds. The expansion MUST use checked coordinates and dimensions. [just go-check: TestStateNoteRoutingPreservesTransitionLabel]
- state-41: A floating-note alternative MUST be accepted but MUST have no model effect, because its authority production has no note-object action. [just oracle]
- state-42: A direction statement MUST retain its local scope and set that scope's final direction; the last direction in a scope MUST win. [just parity]
- state-43: classDef MUST create or reuse its class definition and append comma-separated styles after removing semicolons and trimming; a component containing `color` MUST also produce a text style with `fill` changed to `bgFill` and `color` changed to `fill`. [just parity]
- state-44: class statements and inline `:::` assignments MUST append the class name to every target and MUST create absent target states in target order. [just oracle]
- state-45: style MUST create absent targets and replace their direct styles with the trimmed comma-separated components after removing semicolons. [just parity]
- state-46: Styling values MUST remain literal and MUST NOT undergo label-entity decoding. [just parity]
- state-47: Click statements MUST retain the target, URL, and optional tooltip; the href form MUST use an empty tooltip, and the last link for a target MUST win without creating an absent target. [just parity]
- state-48: Static output MUST apply the shared URL-scheme restriction and MUST NOT install browser handlers or execute callbacks; this grammar MUST NOT accept a callback form absent from its productions. [just parity]
- state-49: Accessibility statements MUST trim their values and replace the preceding value; they MUST NOT create states. [just parity]
- state-50: Scale and hide-empty-description statements MUST be accepted without changing geometry or creating model elements. [just oracle]
- state-51: Ordinary states MUST use layered node sizing and measurement; group frames MUST use group style and transitions MUST use solid edge style. [just validate]

## Diagnostics

- state-52: Rejected syntax and enforced database checks MUST use exactly the following state diagnostic rows in this order. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `state/unexpected-token` | error | parser | token fits no current production | offending token | `unexpected TOKEN, expected one of: LIST` |
| `state/unknown-statement` | error | parser | first token starts no statement | first token through next boundary | `unknown statement TOKEN` |
| `state/unterminated` | error | parser | EOF inside a delimiter or block | opening delimiter through EOF | `unterminated TOKEN` |
| `state/multiword-state-name` | error | lexer | unquoted composite name contains two word groups before its opening brace | name through opening brace | `state name must be a single word: NAME` |
| `state/group-description` | error | model | composite label has additional description rows | first additional description | `composite state ID cannot have additional descriptions` |

- state-53: TOKEN MUST be source text; LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `. [just parity]
- state-54: A named diagnostic MUST take precedence over the generic unterminated diagnostic for the same failure. [just go-check]
- state-55: Duplicate states, duplicate transitions, unknown class names, and implicit style targets MUST NOT become syntax errors when upstream accepts them. [just oracle]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| Header case | lexer folds case but shared detection is case-sensitive | preserve shared detection; fold body keywords only |
| Header EOF | lexer requires whitespace after SD and returns NL at EOF | accept EOF as header boundary after shared detection; terminate once, never synthesize repeated NL |
| Default classDef | lexer returns DEFAULT_CLASSDEF_ID but production expects DEFAULT | preserve this lexical rejection with unexpected-token; do not silently repair the token name |
| Unused modes and eol | several modes have no entering rule; eol has no caller | retain names without extending acceptance |
| Floating notes and bare state keyword | productions lack model-object actions | accept without a model effect |
| Start/end helpers | legacy extraction generates counters; v2 translation uses parent suffixes | use one scoped start and end in both header forms, as required by the product contract |
| Concurrency translation | final empty region can prevent replacement; final nonempty region uses generated id | retain all regions and deterministic indices; do not reproduce accidental region loss or nondeterminism |
| Direction side effects | parsing calls a root setter before the root document is installed; direction objects also remain in bodies | resolve final direction per scope from statement order, not parser-global mutable state |
| Group descriptions | extract rejects groups with rows after the label | report group-description at the first extra row |
| State-not-found exceptions | addState inserts before lookup; failed lookup is not reachable from valid input | no artificial unknown-state semantic diagnostic |
| Sanitization and links | database uses DOM sanitization and event binding | keep semantic text; escape and restrict links at shared static output stages |
| Semicolon | eol is unreachable; style values consume line tails | no general semicolon separator; keep semicolons inside raw style tokens |

- state-56: An unreachable helper or accidental undefined semantic value MUST NOT add a new statement form. [just oracle]
- state-57: Go and Rust MUST resolve the same ordered boxes, clusters, transitions, notes, and labels under both metric profiles. [just parity]
- state-58: A `click` link whose URL, trimmed of ASCII whitespace, starts with `http:`, `https:`, or `mailto:` with the scheme compared ASCII case-insensitively MUST reach the scene as one `<a>` wrapping the scene group of role `node` whose owner is the target id. A target that is a composite state or is absent, and a link of any other scheme, MUST draw no anchor, and an empty tooltip MUST emit no `<title>`. Go and Rust MUST emit the same anchors. [just go-check: TestStateClickLinksWrapTheirSimpleStateOnly]
