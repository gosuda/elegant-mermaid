# Sequence grammar

This file fixes the lexer, grammar, abstract syntax, model resolution, and diagnostics of the `sequence` kind. Layout follows `spec/layout/sequence.md`.

## Scope

- seqgrammar-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/sequence/parser/sequenceDiagram.jison`; semantic resolution MUST follow `sequenceDb.ts` in the same diagram directory. [just oracle]
- seqgrammar-02: The parser MUST accept every reachable statement alternative below. [just oracle]
- seqgrammar-03: Preprocessing MUST follow `spec/preprocessing.md`; spans MUST index repaired source bytes with an exclusive end. [just parity]

## Header forms

- seqgrammar-04: Shared detection MUST recognize `sequenceDiagram` with its written case and the boundary of `spec/detection.md`. [just oracle]
- seqgrammar-05: The body lexer MUST fold ASCII keyword case; participant ids and label text MUST retain their case. [just parity]

## Lexer modes

- seqgrammar-06: The lexer MUST use the exclusive modes below and MUST select the first matching rule in each mode. [just parity]

| Mode | Entry | Exit |
|---|---|---|
| `INITIAL` | source start | none |
| `ID` | participant, actor, destroy, activate, deactivate | actor token, invalid token, alias completion, or config completion |
| `ALIAS` | id followed by `as`, or config followed by `as` | `as` or empty fallback |
| `LINE` | box or control keyword, or `as` | rest-of-line token |
| `CONFIG` | `@{` in ID | first closing brace |
| `CONFIG_DATA` | no entry rule | no exit rule |
| `acc_title` | `accTitle:` | value |
| `acc_descr` | `accDescr:` | value |
| `acc_descr_multiline` | `accDescr {` | closing brace |

## Lexical rules in first-match order

The order column is the authority line number. An unqualified rule applies in INITIAL. This table describes patterns, not host-language character categories.

- seqgrammar-07: The lexer MUST apply the following rules in source order after preprocessing. [just parity]

| Order | Pattern and modes | Result |
|---|---|---|
| 24 | one or more LF | NEWLINE |
| 25 | whitespace run | skip |
| 26 | ID, ALIAS, LINE: whitespace other than LF | skip |
| 27 | INITIAL, ID, ALIAS, LINE: hash through line end | skip |
| 28 | two percent signs not followed by opening brace, through line end | skip |
| 29 | non-closing-brace byte followed by two percent signs and line tail | skip |
| 30 | nonnegative decimal with at most two fraction digits, followed by space or LF | NUM |
| 31 | ID: `@{` | CONFIG_START; push CONFIG |
| 32 | CONFIG: nonempty text before closing brace | CONFIG_CONTENT |
| 33 | CONFIG: closing brace before whitespace, `as`, whitespace | CONFIG_END; replace CONFIG with ALIAS |
| 34 | CONFIG: closing brace | CONFIG_END; pop CONFIG and ID |
| 35 | ID: nonempty id without angle brackets, colon, LF, comma, semicolon, at-sign, or whitespace, before optional whitespace and `@{` | trimmed ACTOR |
| 36 | ID: same id before whitespace, `as`, whitespace | trimmed ACTOR; push ALIAS |
| 37 | ID: text without angle brackets, colon, LF, comma, semicolon, or at-sign, before line end, semicolon, hash, or EOF | trimmed ACTOR; pop ID |
| 38 | ID: otherwise allowed prefix followed by less-than and line tail | INVALID; pop ID |
| 39 | ID: remaining nonempty line tail | trimmed INVALID; pop ID |
| 40–44 | `box`, `participant`, `actor`, `create`, `destroy`, in this order | box enters LINE; participant and actor enter ID; destroy enters ID |
| 45 | ALIAS: `as` | AS; pop ALIAS and ID; push LINE |
| 46 | ALIAS: empty fallback | NEWLINE; pop ALIAS and ID |
| 47–57 | `loop`, `rect`, `opt`, `alt`, `else`, `par`, `par_over`, `and`, `critical`, `option`, `break`, in this order | corresponding token; push LINE |
| 58 | LINE: optional colon and wrap marker, then text excluding hash, LF, semicolon | restOfLine; pop LINE |
| 59–61 | `end`, `left of`, `right of` | corresponding token |
| 62–65 | `links`, `link`, `properties`, `details`, in this order, before horizontal whitespace and a valid initial actor byte | corresponding token |
| 66–69 | `over`, `note`, `activate`, `deactivate` | corresponding token; last two enter ID |
| 70–71 | `title` or `title:`, then whitespace and nonempty text excluding hash, LF, semicolon | title or legacy_title |
| 72–73 | accessibility title keyword and colon; acc_title line value | acc_title then acc_title_value; return to prior mode |
| 74–75 | accessibility description keyword and colon; acc_descr line value | acc_descr then acc_descr_value; return to prior mode |
| 76–78 | accessibility description keyword and opening brace; closing brace; text before brace | enter acc_descr_multiline; pop on close; emit value text |
| 79–83 | `sequenceDiagram`, `autonumber`, `off`, comma, semicolon | SD, autonumber, off, comma, NEWLINE |
| 84 | ordinary actor text | trimmed ACTOR |
| 85–94 | first ten arrow tokens in the table below | corresponding signal token |
| 97–100 | four forward dotted half-arrow tokens | corresponding signal token |
| 103–106 | four reverse dotted half-arrow tokens | corresponding signal token |
| 109–112 | four forward solid half-arrow tokens | corresponding signal token |
| 115–118 | four reverse solid half-arrow tokens | corresponding signal token |
| 120 | colon, optional wrap marker, then text excluding hash, LF, semicolon | TXT |
| 121 | colon alone | empty TXT |
| 122–124 | plus, minus, `()` | corresponding token |
| 125 | EOF | one synthetic NEWLINE, then end of input |
| 126 | any unmatched byte | INVALID |

- seqgrammar-08: Ordinary actor scanning MUST stop before colon, comma, semicolon, line end, plus, parentheses, angle-arrow syntax, or any arrow spelling below; slash and backslash MUST NOT start an ordinary actor token. [just oracle]
- seqgrammar-09: The ordinary actor continuation MUST retain hyphens only when they do not start an arrow; it MUST trim surrounding whitespace. [just parity]
- seqgrammar-10: Shared preprocessing MUST give LF, CRLF, and lone CR the same statement-boundary effect; a semicolon MUST also return NEWLINE outside text modes. [just parity]

| Ordered arrow token | Signal kind |
|---|---|
| `->>` | SOLID |
| `<<->>` | BIDIRECTIONAL_SOLID |
| `-->>` | DOTTED |
| `<<-->>` | BIDIRECTIONAL_DOTTED |
| `->` | SOLID_OPEN |
| `-->` | DOTTED_OPEN |
| `-x` | SOLID_CROSS |
| `--x` | DOTTED_CROSS |
| `-)` | SOLID_POINT |
| `--)` | DOTTED_POINT |
| `--|\` | SOLID_TOP_DOTTED |
| `--|/` | SOLID_BOTTOM_DOTTED |
| `--\\` | STICK_TOP_DOTTED |
| `--//` | STICK_BOTTOM_DOTTED |
| `/|--` | SOLID_ARROW_TOP_REVERSE_DOTTED |
| `\|--` | SOLID_ARROW_BOTTOM_REVERSE_DOTTED |
| `//--` | STICK_ARROW_TOP_REVERSE_DOTTED |
| `\\--` | STICK_ARROW_BOTTOM_REVERSE_DOTTED |
| `-|\` | SOLID_TOP |
| `-|/` | SOLID_BOTTOM |
| `-\\` | STICK_TOP |
| `-//` | STICK_BOTTOM |
| `/|-` | SOLID_ARROW_TOP_REVERSE |
| `\|-` | SOLID_ARROW_BOTTOM_REVERSE |
| `//-` | STICK_ARROW_TOP_REVERSE |
| `\\-` | STICK_ARROW_BOTTOM_REVERSE |

## Grammar

- seqgrammar-11: The parser MUST use this EBNF without backtracking over consumed tokens; production names MUST retain the authority names. [just parity]

```ebnf
start = { NEWLINE }, SD, document ;
document = { line } ;
line = statement | NEWLINE | INVALID ;
box_section = { box_line } ;
box_line = participant_statement | NEWLINE ;
statement = participant_statement | 'create', participant_statement
          | 'box', restOfLine, box_section, 'end'
          | signal, NEWLINE
          | 'autonumber', [ NUM, [ NUM ] | 'off' ], NEWLINE
          | ( 'activate' | 'deactivate' ), actor, NEWLINE
          | ( note_statement | links_statement | link_statement
            | properties_statement | details_statement ), NEWLINE
          | title | legacy_title | acc_title, acc_title_value
          | acc_descr, acc_descr_value | acc_descr_multiline_value
          | ( 'loop' | 'rect' | 'opt' | 'break' ), restOfLine, document, 'end'
          | 'alt', restOfLine, else_sections, 'end'
          | ( 'par' | 'par_over' ), restOfLine, par_sections, 'end'
          | 'critical', restOfLine, option_sections, 'end' ;
option_sections = document, { 'option', restOfLine, document } ;
par_sections = document, { 'and', restOfLine, document } ;
else_sections = document, { 'else', restOfLine, document } ;
participant_statement = ( 'participant' | 'actor' ),
                        ( actor | actor_with_config ), [ AS, restOfLine ], NEWLINE
                      | 'destroy', actor, NEWLINE ;
note_statement = 'note', placement, actor, text2
               | 'note', 'over', actor_pair, text2 ;
links_statement = 'links', actor, text2 ;
link_statement = 'link', actor, text2 ;
properties_statement = 'properties', actor, text2 ;
details_statement = 'details', actor, text2 ;
actor_pair = actor, [ ',', actor ] ;
placement = 'left_of' | 'right_of' ;
signal = actor, signaltype, [ '+' | '-' ], actor, text2
       | actor, signaltype, '()', actor, text2
       | actor, '()', signaltype, actor, text2
       | actor, '()', signaltype, '()', actor, text2 ;
actor_with_config = actor, config_object ;
config_object = CONFIG_START, CONFIG_CONTENT, CONFIG_END ;
actor = ACTOR | 'participant' | 'link' | 'actor', ACTOR ;
signaltype = any arrow token in the ordered table ;
text2 = TXT ;
```

- seqgrammar-12: A box body MUST contain only participant statements and blank lines; a control body MUST contain document statements. [just oracle]
- seqgrammar-13: A message and a note MUST contain a colon text token; an empty colon value MUST be accepted. [just oracle]
- seqgrammar-14: Alias and control text MUST end at hash, semicolon, or line end; quotes MUST remain ordinary text and MUST NOT hide these terminators. [just oracle]

## Statement boundary

- seqgrammar-15: Recovery MUST stop at the next physical line end or semicolon outside metadata and multiline accessibility text, or at a matching control separator or end at the current scope. [just go-check]
- seqgrammar-16: Recovery MUST preserve the enclosing block and MUST NOT create participants from a rejected statement. [just go-check]
- seqgrammar-17: EOF inside a block, metadata object, or accessibility block MUST raise the unterminated diagnostic; EOF after a complete final statement MUST supply exactly one terminator. [just go-check]
- seqgrammar-18: Block nesting MUST stop before level 65 with the shared nesting-limit diagnostic. [just go-check]

## Abstract syntax tree

- seqgrammar-19: Each AST node MUST take its upstream production name in PascalCase and MUST span its first through last consumed token, without a trailing statement separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| `Start`, `Document` | header and ordered lines; ordered lines | header through source end; first through last child |
| `Line`, `Statement` | selected alternative | selected alternative |
| `BoxSection`, `BoxLine` | ordered declarations; selected declaration | first through last child |
| `ParticipantStatement` | action, draw kind, actor, alias, config | keyword through alias, config, or actor |
| `OptionSections`, `ParSections`, `ElseSections` | ordered documents and separator labels | first through last child, including separators |
| `NoteStatement` | placement, actors, text | note keyword through text |
| `LinksStatement`, `LinkStatement`, `PropertiesStatement`, `DetailsStatement` | actor and text | keyword through text |
| `ActorPair` | one or two actors | first through last actor |
| `Placement` | left or right | placement token |
| `Signal` | source, target, signal type, activation suffix, central endpoints, text | source through text |
| `ActorWithConfig`, `ConfigObject` | actor and metadata; raw metadata | actor through brace; both delimiters included |
| `Actor`, `Signaltype`, `Text2` | id; arrow kind; text and wrap override | token span; Text2 includes colon |

- seqgrammar-20: AST tokens MUST borrow source text; the model MUST retain id, declaration, message, suffix, and block-opening spans for diagnostics. [just parity]

## Semantic resolution

- seqgrammar-21: Resolution MUST process statements in source order and MUST keep participant order at first insertion. [just parity]
- seqgrammar-22: Message endpoints and note actors MUST create absent participants with their id as label; an explicit participant or actor MUST replace its existing description and type without moving its index. [just oracle]
- seqgrammar-23: An explicit alias MUST replace the display label, not the id; metadata alias MUST apply only when no distinct explicit alias exists. [just parity]
- seqgrammar-24: Metadata MUST use the shared config-value reader; a single-line metadata body MUST be read as a mapping body, and a multiline body MUST be read as a block mapping. [just parity]
- seqgrammar-25: Metadata type MUST override participant or actor draw kind; other metadata fields MUST be retained without inventing syntax statements. [just parity]
- seqgrammar-26: A participant MUST retain its first assigned box; assignment to a different box MUST report the box-conflict diagnostic. [just oracle]
- seqgrammar-27: A box MUST retain its ordered participants, title, wrap override, and optional color; its closing end MUST clear the current box. [just parity]
- seqgrammar-28: Every arrow token MUST retain the signal kind in the table; bidirectional tokens MUST mark both ends, and reverse half-arrow tokens MUST mark the source end without swapping message endpoints. [just parity]
- seqgrammar-29: A plus suffix MUST append a target activation after its message; a minus suffix MUST append a source deactivation after its message. [just oracle]
- seqgrammar-30: Explicit activation MUST append an activation event for its actor; deactivation MUST reject a participant whose activation count is zero. [just oracle]
- seqgrammar-31: Central connection after the arrow MUST append a target central event; central connection before the arrow MUST append a source reverse-central event; both MUST append target then source events. [just parity]
- seqgrammar-32: Central connection events MUST NOT change activation counts. [just oracle]
- seqgrammar-33: A create statement MUST reject any id already present, including a destroyed id; otherwise it MUST record the current event index and set the pending-created actor. [just oracle]
- seqgrammar-34: The next message while a created actor is pending MUST target that actor; a different target MUST report the creating-message diagnostic. [just oracle]
- seqgrammar-35: A destroy statement MUST record the current event index and set the pending-destroyed actor; the next message checked for destruction MUST have that actor as source or target. [just oracle]
- seqgrammar-36: When creation and destruction are both pending, creation MUST be checked first and destruction MUST remain pending until a later message. [just oracle]
- seqgrammar-37: End of input with a pending create or destroy MUST NOT add an error; later messages involving a previously destroyed actor MUST NOT add an error solely for that fact. [just oracle]
- seqgrammar-38: A left or right note MUST retain one actor; an over note MUST retain its two actors, duplicating a single actor as both endpoints. [just parity]
- seqgrammar-39: Control blocks MUST emit start, ordered content, separators, and end events; par_over MUST retain its distinct start kind, and rect MUST retain its color text. [just parity]
- seqgrammar-40: Message, alias, note, and control text MUST trim outer whitespace and remove an initial wrap: or nowrap: marker, with an optional preceding colon; an absent override MUST use the shared wrap setting before sequence.wrap. [just parity]
- seqgrammar-41: Autonumber MUST start with counter 1 and step 1; explicit nonzero start and step MUST replace those values, and zero MUST retain the current value, as upstream's fallback does. [just parity]
- seqgrammar-42: Autonumber off MUST hide numbering without resetting the counter; bare autonumber MUST enable it without resetting the counter. [just parity]
- seqgrammar-43: Number arithmetic MUST use integer hundredths; each message MUST advance the counter once, including messages while numbering is hidden. [just parity]
- seqgrammar-44: A visible message number MUST prefix the label as `(NUMBER) `, or `(NUMBER)` for empty text; NUMBER MUST omit unnecessary fractional zeros. [just parity]
- seqgrammar-45: Links and properties MUST create an absent target through their actor production; valid JSON mappings MUST merge in source order with later keys replacing earlier keys; malformed JSON MUST have no model effect and MUST NOT become a syntax error. [just oracle]
- seqgrammar-46: A link statement MUST split its text at the first at-sign; its label MUST use the trimmed prefix excluding the character immediately before that sign, and its URL MUST use the trimmed suffix. [just oracle]
- seqgrammar-47: Details MUST retain its reference as static metadata and MUST NOT query a DOM, file, or network resource. [just parity]
- seqgrammar-48: Title, legacy title, accessibility title, and accessibility description MUST replace the preceding value; accessibility values MUST trim surrounding whitespace. [just parity]

## Diagnostics

- seqgrammar-49: A parser rejection or database exception MUST produce the corresponding diagnostic below rather than a panic. [just go-check]
- seqgrammar-50: The diagnostic registry MUST contain exactly these rows in this order. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `sequence/unexpected-token` | error | token fits no current production, including INVALID | offending token | unexpected TOKEN, expected one of: LIST |
| `sequence/unknown-statement` | error | first token starts no statement | first token through next boundary | unknown statement TOKEN |
| `sequence/unterminated` | error | EOF inside block or delimiter | opening token through EOF | unterminated TOKEN |
| `sequence/inactive-participant` | error | deactivation count is zero | deactivate actor token, or minus suffix | participant ID is not active |
| `sequence/participant-box-conflict` | error | actor belongs to a different box | later actor id | participant ID belongs to more than one box |
| `sequence/create-existing-participant` | error | create names an existing actor | created actor id | cannot create existing participant ID |
| `sequence/creating-message-missing` | error | next message has wrong target | message target id | next message must target created participant ID |
| `sequence/destroying-message-missing` | error | next checked message does not involve destroyed actor | whole signal | next message must involve destroyed participant ID |

- seqgrammar-51: LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; TOKEN MUST be source text. [just parity]
- seqgrammar-52: Shared metadata-reader diagnostics MUST retain their shared codes; named semantic diagnostics MUST take precedence over generic diagnostics for the same failure. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| Header and body case | lexer folds case, detector does not | shared detection stays case-sensitive; body folds ASCII |
| EOF | lexer returns NEWLINE repeatedly | synthesize one terminator, then terminate |
| INVALID line | grammar silently discards INVALID | report a generic error; do not create a phantom participant |
| SPACE and spaceList | SPACE has no producing lexer rule; spaceList is unreachable | omit unreachable SPACE alternatives and spaceList from executable grammar |
| CONFIG_DATA | declared but never entered | retain mode name without adding acceptance |
| Quoted labels | no quote lexer mode exists | quotes are literal and never a syntax error; a participant or actor name or alias that starts a quote without closing it raises only the warning `sequence/quote-unclosed` (seqgrammar-55) |
| Box colors | database uses browser CSS validation | recognize rgb/rgba/hsl/hsla functions and standard CSS named colors deterministically; otherwise use transparent and the entire text as title |
| Participant metadata | database uses a full YAML library | shared subset reader applies; anchors and tags use shared diagnostics |
| Types | database accepts arbitrary metadata type strings | retain the string; unsupported drawing types use participant presentation, not a syntax error |
| Repeated actors | database rewrites linked-list pointers and resets metadata | keep first insertion order, replace fields, reset links and properties on explicit redeclaration |
| Create syntax | create can prefix any participant_statement, even destroy | preserve grammar acceptance; resolve its actor as creation with default participant kind when no draw kind exists |
| Pending lifetimes | database checks only when another message arrives | no end-of-input lifetime diagnostic; no invented post-destruction ban |
| Details | database reads an element by DOM id | preserve reference without external lookup |
| Numbering | renderer uses floating point and rounds to hundredths | integer hundredths preserve decimal input; visible numbers become label prefixes |
| Link separator | database slices one character before at-sign | preserve that behavior, counting Unicode scalar values, including a missing separator using the equivalent slice bounds (seqgrammar-59) |
| Sanitization | database uses HTML sanitization | retain semantic text; shared static-output escaping and URL rules apply |

- seqgrammar-53: An unreachable helper or accidental runtime failure MUST NOT add a new statement form or an invented semantic rejection. [just oracle]
- seqgrammar-54: Go and Rust MUST resolve the same ordered participants, events, notes, boxes, and text under both metric profiles. [just parity]
- seqgrammar-55: The parser MUST raise the warning `sequence/quote-unclosed` for a participant or actor declaration whose name or alias token, with its leading and trailing blanks removed, starts with a `"` and holds an odd number of `"` characters; its message and help MUST be the `summary` and `help` of the row `sequence/quote-unclosed` in `spec/data/lint-rules/sequence.json`, its span MUST be that token, and its single fix MUST be unsafe and MUST insert a `"` after the token. The row is a maid syntax row, so `check` and `lint` both report it, and the parse MUST NOT change. [just go-check: TestUnclosedQuoteWarnsOnNamesAndAliases]
- seqgrammar-56: A metadata body MUST have its outer whitespace removed before the shared reader runs, as upstream trims the config text. A trimmed body without a line break MUST be read as a flow mapping closed by the delimiters of the body; a trimmed body with a line break MUST be read as a block mapping whose first line carries no indentation, so a body whose later lines are indented MUST raise `config/malformed` where upstream's YAML load throws. [just go-check: TestIndentedMetadataOnSeveralLinesIsRejectedLikeUpstream]
- seqgrammar-57: Every diagnostic of the shared metadata reader MUST reach the document diagnostics with its code and message unchanged and with a span in source bytes. The single-line reading adds a leading and a trailing brace: a position on the leading brace MUST map to the opening brace of `@{`, and a position on the trailing brace MUST map to the closing brace of the body. [just go-check: TestMetadataReaderDiagnosticsReachTheSourceSpans]
- seqgrammar-58: A link statement MUST insert its label and URL pair into the links of its actor, and a label that repeats an earlier label of that actor MUST replace the earlier URL and keep the earlier position, as upstream keeps links in a keyed object. [just go-check: TestRepeatedLinkLabelReplacesTheEarlierURL]
- seqgrammar-59: When the text of a link statement holds no at-sign, the label MUST drop the last two characters of the trimmed text and the URL MUST be the whole trimmed text, because the upstream index is -1 in both slices. When the at-sign is the first character, the label MUST drop the last character. A character MUST be a Unicode scalar value. [just go-check: TestLinkWithoutAtSignKeepsTheWholeTextAsTheURL]
- seqgrammar-60: A `properties` statement MUST read its text as one JSON object and MUST merge each member whose value is a string, a number, or a boolean into the properties of its actor in source order, a later key replacing the earlier value. A member whose value is null, an array, or an object, a text that is not a JSON object, and a malformed text MUST have no effect and MUST NOT raise a diagnostic. A `links` statement MUST read its text the same way into the links of its actor. [just go-check: TestPropertiesAndDetailsJSONFormsMapOntoPropertiesAndLinks]
- seqgrammar-61: A `details` statement MUST read its text as the JSON text that upstream finds inside the referenced element, because static output has no DOM. A `properties` member that is an object MUST merge into the properties of its actor as seqgrammar-60 states, and a `links` member that is an object MUST merge into the links of its actor. Every other member, a text that is not a JSON object, and a bare element reference MUST have no effect and MUST NOT raise a diagnostic. [just go-check: TestPropertiesAndDetailsJSONFormsMapOntoPropertiesAndLinks]
