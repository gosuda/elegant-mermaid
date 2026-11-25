# Flowchart grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `flowchart` kind.

## Scope

- flowchart-001: The grammar authority MUST be `flowchart` in `.references/mermaid/packages/mermaid/src/diagrams/flowchart/parser/flow.jison`, with `flowDb.ts` in the same directory for the semantic resolution. [just go-check]
- flowchart-002: This file MUST cover every statement form of the authority except the forms of another kind. [just go-check]
- flowchart-003: The header keyword `swimlane-beta` MUST NOT be accepted here, because it belongs to `spec/grammar/swimlane.md`. [just oracle]
- flowchart-004: The pseudo-diagram keywords `error` and `---` MUST NOT be accepted here, and `spec/detection.md` MUST decide the kind before this grammar runs. [just gen-check]
- flowchart-005: Frontmatter, directives, and `%%` comments MUST be removed by `spec/preprocessing.md` before the lexer reads a byte, and this grammar MUST NOT hold a rule for them. [just go-check]
- flowchart-006: Every span in this file MUST be a byte span with an exclusive end, as `spec/source-and-positions.md` defines it. [just go-check]

## Header forms

- flowchart-007: The header MUST be one keyword of `flowchart`, `graph`, or `flowchart-elk`, matched case-sensitively, followed by an optional direction. [just oracle]
- flowchart-008: The direction MUST be one keyword of the table below, and the parser MUST resolve it to the layout direction of that row. [just parity]

| Direction keyword | Layout direction |
|---|---|
| `TB` | `TB` |
| `TD` | `TB` |
| `BT` | `BT` |
| `LR` | `LR` |
| `RL` | `RL` |
| `>` | `LR` |
| `<` | `RL` |
| `^` | `BT` |
| `v` | `TB` |

- flowchart-009: The keyword `BR` MUST lex as `DIR` and MUST raise no diagnostic, because the authority accepts it and stores it as the direction; the model MUST resolve it to `TB`, which is the fallback of `flowchart-012` for a direction outside the nine keywords. [just oracle]
- flowchart-010: A header with no direction MUST be accepted and MUST resolve to `TB`, which is the authority action for `NODIR`. [just oracle]
- flowchart-011: The header MUST end at a line end, at `;`, or at the end of the input, and spaces before that byte MUST be accepted. [just go-check]
- flowchart-012: The header MUST set the resolved direction of the model, and the dump MUST report a `TD` header as `TB`. [just validate]
- flowchart-013: A header keyword after the first one MUST NOT change the direction. [just go-check]
- flowchart-014: A first statement that matches no header keyword MUST raise `common/unknown-diagram-kind`, and this grammar MUST NOT run. [just go-check]

## Lexer modes

The authority declares one start condition per row of the table below. The lexer MUST hold one mode per row, with the same name.

- flowchart-015: Each rule of this file MUST be reachable only in the modes of its row of the table below. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| `INITIAL` | the start of the input | none |
| `string` | `"` in any mode | `"` inside the mode |
| `md_string` | `` "` `` in any mode | `` `" `` inside the mode |
| `acc_title` | `accTitle` then a colon | the end of the line |
| `acc_descr` | `accDescr` then a colon | the end of the line |
| `acc_descr_multiline` | `accDescr` then `{` | `}` |
| `dir` | a header keyword that is the first one | a `dir` rule below |
| `text` | a shape opener of the `INITIAL` table | its matching closer |
| `ellipseText` | `(-` | `-)` |
| `trapText` | `[/` or `[\` | `\]` or `/]`; a bare `]` does not close the label |
| `edgeText` | the start half of a normal link | the end half of that link |
| `thickEdgeText` | the start half of a thick link | the end half of that link |
| `dottedEdgeText` | the start half of a dotted link | the end half of that link |
| `click` | `click` and one space | the target id |
| `callbackname` | `call` and spaces | `(` |
| `callbackargs` | `(` inside `callbackname` | `)` |
| `shapeData` | `@{` | `}` |
| `shapeDataStr` | `"` inside `shapeData` | `"` inside the mode |

- flowchart-016: The modes `vertex`, `href`, and `shapeDataEndBracket` MUST NOT exist, because no authority rule enters them. [just go-check]
- flowchart-017: Within a mode, the lexer MUST take the first rule that matches at the current byte, in the order of the tables below, and MUST NOT prefer the longer match of a later rule; a word literal MUST end at a word boundary, as Jison adds to quoted word patterns, so a keyword MUST NOT match the prefix of a longer identifier. [just parity]
- flowchart-018: The lexer MUST NOT panic on any input, and a byte that no rule of the mode matches MUST raise `flowchart/unexpected-token`. [just go-check]
- flowchart-019: The lexer MUST read the repaired UTF-8 text of `spec/source-and-positions.md`, and a token MUST carry the span of every byte that its rule consumed, whitespace included. [just go-check]

### Lexical rules of `INITIAL`

A rule whose authority pattern starts with `.*` MUST match from the current byte, as the JavaScript regular expression does, not from the start of the line.

| Order | Pattern | Token | Mode change |
|---|---|---|---|
| 31 | `accTitle` `\s*` `:` `\s*` | `acc_title` | push `acc_title` |
| 33 | `accDescr` `\s*` `:` `\s*` | `acc_descr` | push `acc_descr` |
| 35 | `accDescr` `\s*` `{` `\s*` | none | push `acc_descr_multiline` |
| 41 | `@{` | `SHAPE_DATA` | push `shapeData`, with token text empty |
| 74 | `call` and one or more spaces | none | push `callbackname` |
| 84 | `"` then `` ` `` | none | push `md_string` |
| 87 | `"` | none | push `string` |
| 88 | `style` | `STYLE` | none |
| 89 | `default` | `DEFAULT` | none |
| 90 | `linkStyle` | `LINKSTYLE` | none |
| 91 | `interpolate` | `INTERPOLATE` | none |
| 92 | `classDef` | `CLASSDEF` | none |
| 93 | `class` | `CLASS` | none |
| 103 | `href` and one whitespace byte | `HREF` | none |
| 112 | `click` and one or more spaces | none | push `click` |
| 116 | `flowchart-elk` | `GRAPH` | push `dir` when this is the first `GRAPH` |
| 118 | `graph` | `GRAPH` | push `dir` when this is the first `GRAPH` |
| 119 | `flowchart` | `GRAPH` | push `dir` when this is the first `GRAPH` |
| 120 | `subgraph` | `subgraph` | none |
| 121 | `end` at a word boundary, then spaces | `end` | none |
| 123 | `_self` | `LINK_TARGET` | none |
| 124 | `_blank` | `LINK_TARGET` | none |
| 125 | `_parent` | `LINK_TARGET` | none |
| 126 | `_top` | `LINK_TARGET` | none |
| 140 | `.*direction\s+TB[^\n]*` | `direction_tb` | none |
| 141 | `.*direction\s+BT[^\n]*` | `direction_bt` | none |
| 142 | `.*direction\s+RL[^\n]*` | `direction_rl` | none |
| 143 | `.*direction\s+LR[^\n]*` | `direction_lr` | none |
| 144 | `.*direction\s+TD[^\n]*` | `direction_td` | none |
| 146 | one or more bytes of `[^\s"\[\]\(\)\{\}\|]`, then `@`, then a byte other than `{` and `"` | `LINK_ID` | none |
| 147 | `[0-9]+` | `NUM` | none |
| 148 | `#` | `BRKT` | none |
| 149 | `:::` | `STYLE_SEPARATOR` | none |
| 150 | `:` | `COLON` | none |
| 151 | `&` | `AMP` | none |
| 152 | `;` | `SEMI` | none |
| 153 | `,` | `COMMA` | none |
| 154 | `*` | `MULT` | none |
| 156 | `\s*` `[xo<]?` `--+` `[-xo>]` `\s*` | `LINK` | pop the edge mode |
| 157 | `\s*` `[xo<]?` `--` `\s*` | `START_LINK` | push `edgeText` |
| 160 | `\s*` `[xo<]?` `==+` `[=xo>]` `\s*` | `LINK` | pop the edge mode |
| 161 | `\s*` `[xo<]?` `==` `\s*` | `START_LINK` | push `thickEdgeText` |
| 164 | `\s*` `[xo<]?` `-?` `.` `+` `-[xo>]?` `\s*` | `LINK` | pop the edge mode |
| 165 | `\s*` `[xo<]?` `-.` `\s*` | `START_LINK` | push `dottedEdgeText` |
| 169 | `\s*` `~~` `~+` `\s*` | `LINK` | none |
| 173 | `(-` | `ELLIPSE_START` | push `ellipseText` |
| 176 | `([` | `STADIUMSTART` | push `text` |
| 179 | `[[` | `SUBROUTINESTART` | push `text` |
| 181 | `[\|` | `VERTEX_WITH_PROPS_START` | none |
| 183 | `>` | `TAGEND` | push `text` |
| 186 | `[(` | `CYLINDERSTART` | push `text` |
| 189 | `(((` | `DOUBLECIRCLESTART` | push `text` |
| 194 | `[/` | `TRAPSTART` | push `trapText` |
| 196 | `[\` | `INVTRAPSTART` | push `trapText` |
| 199 | `<` | `TAGSTART` | none |
| 200 | `>` | `TAGEND` | none |
| 201 | `^` | `UP` | none |
| 203 | `v` | `DOWN` | none |
| 207 | one or more bytes of `[A-Za-z0-9!"#$%&'*+.\x60?\\_/]`, of `-` that is not followed by `>`, `-`, or `.`, or of `=` that is not followed by `=` | `NODE_STRING` | none |
| 210 | `-` | `MINUS` | none |
| 211 | the Unicode letter ranges of authority lines 211 to 272 | `UNICODE_TEXT` | none |
| 275 | `\|` | `PIPE` | push `text` |
| 278 | `(` | `PS` | push `text` |
| 281 | `[` | `SQS` | push `text` |
| 284 | `{` | `DIAMOND_START` | push `text` |
| 288 | one or more line ends | `NEWLINE` | none |
| 289 | one or more bytes of `[^\S\n\r]` | `SPACE` | none |
| 290 | the end of the input | `EOF` | none |

- flowchart-020: The `\|` row MUST be authority line 275 and MUST NOT be line 202, because line 202 returns `SEP`, which no production consumes, while line 275 returns `PIPE` and pushes `text` for the edge label form `-->|label|` and the `rect` form `[\|k:v\|label]`. [just oracle]
- flowchart-021: The rules at authority lines 204, 205, and 206 MUST NOT be implemented, because lines 154, 148, and 151 match the same bytes first. [just go-check]
- flowchart-022: The `UNICODE_TEXT` rule MUST use the ranges of authority lines 211 to 272 unchanged, and MUST NOT be replaced by a Unicode general-category test. [just parity]
- flowchart-023: The `"` rule MUST push `string` and return no token, because no production consumes a quote token and the string mode supplies `STR`. [just parity]
- flowchart-024: A `dir` mode rule MUST be one row of the table below, and the first match MUST leave the mode. [just go-check]

| Order | Pattern | Token |
|---|---|---|
| 128 | line ends, then `\s*` and a line end | `NODIR` |
| 129 | `\s*LR` | `DIR` |
| 130 | `\s*RL` | `DIR` |
| 131 | `\s*TB` | `DIR` |
| 132 | `\s*BT` | `DIR` |
| 133 | `\s*TD` | `DIR` |
| 134 | `\s*BR` | `DIR` |
| 135 | `\s*<` | `DIR` |
| 136 | `\s*>` | `DIR` |
| 137 | `\s*^` | `DIR` |
| 138 | `\s*v` | `DIR` |

### Lexical rules of the text and shape modes

- flowchart-025: The modes `text`, `ellipseText`, and `trapText` MUST use the rules of the table below in this order, and a closer rule MUST leave its mode. [just parity]

| Order | Mode | Pattern | Token |
|---|---|---|---|
| 171 | `ellipseText` | `-` or `/`, then `)` | `ELLIPSE_END` |
| 172 | `ellipseText` | one or more bytes other than `(`, `)`, `[`, `]`, `{`, `}`, and a `-!)` run | `TEXT` |
| 175 | `text` | `])` | `STADIUMEND` |
| 178 | `text` | `]]` | `SUBROUTINEEND` |
| 185 | `text` | `)]` | `CYLINDEREND` |
| 188 | `text` | `)))` | `DOUBLECIRCLEEND` |
| 191 | `trapText` | `\]` or `]` | `TRAPEND` |
| 192 | `trapText` | `/]` | `INVTRAPEND` |
| 193 | `trapText` | one or more bytes other than `\`, `[`, `]`, `(`, `)`, `{`, `}`, and `/`, where a lone `\` or `/` that starts no closer is text | `TEXT` |
| 274 | `text` | `\|` | `PIPE`, then leave the mode |
| 277 | `text` | `)` | `PE`, then leave the mode |
| 280 | `text` | `]` | `SQE`, then leave the mode |
| 283 | `text` | `}` | `DIAMOND_STOP`, then leave the mode |
| 285 | `text` | one or more bytes other than `[`, `]`, `(`, `)`, `{`, `}`, `\|`, and `"` | `TEXT` |

- flowchart-026: The `<*>` rules of authority lines 174 to 284 MUST apply in every mode, and each of them MUST push `text` beside its token, so a bracket pair inside a label opens a nested `text` mode. [just parity]

### Lexical rules of the string, edge, and interaction modes

- flowchart-027: The string and interaction modes MUST use the rules of the table below, and a string token MUST NOT hold its delimiters. [just parity]

| Order | Mode | Pattern | Token | Mode change |
|---|---|---|---|---|
| 32 | `acc_title` | text up to a line end, `;`, or `#` | `acc_title_value` | leave the mode |
| 34 | `acc_descr` | text up to a line end, `;`, or `#` | `acc_descr_value` | leave the mode |
| 36 | `acc_descr_multiline` | `}` | none | leave the mode |
| 37 | `acc_descr_multiline` | bytes other than `}` | `acc_descr_multiline_value` | none |
| 75 | `callbackname` | `(`, spaces, `)` | none | leave the mode |
| 76 | `callbackname` | `(` | none | leave the mode and push `callbackargs` |
| 77 | `callbackname` | bytes other than `(` | `CALLBACKNAME` | none |
| 78 | `callbackargs` | `)` | none | leave the mode |
| 79 | `callbackargs` | bytes other than `)` | `CALLBACKARGS` | none |
| 82 | `md_string` | one or more bytes other than `` ` `` and `"` | `MD_STR` | none |
| 83 | `md_string` | `` ` `` then `"` | none | leave the mode |
| 85 | `string` | one or more bytes other than `"` | `STR` | none |
| 86 | `string` | `"` | none | leave the mode |
| 113 | `click` | one whitespace byte | none | leave the mode |
| 114 | `click` | bytes other than whitespace | `CLICK` | none |
| 158 | `edgeText` | one byte other than `-`, or `-` not followed by `-` | `EDGE_TEXT` | none |
| 162 | `thickEdgeText` | one byte other than `=`, or `=` not followed by `=` | `EDGE_TEXT` | none |
| 166 | `dottedEdgeText` | one byte other than `.`, or `.` not followed by `-` | `EDGE_TEXT` | none |

- flowchart-028: The shape-data modes MUST use the rules of the table below. [just parity]

| Order | Mode | Pattern | Token | Mode change |
|---|---|---|---|---|
| 44 | `shapeData` | `"` | `SHAPE_DATA` | push `shapeDataStr` |
| 49 | `shapeDataStr` | `"` | `SHAPE_DATA` | leave the mode |
| 52 | `shapeDataStr` | one or more bytes other than `"` | `SHAPE_DATA` | replace each line end and the spaces after it with `<br/>` |
| 57 | `shapeData` | one or more bytes other than `}`, `^`, and `"` | `SHAPE_DATA` | none |
| 61 | `shapeData` | `}` | none | leave the mode |

- flowchart-029: A quoted edge text MUST be accepted between the two halves of a link, and `MD_STR` MUST set the label type `markdown`, `STR` MUST set `string`, and a bare text run MUST set `text`. [just parity]

## Tokens

- flowchart-030: The token set MUST be exactly this list: `GRAPH`, `NODIR`, `DIR`, `direction_tb`, `direction_bt`, `direction_rl`, `direction_lr`, `direction_td`, `subgraph`, `end`, `LINK_TARGET`, `LINK_ID`, `LINK`, `START_LINK`, `EDGE_TEXT`, `TEXT`, `STR`, `MD_STR`, `SHAPE_DATA`, `NUM`, `BRKT`, `STYLE_SEPARATOR`, `COLON`, `AMP`, `SEMI`, `COMMA`, `MULT`, `MINUS`, `PS`, `PE`, `SQS`, `SQE`, `DIAMOND_START`, `DIAMOND_STOP`, `TAGSTART`, `TAGEND`, `UP`, `DOWN`, `PIPE`, `ELLIPSE_START`, `ELLIPSE_END`, `STADIUMSTART`, `STADIUMEND`, `SUBROUTINESTART`, `SUBROUTINEEND`, `CYLINDERSTART`, `CYLINDEREND`, `DOUBLECIRCLESTART`, `DOUBLECIRCLEEND`, `TRAPSTART`, `INVTRAPSTART`, `TRAPEND`, `INVTRAPEND`, `VERTEX_WITH_PROPS_START`, `STYLE`, `DEFAULT`, `LINKSTYLE`, `INTERPOLATE`, `CLASSDEF`, `CLASS`, `HREF`, `CLICK`, `CALLBACKNAME`, `CALLBACKARGS`, `acc_title`, `acc_title_value`, `acc_descr`, `acc_descr_value`, `acc_descr_multiline_value`, `NODE_STRING`, `UNICODE_TEXT`, `NEWLINE`, `SPACE`, `EOF`. [just parity]
- flowchart-031: The tokens `TESTSTR`, `QUOTE`, and `SEP` of the authority MUST NOT exist, because no production of the grammar consumes them. [just go-check]
- flowchart-032: The token name `ELLIPSE_START` MUST stand for the authority literal `(-`, and `ELLIPSE_END` for `-)`. [just parity]
- flowchart-033: The `TOKEN` of an `flowchart/unexpected-token` message MUST be the source text of the offending token, and its accepted list MUST hold token names sorted bytewise and joined by `, `. [just go-check]

## Grammar

- flowchart-034: The parser MUST be hand-written recursive descent over the grammar of this block, and MUST NOT backtrack over a consumed token. [just parity]
- flowchart-035: `SP` in this block MUST mean one or more bytes of `[^\S\n\r]`, and a `SP` at the end of a statement MUST NOT change the statement. [just go-check]

```
document        = header , { statement | SP } , [ EOF ] ;
header          = GRAPH , [ SP , direction ] , header-end ;
header-end      = NEWLINE | SEMI | EOF ;
direction       = DIR | direction_tb | direction_bt | direction_rl | direction_lr | direction_td ;

statement       = vertex-statement , separator
                | style-statement , separator
                | class-def-statement , separator
                | class-statement , separator
                | link-style-statement , separator
                | click-statement , separator
                | subgraph-statement
                | direction-statement , separator
                | acc-title , separator
                | acc-descr , separator
                | acc-descr-block , separator ;
separator       = NEWLINE | SEMI | EOF ;

vertex-statement = node-group , { link , node-group } , [ SP ] ;
node-group      = styled-node , { [ SP ] , AMP , [ SP ] , styled-node } ;
styled-node     = node , [ STYLE_SEPARATOR , id-string ] , [ shape-data ] ;
node            = id-string , [ label ] ;
label           = SQS , text , SQE
                | PS , text , PE
                | PS , PS , text , PE , PE
                | DOUBLECIRCLESTART , text , DOUBLECIRCLEEND
                | ELLIPSE_START , text , ELLIPSE_END
                | STADIUMSTART , text , STADIUMEND
                | SUBROUTINESTART , text , SUBROUTINEEND
                | VERTEX_WITH_PROPS_START , NODE_STRING , COLON , NODE_STRING , PIPE , text , SQE
                | CYLINDERSTART , text , CYLINDEREND
                | DIAMOND_START , text , DIAMOND_STOP
                | DIAMOND_START , DIAMOND_START , text , DIAMOND_STOP , DIAMOND_STOP
                | TAGEND , text , SQE
                | TRAPSTART , text , TRAPEND
                | INVTRAPSTART , text , INVTRAPEND
                | TRAPSTART , text , INVTRAPEND
                | INVTRAPSTART , text , TRAPEND ;

link            = link-statement , [ arrow-text ] ;
link-statement  = [ LINK_ID ] , LINK
                | [ LINK_ID ] , START_LINK , [ edge-text ] , LINK ;
arrow-text      = PIPE , text , PIPE ;
edge-text       = EDGE_TEXT , { EDGE_TEXT }
                | STR , { EDGE_TEXT }
                | MD_STR , { EDGE_TEXT } ;
text            = text-token , { text-token }
                | STR , { text-token }
                | MD_STR , { text-token } ;
text-token      = TEXT | TAGSTART | TAGEND | UNICODE_TEXT ;
text-no-tags    = text-no-tags-token , { text-no-tags-token }
                | STR , { text-no-tags-token }
                | MD_STR , { text-no-tags-token } ;
text-no-tags-token = NUM | NODE_STRING | SPACE | MINUS | AMP | UNICODE_TEXT | COLON | MULT | BRKT
                | STYLE | LINKSTYLE | CLASSDEF | CLASS | CLICK | DOWN | UP | subgraph | end
                | GRAPH | DIR | direction_tb | direction_bt | direction_rl | direction_lr
                | direction_td | START_LINK ;

subgraph-statement = subgraph , SP , text-no-tags , SQS , text , SQE , separator , body , end
                | subgraph , SP , text-no-tags , separator , body , end
                | subgraph , separator , body , end ;
body            = { statement } ;

style-statement      = STYLE , SP , id-string , SP , styles-opt ;
class-def-statement  = CLASSDEF , SP , id-string , SP , styles-opt ;
class-statement      = CLASS , SP , id-string , SP , id-string ;
link-style-statement = LINKSTYLE , SP , link-selector , SP , styles-opt
                | LINKSTYLE , SP , link-selector , SP , INTERPOLATE , SP , alpha-num , [ SP , styles-opt ] ;
link-selector   = DEFAULT | num-list ;
num-list        = NUM , { COMMA , NUM } ;
styles-opt      = style , { COMMA , style } ;
style           = style-component , { style-component } ;
style-component = NUM | NODE_STRING | COLON | SPACE | BRKT | STYLE ;

click-statement = CLICK , click-action ;
click-action    = call-action | plain-call-action | link-action ;
call-action     = CALLBACKNAME , [ CALLBACKARGS ] , [ SP , STR ] ;
plain-call-action = alpha-num , [ SP , STR ] ;
link-action     = [ HREF ] , STR , [ SP , STR ] , [ SP , LINK_TARGET ] ;

direction-statement = direction_tb | direction_bt | direction_rl | direction_lr | direction_td ;
acc-title       = acc_title , acc_title_value ;
acc-descr       = acc_descr , acc_descr_value ;
acc-descr-block = acc_descr_multiline_value ;

id-string       = id-string-token , { id-string-token } ;
id-string-token = NUM | NODE_STRING | DOWN | MINUS | DEFAULT | COMMA | COLON | AMP | BRKT | MULT
                | UNICODE_TEXT ;
alpha-num       = alpha-num-token , { alpha-num-token } ;
alpha-num-token = NUM | UNICODE_TEXT | NODE_STRING | DIR | DOWN | MINUS | COMMA | COLON | AMP
                | BRKT | MULT ;
shape-data      = SHAPE_DATA , { SHAPE_DATA } ;
```

- flowchart-036: The `CLICK` token MUST hold the target id of its `click` statement, and every `click` statement MUST hold one of the three actions of the grammar. [just parity]
- flowchart-037: A `click` action MUST accept the four callback forms `CLICK CALLBACKNAME`, `CLICK CALLBACKNAME SP STR`, `CLICK CALLBACKNAME CALLBACKARGS`, and `CLICK CALLBACKNAME CALLBACKARGS SP STR`. [just parity]
- flowchart-038: A `click` action MUST accept the four link forms of `CLICK STR`, `CLICK STR SP STR`, `CLICK STR SP LINK_TARGET`, and `CLICK STR SP STR SP LINK_TARGET`, and the same four forms with `HREF` before the first `STR`. [just parity]
- flowchart-039: A `click` action MUST accept the two plain callback forms `CLICK alpha-num` and `CLICK alpha-num SP STR`. [just parity]
- flowchart-040: A callback MUST accept an optional quoted tooltip, also after an argument list, and a `click` statement that holds a link target after a callback, with or without a tooltip, MUST raise `flowchart/click-call-extra-text` (error) at the target token. [just oracle]
- flowchart-041: The parser MUST accept the spaces around `&` as optional, and MUST accept a shape-data block between a node and a following `&` or link. [just parity]
- flowchart-042: The parser MUST accept a vertex statement that is one node with no label, and that node MUST take its id as its label text. [just parity]
- flowchart-043: The parser MUST accept a chain of links of any length, and a `&` group on either side of a link MUST produce one edge for each pair of a last start node and a first end node. [just oracle]
- flowchart-044: The parser MUST accept a `:::` shorthand after a node and before its shape data, and the class name MUST be the `id-string` that follows it. [just parity]
- flowchart-045: The parser MUST accept the three `subgraph` forms of the grammar, and a `subgraph` inside the body of another MUST be a member of the outer one. [just oracle]
- flowchart-046: A `direction` statement MUST be recognised only at a statement start, and its span MUST run from the first byte of the match to the end of that line, which is the greedy `.*` match of authority rules 140 to 144. [just parity]
- flowchart-047: A statement MUST end at a line end, at `;`, or at the end of the input, and a run of spaces alone MUST be an accepted line. [just oracle]
- flowchart-048: The parser MUST record each statement of the body in source order, and a subgraph body MUST be recorded as the member statements of that subgraph. [just parity]

## Statement boundary

- flowchart-049: The statement boundary MUST be the first `;` or line end that lies outside a string, a shape bracket pair, a `PIPE` label, and a shape-data block. [just go-check]
- flowchart-050: The recovery point of an `flowchart/unexpected-token` and of an `flowchart/unknown-statement` MUST be the next statement boundary at bracket depth 0. [just go-check]
- flowchart-051: The bracket depth MUST count `[`, `(`, `{`, `((`, `[[`, `([`, `[(`, and `{{` as openings and their matching closers as closings, and an unclosed string MUST hold the depth at its value until the end of the input. [just go-check]
- flowchart-052: Recovery MUST NOT create a node, an edge, or a group, and the statement after the boundary MUST be parsed as if the failing statement were absent. [just oracle]

## Abstract syntax tree

- flowchart-053: Each tree node MUST take the name of its authority rule in PascalCase, and the Go and Rust types MUST use the same name. [just parity]
- flowchart-054: Each tree node MUST carry the span of its first token to the end of its last token, with no trailing separator, as the table below states. [just parity]

| Node | Authority rule | Span |
|---|---|---|
| `Start` | `start` | the whole input |
| `GraphConfig` | `graphConfig` | the header keyword to the end of the direction, or to the end of the keyword |
| `Document` | `document` | the first byte of the first statement to the end of the last one |
| `Line` | `line` | the statement it holds |
| `VertexStatement` | `vertexStatement` | the first styled node to the last node group |
| `Node` | `node` | the first id byte to the end of the group |
| `StyledVertex` | `styledVertex` | the id byte to the end of the class name or the shape data |
| `Vertex` | `vertex` | the id byte to the end of the closing bracket |
| `Link` | `link` | the first byte of the link id or the start half to the end of the arrow text |
| `LinkStatement` | `linkStatement` | the link id to the end half |
| `ArrowText` | `arrowText` | the first `\|` to the second `\|` |
| `EdgeText` | `edgeText` | the first text byte to the last one |
| `ShapeData` | `shapeData` | the `@{` to the closing `}` |
| `Subgraph` | the `subgraph` alternative of `statement` | the `subgraph` keyword to the closing `end` |
| `StyleStatement` | `styleStatement` | the keyword to the last style component |
| `ClassDefStatement` | `classDefStatement` | the keyword to the last style component |
| `ClassStatement` | `classStatement` | the keyword to the end of the class name |
| `LinkStyleStatement` | `linkStyleStatement` | the keyword to the last style component or the interpolation name |
| `ClickStatement` | `clickStatement` | the `click` keyword to the last member |
| `NumList` | `numList` | the first number to the last number |
| `StylesOpt` | `stylesOpt` | the first style byte to the last one |
| `Style` | `style` | the first component to the last component |
| `Direction` | `direction` | the keyword that follows `direction` |
| `AccTitle` | the `acc_title` alternative of `statement` | the `accTitle` keyword to the end of the value |
| `AccDescr` | the `acc_descr` alternative of `statement` | the `accDescr` keyword to the end of the value |
| `AccDescrBlock` | the `acc_descr_multiline_value` alternative of `statement` | the `accDescr` keyword to the closing `}` |
| `IdString` | `idString` | the first token byte to the last token byte |
| `Text` | `text` | the first token byte to the last token byte |
| `TextNoTags` | `textNoTags` | the first token byte to the last token byte |
| `AlphaNum` | `alphaNum` | the first token byte to the last token byte |

- flowchart-055: A string token MUST store its content without its delimiters, and its span MUST include them. [just parity]
- flowchart-056: The tree MUST keep, for each link, its start half, its end half, its edge text with its label type, and its link id. [just parity]

## Semantic resolution

- flowchart-057: A node MUST be created at its first mention, with or without a label, and its declaration index MUST be the order of that first mention in the model. [just parity]
- flowchart-058: A later label on a declared node MUST replace the earlier text, and a later statement with no label MUST keep the text and the shape that the node holds. [just parity]
- flowchart-059: A node MUST carry the shape id of its bracket pair, as the table below states. [just parity]

| Opening | Closing | Authority vertex type | Shape id |
|---|---|---|---|
| `[` | `]` | `square` | `squareRect` |
| `(` | `)` | `round` | `roundedRect` |
| `((` | `))` | `circle` | `circle` |
| `(((` | `)))` | `doublecircle` | `doublecircle` |
| `([` | `])` | `stadium` | `stadium` |
| `[[` | `]]` | `subroutine` | `subroutine` |
| `[\|key:value\|` | `]` | `rect` | `rect` |
| `[(` | `)]` | `cylinder` | `cylinder` |
| `{` | `}` | `diamond` | `diamond` |
| `{{` | `}}` | `hexagon` | `hexagon` |
| `>` | `]` | `odd` | `odd` |
| `[/` | `\]` | `trapezoid` | `trapezoid` |
| `[\` | `/]` | `inv_trapezoid` | `inv_trapezoid` |
| `[/` | `/]` | `lean_right` | `lean_right` |
| `[\` | `\]` | `lean_left` | `lean_left` |
| `(-` | `-)` | `ellipse` | `ellipse` |

- flowchart-060: A node with no bracket pair MUST take the shape id `squareRect`, which is the authority result for the `square` type and for an absent type. [just parity]
- flowchart-061: The label text of a node or an edge MUST be trimmed, and one surrounding pair of `"` MUST be removed when the text starts and ends with that byte. [just parity]
- flowchart-062: The model stage MUST decode `#name;` and `#N;` in label text by the entity rule of `spec/preprocessing.md`, and MUST NOT decode the values of `style`, `classDef`, or `linkStyle`. [just oracle]
- flowchart-063: The model stage MUST replace a line end and the spaces after it inside a quoted shape-data value with `<br/>`, and MUST keep the line ends of a block scalar unchanged. [just parity]
- flowchart-064: The model stage MUST read a shape-data body as a config mapping: a body with no line end MUST be wrapped in `{` and `}` and read by the flow-mapping rule, and a body with a line end MUST be read as a block mapping. [just parity]
- flowchart-065: A shape-data body that fails to parse MUST raise `config/malformed` (error) at the failing byte, and the statement MUST change no node. [just go-check]
- flowchart-066: The model MUST honour the shape-data keys `shape`, `label`, `labelType`, `icon`, `form`, `pos`, `img`, `constraint`, `w`, and `h` on a node, the keys `curve`, `animate`, `animation`, and `step` on an edge, and the key `view` on a subgraph, and MUST ignore every other key with no diagnostic. [just parity]
- flowchart-067: A shape-data block whose id names a declared edge MUST apply its edge keys to that edge and MUST NOT create a node. [just oracle]
- flowchart-068: A `shape` value MUST hold only lowercase ASCII letters, digits, and `-`, and MUST resolve to a shape id of `spec/data/shapes.json` by that id or by an alias of that row. [just gen-check]
- flowchart-069: A `shape` value that resolves to no id, or that holds `_` or an uppercase letter, MUST raise `flowchart/typed-shape-unsupported` (error) at the value token. [just go-check]
- flowchart-070: A node whose shape data holds `img` MUST take the shape id `imageSquare`, and a node with `icon` MUST take `iconCircle`, `iconSquare`, or `iconRounded` from its `form` value, and otherwise `icon`. [just parity]
- flowchart-071: An edge MUST be created for each pair of a last start node and a first end node, and its declaration index MUST be the order of creation in the model. [just parity]
- flowchart-072: The edge stroke and the marker names MUST follow the table below, and a missing marker MUST be `none` in the model. [just parity]

| Half token | Stroke | Marker |
|---|---|---|
| a half with no marker byte | `normal` | `none` |
| `==` | `thick` | `none` |
| `-.` or a run of dots | `dotted` | `none` |
| `~~~` | `invisible` | `none` |
| final `>` | the stroke of the half | `point` at the end |
| final `x` | the stroke of the half | `cross` at the end |
| final `o` | the stroke of the half | `circle` at the end |
| first `<` | the stroke of the half | `point` at the start |
| first `x` | the stroke of the half | `cross` at the start |
| first `o` | the stroke of the half | `circle` at the start |

- flowchart-073: The edge length MUST be the count of stroke bytes of the end half less one, MUST be the count of dots for a dotted half, and MUST be clamped to 10. [just parity]
- flowchart-074: A start half whose stroke differs from the end half, or whose marker type differs from the end type while it is not open, MUST give an edge with no start marker and no end marker, and the stroke and the length MUST come from the end half. [just parity]
- flowchart-075: The dump id of a route MUST be `e` and its decimal declaration index, and the dump id of its label MUST be that id followed by `.label`, which the golden dump fixes. [just validate]
- flowchart-076: A link id of the source MUST be kept in the model beside the dump id, and of a `&` group only the pair of the last start node and the first end node MUST keep it. [just parity]
- flowchart-077: A subgraph MUST become a group box and MUST keep the distinct node ids of its body in body order; a member that a subgraph completed earlier already holds MUST be dropped from the subgraph that completes later, so a nested subgraph claims its members before its enclosing subgraph; upstream `addSubGraph` and `makeUniq` decide this by completion order. [just oracle]
- flowchart-078: A repeated subgraph id MUST merge its members into the first declaration, which keeps the title and the direction of that first one. [just parity]
- flowchart-079: A subgraph id MUST be the `text-no-tags` of its header when that text holds no space, and otherwise `subGraph` and the 0-based index of the declaration among all subgraph declarations, repeated ids counted; quotes delimit the text and MUST NOT stay in the id or the title. [just parity]
- flowchart-080: A subgraph title MUST be the bracketed text when the header holds brackets, otherwise the `text-no-tags` of the header, and it MUST be empty for the form with no text. [just parity]
- flowchart-081: The direction of a subgraph MUST be the last `direction` statement of its body, and it MUST be absent when the body holds none. [just parity]
- flowchart-082: `style` MUST append its declarations to the styles of every named node, and a name that no node declares MUST still create the node. [just parity]
- flowchart-083: `classDef` MUST define a class for each name of its comma list, and `class` and `:::` MUST append the class name to every node of their id list. [just parity]
- flowchart-084: `linkStyle` MUST apply its styles to the edges of its index list, or to every edge for `default`, and it MUST set the interpolation name when `interpolate` is present. [just parity]
- flowchart-085: A `click` link whose scheme is `http`, `https`, or `mailto` MUST reach the scene as an `<a>` element, and any other scheme MUST raise `interaction/unsafe-url` (warning) and MUST NOT emit a link. [just go-check]
- flowchart-086: A `click` callback MUST be recorded, MUST NOT run, and MUST raise `interaction/callback-ignored` (info). [just go-check]
- flowchart-087: `accTitle` MUST set the accessible title of the block, and `accDescr` and its block form MUST set the accessible description. [just go-check]
- flowchart-088: The model MUST keep the resolved graph direction of the header, and a subgraph direction MUST NOT change it. [just validate]
- flowchart-089: The model stage MUST set the `direction` option of the dump to `TB`, `BT`, `LR`, or `RL`, and MUST NOT write any other value. [just validate]

## Diagnostics

- flowchart-090: A code of this kind MUST be raised by the parser when the authority fails to parse its input, by a model check when the authority parses the input and then throws, and by a lint rule otherwise. [just oracle]
- flowchart-091: The rows of `spec/data/diagnostics/flowchart.json` MUST be exactly the five rows of the table below, with the same severity, summary, and span, and that file MUST NOT hold any other code. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `flowchart/unexpected-token` | error | parser | a byte of the current mode is accepted by no rule | the offending token | `unexpected TOKEN, expected one of: LIST` |
| `flowchart/unknown-statement` | error | parser | a statement starts with a token that starts no statement form | the first token to the statement boundary | `unknown statement TOKEN` |
| `flowchart/unterminated` | error | parser | the input ends inside a string, a shape bracket pair, a shape-data block, or a subgraph body | the opening delimiter to the end of the input | `unterminated TOKEN` |
| `flowchart/unclosed-node-bracket` | error | parser | a node bracket pair is never closed before the end of its statement or of the input | the opening bracket to the end of that statement | `node bracket TOKEN is never closed` |
| `flowchart/subgraph-direction-ignored` | warning | model check | a subgraph with a `direction` statement has an edge that crosses its boundary | the `direction` statement | `subgraph direction is ignored because an edge crosses its boundary` |

- flowchart-092: `flowchart/unclosed-node-bracket` MUST be recorded alone when `flowchart/unterminated` also fits, and its row MUST carry the alias `flowchart/node-unclosed-bracket`. [just gen-check]
- flowchart-093: `flowchart/subgraph-direction-ignored` MUST be raised by the layout stage only, so `check` and `lint` MUST NOT print it. [just parity]
- flowchart-094: A code whose row sits in `spec/data/lint-rules/flowchart.json` MUST keep that single row, and this kind MUST NOT hold a second row for it under `spec/data/diagnostics/`. [just gen-check]
- flowchart-095: The parser and the model checks of this kind MUST raise the codes of the table below under the code of their existing row in `spec/data/lint-rules/flowchart.json`. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `flowchart/arrow-invalid` | error | parser | one `-` or one `=` stands where a link half belongs, as in `A -> B` | the arrow bytes | `A single arrow -> is used in a flowchart` |
| `flowchart/link-unsupported-marker` | error | parser | a link half holds a marker byte on one side only, as in `--x-->` | the link | `An inline link uses a one-sided end marker, such as --x--> or --o-->` |
| `flowchart/label-double-in-double` | error | parser | a double-quoted label holds a second `"`, so the run after it mixes a string and plain text | the inner quote | `A double-quoted label contains another double quote` |
| `flowchart/label-double-in-single` | error | parser | a single-quoted label holds an unescaped `"` | the quote | `A single-quoted label contains an unescaped double quote` |
| `flowchart/label-escaped-quote` | error | parser | a bracket label holds a backslash before a quote inside a string token | the escape | `A node label contains a backslash-escaped quote, which Mermaid does not support` |
| `flowchart/label-quote-in-unquoted` | error | parser | a bracket label that starts with no `"` holds one after plain text | the quote | `A double quote appears inside an unquoted label` |
| `flowchart/label-parens-unquoted` | error | parser | a bracket label that starts with no `"` holds a `(` or `)` that the text run cannot cover | the parenthesis | `An unquoted label contains an opening or closing parenthesis` |
| `flowchart/dir-invalid` | error | parser | a token other than a direction keyword or `NODIR` stands where the direction belongs, as in `flowchart XY` or `flowchart BR` | the direction token | `The direction token after the header is not one of TD, TB, BT, RL, LR` |
| `flowchart/dir-kw-invalid` | error | parser | a node string other than a direction keyword precedes the direction keyword before the first line end | the word | `An unknown keyword appears before the direction token` |
| `flowchart/link-missing` | error | parser | two nodes stand on one line with no link between them | the second node | `Two nodes appear on one line without a connecting arrow` |
| `flowchart/meta-unsupported` | error | parser | a `title`, `author`, or other meta statement stands in the body | that statement | `A meta statement such as title appears in a flowchart` |
| `flowchart/end-without-subgraph` | error | parser | an `end` keyword arrives while no subgraph is open | the `end` keyword | `end appears without a matching subgraph` |
| `flowchart/node-mixed-brackets` | error | parser | a closer does not match the open bracket, as in `A[text)` | the closer | `The opening and closing brackets of a node shape do not match` |
| `flowchart/node-empty` | error | parser | a bracket pair holds no text, as in `A[]`, so no text token exists | the bracket pair | `A node shape has empty content, such as A[]` |
| `flowchart/quote-unclosed` | error | parser | the input ends inside a `"` string or a `` "` `` markdown string | the opening quote to the end of the input | `A node label opens a quote but never closes it` |
| `flowchart/class-malformed` | error | parser | a `class` statement ends after its target id with no class name | the statement | `A class statement is missing node ids or the class name` |
| `flowchart/linkstyle-multiline` | error | parser | the style pairs of a `linkStyle` statement start on a later line | the first style byte | `The linkStyle style pairs are placed on a line after the indices` |
| `flowchart/linkstyle-range-not-supported` | error | parser | a `linkStyle` index list holds a colon | the colon | `A range such as 0:3 is used in the linkStyle index list` |
| `flowchart/click-call-extra-text` | error | parser | a tooltip follows an argument list, or a link target follows a callback | the first extra token | `A click call statement carries tooltip or target text after call fn()` |
| `flowchart/linkstyle-id-unknown` | error | model check | a `linkStyle` index is greater than or equal to the edge count, which makes the authority throw | the index | `linkStyle references an edge id that no link defines` |
| `flowchart/typed-shape-unsupported` | error | model check | a `shape` value resolves to no shape id, or holds `_` or an uppercase letter, which makes the authority throw | the value token | `A typed shape in an @{ shape: ... } node is not supported` |

- flowchart-096: The codes of the table below MUST be raised as lint rules over the resolved model, because the authority accepts the input that each one describes. [just oracle]

| Code | Severity | Trigger |
|---|---|---|
| `flowchart/duplicate-ids` | error | one node id is declared twice with different labels |
| `flowchart/prefer-flowchart` | warning | the header keyword is `graph` |
| `flowchart/require-direction` | warning | the header holds no direction |
| `flowchart/dir-missing` | error | the header holds no direction token |
| `flowchart/no-duplicate-edges` | warning | one pair of nodes carries two edges of one kind |
| `flowchart/no-self-loop` | warning | an edge starts and ends at one node |
| `flowchart/no-empty-labels` | warning | a node label is `""` or `" "` |
| `flowchart/no-orphan-nodes` | off | a node carries no edge |
| `flowchart/no-duplicate-node-declarations` | warning | one node id is declared twice with the same label |
| `flowchart/label-backtick` | error | a node label holds a backtick, which the text rules accept |
| `flowchart/class-target-unknown` | error | a `class` statement names a node id that the diagram does not declare |
| `flowchart/style-target-unknown` | error | a `style` statement names a node id that the diagram does not declare |
| `flowchart/subgraph-missing-header` | error | a `subgraph` statement holds no id and no title |
| `flowchart/edge-attr-id-unknown` | error | a shape-data block names an edge id that no link declares |

- flowchart-097: The codes `flowchart/click-target-not-found`, `flowchart/strict-label-quotes-required`, and `flowchart/node-unclosed-bracket` MUST NOT be raised, because their rows are `rejected` in `spec/data/lint-rules/flowchart.json`. [just gen-check]
- flowchart-098: A code that this file names and that holds no row in `spec/data/diagnostics/flowchart.json`, `spec/data/diagnostics/common.json`, or `spec/data/lint-rules/flowchart.json` MUST fail `gen-check`. [just gen-check]
- flowchart-099: Every diagnostic MUST carry the span of its row, and a diagnostic of severity error MUST make `check` exit 1. [just go-check]
- flowchart-100: The parser MUST raise `flowchart/dir-invalid` at the token after the header keyword when that token is neither a direction token of the `dir` mode nor `NODIR`, as in `flowchart XY`, and MUST raise no diagnostic when the header holds no direction at all. [just go-check]
- flowchart-101: A bracket label that holds plain text before a `"` MUST raise `flowchart/label-quote-in-unquoted` as a parser code, because the authority `text` production admits a plain run, or a string or markdown run followed by plain text, and never plain text before a string. [just oracle]
- flowchart-102: The Rust parser MUST be `syntax::flowchart`, module directory `crates/elegant-mermaid/src/syntax/flowchart/`, and it MUST hold the tree nodes of the table above under the same names. [just rust-check]
- flowchart-103: The Go parser MUST be `internal/syntax/flowchart`, with the fuzz target `FuzzFlowchart` beside the package. [just go-check]
- flowchart-104: The Go and Rust models MUST hold the same node list, edge list, and group list, in the same order, for the same source. [just parity]
- flowchart-105: The lexer MUST take the first matching rule of the current mode at the current byte, in the order of the rule tables of this file; jison without `%options flex` does the same. [just parity]
- flowchart-106: A rule that opens a quoted run MUST NOT apply inside the modes `string`, `md_string`, and `shapeDataStr`; each of those modes MUST apply its own closing rule first, and shape-data content MUST NOT change the state that joins string tokens. [just go-check]
- flowchart-107: Every flowchart diagnostic whose registry row has a `fix_safety` other than `none` MUST carry one fix with the title, safety, edit span, and replacement text that `TestDiagnosticFixContracts` and `flowchart_diagnostic_fix_contracts` state, equal in Go and Rust; a row with `fix_safety` `none` MUST carry no fix. [just parity]
- flowchart-108: A `click` link MUST wrap only the scene group of role `node` whose owner is its target id, as upstream sets `link` on vertices only: a target that is a subgraph MUST draw no anchor, and an empty tooltip MUST emit no `<title>`. Go and Rust MUST emit the same anchors. [just go-check: TestFlowchartClickOnASubgraphDrawsNoAnchor]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| `\|` outside a shape | Line 202 returns `SEP` and line 275 returns `PIPE` with `pushState("text")`; no production consumes `SEP` | `PIPE`, dead token `SEP`, `flowchart-020` |
| `"` outside a shape | Line 87 returns `QUOTE`; no production consumes it, and the `string` mode supplies `STR` | no token, dead token `QUOTE`, `flowchart-023` |
| Start condition `vertex`, `href`, `shapeDataEndBracket` | declared at lines 15, 23, and 28, entered by no rule | no mode, `flowchart-016` |
| `link: linkStatement TESTSTR SPACE` | `TESTSTR` is returned by no rule | alternative dropped, `flowchart-031` |
| Plain text before a string in a label | `text: textToken | text textToken | STR | MD_STR`, and `textToken` holds no `STR`; a double quote inside the attributes of an HTML tag in a plain label stays label text | `A["a"b]` parses, `A[foo"bar"]` fails, `A[<img src="x">]` parses, `flowchart-101` |
| A header keyword with no direction | `<dir>(\r?\n)*\s*\n` needs a line end, and the corpus holds `flowchart ` headers | `NODIR` also covers the end of the input, `flowchart-010` |
| `BR` as the direction | `<dir>\s*BR` returns `DIR` and `setDirection` leaves the word unresolved | accepted, resolved to `TB`, `flowchart-009` |
| A trap closer | Line 191 is the class `[\\(?=\])]` followed by `\]`, so one byte of that class then `]` closes | `\]` or `]`, `flowchart-025` |
| A vertex id | Ids are token sequences, not byte runs, so `odd-` is `NODE_STRING` `MINUS` `TAGEND` | `id-string`, `flowchart-042` |
| An edge half that mixes markers and strokes | `x-->` gives `INVALID` and no diagnostic, and `--x-->` lexes as two `LINK` tokens | no diagnostic for the first, `flowchart/link-unsupported-marker` for the second, `flowchart-074` |
