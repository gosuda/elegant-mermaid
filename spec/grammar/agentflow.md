# Agentflow grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `agentflow` kind.

## Scope

- agentflow-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/agentflow/parser/agentflow.jison:35-310` for lexing and `:322-670` for productions. [just oracle]
- agentflow-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/agentflow/agentflowDb.ts:347-560,728-869,902-942,1175-1309,1380-1407,1434-1586,1613-1662,1689-1694,1846-1908`; shape normalization MUST follow `shapes.ts:16-85,114-148` in that directory. [just oracle]
- agentflow-03: Layout inputs MUST follow `renderer.ts:17-60` in that directory and `schemas/config.schema.yaml:2434-2499`; shared preprocessing MUST precede this grammar. [just parity]

## Header forms

- agentflow-04: The header MUST be the case-sensitive keyword `agentflow-beta` with the shared keyword boundary. [just oracle]
- agentflow-05: The header MUST accept `LR`, `RL`, `TB`, `BT`, `TD`, `BR`, `<`, `>`, `^`, or `v`; an omitted direction MUST select `TB`. [just oracle]
- agentflow-06: Resolution MUST map `TD` and `v` to `TB`, `<` to `RL`, `>` to `LR`, and `^` to `BT`; `BR` MUST remain an authored direction token and use `TB` for canonical layout because the shared direction enum has no `BR`. [just parity]

## Lexer modes

- agentflow-07: The lexer MUST retain the authority mode names and MUST use the first matching active rule in source order. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| `INITIAL` | source start | a mode opener |
| `acc_title`, `acc_descr` | corresponding colon keyword | one line value |
| `acc_descr_multiline` | description brace | closing brace |
| `dir` | first header | direction or no-direction newline |
| `string` | double quote in any mode | double quote |
| `md_string` | double quote then backtick in any mode | backtick then double quote |
| `edgeText` | two or more opening hyphens | ending arrow |
| `text` | node or pipe opener | matching delimiter |
| `ellipseText` | `(-` | ellipse close |
| `trapText` | `[/` or `[\` | slanted close |
| `click` | click plus whitespace | whitespace after id |
| `callbackname` | call plus whitespace | opening argument parenthesis or empty arguments |
| `callbackargs` | nonempty argument opener | closing parenthesis |
| `shapeData` | `@{` | closing brace |
| `shapeDataStr` | quote in metadata | quote |
| `vertex`, `href`, `shapeDataEndBracket` | no active entry rule | unreachable |

### Lexical rules in first-match order

- agentflow-08: The lexer MUST apply the rows below in ascending authority-line order; an unqualified row MUST apply in `INITIAL`, and `*` MUST apply in every mode. [just parity]

| Authority lines | Pattern and modes | Result |
|---|---|---|
| 57-63 | accessibility colon openers, line values, description brace opener, closing brace, remaining description content | accessibility tokens; push or pop the named mode |
| 67-90 | `@{`; quote in shapeData; quote in shapeDataStr; nonquote string content; shapeData content excluding brace, caret, and quote; closing brace | SHAPE_DATA pieces; quoted newlines plus following whitespace become `<br/>`; closing brace emits nothing |
| 100-105 | call plus whitespace; empty parentheses; opening parenthesis; callback name; closing parenthesis; argument content | CALLBACKNAME or CALLBACKARGS; change modes |
| 108-113 | md_string content excluding backtick and quote; markdown close; global markdown opener; string nonquote content; string close; global quote opener | MD_STR or STR; delimiters emit nothing |
| 114-119 | style, default, linkStyle, interpolate, classDef, class | respective keyword token |
| 129 | href plus one whitespace | HREF |
| 138-140 | click plus whitespace; click whitespace; click nonwhitespace id | CLICK value; change mode |
| 142-151 | header; flow; connector; global with word boundary; end with word boundary; _self, _blank, _parent, _top | GRAPH, flow, connector, global, end, LINK_TARGET |
| 153-163 | dir newline; dir whitespace plus LR, RL, TB, BT, TD, BR, <, >, ^, v, in that order | NODIR or DIR; pop mode |
| 165-169 | whole-line prefix through direction TB, BT, RL, LR, TD, in that order | direction token |
| 171-179 | nonspace nonquote run then @ before a nonbrace nonquote byte; digits; #; :::; colon; ampersand; semicolon; comma; star | LINK_ID, NUM, BRKT, STYLE_SEPARATOR, COLON, AMP, SEMI, COMMA, MULT |
| 181-185 | INITIAL or edgeText: whitespace, at least two hyphens, x or >, whitespace; INITIAL: opening hyphens; edgeText: nonhyphen or hyphen not followed by hyphen; INITIAL: hyphen, one or more dots, hyphen | LINK; START_LINK; EDGE_TEXT; LINK |
| 187-190 | ellipseText comment; ellipse close; ellipse content excluding structural brackets; global ellipse opener | skip; -); TEXT; (- |
| 192-206 | text stadium close; global stadium open; text subroutine close; global subroutine open; [|; >; text cylinder close; global cylinder open; text doublecircle close; global doublecircle open | delimiter tokens; > enters text |
| 208-214 | trapText comment; backslash close; slash close; trap content; global [/; global [\ | skip or TEXT or slanted delimiter token |
| 217-225 | <, >, ^, pipe, v, star, #, ampersand; optional indentation then %% comment not followed by { | TAGSTART, TAGEND, UP, SEP, DOWN, MULT, BRKT, AMP, COMMENT |
| 226-229 | ASCII identifier run with the authority punctuation set, guarded hyphen, and guarded equals; lone hyphen | NODE_STRING; MINUS |
| 230-291 | the authority's explicit Unicode letter ranges, as one rule | UNICODE_TEXT |
| 293-305 | text pipe close; global pipe open; text parenthesis close; global parenthesis open; text square close; global square open; text brace close; global brace open; text comment; remaining text excluding brackets, pipe, quote, and %% | delimiter token or TEXT; comments emit nothing |
| 307-310 | quote; physical newline run; whitespace; end of source | QUOTE, NEWLINE, SPACE, EOF |

- agentflow-09: NODE_STRING MUST accept ASCII letters, digits, `!"#$%&'*+.\`?\\_/`, a hyphen before a byte other than `>`, `-`, or `.`, and `=` not followed by `=`; the earlier quote and punctuation rules MUST take precedence. [just parity]
- agentflow-10: UNICODE_TEXT MUST use exactly the scalar ranges of authority lines 230-290 rather than the host language's Unicode letter category. [just parity]
- agentflow-11: Token spans MUST include consumed delimiters and whitespace; token values MUST omit string delimiters and metadata closing braces. [just parity]

## Grammar

- agentflow-12: The parser MUST implement the following productions without backtracking over consumed tokens; `+` MUST mean one or more occurrences and `?` MUST mean optional. [just parity]

```ebnf
start = graphConfig document ;
graphConfig = (SPACE | NEWLINE | COMMENT)* GRAPH
              (NODIR | DIR FirstStmtSeparator) ;
FirstStmtSeparator = SEMI | NEWLINE | spaceList NEWLINE | COMMENT ;
document = line* ;
line = statement | COMMENT | SEMI | NEWLINE | SPACE | EOF ;
statement = vertexStatement separator | styleStatement separator
          | linkStyleStatement separator | classDefStatement separator
          | classStatement separator | clickStatement separator
          | flow (SPACE textNoTags (SQS text SQE)? shapeData?)? separator document end
          | global separator document end
          | connector SPACE textNoTags (SQS text SQE)? shapeData? separator
          | direction | acc_title acc_title_value | acc_descr acc_descr_value
          | acc_descr_multiline_value ;
separator = NEWLINE | SEMI | EOF | COMMENT ;
shapeData = SHAPE_DATA+ ;
vertexStatement = node (shapeData | spaceList)?
                  (link node (shapeData | spaceList)?)* ;
node = styledVertex (shapeData? spaceList AMP spaceList styledVertex)* ;
styledVertex = vertex (STYLE_SEPARATOR idString)? ;
vertex = idString (SQS text SQE | DOUBLECIRCLESTART text DOUBLECIRCLEEND
       | PS PS text PE PE | '(-' text '-)' | STADIUMSTART text STADIUMEND
       | SUBROUTINESTART text SUBROUTINEEND
       | VERTEX_WITH_PROPS_START NODE_STRING COLON NODE_STRING PIPE text SQE
       | CYLINDERSTART text CYLINDEREND | PS text PE
       | DIAMOND_START text DIAMOND_STOP
       | DIAMOND_START DIAMOND_START text DIAMOND_STOP DIAMOND_STOP
       | TAGEND text SQE | TRAPSTART text TRAPEND
       | INVTRAPSTART text INVTRAPEND | TRAPSTART text INVTRAPEND
       | INVTRAPSTART text TRAPEND)? ;
link = linkStatement (arrowText SPACE? | TESTSTR SPACE)?
     | LINK_ID? START_LINK edgeText LINK ;
linkStatement = LINK_ID? LINK ;
arrowText = PIPE text PIPE ;
edgeText = edgeTextToken+ | STR | MD_STR ;
text = textToken+ | STR | MD_STR ;
textNoTags = textNoTagsToken+ | STR | MD_STR ;
classDefStatement = CLASSDEF SPACE idString SPACE stylesOpt ;
classStatement = CLASS SPACE idString SPACE idString ;
styleStatement = STYLE SPACE idString SPACE stylesOpt ;
clickStatement = CLICK ((CALLBACKNAME CALLBACKARGS? | alphaNum) (SPACE STR)?
               | HREF? STR (SPACE STR)? (SPACE LINK_TARGET)?) ;
linkStyleStatement = LINKSTYLE SPACE (DEFAULT | numList) SPACE
                   (stylesOpt | INTERPOLATE SPACE alphaNum (SPACE stylesOpt)?) ;
numList = NUM (COMMA NUM)* ;
stylesOpt = style (COMMA style)* ;
style = styleComponent+ ;
styleComponent = NUM | NODE_STRING | COLON | UNIT | SPACE | BRKT | STYLE | PCT ;
idString = idStringToken+ ;
alphaNum = alphaNumToken+ ;
spaceList = SPACE+ ;
spaceListNewline = (SPACE | NEWLINE | COMMENT)+ ;
ending = endToken+ ;
endToken = NEWLINE | SPACE | EOF ;
keywords = STYLE | LINKSTYLE | CLASSDEF | CLASS | CLICK | GRAPH | DIR
         | flow | connector | global | end | DOWN | UP ;
idStringToken = NUM | NODE_STRING | DOWN | MINUS | DEFAULT | COMMA | COLON
              | AMP | BRKT | MULT | UNICODE_TEXT ;
textToken = TEXT | TAGSTART | TAGEND | UNICODE_TEXT ;
textNoTagsToken = NUM | NODE_STRING | SPACE | MINUS | AMP | UNICODE_TEXT
                | COLON | MULT | BRKT | keywords | START_LINK ;
edgeTextToken = EDGE_TEXT | UNICODE_TEXT ;
alphaNumToken = NUM | UNICODE_TEXT | NODE_STRING | DIR | DOWN | MINUS
              | COMMA | COLON | AMP | BRKT | MULT ;
direction = direction_tb | direction_bt | direction_rl | direction_lr | direction_td ;
```

- agentflow-13: TESTSTR, UNIT, and PCT MUST remain unreachable because the lexer emits none of them; `ending` and `spaceListNewline` MUST NOT add statement forms because the start production does not reach them. [just oracle]
- agentflow-14: The parser MUST accept every bracket form in `vertex`, even when shape normalization later rejects its shape. [just oracle]

## Statement boundary

- agentflow-15: Recovery MUST stop at a physical line end, semicolon, EOF, or comment outside a quoted value, bracket label, or metadata block; it MUST also stop before `end` at the current container depth. [just go-check]
- agentflow-16: Recovery MUST emit one primary diagnostic for the rejected statement and MUST NOT create a node from its rejected tokens. [just parity]
- agentflow-17: An EOF inside a string, bracket label, metadata block, flow, or global block MUST report the opening delimiter through EOF as an unterminated span. [just parity]

## Abstract syntax tree

- agentflow-18: AST nodes MUST use the PascalCase name of their authority production and MUST carry repaired-source byte spans with exclusive ends. [just parity]

| Nodes | Fields | Span rule |
|---|---|---|
| Start, GraphConfig, Document, Line, Statement | direction, ordered children or statement alternative | first through last child; Document may have an empty span |
| VertexStatement, Node, StyledVertex, Vertex | ordered endpoint sets, links, id, label, delimiter kind, class, metadata | full construct without final separator |
| ShapeData | raw metadata pieces and parsed value | @{ through closing brace |
| Link, LinkStatement, ArrowText, EdgeText | optional id, operator, label, label type | complete operator or complete label including its delimiters |
| Text, TextNoTags | borrowed text pieces and plain, string, or markdown kind | first through last piece including quote delimiters |
| ClassDefStatement, ClassStatement, StyleStatement | class ids, target ids, ordered styles | keyword through last argument |
| LinkStyleStatement, NumList, StylesOpt, Style, StyleComponent | target indices or default, interpolation, style pieces | first through last token |
| ClickStatement | id, callback and arguments or URL, tooltip, target | click keyword through final argument |
| Direction | normalized direction | whole matched direction line |
| IdString, AlphaNum, Keywords, IdStringToken, TextToken, TextNoTagsToken, EdgeTextToken, AlphaNumToken | borrowed token or concatenated tokens | first through last token |
| FirstStmtSeparator, Separator, SpaceList, SpaceListNewline, Ending, EndToken | separator or whitespace pieces | consumed bytes |

- agentflow-19: A flow, global block, connector, or accessibility declaration MUST be a tagged `Statement` alternative rather than an invented production name; its span MUST include its keyword and closing `end` or description brace when present. [just parity]
- agentflow-20: The model MUST retain id, metadata, index, operator, label, and container-opening spans for diagnostics. [just parity]

## Semantic resolution

- agentflow-21: Resolution MUST retain node insertion order and edge declaration order; a later explicit label or shape MUST replace that property without moving the node. [just parity]
- agentflow-22: Bare endpoints MUST create implicit nodes whose label is the id; blank ids MUST create nothing. [just oracle]
- agentflow-23: Bracket forms MUST resolve in grammar order to square, doublecircle, circle, ellipse, stadium, subroutine, rect with one property, cylinder, round, diamond, hexagon, odd, trapezoid, inv_trapezoid, lean_right, and lean_left. [just parity]
- agentflow-24: Shape aliases MUST map task to roundedRect, tool to subroutine, input and lean_right to lean-right, decision to diamond, refdoc to lin-doc, action to hexagon, and round to rect. [just oracle]
- agentflow-25: Shape normalization MUST map missing shapes, squareRect, and rect to roundedRect; it MUST preserve roundedRect, subroutine, subprocess, subproc, framed-rectangle, lean-right, diamond, lin-doc, lined-document, hexagon, hex, connector, and collapsedGroup. [just oracle]
- agentflow-26: Shape normalization MUST reject doc, stadium, terminal, circle, trapezoid, inv_trapezoid, inv-trapezoid, doublecircle, double-circle, typeDeclaration, procs, lean_left, lean-left, in-out, cylinder, ellipse, odd, tag-rect, tagged-rectangle, delay, half-rounded-rectangle, lin-rect, lined-rectangle, win-pane, window-pane, curv-trap, and curved-trapezoid as removed shapes; it MUST substitute roundedRect. [just oracle]
- agentflow-27: A remaining registered shape outside the allowed set MUST produce a warning and MUST use roundedRect; a truthy metadata shape that is not a string, contains an underscore, contains uppercase letters, or fails the shared shape registry MUST instead produce an error. [just oracle]
- agentflow-28: Metadata MUST parse as a JSON-schema YAML value; inline content MUST be read as a flow mapping, multiline content MUST be read as a block document, and empty content MUST become an empty mapping. [just oracle]
- agentflow-29: A failed multiline metadata parse MUST retry after removing line-trailing commas; a second failure MUST report the original failure against original source bytes. [just oracle]
- agentflow-30: Metadata MUST merge in source order onto an existing flow, connector, or named edge before creating a vertex; prototype keys MUST be discarded, and other unknown keys MUST remain data without property validation. [just oracle]
- agentflow-31: Truthy label metadata MUST replace the label; labelType MUST select plain, string, or markdown text; icon, img, form, pos, w, and h MUST remain metadata rather than select an icon or image node. [just parity]
- agentflow-32: An ordinary vertex named `connectors` MUST be omitted unless that id already names a flow; this reserved id MUST NOT produce an extra container. [just oracle]
- agentflow-33: Each chained link MUST connect the preceding endpoint set to the next endpoint set by their Cartesian product, with sources outermost and targets innermost; endpoint-set syntax MUST require whitespace around `&`. [just parity]
- agentflow-34: Links MUST accept only the lexer families `--+>` and `--+x`, the dotted open form `-.+-`, and the split `-- LABEL -->` or `-- LABEL --x` forms; removed thick, invisible, and bidirectional operators MUST NOT gain acceptance from unused database helpers. [just oracle]
- agentflow-35: Resolution MUST assign sequence semantics to a normal point arrow, failure semantics to a normal cross arrow, and reference semantics to a dotted open edge; the count of hyphens minus one, or the count of dots, MUST set the edge length with a maximum of 10. [just parity]
- agentflow-36: An authored edge id MUST apply only to the last source and first target of an endpoint product; a reused authored id MUST fall back to an automatic unique id without a duplicate-id error. [just oracle]
- agentflow-37: A flow MUST produce a group with optional id, title, metadata, nested document, and direction; an anonymous flow MUST receive a deterministic declaration-based id. [just parity]
- agentflow-38: Flow membership MUST deduplicate statement endpoints, exclude the flow itself and global nodes, and retain the first container that already owns a node; duplicate flow ids MUST merge new children into the first group and replace nonempty title and direction properties. [just oracle]
- agentflow-39: A global block MUST mark its endpoint ids parentless and MUST release them from earlier flows; it MUST emit no group and MUST keep its edges as ordinary edges. [just oracle]
- agentflow-40: A connector MUST produce a connector node with its title or id as label; a later nonempty connector title MUST replace its label, and metadata MUST attach to its connector record. [just oracle]
- agentflow-41: A direction statement inside a flow MUST set that flow's direction; shared layered rules MUST decide whether crossing edges make it ineffective. [just parity]
- agentflow-42: style MUST append vertex styles; classDef MUST store ordered class styles; class and `:::` MUST apply classes to existing nodes, flows, or edges without creating absent targets. [just oracle]
- agentflow-43: linkStyle MUST address existing zero-based edge indices or default styles; interpolation MUST follow the same index bounds, and an indexed style without fill MUST receive no fill. [just oracle]
- agentflow-44: Click declarations MUST retain URL or callback, optional arguments, tooltip, and link target; static output MUST apply the shared safe-link and ignored-callback rules. [just parity]
- agentflow-45: Accessibility declarations MUST trim and replace the accessible title or description; a multiline description MUST end at its first closing brace. [just parity]
- agentflow-46: Text MUST wrap at `agentflow.wrapping_width`, 120 px or 15 cells on x; nodes MUST be at least `agentflow.min_node_width`, 120 px or 15 cells wide. [just parity]
- agentflow-47: Node padding MUST use `flowchart.padding` when set and 8 px otherwise; 8 px MUST become 1 cell on x and 1 row on y, and a set value MUST convert by `ceil_div(px,8)` on x and `ceil_div(px,16)` on y with a minimum of 1. [just parity]
- agentflow-48: `agentflow.node_spacing` and `agentflow.rank_spacing`, each 50 px, MUST replace layered node_gap and rank_gap; the cell profile MUST use those Layered keys' cell values. [just parity]
- agentflow-49: `agentflow.diagram_padding`, 8 px, MUST replace the diagram margin; the cell profile MUST use canvas_margin's cell value from `spec/layout/layered.md`. [just parity]

## Diagnostics

- agentflow-50: Each rejected token or database exception MUST become a diagnostic below rather than a panic; shared source, nesting, edge-limit, config, and interaction diagnostics MUST retain their shared registry codes. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| agentflow/unexpected-token | error | token does not fit the active production | offending token | unexpected TOKEN, expected one of: LIST |
| agentflow/unknown-statement | error | no statement alternative starts here | first token through recovery boundary, excluding separator | unknown statement TOKEN |
| agentflow/unterminated | error | EOF before a required close | opener through EOF | unterminated TOKEN |
| agentflow/metadata-malformed | error | both metadata parsing attempts fail | original failing token, or zero-width metadata end | invalid metadata value |
| agentflow/shape-unknown | error | invalid authored metadata shape | shape value | unknown shape SHAPE |
| agentflow/shape-removed | error | normalized shape is in the removed set | shape value or bracketed vertex | shape SHAPE was removed; using roundedRect |
| agentflow/shape-unsupported | warning | registered shape is outside the allowed set | shape value or bracketed vertex | shape SHAPE is not supported; using roundedRect |
| agentflow/link-style-index | error | index is at least the number of existing edges | index token | linkStyle index INDEX is outside 0..LAST |

- agentflow-51: LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; TOKEN MUST contain the offending source text. [just parity]
- agentflow-52: A named diagnostic MUST replace the generic rejection for the same failure; an absent close at EOF MUST use unterminated rather than metadata-malformed. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| agentflow.jison:181-185,508-537 | implemented operators are narrower than historical comments | only reachable lexical families are accepted |
| agentflowDb.ts:1689-1694; diagnostics.ts:13-17 | post-parse semantic validator is empty; many advertised ids are reserved | no speculative type, template, reference-label, or flow-input checks |
| shapes.ts:127-145 | removed shapes emit errors; other unsupported shapes emit warnings | both normalize to roundedRect but keep distinct severities |
| agentflowDb.ts:403-414,520-541 | alias resolution precedes authored-shape validation | lean_right metadata is rejected for its underscore even though the bracket form resolves through the alias |
| agentflowDb.ts:902-920 | BR has no normalization branch | accept the token and use TB in canonical layout |
| agentflowDb.ts:1636 | padding uses a truthy flowchart value upstream | this project follows the approved set-value rule, including zero converted to minimum one cell |
| agentflow.jison:165-169 | direction token consumes its whole line | direction has a whole-line span and does not require a second separator |

- agentflow-53: Reserved diagnostic ids and unreachable helpers MUST NOT expand validation or syntax beyond these reachable rules. [just oracle]
- agentflow-54: Both implementations MUST resolve the same ordered nodes, groups, connectors, edges, labels, and metadata under both metric profiles. [just parity]

- agentflow-55: A flow with `view: collapsed` MUST become a collapsedGroup node and MUST hide its descendants; edges MUST redirect hidden endpoints to the outermost visible collapsed ancestor, discard collapse-induced self-loops between distinct authored endpoints, and retain authored self-loops. [just oracle]
- agentflow-56: Parent resolution MUST reject an assignment that closes a containment cycle, MUST retain earlier accepted assignments, and MUST emit agentflow/containment-violation at the child id with warning severity and message `container PARENT cannot contain CHILD because it closes a containment cycle`. [just oracle]

The authority for clauses 55 and 56 is `agentflowDb.ts:1706-1855`. These rules run during model export even though the post-parse validator is empty. The containment warning is live; it is not a reserved-only diagnostic.
