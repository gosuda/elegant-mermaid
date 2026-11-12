# XY chart grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `xychart` kind.

## Scope

- xychart-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/xychart/parser/xychart.jison`; resolution MUST follow `xychartDb.ts` in that directory's parent. [just oracle]
- xychart-02: This grammar MUST cover titles, both axes, line and bar plots, orientation, and accessibility statements. [just oracle]
- xychart-03: Geometry and scales MUST follow `spec/layout/charts.md`, not this grammar. [just parity]

## Header forms

- xychart-04: Detection MUST accept `xychart` and `xychart-beta` with the case and boundary rules of `spec/detection.md`. [just oracle]
- xychart-05: After detection, keyword tokens MUST match with ASCII case folding; an orientation token MUST retain its spelling for resolution. [just parity]

## Lexer modes

- xychart-06: The lexer MUST declare the following authority modes and MUST restore the previous mode when a rule pops. [just parity]

| Mode | Kind | Entered by | Left by |
|---|---|---|---|
| INITIAL | default | start | end |
| string | exclusive | double quote | double quote |
| md_string | exclusive | double quote then backtick | backtick then double quote |
| title | exclusive, unused | no reachable rule | no reachable rule |
| acc_title | exclusive | accTitle colon | value token |
| acc_descr | exclusive | accDescr colon | value token |
| acc_descr_multiline | exclusive | accDescr brace | closing brace |
| axis_data | inclusive | x-axis or y-axis | physical line end |
| axis_band_data | inclusive | bracket in axis_data | closing bracket |
| data | inclusive | line or bar | physical line end |
| data_inner | inclusive | bracket in data | closing bracket |

### Lexical rules in first-match order

- xychart-07: Within each mode, the lexer MUST apply the table in source order; inclusive modes MUST also inherit unqualified rules. [just parity]

Order is the authority line number. Patterns describe byte matches. Exclusive modes use only their qualified rules. Shared preprocessing runs first.

| Order | Pattern and modes | Action |
|---|---|---|
| 15 | `%%` not followed by `{`, through before LF | discard comment |
| 16 | one non-`}` character then `%%`, through before LF | discard match |
| 17 | axis_data: CRLF or LF | pop; NEWLINE |
| 18 | data: CRLF or LF | pop; NEWLINE |
| 19 | run of CR or LF | NEWLINE |
| 20 | `%%` through before LF | discard |
| 22 | `title` | title token; do not enter title mode |
| 24 | `accTitle`, whitespace, colon, whitespace | push acc_title; acc_title token |
| 25 | acc_title: remaining non-LF bytes | pop; acc_title_value |
| 26 | `accDescr`, whitespace, colon, whitespace | push acc_descr; acc_descr token |
| 27 | acc_descr: remaining non-LF bytes | pop; acc_descr_value |
| 28 | `accDescr`, whitespace, opening brace, whitespace | push acc_descr_multiline; no token |
| 29 | acc_descr_multiline: closing brace | pop; no token |
| 30 | acc_descr_multiline: bytes before closing brace | acc_descr_multiline_value |
| 32 | `xychart-beta` | XYCHART |
| 33 | `xychart` | XYCHART |
| 34 | `vertical` or `horizontal` | CHART_ORIENTATION |
| 36 | `x-axis` | push axis_data; X_AXIS |
| 37 | `y-axis` | push axis_data; Y_AXIS |
| 38 | axis_data: `[` | push axis_band_data; SQUARE_BRACES_START |
| 39 | axis_data: `-->` | ARROW_DELIMITER |
| 42 | `line` | push data; LINE |
| 43 | `bar` | push data; BAR |
| 44 | data: `[` | push data_inner; SQUARE_BRACES_START |
| 45 | axis_data or data_inner: optional sign, then digits with optional dot and digits, or dot and digits | NUMBER_WITH_DECIMAL |
| 46 | data_inner or axis_band_data: `]` | pop; SQUARE_BRACES_END |
| 51 | double quote then backtick | push md_string; no token |
| 52 | md_string: nonempty run not containing its closing delimiter; dot excludes a line end | MD_STR |
| 53 | md_string: backtick then double quote | pop; no token |
| 54 | double quote | push string; no token |
| 55 | string: double quote | pop; no token |
| 56 | string: bytes other than double quote | STR |
| 59 | `[` | SQUARE_BRACES_START |
| 60 | `]` | SQUARE_BRACES_END |
| 61 | ASCII letters, one or more | ALPHA |
| 62 | `:` | COLON |
| 63 | `+` | PLUS |
| 64 | `,` | COMMA |
| 65 | `=` | EQUALS |
| 66 | `*` | MULT |
| 67 | `#` | BRKT |
| 68 | `_` | UNDERSCORE |
| 69 | `.` | DOT |
| 70 | `&` | AMP |
| 71 | `-` | MINUS |
| 72 | digits, one or more | NUM |
| 73 | whitespace, one or more | discard |
| 74 | `;` | SEMI |
| 75 | end of source | EOF |

- xychart-08: Shared CRLF, LF, and lone-CR handling MUST replace the authority's inconsistent line-end matches; a line end in axis_data or data MUST pop that mode. [just parity]
- xychart-09: A quoted value MUST have no escape syntax; its delimiters MUST remain in its span but not its value. [just oracle]
- xychart-10: Numbers MUST accept `[+-]?(digits[.digits]?|.digits)` with at least one digit after a dot; exponent notation and trailing-dot notation MUST NOT be numbers. [just oracle]

## Grammar

- xychart-11: The parser MUST use this EBNF with the lexer token meanings above. [just parity]

```ebnf
start = eol, start | XYCHART, chartConfig, start | XYCHART, start | document ;
chartConfig = CHART_ORIENTATION ;
document = { statement } ;
statement = statement, eol | title, text
          | X_AXIS, parseXAxis | Y_AXIS, parseYAxis
          | LINE, [ text ], plotData | BAR, [ text ], plotData
          | acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value ;
plotData = SQUARE_BRACES_START, dataPoints, SQUARE_BRACES_END ;
dataPoints = dataPoint, { COMMA, dataPoint } ;
dataPoint = NUMBER_WITH_DECIMAL, [ STR ] ;
parseXAxis = text, [ xAxisData ] | xAxisData ;
xAxisData = bandData | NUMBER_WITH_DECIMAL, ARROW_DELIMITER, NUMBER_WITH_DECIMAL ;
bandData = SQUARE_BRACES_START, commaSeparatedTexts, SQUARE_BRACES_END ;
commaSeparatedTexts = text, { COMMA, text } ;
parseYAxis = text, [ yAxisData ] | yAxisData ;
yAxisData = NUMBER_WITH_DECIMAL, ARROW_DELIMITER, NUMBER_WITH_DECIMAL ;
eol = NEWLINE | SEMI | EOF ;
text = alphaNum | STR | MD_STR ;
alphaNum = alphaNumToken, { alphaNumToken } ;
alphaNumToken = AMP | NUM | ALPHA | PLUS | EQUALS | MULT | DOT | BRKT | MINUS | UNDERSCORE ;
```

- xychart-12: Lists MUST contain at least one item and MUST NOT have a trailing comma. [just oracle]
- xychart-13: An unquoted text value MUST concatenate its token spellings without discarded whitespace; quoted text MUST preserve interior whitespace before resolution trims its ends. [just parity]
- xychart-14: Numeric point labels MUST use STR, not MD_STR; both line and bar syntax MUST accept them. [just oracle]
- xychart-15: A y-axis MUST NOT accept band categories; a title-only axis MUST be valid. [just oracle]
- xychart-16: An empty body MUST be valid after the required detected header; the recursive start production MUST permit additional XYCHART tokens only before document statements. [just oracle]

## Statement boundary

- xychart-17: Recovery MUST stop at a physical line end outside a quoted value or accessibility block, at a semicolon outside those values, or at EOF. [just go-check]
- xychart-18: A statement MAY follow a complete statement without a separator when its leading token is unambiguous; SEMI MUST NOT implicitly pop axis_data or data. [just oracle]
- xychart-19: An unknown statement MUST span its first token through the next recovery boundary, without consuming that boundary. [just parity]
- xychart-20: A parser MUST report EOF inside a string, Markdown string, accessibility block, or bracketed list as unterminated; recovery MUST NOT create a plot or axis from that incomplete statement. [just go-check]

## Abstract syntax tree

- xychart-21: AST nodes MUST take the PascalCase name of their authority production and MUST span their first through last source token, excluding trailing separators. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | headers, configs, document | complete parsed source |
| ChartConfig | orientation token | orientation token |
| Document | ordered statements | first through last statement |
| Statement | variant, child, separators | statement content only |
| PlotData | points | opening through closing bracket |
| DataPoints | ordered DataPoint list | first through last point |
| DataPoint | number, optional label | number through label close when present |
| ParseXAxis | optional title, optional data | first through last axis argument |
| XAxisData | band or range | brackets or first through second number |
| BandData | categories | opening through closing bracket |
| CommaSeparatedTexts | ordered text list | first through last text |
| ParseYAxis | optional title, optional range | first through last axis argument |
| YAxisData | minimum, maximum | first through second number |
| Eol | separator kind | full physical ending, semicolon, or zero-width EOF |
| Text | plain or Markdown value, child | includes quote delimiters |
| AlphaNum | ordered tokens | first through last token |
| AlphaNumToken | token kind and source text | token bytes |

- xychart-22: Tokens MUST borrow source text; the model MUST retain axis, category, numeric, title, orientation, point-label, and plot declaration spans. [just parity]

## Semantic resolution

- xychart-23: Resolution MUST execute statements in declaration order and MUST preserve plot insertion order across line and bar statements. [just parity]
- xychart-24: Orientation MUST start from resolved chartOrientation configuration, default vertical; a header orientation MUST override it with horizontal only when its retained spelling is exactly `horizontal`, and vertical otherwise. [just oracle]
- xychart-25: Repeated diagram titles and accessibility statements MUST replace earlier values; resolution MUST trim their outer whitespace. [just oracle]
- xychart-26: Axis titles and category text MUST be trimmed; an axis data statement without a title MUST clear that axis title. [just parity]
- xychart-27: XAxisData MUST replace the current x-axis with a band category list or linear range and MUST mark that axis set; a title-only statement MUST NOT mark it set. [just parity]
- xychart-28: YAxisData MUST replace the current y range and MUST mark it set; a title-only statement MUST leave range inference active. [just parity]
- xychart-29: Before any plot, x MUST be an unset band axis with no categories and y MUST be an unset linear axis with no finite observations. [just parity]
- xychart-30: The first plot without a set x-axis MUST set a linear x domain from 1 through that plot's data count; this operation MUST mark x set, so later longer plots MUST NOT extend the inferred domain. [just oracle]
- xychart-31: A band plot with excess values MUST discard those excess values before y inference; a shorter plot MUST retain each category with an absent value at each missing position, without a mismatch diagnostic. [just oracle]
- xychart-32: While y is unset, each plot MUST extend the observed y minimum and maximum using its retained values; a later explicit range MUST replace those observations and stop inference. [just oracle]
- xychart-33: Each plot MUST capture the axis state at its declaration; later axis statements MUST NOT reinterpret earlier plot data or repeat their range inference. [just oracle]
- xychart-34: A linear plot MUST retain its ordered values and domain for the scale rules of `spec/layout/charts.md`; a single value MUST correspond to the domain minimum. [just parity]
- xychart-35: Resolution MUST retain an absent value distinctly from numeric zero; it MUST NOT invent observations for an empty diagram or for missing band values. [just parity]
- xychart-36: Series titles MUST default to empty text and MUST be trimmed when present; line plots MUST retain sanitized nonempty point labels, and bar plots MUST ignore point labels after parsing them. [just oracle]
- xychart-37: Numeric conversion MUST use the shared integer-thousandths rule and overflow contract; the parser MUST NOT add range-order, nonnegative-value, equal-length, or minimum-plot-count checks that the database does not enforce. [just parity]
- xychart-38: Plain and Markdown text MUST retain their text-kind tag in the AST; database text normalization MUST trim text without treating source markup as executable content. [just parity]
- xychart-39: The config registry MUST include XYChartConfig properties, inherited BaseDiagramConfig properties, and dotted xAxis and yAxis properties; theme-variable properties MUST NOT enter that registry. [just gen-check]

## Diagnostics

- xychart-40: Rejected syntax MUST use exactly the rows below; the database has no throwing semantic checks that require another xychart diagnostic. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| xychart/unexpected-token | error | parser | token not accepted by the current production | offending token | unexpected TOKEN, expected one of: LIST |
| xychart/unknown-statement | error | parser | no statement production accepts the leading token | statement through recovery boundary, excluding boundary | unknown statement TOKEN |
| xychart/unterminated | error | lexer or parser | EOF before an open value or list closes | opening delimiter through EOF | unterminated TOKEN |

- xychart-41: TOKEN MUST be source text; LIST MUST list accepted token-kind names in bytewise order separated by `, `. [just parity]
- xychart-42: Shared encoding, configuration, and numeric-overflow errors MUST retain their shared codes or typed errors; this grammar MUST NOT rename them as xychart diagnostics. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| xychart.jison:4-13 | exclusive and inclusive mode declarations | mode table |
| xychart.jison:15-75 | first-match rules, including unreachable title mode | lexical table |
| xychart.jison:83-175 | statement forms and point labels | EBNF and AST |
| xychartDb.ts:81-108 | orientation spelling check and explicit-axis flags | orientation and axes |
| xychartDb.ts:112-163 | inference, truncation, missing band values, first-plot x lock | declaration-order resolution |
| xychartDb.ts:175-201 | line labels retained, bar labels ignored | series resolution |
| config.schema.yaml:1427-1581 | axis and chart properties | config registry |

- xychart-43: Shared detection MUST override the authority's case-insensitive header lexer; shared preprocessing MUST override its comment and line-end quirks before kind lexing. [just oracle]
- xychart-44: Go and Rust MUST resolve identical ordered axes, plots, labels, and diagnostics under both metric profiles. [just parity]
