# Radar grammar

This file fixes syntax and semantic resolution for the `radar` kind.

## Scope

- radar-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/radar/radar.langium:1-55`, with imported terminals at `common/common.langium:6-34`; resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/radar/parser.ts:8-22` and `radar/db.ts:23-117`. [just oracle]
- radar-02: Configuration classification MUST use `schemas/config.schema.yaml:476-525,2902-2954`; range inference MUST use `radar/renderer.ts:8-35`, subject to the deliberate empty-range rule below. These paths are relative to `.references/mermaid/packages/mermaid/src/`. [just gen-check]
- radar-03: Shared preprocessing, positions, labels, and detection MUST follow their existing specifications; layout and braille geometry MUST remain owned by `spec/layout/charts.md` and `spec/render-cells.md`. [just parity]

## Header forms

- radar-04: The header MUST be case-sensitive `radar-beta` with the shared keyword boundary; it MAY have one following colon, adjacent or separated by horizontal whitespace. [just oracle]

## Lexer modes

- radar-05: The lexer MUST have one INITIAL mode; it MUST use the following first-match precedence, with importing-grammar terminals before imported terminals and keyword recognition before ID. [just parity]

### Lexical rules in first-match order

| Order | Token | Recognition |
|---|---|---|
| radar 55 | GRATICULE | `circle` or `polygon` |
| common 12 | BOOLEAN | `true` or `false` |
| common 14 | ACC_DESCR | `accDescr:` and remaining line text, or `accDescr` and a brace-delimited description |
| common 15 | ACC_TITLE | `accTitle:` and remaining line text |
| common 16 | TITLE | `title` and optional space-prefixed remaining line text |
| common 18 | FLOAT | one or more digits, dot, one or more digits; no following dot |
| common 19 | INT | `0`, or nonzero digit and remaining digits; no following dot |
| common 20 | NUMBER | FLOAT or INT |
| common 22 | STRING | single- or double-quoted text; backslash consumes the next character |
| common 27 | ID | ASCII letter, digit, or underscore first; letters, digits, underscore, or dash thereafter; no final dash |
| common 29 | NEWLINE | physical line ending |
| common 31 | WHITESPACE | spaces and tabs; hidden |
| common 32 | YAML | frontmatter; handled by shared preprocessing |
| common 33 | DIRECTIVE | directive; handled by shared preprocessing |
| common 34 | SINGLE_LINE_COMMENT | `%%` through line end; hidden |

- radar-06: Punctuation and keywords MUST recognize `radar-beta`, its adjacent-colon header spelling, `axis`, `curve`, `showLegend`, `ticks`, `max`, `min`, `graticule`, comma, colon, square brackets, and braces as grammar literals; matching MUST be case-sensitive. [just oracle]
- radar-07: NUMBER MUST exclude signs, exponents, and leading-zero multi-digit integers; STRING MUST retain its raw token span while its value excludes quotes and applies the common string conversion. [just oracle]
- radar-08: TITLE and accessibility line values MUST stop before `%%`; block accessibility text MUST stop at its first closing brace; shared preprocessing MUST accept LF, CRLF, and lone CR uniformly. [just parity]

## Grammar

- radar-09: The parser MUST accept exactly these productions after preprocessing; `EOF` means end of input and `EOL` is one or more NEWLINE tokens or EOF. [just oracle]

```ebnf
Radar = { NEWLINE }, Header, { NEWLINE },
        { TitleAndAccessibilities | AxisStatement | CurveStatement | OptionStatement | NEWLINE } ;
Header = 'radar-beta', [ ':' ] ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE), EOL,
                         { (ACC_DESCR | ACC_TITLE | TITLE), EOL } ;
AxisStatement = 'axis', Axis, { ',', Axis } ;
CurveStatement = 'curve', Curve, { ',', Curve } ;
OptionStatement = Option, { ',', Option } ;
Label = '[', STRING, ']' ;
Axis = ID, [ Label ] ;
Curve = ID, [ Label ], '{', Entries, '}' ;
Entries = { NEWLINE }, NumberEntry, { ',', { NEWLINE }, NumberEntry }, { NEWLINE }
        | { NEWLINE }, DetailedEntry, { ',', { NEWLINE }, DetailedEntry }, { NEWLINE } ;
DetailedEntry = ID, [ ':' ], NUMBER ;
NumberEntry = NUMBER ;
Option = 'showLegend', BOOLEAN | 'ticks', NUMBER | 'max', NUMBER
       | 'min', NUMBER | 'graticule', GRATICULE ;
```

- radar-10: A curve MUST have at least one entry; one curve MUST NOT mix positional and keyed entries, and a comma MUST NOT trail a list. [just oracle]
- radar-11: NEWLINE MUST be accepted inside Entries only before the first entry, after a comma, or before its close; other lists MUST NOT gain newline continuations not present in the grammar. [just oracle]
- radar-12: Axis, curve, and option statements MUST NOT require a line separator when the next token starts another accepted statement; semicolons MUST NOT become separators. [just oracle]

## Statement boundary

- radar-13: Recovery MUST skip to a physical line end outside strings and curve braces, or to the current curve's closing brace; recovery MUST resume at the following statement and MUST NOT create phantom axes or curves. [just go-check]
- radar-14: An unclosed string, curve, label, or accessibility brace at EOF MUST report the opening delimiter through EOF; recursion MUST obey the shared depth limit of 64. [just parity]

## Abstract syntax tree

- radar-15: AST names MUST follow upstream productions in PascalCase; grammar fragments MUST remain fields rather than invented semantic nodes. [just parity]

| Node | Fields | Span |
|---|---|---|
| Radar | axes, curves, options, title, accTitle, accDescr | header start through final consumed token |
| Axis | name, optional label | ID through optional label close |
| Curve | name, optional label, entries | ID through closing brace |
| DetailedEntry | axis reference text, value | ID through NUMBER |
| NumberEntry | value | NUMBER token |
| Option | name, value | option keyword through value token |

- radar-16: DetailedEntry and NumberEntry MUST implement the common Entry shape with optional axis reference and numeric value; all tokens MUST borrow source bytes and keep half-open byte spans excluding trailing separators. [just parity]

## Semantic resolution

- radar-17: Resolution MUST collect every Axis in declaration order before it resolves any Curve, even when a curve statement occurs before an axis statement; it MUST then apply options. [just parity]
- radar-18: An axis or curve label MUST default to its name only when the label is absent; an explicitly empty string MUST remain empty. Repeated names MUST remain separate declarations because the database maps lists without deduplication. [just oracle]
- radar-19: A positional curve MUST retain all values in entry order; the resolver MUST NOT reject a positional length that differs from the axis count. [just oracle]
- radar-20: A keyed curve MUST require at least one declared axis; it MUST emit one value per declared axis in axis order, using the first entry whose reference text equals that axis name. A missing axis entry MUST be an error. [just oracle]
- radar-21: Extra keyed entries MUST NOT create axes; reference text MUST remain available for matching, and this resolver MUST NOT invent an unknown-axis rejection beyond an upstream parser or linker rejection. [just oracle]
- radar-22: Options MUST use the last declaration of each option name; defaults MUST be `showLegend=true`, `ticks=5`, absent max, `min=0`, and `graticule=circle`. [just parity]
- radar-23: A ticks value above 32 MUST produce a warning and resolve to 32; zero and fractional ticks MUST remain accepted numeric values, with no invented positivity or integrality error. [just oracle]
- radar-24: The resolved maximum MUST be the explicit max when present, otherwise the largest curve entry; a finite resolved maximum not greater than min MUST raise `radar/empty-range` and MUST produce no curve scene. This plan rule deliberately adds a check absent from the upstream parser. An empty curve list MUST remain syntactically valid and MUST NOT synthesize a maximum or a range error. [just parity]
- radar-25: Numeric values MUST use the shared chart thousandths conversion with half-away-from-zero rounding and checked range; geometry MUST NOT use floating point. [just parity]
- radar-26: Title and accessibility fields MUST retain the last parsed value and their source spans; model labels MUST follow shared label processing without changing source offsets. [just parity]
- radar-27: The chart payload MUST contain ordered axis labels, ordered curve names and values, min, optional max, ticks, graticule, and showLegend; curve declaration index MUST determine series identity. Legend visibility MUST follow showLegend without removing curve identity or its label from the model. [just parity]
- radar-28: The config registry MUST honour width, height, marginTop, marginRight, curveTension, theme, and look; it MUST accept and ignore the other schema keys listed in its radar file. Axis label placement MUST use the plan's fixed label-gap rule rather than read axisLabelFactor. [just gen-check]

## Diagnostics

- radar-29: Parser and model diagnostics MUST use the following registry rows; all rows MUST have no fixes. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| radar/unexpected-token | error | token rejected in a known production | offending token | unexpected TOKEN, expected one of: LIST |
| radar/unknown-statement | error | no statement accepts its first token | first token through recovery boundary, excluding separator | unknown statement TOKEN |
| radar/unterminated | error | EOF within a delimiter | opening delimiter through EOF | unterminated TOKEN |
| radar/axes-required | error | keyed curve with no axes | curve span | keyed curve requires declared axes |
| radar/missing-axis-entry | error | keyed curve has no value for a declared axis | curve span | missing entry for axis LABEL |
| radar/ticks-clamped | warning | ticks above 32 | winning ticks value | ticks VALUE exceeds 32; using 32 |
| radar/empty-range | error | finite resolved max is not greater than min | explicit max value, otherwise min value, otherwise header | radar maximum must be greater than minimum |

- radar-30: TOKEN MUST be source text and LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `; recovery MUST emit only the most specific applicable error at EOF. [just parity]

## Upstream readings

| Reading | Authority fact | Interpretation |
|---|---|---|
| radar.langium:4-14 | top-level lists do not require EOL | adjacent statements remain accepted |
| radar.langium:29-42 | two nonempty entry alternatives | mixing entry styles is rejected |
| radar/db.ts:56-91 | axes resolved first; first matching keyed entry wins | duplicate axis declarations remain ordered |
| radar/db.ts:93-117 | last option wins; high ticks warn and clamp | no extra lower-bound syntax check |
| radar/renderer.ts:8-35 | inferred maximum reads all curve entries | range validation adds only the named plan check |

- radar-31: An oracle verdict that conflicts with an authority reading MUST control acceptance; the implementation MUST record the precise grammar note rather than silently broaden this grammar. [just oracle]
