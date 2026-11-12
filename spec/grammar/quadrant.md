# Quadrant grammar

This file defines syntax and model resolution for kind `quadrant`.

## Scope

- quadrant-01: The parser MUST use `.references/mermaid/packages/mermaid/src/diagrams/quadrant-chart/parser/quadrant.jison:1-189` as its grammar authority, `quadrantDb.ts:21-109` for storage and style checks, `utils.ts:1-18` for validators, and `quadrantBuilder.ts:209-218,488-510` for ordering and class application. [just oracle]
- quadrant-02: Preprocessing and byte spans MUST follow `spec/preprocessing.md` and `spec/source-and-positions.md`; geometry MUST remain in `spec/layout/charts.md`. [just parity]

## Header forms

- quadrant-03: Detection MUST accept the case-sensitive header `quadrantChart` with the boundary in `spec/detection.md`; subsequent keyword matching MUST use the authority's ASCII case-insensitive lexer. [just oracle]
- quadrant-04: A header alone MUST be valid; the document production permits zero lines. [just oracle]

## Lexer modes

- quadrant-05: The lexer MUST retain modes `INITIAL`, `string`, `md_string`, `title`, `acc_title`, `acc_descr`, `acc_descr_multiline`, `point_start`, `point_x`, `point_y`, and `class_name`; the repeated declaration of `string` MUST NOT create another mode. [just parity]

### Lexical rules in first-match order

- quadrant-06: Within each active mode the lexer MUST take the first applicable rule in this table; the Order column gives authority lines, not a longest-match priority. [just parity]

| Order | Mode and match | Effect |
|---|---|---|
| 16-19 | INITIAL: `%%` not followed by `{` through line end; non-`}` byte followed by `%%` through line end; CR/LF run; remaining `%%` line | Skip comment rules; return NEWLINE for the CR/LF rule |
| 21-22 | INITIAL `title`; title: rest of non-LF line | Enter title and emit title; return title_value and restore mode |
| 24-30 | INITIAL `accTitle` plus colon and whitespace; its line value; `accDescr` plus colon and whitespace; its line value; `accDescr` plus opening brace; closing brace; multiline non-`}` run | Enter corresponding accessibility mode; return value then restore mode; multiline close restores mode without a token |
| 32-38 | INITIAL optional spaces, `x-axis`, `y-axis`, `--+>`, `quadrant-1`, `quadrant-2`, `quadrant-3`, `quadrant-4`, optional spaces | Return axis, delimiter, or quadrant token |
| 39 | INITIAL `classDef` | Return CLASSDEF |
| 41-46 | INITIAL double quote plus backtick; md_string non-backtick/non-quote run; backtick plus quote; INITIAL double quote; string double quote; string non-quote run | Open Markdown, return MD_STR, close Markdown; open string, close string, return STR |
| 48-49 | INITIAL `:::`; class_name word run | Enter class_name; return class_name and restore mode |
| 51 | INITIAL whitespace, colon, whitespace, `[`, whitespace | Return point_start and enter point_start |
| 52-55 | point_start `1` or `0` with optional `.` and digits; point_start whitespace and `]`; point_x whitespace/comma/whitespace; point_y same numeric pattern | Return point_x and push point_x; closing bracket restores prior mode; comma restores point_start then pushes point_y; point_y returns value and restores point_start |
| 57 | INITIAL optional spaces, `quadrantChart`, optional spaces | Return QUADRANT |
| 59-61 | INITIAL ASCII letter run; non-ASCII run | Return ALPHA or UNICODE_TEXT |
| 62-76 | INITIAL `:`, `+`, comma, `=`, duplicate equals rule, `*`, `#`, `_`, `.`, `&`, `-`, digits, whitespace, semicolon, remaining punctuation from `!"#$%&'*+,-.\u0060?\\_/` | Return COLON, PLUS, COMMA, EQUALS, EQUALS, MULT, BRKT, UNDERSCORE, DOT, AMP, MINUS, NUM, SPACE, SEMI, PUNCTUATION respectively |
| 77 | End of input | Return EOF |

- quadrant-07: Quoted text MUST have no escape decoding; Markdown quotes MUST use the paired double-quote/backtick delimiters. Ordinary text MUST retain its text type; MD_STR MUST retain its Markdown type in the AST. [just oracle]
- quadrant-08: Coordinates MUST use the authority's ordered numeric alternatives and point modes; ordinary inputs are `0`, `1`, or `0.` followed by digits. The authority's unescaped dot in `0(.\d+)?` is a wildcard, not a decimal-only assertion; implementations MUST preserve oracle acceptance for that lexical quirk and MUST NOT invent a coordinate-range diagnostic. [just oracle]

## Grammar

- quadrant-09: The parser MUST implement the following EBNF; spaces explicitly required by classDefStatement MUST NOT be omitted. [just oracle]

```ebnf
start = { eol | SPACE }, QUADRANT, document ;
document = { line } ;
line = statement, eol ;
eol = NEWLINE | SEMI | EOF ;
statement = [ SPACE, statement | classDefStatement | axisDetails
            | quadrantDetails | points | title, title_value
            | acc_title, acc_title_value | acc_descr, acc_descr_value
            | acc_descr_multiline_value ] ;
classDefStatement = CLASSDEF, SPACE, idString, SPACE, stylesOpt ;
points = text, [ class_name ], point_start, point_x, point_y, [ stylesOpt ] ;
axisDetails = ( X-AXIS | Y-AXIS ), text, [ AXIS-TEXT-DELIMITER, [ text ] ] ;
quadrantDetails = ( QUADRANT_1 | QUADRANT_2 | QUADRANT_3 | QUADRANT_4 ), text ;
stylesOpt = style, { COMMA, style } ;
style = styleComponent, { styleComponent } ;
idString = idStringToken, { idStringToken } ;
text = alphaNumToken, { textNoTagsToken } | STR | MD_STR ;
alphaNum = alphaNumToken, { alphaNumToken } ;
alphaNumToken = PUNCTUATION | AMP | NUM | ALPHA | COMMA | PLUS
              | EQUALS | MULT | DOT | BRKT | UNDERSCORE | UNICODE_TEXT ;
textNoTagsToken = alphaNumToken | SPACE | MINUS ;
idStringToken = ALPHA | NUM | NODE_STRING | DOWN | MINUS | DEFAULT
              | COMMA | COLON | AMP | BRKT | MULT | UNICODE_TEXT ;
styleComponent = ALPHA | NUM | NODE_STRING | COLON | UNIT | SPACE
               | BRKT | STYLE | PCT | MINUS ;
```

- quadrant-10: The parser MUST NOT add a `section` statement or tokens for NODE_STRING, DOWN, DEFAULT, UNIT, STYLE, or PCT; these production references have no producing lexer rule in this authority. [just oracle]

## Statement boundary

- quadrant-11: Recovery MUST stop at NEWLINE, SEMI, or EOF outside quoted and accessibility modes; an unknown statement MUST NOT create a point. [just parity]
- quadrant-12: Unexpected tokens MUST report the offending token and sorted accepted token-kind names; EOF in an open string or multiline accessibility block MUST report the opening delimiter through source end. [just parity]

## Abstract syntax tree

- quadrant-13: AST nodes MUST use upstream production names in PascalCase: Start, Document, Line, Statement, ClassDefStatement, Points, AxisDetails, QuadrantDetails, StylesOpt, Style, StyleComponent, IdString, IdStringToken, Text, AlphaNum, AlphaNumToken, TextNoTagsToken, and Eol. [just parity]
- quadrant-14: A node span MUST extend from its first consumed byte through its last consumed byte; Line MUST include its terminator, while Statement MUST exclude it. Empty productions MUST use a zero-width span at the current byte. Text MUST keep its token content span and delimiter-inclusive span separately. [just parity]
- quadrant-15: Points MUST retain text, optional class token, both coordinate lexemes, and ordered style spans; ClassDefStatement MUST retain its name and ordered style spans. AxisDetails MUST distinguish a missing delimiter from a delimiter with no second text. [just parity]

## Semantic resolution

- quadrant-16: Title and accessibility values MUST be trimmed before storage; a later assignment MUST replace the previous value. Multiline accDescr MUST use the same description field as its single-line form. [just oracle]
- quadrant-17: Axis and quadrant texts MUST be trimmed and sanitized as database label text. X labels MUST populate left then right; Y labels MUST populate bottom then top. A one-label assignment MUST change only left or bottom. A trailing delimiter MUST append ` ⟶ ` to the first text before trimming and MUST NOT clear the other field. [just oracle]
- quadrant-18: Points MUST retain duplicate labels and class names without uniqueness validation. Each added point MUST be prepended to the database point list; the AST MUST keep declaration order and the model MUST retain the upstream storage order explicitly. [just oracle]
- quadrant-19: Style parsing MUST trim each comma-separated entry, split it on colon with surrounding whitespace removed, and use only the first key and value. Repeated supported keys MUST take the last value. Keys MUST be case-sensitive even though lexer keywords are not. [just oracle]
- quadrant-20: `radius` MUST accept only ASCII digits and store their integer value; `color` and `stroke-color` MUST accept exactly three or six hexadecimal digits with an optional leading `#`; `stroke-width` MUST accept ASCII digits followed by lowercase `px` and store the text unchanged. Zero MUST be accepted for radius and width. [just oracle]
- quadrant-21: Class definitions MUST use the same style validator as inline point styles. A later definition MUST replace the entire earlier class object. Undefined classes MUST add no diagnostic. Class lookup MUST use the final class map, so definitions after a point MUST apply to that point. Inline properties MUST override class properties; absent properties MUST use database defaults. [just oracle]
- quadrant-22: Resolution MUST preserve text type in the AST but MUST store the database's sanitized text string for points, axes, and quadrants; the database does not retain Markdown type in those fields. [just parity]

## Diagnostics

- quadrant-23: The parser MUST emit exactly the following kind-specific diagnostics; each row MUST exist in `spec/data/diagnostics/quadrant.json`. Named style errors MUST apply to points and classDef alike. [just gen-check]

| Code | Severity | Message template | Span |
|---|---|---|---|
| `quadrant/unexpected-token` | error | `unexpected TOKEN, expected one of: LIST` | Offending token; zero-width at EOF |
| `quadrant/unknown-statement` | error | `unknown statement TOKEN` | First token through statement boundary, excluding terminator |
| `quadrant/unterminated` | error | `unterminated CONSTRUCT` | Opening delimiter through source end |
| `quadrant/invalid-radius` | error | `value for radius VALUE is invalid, please use a valid number` | Style value, or zero-width after colon when absent |
| `quadrant/invalid-color` | error | `value for color VALUE is invalid, please use a valid hex code` | Style value |
| `quadrant/invalid-stroke-color` | error | `value for stroke-color VALUE is invalid, please use a valid hex code` | Style value |
| `quadrant/invalid-stroke-width` | error | `value for stroke-width VALUE is invalid, please use a valid number of pixels (eg. 10px)` | Style value |
| `quadrant/unsupported-style` | error | `style named KEY is not supported.` | Style key |

- quadrant-24: All rows MUST have empty help, no fixes, and no aliases; a missing value MUST print `undefined` as VALUE, matching the thrown validation message. [just parity]

## Upstream readings

- quadrant-25: Config classification MUST enumerate QuadrantChartConfig at `config.schema.yaml:1306-1425` and inherited BaseDiagramConfig keys. Keys not read by an approved plan rule MUST be accepted and ignored. [just gen-check]
- quadrant-26: When the unused `section` reference, coordinate wildcard, or mode-stack behavior conflicts with a fixture verdict, the recorded upstream oracle verdict MUST decide acceptance; implementations MUST NOT silently broaden the grammar to match documentation examples. [just oracle]
