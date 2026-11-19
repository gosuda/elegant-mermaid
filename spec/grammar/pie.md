# Pie grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `pie` kind.

## Scope

- pie-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/pie/pie.langium:4-20`, with imported terminals and metadata at `language/common/common.langium:6-34`; both paths are relative to `packages/parser/src/`. [just oracle]
- pie-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/pie/pieParser.ts:9-19` and `pieDb.ts:18-46,50-54`; shared metadata conversion MUST follow `packages/parser/src/language/common/valueConverter.ts:44-68` and `packages/mermaid/src/diagrams/common/populateCommonDb.ts:4-13`. [just oracle]
- pie-03: Shared preprocessing and source-position rules MUST run before this grammar; every span MUST use repaired-source byte offsets with an exclusive end. [just parity]

## Header forms

- pie-04: The header MUST be the case-sensitive keyword `pie`, with the keyword boundary of `spec/detection.md`; an optional case-sensitive `showData` MUST occur immediately after the header and before the body. [just oracle]
- pie-05: The parser MUST accept an empty body and MUST NOT require a line end between the header, optional `showData`, and the first body statement. [just oracle]

## Lexer modes

- pie-06: The lexer MUST use one default mode; this Langium authority defines no named start conditions or mode transitions. [just parity]

### Lexical rules in first-match order

- pie-07: The lexer MUST keep the local terminal order below before the imported terminal order; fixed grammar literals MUST be recognised as keywords, and the first applicable terminal rule MUST win. [just parity]

| Order | Terminal or literal | Recognition and result |
|---|---|---|
| Local literals | `pie`, `showData`, `:` | Case-sensitive grammar punctuation and keywords |
| pie:18 | `FLOAT_PIE` | Optional minus, one or more digits, dot, one or more digits; the next byte must not be a dot |
| pie:19 | `INT_PIE` | Optional minus, then `0` or a non-zero digit followed by digits; the next byte must not be a dot |
| pie:20 | `NUMBER_PIE` | The float alternative, then the integer alternative |
| common:12 | `BOOLEAN` | `true` or `false`; not a pie statement |
| common:14 | `ACC_DESCR` | Optional horizontal whitespace and `accDescr`, then a colon and text to the line end or comment, or whitespace and a brace body through its first closing brace |
| common:15 | `ACC_TITLE` | Optional horizontal whitespace, `accTitle`, optional horizontal whitespace, colon, and text to the line end or comment |
| common:16 | `TITLE` | Optional horizontal whitespace and `title`, then horizontal whitespace and text to the line end or comment, or no title text |
| common:18 | `FLOAT` | Unsigned digits, dot, digits, not followed by a dot; not a pie value alternative |
| common:19 | `INT` | Unsigned integer; not a pie value alternative |
| common:20 | `NUMBER` | Imported float or integer; not a pie value alternative |
| common:22 | `STRING` | Matching single or double quotes; each interior unit is a byte other than that quote or backslash, or a backslash followed by a non-line-ending character |
| common:27 | `ID` | Word character followed by word characters or internal hyphens, with no final hyphen; not a pie statement |
| common:29 | `NEWLINE` | A physical line end; the shared LF, CRLF, and lone-CR rule applies |
| common:31 | `WHITESPACE` | Skip spaces and tabs |
| common:32 | `YAML` | Shared frontmatter handling |
| common:33 | `DIRECTIVE` | Shared directive handling |
| common:34 | `SINGLE_LINE_COMMENT` | Skip percent-percent comment text outside strings and metadata tokens |

- pie-08: Strings MUST allow the other quote character and unescaped line ends inside their content; an escaped quote MUST NOT close the string, and its opening and closing quotes MUST remain in the token span. [just oracle]
- pie-09: Pie numbers MUST NOT accept a plus sign, exponent, leading decimal point, or trailing decimal point; integer leading zeros MUST NOT be accepted as one integer, but a float MAY have leading zeros before its dot. [just oracle]
- pie-10: Comments inside a quoted label MUST remain label text; metadata line tokens MUST stop before an unquoted `%%`, and a brace description MUST stop at its first `}` without nesting. [just oracle]

## Grammar

- pie-11: The parser MUST use this EBNF without backtracking over consumed tokens; `EOL` MUST mean one or more physical line ends or end of input. [just parity]

```ebnf
Pie = { NEWLINE }, "pie", [ "showData" ],
      { TitleAndAccessibilities | PieSection | NEWLINE } ;
TitleAndAccessibilities = ( ACC_DESCR | ACC_TITLE | TITLE ), EOL,
                         { ( ACC_DESCR | ACC_TITLE | TITLE ), EOL } ;
PieSection = STRING, ":", NUMBER_PIE, EOL ;
NUMBER_PIE = FLOAT_PIE | INT_PIE ;
```

- pie-12: The parser MUST accept only a quoted section label, a colon, and one pie number as a section; it MUST NOT accept bare labels, comma-separated sections, semicolon separators, arbitrary identifiers, or a second `showData` statement. [just oracle]

## Statement boundary

- pie-13: Each section and metadata statement MUST end at `EOL`; a line end inside a string or brace description MUST NOT be a recovery boundary. [just oracle]
- pie-14: After an unexpected token, recovery MUST skip to the next physical line end outside a complete string or description body; an unknown statement MUST NOT create a section. [just go-check]
- pie-15: If input ends in a string or brace description, the parser MUST emit `pie/unterminated` from its opening delimiter through end of input and MUST NOT emit another generic diagnostic for that same incomplete construct. [just go-check]

## Abstract syntax tree

- pie-16: AST nodes MUST use the authority production names in PascalCase and MUST retain the spans below; terminal values MUST borrow source text until model resolution needs an owned value. [just parity]

| Node | Fields | Span |
|---|---|---|
| `Pie` | Header span, `showData`, ordered `sections`, final `title`, `accTitle`, and `accDescr`, plus ordered metadata occurrences | Header start through the last non-separator token; leading blank lines are excluded |
| `PieSection` | Quoted label token and number token | Label opening quote through the last number byte; trailing EOL is excluded |
| `TitleAndAccessibilities` | Ordered metadata token occurrences, each tagged title, accessibility title, or accessibility description | First metadata keyword through the last metadata value; trailing EOL is excluded |
| `EOL` | Consumed line-ending span or EOF position | All consumed line-ending bytes, or a zero-width EOF span |

- pie-17: `TitleAndAccessibilities` MUST be a source-record fragment of `Pie`, not a separately resolved model object; the model MUST keep each section's label, value, and declaration spans for diagnostics. [just parity]

## Semantic resolution

- pie-18: Resolution MUST initialise `ShowData` to false and MUST set it to true only when the header contains `showData`; this flag MUST request a legend value after each label in the form `LABEL [VALUE]`. [just parity]
- pie-19: Each quoted label MUST lose only its surrounding quote pair during token conversion; label whitespace MUST NOT be trimmed by the unused `PIE_SECTION_LABEL` converter, because the grammar uses `STRING`. [just oracle]
- pie-20: Label resolution MUST apply the shared entity rule of `spec/preprocessing.md` without changing source text or spans. [just parity]
- pie-21: Resolution MUST inspect every section in declaration order and MUST reject a mathematically negative value with `pie/negative-value` before duplicate-label elimination; `-0` and negative decimal zero MUST be accepted as zero. [just oracle]
- pie-22: The sign check MUST use the source numeric value before rounding to thousandths, so a negative non-zero value that would round to zero MUST still be rejected. [just oracle]
- pie-23: A duplicate converted label MUST keep the first section's value and position without a diagnostic; later declarations MUST NOT add a slice or replace its value. [just oracle]
- pie-24: Each retained section MUST carry its label, value, and source declaration index; the model MUST keep first-declaration order and MUST NOT sort sections by value. [just parity]
- pie-25: Numeric storage MUST use checked integer thousandths, with more than three fractional digits rounded half away from zero; the chart overflow rule MUST return the shared overflow error rather than invent a pie syntax diagnostic. [just parity]
- pie-26: Zero values and a zero total MUST remain valid model data; a zero total MUST produce no slices, and retained zero-valued labels MUST remain available to the legend. [just parity]
- pie-27: The model MUST retain every non-negative first-declared section, including a positive section below one percent of the total; it MUST NOT port the renderer's one-percent filter, because the plan allocates angles over every retained value. [just parity]
- pie-28: Metadata assignments MUST use the last occurrence of each field; line metadata MUST trim outer whitespace and replace each run of two or more spaces or tabs with one space, while a brace description MUST also trim each line and collapse repeated line endings to one LF. [just oracle]
- pie-29: The resolved payload MUST contain `Sections`, `ShowData`, title, accessibility title, accessibility description, and honoured config values; geometry, cumulative angles, remainder allocation, and braille rendering MUST follow `spec/layout/charts.md` and `spec/render-cells.md`, not this grammar. [just parity]
- pie-30: Configuration MUST classify the inherited `layout`, `useWidth`, and `useMaxWidth` keys and the local `legendPosition` and `highlightSlice` keys as accepted-ignored; `theme`, `look`, `textPosition`, and `donutHole` MUST be honoured as the plan defines. [just gen-check]

## Diagnostics

- pie-31: The parser and model MUST emit only the pie codes below for this grammar; shared preprocessing, source, config, and limit diagnostics MUST keep their shared registry codes. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `pie/unexpected-token` | error | A token does not fit the current production | Offending token, or zero-width EOF | `unexpected TOKEN, expected one of: LIST` |
| `pie/unknown-statement` | error | A body statement starts with no accepted statement form | First token through statement boundary, excluding its line end | `unknown statement TOKEN` |
| `pie/unterminated` | error | Input ends inside a quoted label or brace description | Opening delimiter through EOF | `unterminated TOKEN` |
| `pie/negative-value` | error | A section's source value is below zero, including a duplicate section | Number token including its minus | `slice LABEL has negative value VALUE` |

- pie-32: `TOKEN` MUST be source text, `LIST` MUST contain accepted token-kind names sorted bytewise and joined with `, `, `LABEL` MUST be the converted label, and `VALUE` MUST be the original number text. [just parity]

## Upstream readings

| Reading | Authority fact | Resolution |
|---|---|---|
| `pie.langium:4-20` | Empty body, optional header flag, quoted sections, signed decimal terminals | All reachable forms are in scope |
| `pie/valueConverter.ts:5-15` | Custom conversion names `PIE_SECTION_LABEL`, which this grammar never emits | Do not apply its global quote removal or trimming to `STRING` |
| `pieDb.ts:36-46` | Reject negative values before keeping only the first label | Duplicate negative values still fail |
| `pieRenderer.ts:12-22,175-180` | Upstream filters small slices, preserves remaining order, and adds legend values for `showData` | Plan keeps all retained sections for angle allocation; legend values follow the header flag |
| `config.schema.yaml:476-525,1274-1304` | Base keys and four local pie keys | Classify each key by whether the plan reads it |

- pie-33: An oracle verdict that conflicts with a grammar reading MUST control acceptance unless the plan explicitly defines the difference; Go and Rust MUST resolve the same ordered sections under both profiles. [just oracle]
