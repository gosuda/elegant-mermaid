# Sankey grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `sankey` kind.

## Scope

- sankey-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/sankey/parser/sankey.jison:11-67`; resolution MUST follow `sankeyDB.ts:13-69` in the same diagram directory. [just oracle]
- sankey-02: Input preparation MUST follow `sankeyUtils.ts:1-7`, invoked by `sankeyDiagram.ts:9-10`; configuration keys MUST follow `config.schema.yaml:2691-2753` and its base definition at lines 476-525. [just oracle]
- sankey-03: Shared preprocessing and repaired-source byte positions MUST apply before this grammar; preparation MUST retain an offset map to the original source instead of changing diagnostic coordinates. [just parity]

## Header forms

- sankey-04: The header MUST be `sankey` or `sankey-beta`, case-sensitive, with the boundary defined by `spec/detection.md`; this detection rule MUST override the authority's case-insensitive lexer option. [just oracle]
- sankey-05: A header MUST be followed by a line end and at least one record; an absent direction MUST resolve to `TB`. [just oracle]

## Lexer modes

- sankey-06: The lexer MUST use `INITIAL`, exclusive `csv`, and exclusive `escaped_text`; a header pushes `csv`, an opening quote pushes `escaped_text`, and a closing quote restores `csv`. [just parity]
- sankey-07: Preparation MUST remove horizontal whitespace only at the beginning and end of the whole input, collapse each consecutive run of CR or LF into one LF, and then trim the whole result; it MUST NOT trim every record separately or preserve repeated line ends inside quoted fields. [just oracle]

The utility's first regular expression has no multiline flag. Its comment does not change its whole-input behavior. After preparation, a physically empty line disappears, but a line containing spaces remains a record candidate. Preparation also collapses line-end runs within quotes.

- sankey-08: Within each active mode the lexer MUST take the first matching rule in the following authority order; TEXTDATA MUST mean U+0020–U+0021, U+0023–U+002B, or U+002D–U+007E. [just parity]

| Authority line | Modes | Match | Action |
|---|---|---|---|
| 29 | INITIAL | `sankey-beta` | push csv; SANKEY |
| 30 | INITIAL | `sankey` | push csv; SANKEY |
| 31 | INITIAL, csv | end of input | EOF |
| 32 | INITIAL, csv | CRLF or LF | NEWLINE |
| 33 | INITIAL, csv | comma | COMMA |
| 34 | INITIAL, csv | double quote | push escaped_text; DQUOTE |
| 35 | INITIAL, csv | zero or more TEXTDATA | NON_ESCAPED_TEXT |
| 36 | INITIAL, csv, escaped_text | double quote not followed by another double quote | restore previous mode; DQUOTE |
| 37 | INITIAL, csv, escaped_text | zero or more TEXTDATA, commas, CR, LF, or doubled double quotes | ESCAPED_TEXT |

- sankey-09: Empty fields MUST be representable without a non-advancing lexer loop; the empty matches above MUST produce at most the one field token required at that position. [just go-check]
- sankey-10: A quoted field MUST use two adjacent double quotes for one embedded double quote; backslash MUST have no escape meaning, and a quote inside an unquoted field MUST NOT become literal text. [just oracle]
- sankey-11: A TAB, non-ASCII scalar, or other character outside the active rule's character set MUST be rejected; the parser MUST NOT extend TEXTDATA to arbitrary Unicode. [just oracle]

## Grammar

- sankey-12: The parser MUST implement the following EBNF with the authority's production names; the record MUST contain exactly three fields. [just parity]

```ebnf
start       = SANKEY, NEWLINE, csv, opt_eof ;
csv         = record, csv_tail ;
csv_tail    = NEWLINE, csv | empty ;
opt_eof     = EOF | empty ;
record      = field, COMMA, field, COMMA, field ;
field       = escaped | non_escaped ;
escaped     = DQUOTE, ESCAPED_TEXT, DQUOTE ;
non_escaped = NON_ESCAPED_TEXT ;
```

- sankey-13: Source, target, and value MUST each accept quoted or unquoted fields; commas and prepared newlines inside quoted fields MUST be field content, not record boundaries. [just oracle]
- sankey-14: The body MUST NOT accept standalone node declarations, title statements, accessibility statements, semicolon separators, or additional CSV columns; shared frontmatter and directives remain governed by preprocessing. [just oracle]

## Statement boundary

- sankey-15: Recovery MUST skip to the next prepared newline outside a quoted field or to EOF; a newline inside escaped_text MUST NOT terminate recovery. [just go-check]
- sankey-16: A malformed record MUST contribute no nodes or links; recovery MUST continue with the next complete record. [just parity]

## Abstract syntax tree

- sankey-17: AST nodes MUST use the PascalCase names of the authority productions and MUST keep the following fields and byte spans. [just parity]

| Node | Fields | Span |
|---|---|---|
| Start | header, Csv, OptEof | header start through input end |
| Csv | Record, CsvTail | first record start through last record end |
| CsvTail | optional following Csv | separator through following Csv; empty at prior record end |
| OptEof | EOF presence | zero-width at input end |
| Record | source Field, target Field, value Field, declaration index | first field start through third field end, without separator |
| Field | Escaped or NonEscaped | complete field including quotes when present |
| Escaped | borrowed content slices | opening quote through closing quote |
| NonEscaped | borrowed text | field bytes; empty at comma or EOF |

- sankey-18: Tokens MUST borrow source slices, and normalized content MUST keep the source-piece map needed for spans; an escaped field's value MUST omit its outer delimiters. [just parity]

## Semantic resolution

- sankey-19: Resolution MUST process complete records in source order, resolve the source before the target, and create each node only at its first occurrence of the resolved id. [just parity]
- sankey-20: Resolution MUST trim each endpoint field and then replace each doubled double quote with one double quote; equality MUST be case-sensitive, and empty ids and ids such as `__proto__` MUST remain valid ids. [just oracle]
- sankey-21: Node Index MUST be its zero-based first-insertion index; Link Index MUST be its zero-based record index, and duplicate links, self-links, and cycles MUST remain in declaration order without parser diagnostics. [just parity]
- sankey-22: The model MUST retain plain escaped text instead of performing DOM sanitization; label entity decoding MUST follow `spec/preprocessing.md` without changing source spans. [just parity]
- sankey-23: Value parsing MUST trim the field and select the longest prefix accepted by JavaScript parseFloat: an optional sign followed by `Infinity` or by a decimal mantissa with an optional complete exponent; trailing text MUST NOT invalidate a numeric prefix. [just oracle]
- sankey-24: A decimal mantissa MUST contain at least one digit and MAY use either `digits[.digits]` or `.digits`; an incomplete exponent MUST be excluded from the prefix, and a hexadecimal-looking value such as `0x10` MUST resolve from prefix `0`. [just oracle]
- sankey-25: Finite numeric prefixes MUST convert directly to signed integer thousandths without binary floating point, with excess fractional digits rounded half away from zero; a magnitude above 2147483647 thousandths MUST retain a typed overflow outcome for layout. [just parity]
- sankey-26: An empty or nonnumeric value, or a signed Infinity prefix, MUST remain syntactically accepted as upstream accepts it; the model MUST retain a non-finite numeric outcome rather than inventing a zero value or an error-severity parser diagnostic. [just oracle]
- sankey-27: Negative and zero finite values MUST NOT receive a parser diagnostic; requirements for feasible chart geometry and numeric failure handling MUST remain in `spec/layout/charts.md` and the typed layout error contract. [just oracle]
- sankey-28: The chart payload MUST contain ordered Nodes with id and Index and ordered Links with source index, target index, value outcome, and Index; it MUST contain no coordinates. [just parity]
- sankey-29: The adapter MUST use the chart family's one layout path and the vector-scene Braille strategy with node labels; series identity MUST be the node's first-appearance index modulo 12, and a link MUST take its source node's series identity. [just parity]
- sankey-30: The configuration registry MUST honour width, height, nodeAlignment, showValues, theme, and look because the plan reads them; all other schema keys MUST be accepted and ignored, including nodeWidth and nodePadding whose plan values are fixed constants rather than config reads. [just gen-check]

## Diagnostics

- sankey-31: Parser rejections MUST use the following registry rows; the database's append and lookup actions MUST NOT introduce additional semantic rejection codes. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| sankey/unexpected-token | error | token cannot complete the active production, invalid character, or wrong field count | offending token; zero-width at EOF | `unexpected TOKEN, expected one of: LIST` |
| sankey/unknown-statement | error | a statement is not a CSV record | first token through recovery boundary, excluding separator | `unknown statement TOKEN` |
| sankey/unterminated | error | EOF while escaped_text is open | opening double quote through source end | `unterminated TOKEN` |

- sankey-32: TOKEN MUST be the offending source text, LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `, and an unterminated field MUST emit only the unterminated diagnostic rather than a second unexpected-token diagnostic for the same EOF. [just parity]

## Upstream readings

| Reading | Authority fact | Decision |
|---|---|---|
| sankey.jison:13,29-37 | lexer folds case and has two exclusive modes | shared header detection stays case-sensitive; mode names and rule order stay unchanged |
| sankeyUtils.ts:1-7 | normalization operates before CSV recognition | retain original spans and preserve its whole-input, not per-row, trim behavior |
| sankey.jison:51-67 | each record has three general fields and uses parseFloat | accept prefix numbers and preserve non-finite outcomes; finite values use exact thousandths |
| sankeyDB.ts:40-57 | links append and nodes reuse first insertion | preserve duplicates and source-before-target node order |
| sankeyDB.ts:49 | upstream applies HTML-oriented sanitization | static output escapes labels; model has no DOM dependency |

- sankey-33: A disagreement between this authority reading and an upstream corpus verdict MUST be resolved in favour of the oracle, except for an explicit plan difference recorded by the parent. [just oracle]
