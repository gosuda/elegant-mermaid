# Info grammar

This file fixes syntax and model resolution for `info`.

## Scope

- info-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/info/info.langium:1-9`, with `common/common.langium:6-34` for imported terminals; semantic authorities MUST be `.references/mermaid/packages/mermaid/src/diagrams/info/infoParser.ts:1-11`, `infoDb.ts:1-11`, and `infoRenderer.ts:13-27`. [just oracle]
- info-02: Preprocessing and spans MUST follow `spec/preprocessing.md` and `spec/source-and-positions.md`; all spans MUST index repaired source bytes with exclusive ends. [just parity]

## Header forms

- info-03: The header MUST be case-sensitive `info`, with the keyword boundary of `spec/detection.md`. [just oracle]
- info-04: A header alone MUST be accepted; whitespace and a line end MUST NOT be required before showInfo. [just oracle]

## Lexer modes

- info-05: The lexer MUST use one default mode, local keywords before imported terminals, and first-match precedence; it MUST NOT add Jison modes. [just parity]

### Lexical rules in first-match order

| Order | Token | Match |
|---|---|---|
| local | keyword | `info`, `showInfo` |
| common 12 | BOOLEAN | lowercase true or false |
| common 14–16 | ACC_DESCR, ACC_TITLE, TITLE | accessibility colon or description-brace form, title text; percent-percent starts a comment after inline text |
| common 18–20 | FLOAT, INT, NUMBER | unsigned fraction, integer without leading zero, numeric union |
| common 22 | STRING | paired single or double quotes with backslash escapes |
| common 27 | ID | word initial, then word or internal hyphen characters, no final hyphen |
| common 29 | NEWLINE | physical line end |
| common 31–34 | WHITESPACE, YAML, DIRECTIVE, SINGLE_LINE_COMMENT | hidden spaces/tabs and shared preprocessing constructs |

- info-06: Imported tokens that no production consumes MUST remain invalid body tokens; STRING, ID, and numbers MUST NOT become new statement forms. [just oracle]
- info-07: Shared preprocessing MUST treat LF, CRLF, and lone CR as line ends; token spans MUST preserve source bytes. [just parity]

## Grammar

- info-08: The parser MUST implement this EBNF and MUST consume the complete body. [just parity]

```ebnf
Info = { NEWLINE }, 'info', { NEWLINE },
       [ 'showInfo', { NEWLINE } ], [ TitleAndAccessibilities ] ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE), EOL,
                         { (ACC_DESCR | ACC_TITLE | TITLE), EOL } ;
EOL = NEWLINE, { NEWLINE } | EOF ;
```

- info-09: showInfo MUST be the only optional ordinary statement and MUST appear at most once, before any title or accessibility field. [just oracle]
- info-10: The metadata fragment MUST allow multiple consecutive title and accessibility assignments, each ending at EOL; a showInfo after that fragment MUST be rejected. [just oracle]

## Statement boundary

- info-11: Recovery MUST stop at the next physical line end outside an accessibility brace value, or at EOF; rejected text MUST NOT create model objects. [just go-check]
- info-12: EOF within an accessibility brace value MUST report unterminated from its opening brace through EOF. [just go-check]

## Abstract syntax tree

- info-13: The AST MUST contain the authority node Info, with title and accessibility fields from its fragment and a span from the header through the last consumed body token, excluding a trailing EOL. [just parity]
- info-14: showInfo MUST NOT create a new AST node or boolean field: its authority keyword is unassigned; the parser MAY retain its token span for diagnostics. [just parity]
- info-15: TitleAndAccessibilities MUST populate Info fields rather than create a new node; tokens MUST borrow source text. [just parity]

## Semantic resolution

- info-16: showInfo MUST be accepted without changing the output; an absent showInfo MUST produce the same model as a present showInfo. [just oracle]
- info-17: The model MUST supply the project's Version constant, `0.1.0`, not the upstream package version, a tiny-build suffix, the clock, or host data; visible version text MUST be `v0.1.0`. [just parity]
- info-18: The chart adapter MUST own version-text geometry as `spec/layout/charts.md` defines; the parser MUST NOT assign coordinates or measure text. [just validate]
- info-19: Parsed body title and accessibility fields MUST have no model effect, because infoParser only validates its AST and does not populate commonDb; shared frontmatter handling MUST remain separate. [just oracle]
- info-20: No per-kind configuration schema exists for info; its configuration registry MUST be empty, and common theme, look, and output settings MUST remain owned by their shared specifications. [just gen-check]

## Diagnostics

- info-21: The registry MUST contain exactly these kind diagnostics; valid input MUST NOT invent a semantic check absent from upstream. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `info/unexpected-token` | error | token cannot continue the current production, including a second showInfo | offending token | `unexpected TOKEN, expected one of: LIST` |
| `info/unknown-statement` | error | first token starts no supported statement | first token through recovery boundary | `unknown statement TOKEN` |
| `info/unterminated` | error | EOF inside accessibility braces | opening brace through EOF | `unterminated TOKEN` |

- info-22: TOKEN MUST be source text; LIST MUST contain accepted token-kind names sorted bytewise and joined with comma and space. [just parity]

## Upstream readings

| Reading | Choice |
|---|---|
| Optional unassigned showInfo | accept once with no model effect |
| Optional final metadata fragment | retain grammar acceptance, but no commonDb population |
| Upstream version comes from the build | substitute this project's Version as the plan requires |
| Info has no per-kind schema object | empty config registry; no invented width or height config keys |
| Shared NEWLINE excludes lone CR | shared preprocessing wins |

- info-23: Go and Rust MUST resolve the same model for both profiles and MUST keep output independent of host state. [just parity]
