# Cynefin grammar

This file fixes syntax and model resolution for `cynefin`.

## Scope

- cynefin-01: The authority MUST be `.references/mermaid/packages/parser/src/language/cynefin/cynefin.langium:1-30`, with `common/common.langium:6-34` for shared terminals, and `.references/mermaid/packages/mermaid/src/diagrams/cynefin/cynefinDb.ts:34-68` and `cynefinParser.ts:8-19` for resolution. [just oracle]
- cynefin-02: Preprocessing and repaired-source byte spans MUST follow `spec/preprocessing.md` and `spec/source-and-positions.md`. [just parity]

## Header forms

- cynefin-03: The header MUST be case-sensitive `cynefin-beta`, with the boundary of `spec/detection.md`; an immediately following colon MUST also be accepted. [just oracle]
- cynefin-04: An empty body MUST be accepted; no newline MUST be required between the header and its first body token. [just oracle]

## Lexer modes

- cynefin-05: The lexer MUST use one default mode and first-match precedence, with local DOMAIN_NAME before imported terminals; it MUST NOT invent Jison modes. [just parity]

### Lexical rules in first-match order

| Order | Token | Match |
|---|---|---|
| local | keywords and punctuation | header forms, `-->`, `:` |
| local terminal | DOMAIN_NAME | `complex`, `complicated`, `clear`, `chaotic`, `confusion` |
| common 12 | BOOLEAN | lowercase true or false |
| common 14–16 | ACC_DESCR, ACC_TITLE, TITLE | accessibility colon or description-brace form and title line; a percent-percent comment ends inline text |
| common 18–20 | FLOAT, INT, NUMBER | unsigned decimal fraction, integer without leading zero, numeric union |
| common 22 | STRING | single- or double-quoted text; backslash plus a following character stays inside the token |
| common 27 | ID | ASCII word initial, then word characters or internal hyphens; no terminal hyphen |
| common 29 | NEWLINE | physical line ending |
| common 31–34 | WHITESPACE, YAML, DIRECTIVE, SINGLE_LINE_COMMENT | hidden spaces/tabs, frontmatter, directives, comments |

- cynefin-06: Shared preprocessing MUST handle LF, CRLF, and lone CR uniformly; quoted strings MUST retain internal line endings and MUST include their delimiters in spans. [just parity]
- cynefin-07: String values MUST use the upstream Langium STRING value conversion; the implementation MUST NOT add JSON-only escape validation, and token spans MUST retain the quoted source bytes. [just parity]

## Grammar

- cynefin-08: The parser MUST implement this EBNF; EOL MUST mean one or more line endings or EOF. [just parity]

```ebnf
Cynefin = { NEWLINE }, ('cynefin-beta' | 'cynefin-beta:'), { NEWLINE },
          { TitleAndAccessibilities | DomainBlock | Transition | NEWLINE } ;
DomainBlock = DOMAIN_NAME, { NEWLINE }, { DomainItem, { NEWLINE } } ;
DomainItem = STRING ;
Transition = DOMAIN_NAME, '-->', DOMAIN_NAME, [ ':', STRING ], EOL ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE), EOL,
                         { (ACC_DESCR | ACC_TITLE | TITLE), EOL } ;
```

- cynefin-09: A domain name followed by an arrow MUST start Transition rather than an empty DomainBlock; domain blocks MUST allow zero items and quoted items on the same line. [just oracle]
- cynefin-10: Domain names MUST remain case-sensitive and MUST NOT accept arbitrary identifiers as domains. [just oracle]

## Statement boundary

- cynefin-11: Recovery MUST stop at the next physical line end outside a string or accessibility brace value, or at EOF; a rejected statement MUST NOT produce model elements. [just go-check]
- cynefin-12: EOF inside a quote or accessibility brace MUST report unterminated from the opening delimiter through EOF. [just go-check]

## Abstract syntax tree

- cynefin-13: AST nodes MUST use the following authority names in PascalCase and spans from first through last consumed token, excluding trailing EOL. [just parity]

| Node | Fields | Span |
|---|---|---|
| Cynefin | ordered domain blocks, transitions, title and accessibility fields | header through final body token |
| DomainBlock | domain, ordered DomainItem children | domain through final item, or domain alone |
| DomainItem | label | quoted token including delimiters |
| Transition | from, to, optional label | source domain through target or final quoted label |

- cynefin-14: TitleAndAccessibilities MUST populate fields on Cynefin, not create an invented AST statement type; every model field MUST retain its source span. [just parity]

## Semantic resolution

- cynefin-15: Domains MUST use first-insertion order; a repeated domain block MUST replace its items, not append them, without changing that domain's position. [just oracle]
- cynefin-16: Transitions MUST preserve declaration order and duplicate non-self transitions; an empty label MUST resolve as absent. [just parity]
- cynefin-17: A transition to the same domain MUST emit the warning below and MUST be omitted from the resolved transitions. [just oracle]
- cynefin-18: A transition MUST NOT require explicit domain blocks for its endpoints; the model MUST represent the five fixed domains even when their item lists are empty. [just oracle]
- cynefin-19: Title and accessibility assignments MUST use the last value, with shared prefix removal and trimming. [just parity]
- cynefin-20: The model MUST hand the chart family the five domain item lists and ordered transitions; geometry and paint MUST follow `spec/layout/charts.md` and `spec/scene.md`, not parser-generated coordinates. [just validate]
- cynefin-21: Configuration MUST honour width, height, boundaryAmplitude, and seed; absent amplitude MUST use the chart-family default rather than the upstream schema's amplitude default. [just parity]
- cynefin-22: Seed zero MUST select the fixed default seed, not a DOM id or random value; the chart family MUST use one xorshift32 stream with exactly fifteen draws, as `spec/layout/charts.md` defines. [just parity]
- cynefin-23: Padding and showDomainDescriptions MUST be accepted and ignored because no plan rule reads them; inherited theme and look MUST use shared resolution, and layout and responsive width controls MUST be accepted and ignored. [just gen-check]

## Diagnostics

- cynefin-24: The registry MUST contain exactly these kind diagnostics. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `cynefin/unexpected-token` | error | token cannot continue the current production | offending token | `unexpected TOKEN, expected one of: LIST` |
| `cynefin/unknown-statement` | error | first token starts no statement | first token through recovery boundary | `unknown statement TOKEN` |
| `cynefin/unterminated` | error | EOF within an open delimiter | opener through EOF | `unterminated TOKEN` |
| `cynefin/self-loop-transition` | warning | equal source and target domains | complete transition without EOL | `self-loop transition on domain DOMAIN is skipped` |

- cynefin-25: TOKEN MUST be source text and LIST MUST contain accepted token-kind names sorted bytewise, joined with comma and space. [just parity]

## Upstream readings

| Reading | Choice |
|---|---|
| Repeated blocks overwrite a Map entry | retain first insertion index and replace item list |
| Self-transitions only log and are filtered | emit warning, preserve acceptance, omit transition |
| Imported NEWLINE excludes lone CR | shared preprocessing wins |
| DOM-derived seed at zero | deterministic chart-family seed wins |
| Fixed domain geometry | parser retains semantic data; layout owns the frame, confusion ellipse, cliff, and fold |

- cynefin-26: Go and Rust MUST produce the same ordered resolved model under both metric profiles. [just parity]
