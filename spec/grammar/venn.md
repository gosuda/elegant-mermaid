# Venn grammar

This file fixes syntax and model resolution for the `venn` kind.

## Scope

- venn-01: The implementation MUST use `.references/mermaid/packages/mermaid/src/diagrams/venn/parser/venn.jison:1-133` as its syntax authority, `vennDB.ts:16-95` as its resolution authority, and `vennTypes.ts:4-35` as its record authority. [just oracle]
- venn-02: Configuration MUST cover `config.schema.yaml:3070-3099` and the inherited properties at `476-525`; the classification is in `spec/data/config-keys/venn.json`. [just gen-check]

## Header forms

- venn-03: Detection MUST accept only the case-sensitive header `venn-beta` with the boundary of `spec/detection.md`; after detection, body keywords MUST use ASCII case-insensitive matching, as the authority lexer requests. [just oracle]

## Lexer modes

- venn-04: The lexer MUST retain `INITIAL` and the inclusive mode `bol`; a line ending enters `bol`, and its first non-indentation byte returns to `INITIAL` without consuming that byte. [just parity]
- venn-05: The lexer MUST take the first matching rule in the following order; the line-ending rule MUST use the shared LF, CRLF, and lone-CR contract. [just parity]

| Authority line | Mode | Match and action |
|---|---|---|
| 7 | all inclusive modes | `%%` not followed by `{`, through the next LF: discard comment |
| 8 | all inclusive modes | a byte other than `}` followed by `%%`, through the next LF: discard the whole match |
| 10 | bol | spaces or tabs before a line ending: discard |
| 11-17 | bol | spaces or tabs before the word `text`: if indent mode is on, emit `INDENT_TEXT`, set consume-indent-text, and enter INITIAL; otherwise discard |
| 18 | bol | remaining spaces or tabs: discard |
| 19 | bol | another non-whitespace byte: clear indent mode, enter INITIAL, and retry the byte |
| 21 | both | one or more line-ending bytes: emit NEWLINE and enter bol |
| 22 | both | remaining `%%` comment through LF: discard |
| 23 | both | spaces and tabs: discard |
| 24 | both | end of input: EOF |
| 26 | both | `title`, whitespace, then one or more bytes other than `#`, LF, or `;`: TITLE |
| 27-31 | both | `venn-beta`, `set`, `union`, `text`, `style`: VENN, SET, UNION, TEXT, STYLE; consume the first `text` without emitting TEXT when consume-indent-text is set, then clear that flag |
| 33 | both | bracketed double-quoted label: BRACKET_LABEL; remove the bracket and quote delimiters |
| 34 | both | nonempty bracket label containing neither `]` nor double quote: BRACKET_LABEL; remove brackets and trim |
| 36 | both | optional sign followed by digits with optional fraction, or a leading-dot fraction: NUMERIC |
| 37 | both | `#` followed by 3 through 8 hex digits: HEXCOLOR |
| 38 | both | rgba function with four comma-separated digit/dot components and optional spaces: RGBACOLOR |
| 39 | both | rgb function with three such components: RGBCOLOR |
| 40 | both | ASCII letter or underscore, then ASCII letters, digits, hyphens, or underscores: IDENTIFIER |
| 41 | both | double-quoted text without an embedded double quote: STRING; retain quotes in token value |
| 43-44 | both | comma, colon: COMMA, COLON |

- venn-06: Quoted strings MUST NOT interpret escapes; their lexer pattern can include line endings, and their span MUST include the quotes. [just oracle]
- venn-07: Body keyword rules MUST retain their position before IDENTIFIER, including their prefix-matching behavior; the stricter detection boundary MUST apply to the header only. [just oracle]

## Grammar

- venn-08: The parser MUST implement the following productions without backtracking; a statement MUST NOT require a newline after it. [just parity]

```ebnf
start = optNewlines, VENN, document, EOF ;
optNewlines = { NEWLINE } ;
document = { line } ;
line = NEWLINE | statement ;
statement = TITLE
          | SET, identifier, [ BRACKET_LABEL ], [ COLON, NUMERIC ]
          | UNION, identifierList, [ BRACKET_LABEL ], [ COLON, NUMERIC ]
          | TEXT, identifierList, ( IDENTIFIER | STRING ), [ BRACKET_LABEL ]
          | TEXT, identifierList, NUMERIC
          | INDENT_TEXT, indentedTextTail
          | STYLE, identifierList, stylesOpt ;
indentedTextTail = ( IDENTIFIER | STRING ), [ BRACKET_LABEL ] | NUMERIC ;
stylesOpt = styleField, { COMMA, styleField } ;
styleField = IDENTIFIER, COLON, styleValue ;
styleValue = STRING | valueTokens ;
valueTokens = valueToken, { valueToken } ;
valueToken = IDENTIFIER | NUMERIC | HEXCOLOR | RGBCOLOR | RGBACOLOR ;
identifierList = identifier, { COMMA, identifier } ;
identifier = IDENTIFIER | STRING ;
```

- venn-09: A numeric text id MUST NOT take a bracket label; a set MUST take exactly one identifier, while a union MUST take at least two identifiers. [just oracle]

## Statement boundary

- venn-10: Recovery MUST skip to the next physical line ending outside a quoted string or bracket label, or to EOF; an unknown statement MUST NOT create a set. [just go-check]
- venn-11: EOF inside a string or label MUST raise `venn/unterminated` from its opening delimiter through EOF. [just go-check]

## Abstract syntax tree

- venn-12: AST nodes MUST use authority production names in PascalCase and MUST carry half-open byte spans from their first token through their last token, excluding trailing separators. [just parity]

| Node | Fields and span |
|---|---|
| Start | header, Document; full parsed source range |
| OptNewlines | leading separator spans |
| Document | ordered Line nodes; body range |
| Line | newline token or Statement; its consumed range |
| Statement | title, set, union, text, indented text, or style variant; ordered tokens and child nodes |
| IndentedTextTail | id and optional label; payload range |
| StylesOpt | ordered StyleField nodes; first through last field |
| StyleField | key and StyleValue; key through value |
| StyleValue | STRING or ValueTokens; value range |
| ValueTokens | ordered ValueToken nodes |
| ValueToken | kind and borrowed source span |
| IdentifierList | ordered Identifier nodes including repeated ids |
| Identifier | borrowed IDENTIFIER or STRING token |

- venn-13: The model MUST retain statement, identifier, label, numeric, and style-field spans so diagnostics do not need to search source text. [just parity]

## Semantic resolution

- venn-14: Resolution MUST process statements in declaration order and retain separate ordered subset, text, and style records; duplicate declarations MUST remain records rather than overwrite earlier subsets. [just parity]
- venn-15: Identifier normalization MUST trim surrounding whitespace and remove one enclosing pair of double quotes; each record's normalized set or target list MUST sort bytewise while retaining duplicate entries. [just parity]
- venn-16: A SET MUST register its normalized identifier as known; a UNION MUST reject every identifier not registered by an earlier SET, and MUST NOT create implicit sets. [just oracle]
- venn-17: A subset MUST store its normalized optional label and explicit numeric size; an omitted size MUST mean `10 / k²` for list length `k`, converted to thousandths with the chart numeric rule. [just parity]
- venn-18: Numeric literals MUST use checked integer thousandths and half-away-from-zero rounding; negative and zero sizes MUST NOT be rejected merely for their sign because the upstream database accepts them. [just oracle]
- venn-19: SET and UNION MUST set currentSets to their sorted identifier list and enable indent mode; an unindented nonblank statement MUST clear indent mode, while blank lines and comments MUST NOT clear it. [just oracle]
- venn-20: An indented text statement MUST use currentSets and MUST report `venn/text-requires-set` if none exists; explicit TEXT MUST use its own identifier list without validating that list against known sets. [just oracle]
- venn-21: Text records MUST store the normalized id and optional normalized label; style records MUST store sorted targets and source-ordered key/value pairs with the later value of a duplicate key winning. [just parity]
- venn-22: Style valueTokens MUST join with one space; quoted style values MUST normalize by the same trim-and-unquote operation, and style targets MUST NOT require prior declarations. [just oracle]
- venn-23: TITLE MUST set the diagram title from the token after its six-byte prefix; a later title MUST replace an earlier one. [just oracle]
- venn-24: The resolved model MUST count distinct singleton set identifiers; zero sets MUST raise `venn/no-sets`, and more than three MUST raise `venn/too-many-sets`, both as errors with no scene, under the deliberate `venn-set-count` divergence. [just oracle]
- venn-25: The chart payload MUST preserve singleton sets, pair overlap records, labels, text records, style records, and their declaration indices; an absent pair overlap MUST be zero, and a three-set overlap MUST remain available as a region label even though the fixed three-circle geometry does not match overlap values. [just parity]
- venn-26: Layout MUST remain owned by `spec/layout/charts.md`; set series indices MUST follow declaration order, labels MUST remain available for text output, and the parser MUST NOT import the upstream Venn layout library. [just parity]

## Diagnostics

- venn-27: Rejections MUST use the following registry rows; LIST MUST list accepted token-kind names in bytewise order, joined with `, `, and TOKEN MUST be offending source text. [just parity]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| venn/unexpected-token | error | token fails the active production | offending token | unexpected TOKEN, expected one of: LIST |
| venn/unknown-statement | error | no statement form starts here | first token through recovery boundary | unknown statement TOKEN |
| venn/unterminated | error | EOF in quoted string or bracket label | opener through EOF | unterminated TOKEN |
| venn/union-requires-multiple-identifiers | error | union has fewer than two ids | union identifier list | union requires multiple identifiers |
| venn/unknown-set-identifier | error | union names undeclared ids | first unknown identifier; remaining unknown ids as related spans | unknown set identifier: IDS |
| venn/text-requires-set | error | indented text has no current subset | indented text statement | text requires set |
| venn/no-sets | error | no distinct singleton set exists | header keyword | venn diagram has no sets |
| venn/too-many-sets | error | fourth distinct singleton set appears | fourth distinct set declaration | venn diagram has more than three sets |

## Upstream readings

- venn-28: The implementation MUST retain these authority distinctions: `union` stores an intersection record despite its name; explicit text and style targets are not validated; subset duplication is not rejected; sizes default by identifier-list length, not distinct count. [just oracle]
- venn-29: The set-count code names MUST follow the plan's Venn count and theorem sections; because those sections specify no literal diagnostic message, the two message templates in this file MUST be the stable project wording. [just parity]
