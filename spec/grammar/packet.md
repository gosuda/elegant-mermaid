# Packet grammar

This file fixes packet tokens, syntax, source spans, model resolution, and diagnostics.

## Scope

- packet-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/packet/packet.langium:1-21`, with `common/common.langium:6-34` for imported productions and terminals. [just oracle]
- packet-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/packet/parser.ts:9-107` and `db.ts:18-53`; common metadata conversion MUST follow `packages/parser/src/language/common/valueConverter.ts:44-68` and `packages/mermaid/src/diagrams/common/populateCommonDb.ts:4-13`. [just oracle]
- packet-03: Shared preprocessing and source-position rules MUST run first; spans MUST index repaired UTF-8 source bytes with exclusive ends. [just parity]

## Header forms

- packet-04: The first header MUST be `packet` or `packet-beta`, case-sensitive, with the boundary in `spec/detection.md`. [just oracle]
- packet-05: The parser MUST accept an empty body and MUST NOT require a line ending immediately after the header. [just oracle]

## Lexer modes

- packet-06: The lexer MUST use one `INITIAL` mode; this Langium grammar defines no start conditions. [just parity]
- packet-07: The lexer MUST take the first matching token in authority order, with generated literal tokens before imported terminals; the longer header literal `packet-beta` MUST precede `packet`. [just parity]

### Lexical rules in first-match order

The imported terminal order is below. Rules that the packet productions do not consume remain lexical rules, not additional statement forms.

| Order | Pattern or token | Result |
|---|---|---|
| literals | `packet-beta`, `packet`, `-`, `+`, `:` | literal tokens |
| common:12 | `true` or `false` | `BOOLEAN` |
| common:14 | optional horizontal whitespace, `accDescr`, then colon and line text, or whitespace and a brace-delimited body | `ACC_DESCR` |
| common:15 | optional horizontal whitespace, `accTitle`, optional horizontal whitespace, colon, line text | `ACC_TITLE` |
| common:16 | optional horizontal whitespace, `title`, then horizontal whitespace and line text, or no text | `TITLE` |
| common:18 | digits, dot, digits, not followed by another dot | `FLOAT` |
| common:19 | `0`, or a nonzero digit followed by digits, not followed by a dot | `INT` |
| common:20 | `FLOAT` or `INT` | `NUMBER` |
| common:22 | matching single or double quotes; interior is a non-quote, non-backslash scalar or backslash plus one scalar | `STRING` |
| common:27 | ASCII word character followed by word characters or internal hyphens; final character is a word character | `ID` |
| common:29 | LF or CRLF | `NEWLINE` |
| common:31 | one or more spaces or tabs | hidden `WHITESPACE` |
| common:32 | frontmatter fences and their body | hidden `YAML` |
| common:33 | directive opener through closing delimiter | hidden `DIRECTIVE` |
| common:34 | optional spaces or tabs, `%%`, text to line end | hidden `SINGLE_LINE_COMMENT` |

- packet-08: `INT` MUST contain decimal digits only; signed, fractional, exponent, and leading-zero multi-digit values MUST NOT be accepted as a field operand. [just oracle]
- packet-09: A `STRING` MUST keep its delimiters in its span and MUST remove them from its value; the default Langium string conversion MUST remove each escape backslash and retain the next character, without JSON escape interpretation. [just parity]
- packet-10: Quoted labels MUST permit physical line endings and escaped quote characters; comments, colons, and range punctuation inside a label MUST remain label text. [just oracle]
- packet-11: Metadata line values MUST stop before `%%` or the physical line end; brace descriptions MUST stop at the first closing brace. [just oracle]
- packet-12: Shared line-ending handling MUST also treat lone CR as a line ending, as `spec/preprocessing.md` requires. [just parity]

## Grammar

- packet-13: The parser MUST implement this EBNF; `EOF` consumes no source byte and `EOL` does not imply a semicolon separator. [just parity]

```ebnf
Packet = { NEWLINE }, ("packet" | "packet-beta"),
         { TitleAndAccessibilities | PacketBlock | NEWLINE } ;
PacketBlock = (INT, ["-", INT] | "+", INT), ":", STRING, EOL ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE), EOL,
                         { (ACC_DESCR | ACC_TITLE | TITLE), EOL } ;
EOL = NEWLINE, { NEWLINE } | EOF ;
```

- packet-14: The only body statements MUST be a packet field, title, accessibility title, or accessibility description; an identifier or an unquoted label MUST NOT create a field. [just oracle]

## Statement boundary

- packet-15: Recovery MUST skip to the next physical line ending outside a quoted label or brace description; an EOF inside either delimiter MUST report `packet/unterminated`. [just go-check]
- packet-16: An unknown statement MUST span its first token through its boundary, excluding the line ending; recovery MUST NOT append a partial field. [just parity]

## Abstract syntax tree

- packet-17: AST names MUST follow authority productions in PascalCase; the parser MUST keep the following nodes and token spans. [just parity]

| Node | Fields | Span |
|---|---|---|
| `Packet` | header, ordered blocks, title, accTitle, accDescr | header through last statement, excluding trailing separators |
| `PacketBlock` | optional start, optional end, optional bits, label; operand and label spans | first operand or `+` through closing label quote |
| `TitleAndAccessibilities` | ordered metadata assignments and their value spans | first metadata token through last metadata token, excluding EOL |
| `EOL` | newline token spans or EOF offset | consumed line endings, or zero width at EOF |

- packet-18: `TitleAndAccessibilities` MUST remain a syntactic view, not a separate semantic entity, because the authority declares it as a fragment; tokens MUST borrow the source. [just parity]

## Semantic resolution

- packet-19: Resolution MUST process fields in declaration order with `lastBit = -1`; a single-bit form MUST resolve to `start = end` and `bits = 1`. [just oracle]
- packet-20: An explicit range MUST reject `end < start` before the contiguity check; equal endpoints MUST be accepted despite the wording of the upstream error. [just oracle]
- packet-21: An omitted start in `+count` MUST become `lastBit + 1`; every explicit start MUST equal `lastBit + 1`, including start 0 for the first field. [just oracle]
- packet-22: A relative count of zero MUST be rejected after contiguity; a positive relative count MUST resolve `end = start + count - 1`. [just oracle]
- packet-23: An explicit range MUST resolve `bits = end - start + 1`; the resolved end MUST become `lastBit` before the next declaration. [just parity]
- packet-24: The model MUST retain the inclusive start, inclusive end, bit count, label, declaration index, and operand spans for every accepted field. [just parity]
- packet-25: Row splitting MUST preserve field order and repeat the label on every piece; it MUST use the configured `bitsPerRow` and MUST NOT impose a maximum field count or bit count absent from the adapter. [just oracle]
- packet-26: For adapter parity, a split piece MUST end at `row * bitsPerRow - 1`, and its remainder MUST start at `row * bitsPerRow`; the adapter's stored `bits` values MUST be `pieceEnd - pieceStart` for both split records, without an added 1. These stored split values MUST NOT change the original field's inclusive interval or declared bit count. [just parity]
- packet-27: The adapter MUST stop adding pieces when its accumulated packet reaches 10000 completed words or the current word length exceeds `bitsPerRow + 1`; this guard MUST NOT raise a diagnostic because upstream stops silently. Empty words MUST NOT be retained. [just oracle]
- packet-28: Metadata assignments MUST use the last assigned value for each property; a nonempty final value MUST be sent to the common database, and an empty final value MUST NOT invoke its setter. [just oracle]
- packet-29: Single-line metadata MUST trim its ends and replace every run of at least two spaces or tabs with one space; multiline descriptions MUST trim each line, collapse horizontal runs of at least two characters, and collapse consecutive CR or LF characters to one LF. [just parity]
- packet-30: Row geometry and bit-number placement MUST remain owned by `spec/layout/grid.md`; this grammar MUST NOT choose layout coordinates. [just parity]
- packet-31: Config classification MUST include the seven direct properties of `PacketDiagramConfig` at `config.schema.yaml:2755-2804` and the five inherited properties at `:476-525`; `layout`, `useWidth`, and `useMaxWidth` MUST be accepted and ignored, and the other listed properties MUST be honoured. [just gen-check]

## Diagnostics

- packet-32: Rejections MUST produce the following error diagnostics instead of throwing; generic messages MUST use source text for TOKEN and sorted bytewise token-kind names joined by `, ` for LIST. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `packet/unexpected-token` | error | token does not fit the current production | offending token | `unexpected TOKEN, expected one of: LIST` |
| `packet/unknown-statement` | error | no body statement starts with this token | statement without its line ending | `unknown statement TOKEN` |
| `packet/unterminated` | error | EOF inside quote or brace description | opener through EOF | `unterminated TOKEN` |
| `packet/range-reversed` | error | explicit end is less than start (`parser.ts:19-20`) | start through end operands | `Packet block START - END is invalid. End must be greater than start.` |
| `packet/non-contiguous` | error | resolved start differs from expected next bit (`:23-28`) | explicit start operand | `Packet block START - END is not contiguous. It should start from EXPECTED.` |
| `packet/zero-bit-field` | error | relative count is zero (`:30-31`) | count operand | `Packet block START is invalid. Cannot have a zero bit field.` |
| `packet/start-unresolved` | error | splitting receives no resolved start (`:60-61`) | field statement | `start should have been set during first phase` |
| `packet/end-unresolved` | error | splitting receives no resolved end (`:63-64`) | field statement | `end should have been set during first phase` |
| `packet/block-start-after-end` | error | splitting receives start greater than end (`:67-68`) | range operands, or relative count | `Block start START is greater than block end END.` |
| `packet/database-unavailable` | error | parser adapter receives the wrong database (`:99-102`) | header keyword | `packet parser database is unavailable` |

- packet-33: Resolution MUST report only the first failing check for one field in adapter order; the missing-start, missing-end, split-order, and wrong-database errors MUST remain internal invariant failures and MUST NOT reject a well-formed source through an unreachable helper path. [just parity]
- packet-34: Every diagnostic above MUST have an empty help string and no fix; all codes MUST occur in `spec/data/diagnostics/packet.json`. [just gen-check]

## Upstream readings

| Reading | Authority fact | Resolution |
|---|---|---|
| `packet.langium:4-21` | fields require EOL; header does not | same-line first field is legal; two fields on one line are not |
| `parser.ts:19-34` | inclusive range checks and relative counts | equality is legal; first explicit start must be zero |
| `parser.ts:38-52,71-90` | bounded row accumulation and split records | silent guard and split count quirk retained |
| `db.ts:21-29,36-39` | showBits adds 10 to effective paddingY; empty words omitted | effective renderer config belongs to the grid stage; no new source diagnostic |
| `packet/tokenBuilder.ts:3-6`, `common/tokenBuilder.ts:14-27` | only packet keyword receives whitespace/comment lookahead | shared detection still supplies this project's header boundary |

- packet-35: Go and Rust MUST resolve the same ordered fields, labels, and metadata under both metric profiles. [just parity]
