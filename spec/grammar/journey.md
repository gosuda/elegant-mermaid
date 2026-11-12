# Journey grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `journey` kind.

## Scope

- journey-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/user-journey/parser/journey.jison:6-69`; semantic resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/user-journey/journeyDb.js:12-130`. [just oracle]
- journey-02: Configuration classification MUST cover `JourneyDiagramConfig` at `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:1820-1959` and inherited `BaseDiagramConfig` properties at lines 476-525. [just gen-check]
- journey-03: Shared preprocessing, source positions, and detection MUST follow their topic specifications; this file MUST NOT define placement or drawing rules. [just parity]

## Header forms

- journey-04: Detection MUST accept only the case-sensitive header `journey` with the keyword boundary of `spec/detection.md`; the body lexer MUST retain the authority's ASCII case-insensitive keyword matching. [just oracle]
- journey-05: The parser MUST accept an empty document after the header and MUST NOT require a newline between the header and the first body token. [just oracle]

## Lexer modes

- journey-06: The lexer MUST use INITIAL and the exclusive modes `acc_title`, `acc_descr`, and `acc_descr_multiline`; within each active mode the first matching rule MUST win. [just parity]

| Mode | Entry | Exit |
|---|---|---|
| INITIAL | start | accessibility opener |
| acc_title | `accTitle` plus optional whitespace, colon, optional whitespace | one value token |
| acc_descr | `accDescr` plus optional whitespace, colon, optional whitespace | one value token |
| acc_descr_multiline | `accDescr` plus optional whitespace, `{`, optional whitespace | `}` |

### Lexical rules in first-match order

- journey-07: The lexer MUST apply the following ordered rules; the order numbers are authority line numbers, and unqualified rules apply only in INITIAL. [just parity]

| Order | Pattern and mode | Action |
|---|---|---|
| 14 | `%%` not followed by `{`, then bytes other than LF | discard comment |
| 15 | one character other than `}`, then `%%`, then bytes other than LF | discard entire match, including its first character |
| 16 | one or more LF | emit NEWLINE |
| 17 | one or more whitespace characters | discard |
| 18 | `#`, then bytes other than LF | discard comment |
| 20 | `journey` | emit journey |
| 21 | `title`, one whitespace character, one or more characters other than `#`, LF, `;` | emit title |
| 22 | `accTitle`, optional whitespace, `:`, optional whitespace | emit acc_title; enter acc_title |
| 23 | acc_title: remaining characters through the next LF, possibly empty | emit acc_title_value; restore INITIAL |
| 24 | `accDescr`, optional whitespace, `:`, optional whitespace | emit acc_descr; enter acc_descr |
| 25 | acc_descr: remaining characters through the next LF, possibly empty | emit acc_descr_value; restore INITIAL |
| 26 | `accDescr`, optional whitespace, `{`, optional whitespace | enter acc_descr_multiline; emit nothing |
| 27 | acc_descr_multiline: `}` | restore INITIAL; emit nothing |
| 28 | acc_descr_multiline: characters other than `}`, possibly including line ends | emit acc_descr_multiline_value |
| 29 | `section`, one whitespace character, one or more characters other than `#`, `:`, LF, `;` | emit section |
| 30 | one or more characters other than `#`, `:`, LF, `;` | emit taskName |
| 31 | `:`, then one or more characters other than `#`, LF, `;` | emit taskData |
| 32 | `:` | emit colon token |
| 33 | end of input | emit EOF |
| 34 | any otherwise unmatched character | emit INVALID |

- journey-08: Tokens MUST retain their exact source text and byte spans; comments and skipped whitespace MUST NOT enter the AST. [just parity]
- journey-09: The lexer MUST preserve the greedy taskName and taskData rules: a quote MUST NOT introduce a string, a later colon MUST remain inside taskData, and a semicolon MUST NOT act as a separator. [just oracle]
- journey-10: Shared preprocessing MUST normalize line handling according to `spec/preprocessing.md`; the ordered lexer table MUST apply to the resulting body view while spans retain original source offsets. [just parity]
- journey-11: Accessibility single-line values MUST retain `#` and `;` as text after entry into their exclusive mode; multiline values MUST end at the first `}` and MUST NOT nest. [just oracle]

## Grammar

- journey-12: The parser MUST use the following EBNF with authority production names; token names refer to the ordered lexer table. [just parity]

```ebnf
start = journey, document, EOF ;
document = { line } ;
line = SPACE, statement | statement | NEWLINE | EOF ;
statement = title
          | acc_title, acc_title_value
          | acc_descr, acc_descr_value
          | acc_descr_multiline_value
          | section
          | taskName, taskData ;
```

- journey-13: SPACE MUST remain unreachable because the lexer emits no SPACE token; the unused precedence declaration for `^` MUST NOT introduce an expression syntax. [just oracle]
- journey-14: A task MUST contain both taskName and taskData; a bare colon, standalone name, or INVALID token MUST be rejected. [just oracle]
- journey-15: The statement forms MUST be limited to title, accessibility title, accessibility description in either form, section, and task; token adjacency MUST be accepted wherever the EBNF permits it. [just oracle]

## Statement boundary

- journey-16: Error recovery MUST skip to the next physical line end outside an accessibility multiline value, or to EOF; a semicolon MUST NOT be a recovery separator. [just go-check]
- journey-17: Recovery MUST emit one primary diagnostic for a rejected statement and MUST NOT create a task from its rejected text. [just parity]
- journey-18: EOF inside `acc_descr_multiline` MUST produce `journey/unterminated` spanning from its opening `{` through EOF; quotes in ordinary task text MUST NOT produce that diagnostic. [just go-check]

## Abstract syntax tree

- journey-19: AST nodes MUST use the upstream production names in PascalCase and MUST use half-open byte spans from their first token through their last token, without a trailing line separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | header token, Document | header start through last document token |
| Document | ordered Line list | first through last line; empty at header end |
| Line | optional Statement or newline/EOF alternative | statement span, or separator span |
| Statement | tagged title, acc_title/value, acc_descr/value, multiline value, section, or taskName/taskData tokens | full matched production; accessibility delimiter spans are retained separately |

- journey-20: A multiline Statement MUST retain the opening and closing braces even though the lexer emits neither; the model MUST retain task-name, score-field, actor-field, section, and metadata spans for diagnostics. [just parity]

## Semantic resolution

- journey-21: Resolution MUST visit statements in declaration order; each section MUST append its text to the section list and replace the current section, whose initial value is the empty string. [just parity]
- journey-22: A section's text MUST be its token after the first eight characters; a title's text MUST be its token after the first six characters; resolution MUST NOT additionally trim section text or task names. [just parity]
- journey-23: Repeated title and accessibility statements MUST replace the previous value; accessibility values MUST be trimmed with ECMAScript String.trim semantics before assignment. [just oracle]
- journey-24: A task MUST append one record with `section` and `type` both equal to the current section, `task` equal to the complete taskName token, and `score` and `people` resolved by the next clauses. [just parity]
- journey-25: Task data MUST lose its first colon and then split at every colon, preserving empty fields; field zero MUST be trimmed with ECMAScript String.trim semantics and parsed as `score = [ "+" | "-" ], digit, { digit }`, where digit is an ASCII decimal digit. [just go-check]
- journey-26: An empty, non-numeric, or non-integer score field MUST raise `journey/unexpected-token` with LIST `integer` and the trimmed score field as TOKEN; decimal points, exponent forms, Infinity, NaN, and radix prefixes MUST NOT be accepted. An integer outside the inclusive bounds `journey.score_min` (1) and `journey.score_max` (5) MUST raise `journey/score-out-of-range` with message `score SCORE is outside the range MIN to MAX` at the score token, excluding surrounding whitespace; resolution MUST NOT clamp it. These checks implement `spec/layout/lanes.md` lanes-26 and differ from upstream's unrestricted Number conversion. [just go-check]
- journey-27: When there is only one field, people MUST be an empty list; otherwise people MUST be field one split on commas and individually trimmed with ECMAScript String.trim semantics; fields after field one MUST be ignored. [just parity]
- journey-28: Actor lists MUST preserve order, duplicates, case, and empty names within each task; the diagram actor list MUST contain distinct names from all tasks sorted by ECMAScript default string order (lexicographic UTF-16 code units). [just parity]
- journey-29: Tasks before any section MUST remain in the empty section, and duplicate section names MUST remain duplicate section declarations; no database validation diagnostic MUST be invented for these cases. [just oracle]
- journey-30: Resolution MUST expose each parsed task once; repeated getter calls MUST NOT duplicate tasks, and the database's bounded scan of unset `processed` flags MUST NOT become a parser loop or an additional language constraint. [just parity]

## Diagnostics

- journey-31: Parser rejections and the planned score-range check MUST use exactly the following codes; upstream adds no throwing validation check to `addSection` or `addTask`, but lanes-26 requires the score-range diagnostic. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| journey/unexpected-token | error | token rejected by the current production | offending token; zero-width at EOF | `unexpected TOKEN, expected one of: LIST` |
| journey/unknown-statement | error | statement start fits no statement form | first token through the recovery boundary, excluding line ending | `unknown statement TOKEN` |
| journey/unterminated | error | input ends inside an accessibility block | opening `{` through EOF | `unterminated TOKEN` |
| journey/score-out-of-range | error | integer score below `journey.score_min` or above `journey.score_max` | score token, excluding surrounding whitespace | `score SCORE is outside the range MIN to MAX` |

- journey-32: TOKEN MUST be the offending source text or opening delimiter; LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; these diagnostics MUST have empty help and no fix. For a rejected score field, the span MUST cover the trimmed field, or be zero-width at the field's start when it is empty. SCORE MUST be the score token text, and MIN and MAX MUST be the minimal decimal values of `journey.score_min` and `journey.score_max`. Integer range comparison MUST NOT wrap or require a machine-sized conversion before it reports an out-of-range score. [just parity]

## Upstream readings

| Reading | Authority fact | Resolution here |
|---|---|---|
| journey.jison:6-34 | case-insensitive lexer, three exclusive modes, first-match rules | body keywords fold ASCII case; shared header detection remains case-sensitive |
| journey.jison:42-66 | six statement alternatives and permissive document sequence | EBNF and production-named AST above |
| journeyDb.js:26-32, 60-83 | section insertion, colon splitting, Number score, trimmed comma list | preserve name and actor semantics; replace Number conversion with the planned integer score and range checks |
| journeyDb.js:34-58, 96-115 | getter appends raw tasks; actors use Set and default sort | immutable model exposes tasks once; actor ordering uses UTF-16 |

- journey-33: An unreachable helper such as `addTaskOrg` MUST NOT add a statement form; Go and Rust MUST resolve the same ordered sections, tasks, metadata, and actor lists. [just parity]
