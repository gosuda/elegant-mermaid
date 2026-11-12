# Timeline grammar

This file fixes lexical rules, syntax, AST spans, semantic resolution, and diagnostics for `timeline`.

## Scope

- timeline-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/timeline/parser/timeline.jison` lines 6–39 (lexer) and 49–87 (productions and actions). [just oracle]
- timeline-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/timeline/timelineDb.js` lines 1–70 and 89–114, with `../common/commonDb.ts` lines 1–32 for metadata; config keys MUST follow `schemas/config.schema.yaml` lines 476–525 and 1961–2087 under the same upstream `src/` directory. [just parity]
- timeline-03: The parser MUST accept headers, title, accessibility title and description, sections, periods, and events; it MUST NOT expose database helpers that no production calls. Layout MUST remain owned by `spec/layout/lanes.md`. [just oracle]

## Header forms

- timeline-04: Detection MUST accept the case-sensitive keyword `timeline` with the boundary of `spec/detection.md`; the kind lexer MUST use ASCII-insensitive keyword matching after detection. [just oracle]
- timeline-05: The header MUST accept `timeline`, `timeline LR`, and `timeline TD`; the direction suffix MUST use one or more spaces or tabs, and LR and TD MUST match ASCII-insensitively. An absent suffix MUST resolve to LR; TD MUST remain TD in the syntax/model direction and normalize to TB only where the dump contract requires it. [just parity]

## Lexer modes

- timeline-06: The lexer MUST use INITIAL and the exclusive modes `acc_title`, `acc_descr`, and `acc_descr_multiline`; it MUST select the first applicable matching rule in source order. [just parity]

| Mode | Entry | Exit |
|---|---|---|
| INITIAL | Start | Accessibility opener |
| acc_title | `accTitle` plus optional whitespace, colon, optional whitespace | Value token restores INITIAL |
| acc_descr | `accDescr` plus optional whitespace, colon, optional whitespace | Value token restores INITIAL |
| acc_descr_multiline | `accDescr` plus optional whitespace, `{`, optional whitespace | `}` restores INITIAL |

### Lexical rules in first-match order

- timeline-07: After shared preprocessing, the lexer MUST use the following authority order; an unqualified rule applies only in INITIAL. LF in these patterns MUST mean the shared physical line-ending rule. [just parity]

| Authority line | Mode and pattern | Result |
|---|---|---|
| 14 | INITIAL: `%%` not followed by `{`, then non-LF bytes | Skip comment |
| 15 | INITIAL: one byte other than `}`, then `%%`, then non-LF bytes | Skip the whole match, including the preceding byte |
| 16 | INITIAL: one or more LF | NEWLINE |
| 17 | INITIAL: one or more whitespace characters | Skip |
| 18 | INITIAL: `#` then non-LF bytes | Skip comment |
| 20 | INITIAL: `timeline`, SP/HT run, `LR` | timeline_lr |
| 21 | INITIAL: `timeline`, SP/HT run, `TD` | timeline_td |
| 22 | INITIAL: `timeline` | timeline |
| 23 | INITIAL: `title`, one whitespace character, one or more non-LF characters | title |
| 24 | INITIAL: `accTitle`, optional whitespace, `:`, optional whitespace | acc_title; enter acc_title |
| 25 | acc_title: all bytes through the next line end, possibly empty | acc_title_value; pop mode |
| 26 | INITIAL: `accDescr`, optional whitespace, `:`, optional whitespace | acc_descr; enter acc_descr |
| 27 | acc_descr: all bytes through the next line end, possibly empty | acc_descr_value; pop mode |
| 28 | INITIAL: `accDescr`, optional whitespace, `{`, optional whitespace | Enter acc_descr_multiline; no token |
| 29 | acc_descr_multiline: `}` | Pop mode; no token |
| 30 | acc_descr_multiline: bytes other than `}`, including line ends | acc_descr_multiline_value |
| 31 | INITIAL: `section`, one whitespace character, one or more bytes other than colon or LF | section |
| 34 | INITIAL: `:`, one whitespace character, then one or more non-colon/non-LF characters or colons not followed by whitespace | event |
| 35 | INITIAL: one or more bytes other than `#`, colon, or LF | period |
| 38 | End of input | EOF |
| 39 | INITIAL: any remaining character | INVALID |

- timeline-08: Keyword prefixes inside the body MUST keep this lexer precedence; the shared header boundary MUST NOT become a new boundary on `title` or `section`. Whitespace consumed by a keyword rule MUST remain in that token. [just oracle]
- timeline-09: A colon followed by whitespace MUST start a new event token only when the event rule can consume its required payload; other colons MUST remain inside the current event, so `http://example.com` stays one value. Semicolons MUST remain text, not separators. [just oracle]
- timeline-10: Quotes MUST remain ordinary text; they MUST NOT create a string mode, conceal a colon separator, or require a closing quote. A hash inside a title, section, event, or accessibility value MUST remain text when that token rule has already consumed it. [just oracle]

## Grammar

- timeline-11: The parser MUST use the following EBNF; quoted lowercase names denote token kinds, not additional source keywords. [just parity]

```ebnf
start = timeline_header, document, EOF ;
timeline_header = "timeline" | "timeline_lr" | "timeline_td" ;
document = { line } ;
line = [ SPACE ], statement | NEWLINE | EOF ;
statement = "title"
          | "acc_title", acc_title_value
          | "acc_descr", acc_descr_value
          | acc_descr_multiline_value
          | "section"
          | period_statement
          | event_statement ;
period_statement = period ;
event_statement = event ;
```

- timeline-12: SPACE MUST remain unreachable because the lexer emits no SPACE token; adjacent period and event statements MUST NOT require a NEWLINE. EOF in `line` MUST NOT require an extra physical end-of-input marker. [just oracle]
- timeline-13: An accessibility block MUST end at its first `}`; its delimiters MUST emit no statement token. An empty block MUST set no description because it emits no value token. [just oracle]

## Statement boundary

- timeline-14: Recovery MUST skip to the next physical line end outside an accessibility block, or through that block's closing brace; it MUST resume with the next line. [just go-check]
- timeline-15: An invalid token in a recognized statement MUST produce `timeline/unexpected-token`; an unrecognized statement MUST produce `timeline/unknown-statement` and MUST NOT create a period. A normal period token MUST remain a valid statement even when its text resembles an unsupported command. [just oracle]
- timeline-16: End of input in an accessibility block MUST produce `timeline/unterminated` from its opening brace to source end. No quote-termination diagnostic MUST be emitted for ordinary timeline text. [just go-check]

## Abstract syntax tree

- timeline-17: AST nodes MUST use upstream production names in PascalCase; each span MUST cover the first through last consumed token and exclude a trailing line separator. [just parity]

| Node | Fields | Span |
|---|---|---|
| Start | TimelineHeader, Document | Header start through final statement |
| TimelineHeader | Header token, optional direction | Complete header token |
| Document | Ordered Line list | First through last line; empty range after header when empty |
| Line | Optional Statement or separator | Statement span, or separator span for a blank line |
| Statement | Title, accessibility value, section, PeriodStatement, or EventStatement variant | Complete statement including metadata opener and block delimiters when present |
| PeriodStatement | Borrowed period token | Whole period token |
| EventStatement | Borrowed event token | Colon through event payload |

- timeline-18: Tokens MUST borrow source text; the AST MUST retain payload ranges separately from whole-token spans, including the accessibility opener that emits no token. [just parity]

## Semantic resolution

- timeline-19: Resolution MUST start with direction LR, empty current section, empty ordered section and period lists, and empty common metadata; it MUST traverse statements in source order. [just parity]
- timeline-20: A section MUST remove exactly the first eight token characters and store the rest without trimming; it MUST append that string even if another section has the same name and MUST replace the current section string. [just parity]
- timeline-21: A period MUST create one task record with its exact token text, current section as both `section` and `type`, score 0, and an empty event list. It MUST receive the next declaration-order id. [just parity]
- timeline-22: An event MUST remove exactly the first two token characters and append the remainder without trimming to the most recently created period; a continuation line that starts with `:` MUST use the same action and MUST NOT create a new period. [just parity]
- timeline-23: A new section MUST NOT reset the current period; an event after a section but before a new period MUST still append to the preceding period, whose stored section MUST remain unchanged. [just oracle]
- timeline-24: An event with no preceding period MUST produce `timeline/event-without-period` rather than reproducing the database's undefined-task exception; it MUST NOT create an implicit period. [just oracle]
- timeline-25: A title MUST remove exactly the first six token characters and replace the diagram title through the common metadata text handling; repeated title or accessibility declarations MUST use the last value. [just parity]
- timeline-26: An accessibility title or description MUST trim its parsed value at both ends before common metadata handling. The common title setter MUST remove leading whitespace after sanitization; the description setter MUST remove whitespace immediately after each LF after sanitization. Metadata MUST use the project's static escaped-text handling, not execute HTML. [just parity]
- timeline-27: Period and event strings MUST preserve trailing spaces and embedded semicolons; entity decoding and text rendering MUST follow the shared label contract without changing source spans. [just parity]
- timeline-28: The model MUST expose one ordered period list with ordered event lists and an ordered section-declaration list; duplicate section names MUST remain strings, not a uniqueness error. Repeated reads MUST NOT duplicate periods or reproduce `getTasks()`'s append-on-read side effect. [just parity]
- timeline-29: Unreachable `addTaskOrg` and the database compilation retry loop MUST NOT add source forms, diagnostics, or layout behavior. Cross-document task-id persistence in upstream `clear()` MUST NOT affect this project's declaration indices. [just parity]

## Diagnostics

- timeline-30: The parser and resolver MUST emit exactly the timeline diagnostics below; shared preprocessing and source diagnostics MUST remain in their shared registries. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| timeline/unexpected-token | error | Parser | Token rejected by current production | Offending token | unexpected TOKEN, expected one of: LIST |
| timeline/unknown-statement | error | Parser | No statement rule accepts the statement | First token through recovery boundary, excluding separator | unknown statement TOKEN |
| timeline/unterminated | error | Lexer/parser | Unclosed accessibility block | Opening brace through source end | unterminated TOKEN |
| timeline/event-without-period | error | Resolver | Event before any period | Whole event token | event has no preceding period |

- timeline-31: TOKEN MUST be the source token text; LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `. Diagnostics MUST have no fix and empty help unless a shared rule defines one. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| timeline.jison 14–39 | First-match tokens, accessibility modes, colon event split | Lexer modes |
| timeline.jison 49–87 | Header direction and complete statement actions | Grammar; semantic resolution |
| timelineDb.js 12–70 | LR reset, section strings, period records, append-to-last events | Semantic resolution |
| timelineDb.js 38–49, 72–101 | Read side effects and unreachable helper | Semantic resolution |
| common/commonDb.ts 16–30 | Metadata replacement and whitespace handling | Semantic resolution |
| timeline.spec.js 78–186 | Colon continuation, URL colon, semicolons, hashes, trailing spaces | Lexer; semantic resolution |
| config.schema.yaml 476–525, 1961–2087 | Inherited and timeline config properties | Config registry |

- timeline-32: Go and Rust MUST preserve the same statement spans, section strings, period strings, event strings, metadata, and declaration order. [just parity]
