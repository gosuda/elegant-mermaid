# Ishikawa grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `ishikawa` kind.

## Scope

- ishikawa-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/ishikawa/parser/ishikawa.jison:1-56`; resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/ishikawa/ishikawaDb.ts:15-71` and `ishikawaTypes.ts:1-4`. [just oracle]
- ishikawa-02: Config classification MUST cover `IshikawaDiagramConfig` at `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:1240-1255` and inherited `BaseDiagramConfig` properties at lines 476-525. [just gen-check]
- ishikawa-03: This grammar MUST accept text nodes and whitespace-only statements; it MUST NOT add category keywords, braces, explicit edges, title directives, accessibility statements, or quoted-string syntax. [just oracle]

## Header forms

- ishikawa-04: The first header MUST be `ishikawa` or `ishikawa-beta`, matched with ASCII case folding and the boundary in `spec/detection.md`. [just oracle]
- ishikawa-05: Shared preprocessing MUST run before kind lexing; source spans MUST continue to index the original document source. [just parity]

## Lexer modes

- ishikawa-06: The lexer MUST have only `INITIAL` mode and MUST take the first matching rule in the following source order. [just parity]

### Lexical rules in first-match order

| Authority line | Pattern | Result |
|---|---|---|
| 6 | Whitespace, possibly empty, then `%%`, then all non-LF bytes on the line | `SPACELINE` |
| 7 | `ishikawa-beta`, case-insensitive | `ISHIKAWA` |
| 8 | `ishikawa`, case-insensitive | `ISHIKAWA` |
| 9 | One or more whitespace characters followed by LF | `SPACELINE` |
| 10 | One or more LF characters | `NL` |
| 11 | One or more whitespace characters | `SPACELIST` |
| 12 | One or more characters other than LF | `TEXT` |
| 13 | End of input | `EOF` |

- ishikawa-07: Whitespace matching and trimming MUST use the authority's ECMAScript whitespace set; shared line-ending handling MUST treat LF, CRLF, and lone CR as line ends. [just parity]
- ishikawa-08: Each selected rule MUST consume its greedy match; whitespace rules MAY consume several line ends, and a `TEXT` match MUST consume the rest of its line, including trailing whitespace. [just oracle]
- ishikawa-09: Header-token rules MUST keep their lexical precedence inside the body; a body token starting with an Ishikawa header spelling MUST NOT automatically become `TEXT`. [just oracle]
- ishikawa-10: Quotes, punctuation, semicolons, and braces inside a `TEXT` token MUST remain label text; they MUST NOT open a string or a block. [just oracle]

## Grammar

- ishikawa-11: The parser MUST use the following EBNF; names MUST retain the authority production names. [just parity]

```ebnf
start      = ishikawa | spaceLines, ishikawa ;
spaceLines = SPACELINE, { SPACELINE | NL } ;
ishikawa   = ISHIKAWA, [ NL ], document ;
stop       = ( NL | EOF | SPACELINE ), { NL | EOF } ;
document   = statement, stop, { statement, stop } ;
statement  = SPACELIST, TEXT | TEXT | SPACELINE | SPACELIST ;
```

- ishikawa-12: Each text statement MUST call node resolution with indentation equal to the `SPACELIST` token's length, or 0 when that token is absent, and with the trimmed `TEXT` value. [just oracle]
- ishikawa-13: Token length for indentation MUST count UTF-16 code units as upstream JavaScript does; a TAB MUST count as one code unit, not as a tab stop. [just parity]
- ishikawa-14: A `SPACELINE` or standalone `SPACELIST` statement MUST create no node and MUST NOT change the parent stack. [just oracle]
- ishikawa-15: A header without a `document` MUST be rejected; this grammar MUST NOT introduce an empty-document alternative. [just oracle]

## Statement boundary

- ishikawa-16: Error recovery MUST stop at the next physical line end or end of input and MUST resume with the next line; a semicolon MUST NOT be a recovery separator. [just go-check]
- ishikawa-17: An invalid statement MUST create no node and MUST NOT change the effect, base indentation, or cause stack. [just parity]
- ishikawa-18: Recovery MUST distinguish a token rejected inside a production from a statement for which no statement alternative applies. [just go-check]

## Abstract syntax tree

- ishikawa-19: AST nodes MUST use the upstream production names in PascalCase and MUST retain byte spans with exclusive ends. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| `Start` | optional `SpaceLines`, `Ishikawa` | First consumed token through the document end |
| `SpaceLines` | ordered whitespace tokens | First token through last token |
| `Ishikawa` | header, `Document` | Header start through document end |
| `Document` | ordered `Statement` and `Stop` pairs | First statement through last stop |
| `Statement` | optional indentation token, optional text token, whitespace-only alternative | First token through final token, without its following stop |
| `Stop` | ordered separator tokens | First separator through last separator; EOF is zero-width |

- ishikawa-20: Tokens MUST borrow source text; a text statement MUST retain separate indentation and text spans, even after model trimming. [just parity]

## Semantic resolution

- ishikawa-21: Resolution MUST start with no root, an empty stack, and no base indentation; clearing a database MUST also clear the common title and accessibility state. [just parity]
- ishikawa-22: The first text statement MUST create the effect as the root node, with its label and an empty ordered children list; it MUST set the diagram title to that label and push `(level = 0, root)`. [just oracle]
- ishikawa-23: The effect's indentation MUST NOT set the base indentation or alter its root status. [just oracle]
- ishikawa-24: The first later text statement MUST set `baseLevel` to its raw indentation; all subsequent text statements MUST retain that same base value. [just oracle]
- ishikawa-25: Each cause MUST have effective level `max(1, rawLevel - baseLevel + 1)`; indentation smaller than the first cause's indentation MUST therefore still produce level 1. [just parity]
- ishikawa-26: Before adding a cause, resolution MUST pop entries while the stack has more than one entry and its top level is greater than or equal to the new level. [just parity]
- ishikawa-27: Resolution MUST append the new cause to the remaining top node's children and then push the new `(level, node)` entry; the parent MUST be the nearest preceding active node with a strictly smaller level, or the effect when no cause qualifies. [just oracle]
- ishikawa-28: An indentation increase MUST attach to the previous active cause even when levels are skipped; equal indentation MUST produce siblings, and a decrease MUST use the stack rule rather than require a previously seen indentation value. [just oracle]
- ishikawa-29: The database MUST store every node as `text` and an ordered `children` list; it MUST NOT store separate category and cause tables or explicit parent fields. [just parity]
- ishikawa-30: Root children MUST represent the top-level categories, and their descendants MUST represent causes and sub-causes; all these nodes MUST use the same node type and preserve statement order. [just parity]
- ishikawa-31: Duplicate and empty trimmed labels MUST NOT be merged or rejected by a semantic uniqueness check; the upstream database enforces no such check. [just oracle]
- ishikawa-32: Labels MUST use shared label resolution and entity handling; source text and spans MUST NOT change when a resolved label changes. [just parity]
- ishikawa-33: Common database title and accessibility setters MUST NOT create grammar statements; text such as `accTitle: name` MUST remain an ordinary node label. [just oracle]
- ishikawa-34: Config keys `theme` and `look` MUST be honoured by the cross-cutting rules; `layout`, `useWidth`, `useMaxWidth`, and `diagramPadding` MUST be accepted and ignored because no Ishikawa layout rule reads them. [just gen-check]

## Diagnostics

- ishikawa-35: Syntax rejections MUST use exactly the following kind diagnostic rows; database insertion MUST NOT invent an indentation or duplicate-label diagnostic. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `ishikawa/unexpected-token` | error | A token does not fit the current production | Offending token; EOF is zero-width | `unexpected TOKEN, expected one of: LIST` |
| `ishikawa/unknown-statement` | error | No statement alternative accepts the statement | First token through the next statement boundary, excluding the line ending | `unknown statement TOKEN` |
| `ishikawa/unterminated` | error | Input ends inside an open block or string | Opening delimiter through end of input | `unterminated TOKEN` |

- ishikawa-36: LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; TOKEN MUST be source text. [just parity]
- ishikawa-37: The unterminated row MUST remain registered but unreachable for valid Ishikawa lexical constructs, because this grammar opens no block or string. [just oracle]
- ishikawa-38: The shared nesting limit MUST bound the resolved cause depth at 64; its diagnostic MUST remain the common `limit/nesting-depth` row rather than a new Ishikawa code. [just go-check]

## Upstream readings

| Reading | Authority fact | Resolution |
|---|---|---|
| `ishikawa.jison:6-13` | Ordered whitespace and whole-line text rules | Preserve precedence and greedy token consumption |
| `ishikawa.jison:21-54` | Nonempty document, text and whitespace statements | No extra directive or delimiter syntax |
| `ishikawaDb.ts:42-70` | Root first; first cause sets baseline; stack uses strict parent level | Effect indentation is irrelevant; uneven indentation is legal |
| `ishikawaTypes.ts:1-4` | A recursive text-and-children record | Categories and causes are positions in one tree |
| `config.schema.yaml:476-525,1240-1255` | Base keys and two kind properties | Classify all six distinct keys |

- ishikawa-39: Go and Rust MUST produce the same ordered effect and cause tree and the same source spans under both metric profiles; layout MUST remain the responsibility of `spec/layout/tree.md`. [just parity]
