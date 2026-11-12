# Treemap grammar

This file fixes syntax and model resolution for the `treemap` kind.

## Scope

- treemap-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/treemap/treemap.langium:13-89`; conversion MUST follow `valueConverter.ts:5-40`, and validation MUST follow `treemap-validator.ts:30-59` in that directory. [just oracle]
- treemap-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/treemap/parser.ts:13-74`, `utils.ts:8-63`, and `db.ts:37-78`; the model fields MUST follow `types.ts:4-10`. [just parity]
- treemap-03: This grammar MUST cover metadata, sections, valued leaves, class definitions, and class selectors; layout MUST remain owned by `spec/layout/charts.md`. [just oracle]

## Header forms

- treemap-04: The header MUST be `treemap` or `treemap-beta`, case-sensitive, with the boundary and preprocessing rules of `spec/detection.md`. [just oracle]

## Lexer modes

- treemap-05: The lexer MUST use one mode, `INITIAL`; it MUST apply the terminal rules below in authority declaration order, with the first matching rule winning. [just parity]

### Lexical rules in first-match order

| Order (grammar line) | Terminal | Match and result |
|---|---|---|
| 17 | BOOLEAN | `true` or `false`; no production consumes it |
| 19 | ACC_DESCR | Optional spaces or tabs, then `accDescr`, then either a colon and text to comment or line end, or optional whitespace and a brace-delimited body |
| 20 | ACC_TITLE | Optional spaces or tabs, then `accTitle`, optional spaces or tabs, colon, and text to comment or line end |
| 21 | TITLE | Optional spaces or tabs, then `title`, optionally followed by a space or tab and text to comment or line end |
| 50 | TREEMAP_KEYWORD | `treemap-beta` or `treemap` |
| 52 | CLASS_DEF | `classDef`, whitespace, a class name matching `[A-Za-z_][A-Za-z0-9_]+`, optional whitespace and style text through the next semicolon or line end, and an optional semicolon |
| 53 | STYLE_SEPARATOR | `:::` |
| 54 | SEPARATOR | `:` |
| 55 | COMMA | `,` |
| 58 | INDENTATION | One or more spaces or tabs; retained |
| 60 | WS | One or more spaces or tabs; hidden fallback after INDENTATION |
| 61 | ML_COMMENT | `%%` through the next LF; hidden |
| 62 | NL | LF or CRLF; hidden |
| 82 | ID2 | `[A-Za-z_][A-Za-z0-9_]*` |
| 84 | NUMBER2 | One or more ASCII digits, underscores, periods, or commas |
| 89 | STRING2 | A double-quoted body without a double quote, or a single-quoted body without a single quote |

- treemap-06: Shared line-ending handling MUST also accept lone CR; source spans MUST retain original bytes. [just parity]
- treemap-07: STRING2 MUST remove its two quote delimiters from its value, but MUST retain them in its span; backslashes MUST NOT escape quote delimiters. [just oracle]
- treemap-08: An INDENTATION value MUST equal its byte count; each tab MUST count as one, not as a tab stop. [just parity]
- treemap-09: NUMBER2 conversion MUST remove commas and consume the longest initial decimal prefix as upstream `parseFloat` does; underscores MUST NOT be removed, and trailing numeric-token text MUST remain in the AST span. [just oracle]
- treemap-10: A NUMBER2 with no convertible prefix MUST retain an invalid-number state rather than panic; this conversion alone MUST NOT introduce an error that upstream does not raise. [just oracle]

## Grammar

- treemap-11: The parser MUST implement this EBNF without backtracking over a completed row. [just parity]

```ebnf
Treemap = TREEMAP_KEYWORD, { TitleAndAccessibilities | TreemapRow } ;
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE),
                         { ACC_DESCR | ACC_TITLE | TITLE } ;
TreemapRow = [INDENTATION], (Item | ClassDef) ;
ClassDef = CLASS_DEF ;
Item = Leaf | Section ;
Section = STRING2, [STYLE_SEPARATOR, ID2] ;
Leaf = STRING2, [INDENTATION], (SEPARATOR | COMMA),
       [INDENTATION], MyNumber, [STYLE_SEPARATOR, ID2] ;
MyNumber = NUMBER2 ;
```

- treemap-12: After a name, a colon or comma MUST select Leaf before Section completes; a name without a numeric separator MUST select Section. [just oracle]
- treemap-13: A section and a leaf MUST each accept at most one `:::class` suffix; the suffix MUST name one ID2, not a class list. [just oracle]
- treemap-14: Class definitions MUST accept style text as opaque text; a class definition name MUST contain at least two characters, while a selector MAY contain one character. [just oracle]
- treemap-15: Newlines MUST be hidden grammar tokens, not mandatory row separators; quoted names MAY contain line ends because STRING2 excludes only its matching quote. [just oracle]

## Statement boundary

- treemap-16: Recovery MUST skip to the next physical line end outside a quoted name or accessibility brace body, then resume at the next row or metadata token. [just go-check]
- treemap-17: Recovery MUST NOT create a section or leaf from an unknown statement; a semicolon MUST NOT act as a general row separator. [just oracle]

## Abstract syntax tree

- treemap-18: AST nodes MUST use the authority production names below in PascalCase and MUST retain declaration order. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Treemap | Header, TreemapRows, title, accTitle, accDescr | Header start through final consumed token |
| TitleAndAccessibilities | Ordered metadata tokens | First metadata token through last token |
| TreemapRow | Optional indent, item or ClassDef | Indent start when present, otherwise first content token, through final row token |
| Item | Leaf or Section | Same as selected alternative |
| Section | Name, optional classSelector | Opening name quote through closing name quote or selector end |
| Leaf | Name, MyNumber, optional classSelector | Opening name quote through number or selector end |
| MyNumber | Raw token, converted value or invalid-number state | Entire NUMBER2 token |
| ClassDef | Class name and optional style text | Entire CLASS_DEF token, including optional semicolon |

- treemap-19: The converted ClassDef value MUST have the semantic tag `ClassDefStatement`; this tag MUST NOT add a second grammar production. [just parity]
- treemap-20: Tokens MUST borrow source text; name, value, selector, and metadata spans MUST remain available for diagnostics. [just parity]

## Semantic resolution

- treemap-21: Metadata MUST populate the common title and accessibility fields; repeated metadata of one kind MUST replace its earlier value. [just parity]
- treemap-22: Resolution MUST collect all class definitions before resolving any item, so a selector MAY refer to a later definition. [just parity]
- treemap-23: A repeated class definition MUST append styles to the existing class in source order; an unknown selector MUST resolve to an empty style list without a diagnostic. [just oracle]
- treemap-24: Class style splitting MUST preserve escaped commas, replace other commas with separators, then split on semicolons; label styles MUST also enter the text-style list. [just parity]
- treemap-25: Each Section MUST store its name, selector, compiled style list when nonempty, declaration index, and an initially empty children list; it MUST NOT store a literal leaf value. [just parity]
- treemap-26: Each Leaf MUST store its name, converted numeric value, selector, compiled style list when nonempty, and declaration index; it MUST NOT enter the parent stack. [just parity]
- treemap-27: For each item in order, resolution MUST pop every stack entry whose indentation is greater than or equal to that item's indentation; the remaining top section MUST be its parent, or the item MUST be a root when the stack is empty. [just parity]
- treemap-28: Resolution MUST push each Section with its indentation after attaching it; indentation jumps MUST NOT create intermediate sections, and a leaf MUST NOT become a parent. [just oracle]
- treemap-29: Resolution MUST retain root order and child order; duplicate names MUST remain distinct nodes, and the database view MUST enumerate nodes in preorder with structural depth rather than indentation width. [just parity]
- treemap-30: The model MUST expose an unnamed synthetic root whose children are all root items; section aggregate values MUST be derived from descendants rather than parsed as section literals. [just parity]
- treemap-31: Validation MUST remember when the first item without an INDENTATION token occurs and MUST reject every later item without indentation; it MUST NOT infer that the first indented item establishes a root indentation. [just oracle]
- treemap-32: An empty diagram and multiple indented root items MUST NOT fail the single-root check; no positivity, duplicate-name, missing-class, or indentation-step check MUST be added. [just oracle]
- treemap-33: Nesting beyond 64 structural levels MUST use the shared `limit/nesting-depth` diagnostic and MUST NOT recurse further. [just go-check]

## Diagnostics

- treemap-34: Syntax and semantic failures MUST use the following kind codes; source, config, and nesting failures MUST use their shared registries. [just oracle]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| `treemap/unexpected-token` | error | A known statement has a token that its production cannot consume | Offending token, or zero-width EOF | `unexpected TOKEN, expected one of: LIST` |
| `treemap/unknown-statement` | error | No row or metadata production accepts the statement start | First token through recovery boundary, excluding line end | `unknown statement TOKEN` |
| `treemap/unterminated` | error | EOF inside a quoted name or accessibility brace body | Opening delimiter through EOF | `unterminated TOKEN` |
| `treemap/multiple-roots` | error | A later item has no indentation after an unindented item was seen | Later item's span, excluding its indentation | `multiple root nodes are not allowed in a treemap` |

- treemap-35: LIST MUST name accepted token kinds in ascending byte order joined by `, `, and TOKEN MUST be the source token text; an unterminated construct MUST emit only its unterminated diagnostic. [just parity]
- treemap-36: A missing TreemapDB in the upstream adapter MUST be treated as an integration failure, not as an input diagnostic; the adapter has no other input-dependent thrown validation beyond parser and validator failures. [just oracle]

## Upstream readings

The header detector boundary follows this repository's shared detection contract. The grammar declares visible indentation before hidden whitespace; indentation is counted as raw spaces and tabs. The single-root validator tests absence of indentation, not the minimum indentation among rows. These distinctions are intentional readings of the cited authority.

The schema file `packages/mermaid/src/schemas/config.schema.yaml:476-525` defines inherited base keys but contains no treemap definition in this checkout. The local interface `diagrams/treemap/types.ts:69-80` supplies its nine kind-specific keys. Their classification is in `spec/data/config-keys/treemap.json`; this is not a claim that a missing schema definition exists.
