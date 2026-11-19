# Treeview grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `treeview` kind.

## Scope

- treeview-01: The grammar authority MUST be `.references/mermaid/packages/parser/src/language/treeView/treeView.langium:15-64`; conversion MUST follow `valueConverter.ts:10-35` in that directory. [just oracle]
- treeview-02: Resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/treeView/parser.ts:11-40`, `db.ts:17-75`, and `types.ts:12-25`; box input MUST follow `boxDrawingPreprocessor.ts:8-209` in that directory. [just oracle]
- treeview-03: Config classification MUST cover `TreeViewDiagramConfig` at `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:2834-2900` and inherited `BaseDiagramConfig:476-525`; layout MUST remain owned by `spec/layout/tree.md`. [just gen-check]

## Header forms

- treeview-04: The header MUST be `treeView-beta`, case-sensitive, with the boundary and preprocessing rules of `spec/detection.md`. [just oracle]

## Lexer modes

- treeview-05: The lexer MUST use one default mode; there are no named start conditions. [just parity]

### Lexical rules in first-match order

- treeview-06: After the fixed header keyword, the lexer MUST try the following terminals in authority declaration order; the first matching rule MUST win. [just parity]

| Order (authority line) | Terminal | Pattern and action |
|---|---|---|
| 15 | ACC_DESCR | Optional SP/HT, `accDescr`, then optional SP/HT and `:` with text to CR/LF or before `%%`, or whitespace and `{` with text through the first `}`. |
| 16 | ACC_TITLE | Optional SP/HT, `accTitle`, optional SP/HT, `:`, then text to CR/LF or before `%%`. |
| 17 | TITLE | Optional SP/HT, `title`, then SP/HT and text to CR/LF or before `%%`, or no suffix. |
| 40 | CLASS_ANNOTATION | One or more SP/HT, `:::`, optional SP/HT, ASCII letter or underscore, then ASCII word characters or hyphens. |
| 42 | ICON_ANNOTATION | One or more SP/HT, `icon(`, zero or more ASCII word characters or hyphens, optional `:` and one or more such characters, then `)`. |
| 43 | DESC_ANNOTATION | One or more SP/HT, `##`, then all text to CR/LF. |
| 46 | INDENTATION | One or more SP/HT; emit the run, do not hide it. |
| 49 | QUOTED_NAME | Double quotes around any non-double-quote characters, or single quotes around any non-single-quote characters. No escape processing. |
| 51 | WS | SP/HT run; hidden, but shadowed by INDENTATION. |
| 52 | ML_COMMENT | `%%` through the next LF; hidden. Shared line-ending normalization applies. |
| 53 | NL | CRLF or LF; hidden. Shared preprocessing also recognizes lone CR. |
| 57 | BARE_NAME | First character is not whitespace or either quote and does not begin `:::`, `icon(`, or `##`; continue to CR/LF, stopping before whitespace followed by a valid class opener, `icon(`, or `##`. |

- treeview-07: BARE_NAME MUST retain internal spaces and quote characters after its first character; conversion MUST remove only trailing SP/HT. QUOTED_NAME MUST remove only its outer quotes. [just parity]
- treeview-08: Annotation conversion MUST remove surrounding whitespace and its marker; class conversion MUST remove `:::`, icon conversion MUST remove `icon(` and `)`, and description conversion MUST remove `##` and trim its content. A description MUST consume the remaining line, including apparent annotations. [just parity]

## Grammar

- treeview-09: The parser MUST use the following EBNF; hidden tokens MUST NOT create statement boundaries in the accepted grammar. [just parity]

```ebnf
TreeView = "treeView-beta", [TitleAndAccessibilities], {TreeNode};
TitleAndAccessibilities = (ACC_DESCR | ACC_TITLE | TITLE),
                         {ACC_DESCR | ACC_TITLE | TITLE};
TreeNode = [INDENTATION], (QUOTED_NAME | BARE_NAME),
           {CLASS_ANNOTATION | ICON_ANNOTATION | DESC_ANNOTATION};
```

- treeview-10: Metadata MUST occur before the first TreeNode; repeated scalar assignments, including repeated annotations, MUST retain the last assigned value. Empty node lists MUST be accepted. [just oracle]
- treeview-11: A quoted name MAY span physical lines because the authority excludes only its matching quote; backslash MUST NOT escape that quote. [just oracle]

## Statement boundary

- treeview-12: Recovery MUST skip to the next physical line end outside a quoted name or accessibility block; it MUST NOT create a node for skipped text. An unclosed delimiter at end of input MUST retain its opening-to-end span. [just go-check]
- treeview-13: The parser MUST enforce the shared nesting limit of 64 on the resolved parent chain and use the shared `limit/nesting-depth` diagnostic, not a treeview-specific alias. [just go-check]

## Abstract syntax tree

- treeview-14: AST nodes MUST use the authority production names below and MUST retain original-source byte spans; preprocessing MUST NOT expose transformed offsets to diagnostics. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| TreeView | ordered nodes; optional title, accTitle, accDescr | Header start through last consumed token. |
| TitleAndAccessibilities | ordered metadata assignments | First metadata token through last metadata token. This is a fragment, not an extra model object. |
| TreeNode | indent; name; optional classAnnotation, iconAnnotation, descAnnotation | First indentation or name byte through last annotation or name byte, excluding hidden line separators. |

- treeview-15: Tokens MUST borrow source text; name, indentation, annotation, and opening delimiter spans MUST remain available after value conversion. [just parity]

## Semantic resolution

- treeview-16: An absent indentation MUST give level 0. Otherwise level MUST equal the count of characters in the SP/HT run, with each TAB counting as one, not a tab stop. Indentation MUST NOT require a fixed unit or a match to an earlier level. [just oracle]
- treeview-17: The database MUST start with count 1 and a stack containing one synthetic directory node: id 0, level -1, name `/`, empty children. This root MUST NOT be a source declaration. [just parity]
- treeview-18: For each TreeNode in source order, resolution MUST pop the stack while the incoming level is less than or equal to its last node's level. The remaining last node MUST be the parent. Resolution MUST append the new node to that parent's children and then push the new node. [just parity]
- treeview-19: A greater level MUST make the node a child of the immediately preceding node, even after a large indentation jump or when that node is a file. Equal levels MUST make siblings. A decrease to an unseen level MUST attach to the nearest preceding ancestor with a strictly smaller level. [just oracle]
- treeview-20: Each stored node MUST receive the next count as its id and increment the count once; it MUST store level, name, nodeType, optional icon, cssClass, description, and ordered children. Duplicate names MUST remain distinct nodes. `getRoot` MUST return stack element 0; `getCount` MUST include the synthetic root. [just parity]
- treeview-21: A name ending in `/` MUST become a directory and lose exactly its last slash; every other name MUST become a file. No path splitting or name uniqueness check MUST occur. [just oracle]
- treeview-22: A missing class or empty description MUST become absent. A present `icon()` MUST store `none`; a missing icon annotation MUST remain absent. A non-empty description MUST pass through the shared static-text sanitization policy. [just parity]
- treeview-23: Common metadata MUST populate diagram title and accessibility fields before node insertion. Node declarations MUST NOT be interpreted as edges, class definitions, or style statements. [just parity]

### Box-drawing input

- treeview-24: Box conversion MUST activate only when a line trimmed of whitespace equals the header and a later content line contains any of `─━│┃└┗├┣`; detection MUST ignore blank, comment, metadata, and vertical-decoration-only lines. TAB MUST expand to four spaces for box conversion only. [just oracle]
- treeview-25: Segment width MUST be the column of the first branch character `└┗├┣` at a positive column in content order, or 4 when none exists. A branch at column c MUST produce indentation of `4 * (floor(c / segmentWidth + 1/2) + 1)` spaces. [just parity]
- treeview-26: Branch conversion MUST remove the branch character, following `─` or `━` characters, and following spaces; it MUST trim the remaining content at the end. Empty content MUST raise `treeview/empty-box-node`. [just oracle]
- treeview-27: In box mode, blank, comment, and metadata lines MUST pass through; decoration-only lines MUST be omitted. A line with box characters but no branch MUST pass through unchanged. A non-decoration line with leading whitespace and no box characters MUST raise `treeview/mixed-indentation`; an unindented line MUST pass through unchanged. [just oracle]
- treeview-28: Conversion MUST preserve an original-line and content-offset mapping for diagnostics and AST spans, including omitted decoration lines and replaced prefixes. [just parity]

## Diagnostics

- treeview-29: Rejections MUST use the following rows; the database MUST NOT add indentation-step, duplicate-name, or file-parent errors because upstream enforces none. [just gen-check]

| Code | Severity | Trigger | Span | Message |
|---|---|---|---|---|
| treeview/unexpected-token | error | Known production cannot accept the token. | Offending token. | `unexpected TOKEN, expected one of: LIST` |
| treeview/unknown-statement | error | No statement form accepts the input. | First token through recovery boundary, excluding its separator. | `unknown statement TOKEN` |
| treeview/unterminated | error | Input ends inside a quote or accessibility block. | Opening delimiter through source end. | `unterminated TOKEN` |
| treeview/empty-box-node | error | Box branch has no content. | Branch prefix through physical line end, excluding separator. | `expected a filename or directory name after the box-drawing prefix` |
| treeview/mixed-indentation | error | Indentation-only syntax occurs within box mode. | Leading indentation of the line. | `unexpected indentation without box-drawing characters` |

- treeview-30: TOKEN MUST be the original token text; LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `. All rows MUST have empty help and no fix. [just parity]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| treeView.langium:26-34,59-64 | Metadata precedes the flat node sequence; annotations assign scalar fields. | Grammar and AST. |
| valueConverter.ts:10-35 | Indent counts characters, quotes are stripped, annotation markers are removed. | Lexical conversion. |
| parser.ts:11-40 | Directory suffix, empty icon sentinel, description sanitization. | Semantic resolution. |
| db.ts:22-33,52-75 | Synthetic root, increasing ids, strict-smaller-level stack parent. | Storage and parent selection. |
| boxDrawingPreprocessor.ts:36-43,70-209 | Segment inference, normalization, conversion and two throwing checks. | Box-drawing input and diagnostics. |

- treeview-31: Go and Rust MUST produce the same ordered parent relations and node fields for both metric profiles; an oracle verdict MUST decide any conflict between this reading and an accepted corpus input. [just parity]
