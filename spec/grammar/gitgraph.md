# Gitgraph grammar

This file defines syntax, source spans, model resolution, and diagnostics for `gitgraph`.

## Authorities

The grammar authority is `.references/mermaid/packages/parser/src/language/gitGraph/gitGraph.langium:1-56`. Its imports are `../common/common.langium:1-34` and `reference.langium:1-4`. Token customization is `gitGraph/tokenBuilder.ts:1-7` and `common/tokenBuilder.ts:6-28`; conversion is `common/valueConverter.ts:27-69,73-81`, installed by `gitGraph/module.ts:14-37`. These paths are relative to `.references/mermaid/packages/parser/src/language/`. Resolution authorities are `.references/mermaid/packages/mermaid/src/diagrams/git/gitGraphParser.ts:21-91` and `gitGraphAst.ts:49-68,105-390,457-472` in the same diagram directory. Configuration authority is `.references/mermaid/packages/mermaid/src/schemas/config.schema.yaml:476-525,1028-1098` (base properties and GitGraphDiagramConfig, including NodeLabel).

## Scope and lexing

- gitgraph-01: The parser MUST accept every reachable statement in the authority and MUST use shared preprocessing and repaired-source byte offsets with exclusive ends. [just oracle]
- gitgraph-02: The header MUST be case-sensitive `gitGraph`, with the shared detection boundary; its optional suffix MUST be `:`, or `LR:`, `TB:`, or `BT:` with optional horizontal whitespace between tokens. An absent direction MUST resolve to `LR`. [just parity]
- gitgraph-03: The lexer MUST use first-match terminal precedence in the authority order below; it MUST NOT replace that order with a longest-token scan. [just parity]

The imported common terminals precede the separately imported REFERENCE terminal. Unreachable common terminals are listed to expose precedence; they do not add statement alternatives.

| Order | Terminal | Pattern or action |
|---|---|---|
| 1 | BOOLEAN | `true` or `false`; not consumed by this grammar |
| 2 | ACC_DESCR | Optional horizontal whitespace, `accDescr`, then colon and line text, or a brace body through the first `}`; a line value stops before `%%` |
| 3 | ACC_TITLE | Optional horizontal whitespace, `accTitle`, colon, line text before `%%` |
| 4 | TITLE | Optional horizontal whitespace, `title`, then horizontal whitespace and line text before `%%`, or empty text |
| 5 | FLOAT | Digits, dot, digits, with no second dot immediately after; unreachable here |
| 6 | INT | `0` or nonzero decimal digits, not followed by dot |
| 7 | NUMBER | FLOAT or INT; unreachable here |
| 8 | STRING | Single or double quotes; inside, any byte except the matching quote or backslash, or backslash plus one character; the matching quote closes it |
| 9 | ID | ASCII word character, then word characters or hyphens, ending in a word character; unreachable as a parser alternative |
| 10 | NEWLINE | LF or CRLF in the authority; shared preprocessing also recognizes lone CR |
| 11 | WHITESPACE | One or more spaces or tabs; hidden |
| 12 | YAML | Shared frontmatter; hidden |
| 13 | DIRECTIVE | Shared directive; hidden |
| 14 | SINGLE_LINE_COMMENT | Optional horizontal whitespace, `%%`, bytes through the line end; hidden |
| 15 | REFERENCE | `\w([-\./\w]*[-\w])?`; ASCII letters, digits and underscore for `\w` |

- gitgraph-04: Literal keywords MUST have priority over identifier terminals for an exact keyword; the Langium keyword longer-alternative rule MUST preserve a longer identifier instead of splitting its keyword prefix. Keywords MUST be case-sensitive. Quoted branch names MUST permit reserved words. [just oracle]
- gitgraph-05: The literal vocabulary MUST be `gitGraph`, `gitGraph:`, `:`, `LR`, `TB`, `BT`, `commit`, `id:`, `msg:`, `tag:`, `type:`, `NORMAL`, `REVERSE`, `HIGHLIGHT`, `branch`, `order:`, `merge`, `checkout`, `switch`, `cherry-pick`, and `parent:`. The header token builder's whitespace-or-comment guard MUST NOT change the project's shared header boundary rule. [just parity]
- gitgraph-06: STRING values MUST remove their two quote delimiters and MUST decode escaped characters by the common Langium string converter; spans MUST retain delimiters. INT MUST be an unsigned decimal integer. [just parity]
- gitgraph-07: Common title and accessibility conversion MUST trim line values and collapse runs of two or more spaces or tabs to one space; a brace description MUST trim each line, collapse horizontal runs, and collapse runs of line endings to one LF. The last occurrence of each field MUST win. [just parity]

## EBNF

- gitgraph-08: The parser MUST implement this EBNF; braces mean repetition, brackets mean optional content, and EOF means the end of the source. [just oracle]

```ebnf
GitGraph = { NEWLINE }, Header,
           { NEWLINE | TitleAndAccessibilities | Statement } ;
Header = "gitGraph", [ ":" | Direction, ":" ] ;
Direction = "LR" | "TB" | "BT" ;
Statement = Commit | Branch | Merge | Checkout | CherryPicking ;
Commit = "commit", { "id:", STRING | [ "msg:" ], STRING
       | "tag:", STRING | "type:", CommitType }, EOL ;
CommitType = "NORMAL" | "REVERSE" | "HIGHLIGHT" ;
Branch = "branch", Name, [ "order:", INT ], EOL ;
Merge = "merge", Name, { "id:", STRING | "tag:", STRING
      | "type:", CommitType }, EOL ;
Checkout = ( "checkout" | "switch" ), Name, EOL ;
CherryPicking = "cherry-pick", { "id:", STRING
              | "tag:", STRING | "parent:", STRING }, EOL ;
Name = REFERENCE | STRING ;
TitleAndAccessibilities = ( ACC_DESCR | ACC_TITLE | TITLE ), EOL,
                         { ( ACC_DESCR | ACC_TITLE | TITLE ), EOL } ;
EOL = NEWLINE, { NEWLINE } | EOF ;
```

- gitgraph-09: Repeated scalar assignments MUST retain their last value; repeated `tag:` assignments MUST append tags in source order. A bare STRING on commit MUST set its message. An empty commit or cherry-pick option list MUST parse; semantic validation MUST then run. [just parity]
- gitgraph-10: Semicolons MUST NOT separate statements. Each command MUST end at a physical line end outside STRING and brace descriptions, or at EOF; line ends inside those tokens MUST remain token content. [just oracle]
- gitgraph-11: Recovery MUST skip to the next such statement boundary and continue without adding a commit or branch from the rejected statement. EOF inside STRING or a brace description MUST produce only `gitgraph/unterminated`, from the opening delimiter through EOF. [just go-check]

## Abstract syntax tree

- gitgraph-12: AST names MUST use the upstream production names in PascalCase, as below; fragments and union rules MUST NOT create artificial model objects. [just parity]

| Node or rule view | Fields | Span |
|---|---|---|
| GitGraph | direction, title, accTitle, accDescr, statements | Header start through last content token; empty suffix allowed |
| Direction | dir | Direction keyword only |
| Statement | Commit, Branch, Merge, Checkout, or CherryPicking | Selected statement span |
| Commit | id?, message?, tags[], type? | `commit` through last option token |
| Branch | name, order? | `branch` through name or order value |
| Merge | branch, id?, tags[], type? | `merge` through last option or branch token |
| Checkout | branch | `checkout` or `switch` through name |
| CherryPicking | id?, tags[], parent? | `cherry-pick` through last option token |
| TitleAndAccessibilities (fragment view) | title?, accTitle?, accDescr? | First field token through last field token |
| EOL (separator view) | line endings or EOF | Separator bytes, or zero-width EOF |

- gitgraph-13: Statement spans MUST exclude trailing whitespace, comments, and EOL; field spans MUST cover their value token, including quotes when present. The model MUST keep each declaration, reference, id, and parent span for diagnostics. [just parity]

## Resolution

- gitgraph-14: Resolution MUST process statements in source order, starting with the main branch (named `main` unless requirement gitgraph-28 renames it), no head, and commit index 0. A successful commit-producing statement MUST advance the global commit index once. A rejected statement MUST leave the model unchanged. [just parity]
- gitgraph-15: Commit MUST use its explicit nonempty id, or `<branch>-<n>` when the id is absent or empty; `n` MUST be its zero-based global commit index, including merge and cherry-pick commits. The model MUST NOT generate random ids. A duplicate id in Commit MUST emit `gitgraph/duplicate-commit-id` as a warning and MUST continue. [just parity]
- gitgraph-16: Commit MUST preserve its message (empty by default), ordered tags (empty by default), and type (NORMAL by default); REVERSE and HIGHLIGHT MUST remain distinct. Its parent MUST be the current head when set. It MUST replace the current branch head. `showCommitLabel` MUST show the resolved id. [just parity]
- gitgraph-17: Branch MUST reject an existing name; otherwise it MUST copy the current head, record its declaration index and optional order, and become current. This rule MUST also apply when that head is not the latest globally declared commit: the first new commit's parent MUST be the copied commit, and lane ordering MUST remain unchanged. [just parity]
- gitgraph-18: Explicitly ordered branches MUST sort by ascending order then declaration index; branches without order MUST follow those branches in declaration order, except that `main` without order MUST count as order 0. The model MUST retain absence separately from explicit zero. [just parity]
- gitgraph-19: Checkout and switch MUST be synonyms; they MUST require an existing branch and MUST set the current head to that branch's head, including no head for an empty branch. [just parity]
- gitgraph-20: Merge MUST validate in this order: the current head's originating branch equals the named branch, current branch equals the named branch, current branch has no commit, named branch does not exist, named branch has no commit, both heads are equal, explicit id is duplicate. The first two conditions MUST share the self-merge diagnostic. [just oracle]
- gitgraph-21: A successful merge MUST create a commit on the receiving current branch with parents `[current head, named branch head]`; it MUST preserve optional display type and tags, use the explicit id or the deterministic id rule, update only the receiving head, and remain on the receiving lane. [just parity]
- gitgraph-22: CherryPicking `id:` MUST name an existing source commit, not the new commit's id. A supplied `parent:` MUST name an immediate parent of the source. A merge source MUST require `parent:`. The source MUST NOT originate on the current branch, and the current branch MUST have a commit. These tests MUST run in that order. [just oracle]
- gitgraph-23: A successful cherry-pick MUST create a deterministic-id commit on the receiving current lane, at its next commit step, and update that lane's head. It MUST retain the source as a pick relation and the current head as its history parent; it MUST NOT treat the source as a ranking parent. Tags MUST use supplied tags, or `cherry-pick:ID` with `|parent:PARENT` for a merge source. The grammar MUST NOT expose the database-only targetId parameter. [just parity]
- gitgraph-24: Title, accTitle, and accDescr MUST populate shared metadata, not commits. Configuration rows MUST classify schema keys according to whether the project reads them; no ignored key MUST change the model. [just parity]

## Diagnostics

- gitgraph-25: The parser and resolver MUST use the following codes and messages; duplicate-commit-id MUST have severity warning, and every other row MUST have severity error. All rows MUST have no fix and empty help. A rejected semantic operation MUST emit the first applicable row only. [just oracle]

| Code | Message template | Span |
|---|---|---|
| `gitgraph/unexpected-token` | `unexpected TOKEN, expected one of: LIST` | Offending token; zero-width EOF when a required token is absent |
| `gitgraph/unknown-statement` | `unknown statement TOKEN` | First token through last content token before the recovery boundary |
| `gitgraph/unterminated` | `unterminated TOKEN` | Opening delimiter through EOF |
| `gitgraph/duplicate-commit-id` | `commit id ID already exists` | Later id STRING, or command keyword for a generated collision |
| `gitgraph/merge-duplicate-commit-id` | `merge commit id ID already exists` | Merge id STRING |
| `gitgraph/branch-already-exists` | `branch NAME already exists` | Branch name token |
| `gitgraph/unknown-branch` | `branch NAME does not exist` | Checkout or switch name token |
| `gitgraph/merge-with-self` | `cannot merge branch NAME into itself` | Merge branch token |
| `gitgraph/merge-current-empty` | `current branch NAME has no commits to merge` | Merge keyword |
| `gitgraph/merge-unknown-branch` | `merge branch NAME does not exist` | Merge branch token |
| `gitgraph/merge-branch-empty` | `merge branch NAME has no commits` | Merge branch token |
| `gitgraph/merge-same-head` | `branches have the same head` | Merge branch token |
| `gitgraph/cherry-pick-source-unknown` | `cherry-pick requires an existing source commit ID` | Source id STRING, or cherry-pick keyword when absent |
| `gitgraph/cherry-pick-parent-invalid` | `commit PARENT is not an immediate parent of ID` | Parent STRING |
| `gitgraph/cherry-pick-parent-required` | `cherry-pick of merge commit ID requires a parent` | Source id STRING |
| `gitgraph/cherry-pick-current-branch` | `commit ID is already on the current branch` | Source id STRING |
| `gitgraph/cherry-pick-current-empty` | `current branch NAME has no commits for cherry-pick` | Cherry-pick keyword |

- gitgraph-26: TOKEN MUST be source text; LIST MUST contain accepted token-kind names in ascending byte order, joined with `, `. An unknown leading statement word MUST use unknown-statement; a known statement with an invalid continuation MUST use unexpected-token. [just parity]

## Explicit readings and differences

- gitgraph-27: A duplicate id in Commit MUST replace the existing id-keyed record with the later commit, without moving that key's first insertion position; the later record's message, type, tags, sequence index, parents, and originating branch MUST replace the earlier fields. The current head MUST become that later record, and the current branch head MUST store its id. Other branch heads and parent references MUST retain their id strings and MUST therefore resolve to the replacement record on subsequent lookup; the earlier record MUST NOT remain a second model commit. The sequence counter MUST still advance. Merge's duplicate-id throw MUST instead emit merge-duplicate-commit-id as an error and MUST leave the model unchanged. Repeated unreachable lookup checks in cherryPick MUST map to the same source-unknown or current-empty row, not new codes. [just parity]
- gitgraph-28: The specified lane order MUST take precedence over the parser adapter's `order ?? 0` and the database helper's fractional fallback; no floating-point fallback MUST enter this model. The config keys `gitGraph.mainBranchName` and `gitGraph.mainBranchOrder`, read from frontmatter `config` and from `%%{init}%%` directives with a later source winning, MUST rename the first branch and set its order. A non-empty string `mainBranchName` MUST become the name of that branch: it MUST be the only name that `checkout`, `switch`, and `merge` resolve for it, it MUST appear in generated commit ids as `<name>-<n>`, and `branch main` MUST then create an ordinary branch when the name is not `main`. An integer `mainBranchOrder` MUST become its explicit order, which the model MUST retain as an explicit value even when it is 0. Any other value of either key MUST be ignored and MUST leave the default name `main` or the absent order. [just parity]
- gitgraph-29: The direction field MUST be read from Direction despite the authority adapter's root `ast.dir` access; unsupported directions MUST be syntax errors, not silent LR fallback. Source strings MUST remain plain label data; browser HTML sanitization MUST NOT change ids or references in this static model. [just parity]
