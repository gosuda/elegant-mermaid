# Railroad grammar

This file defines the four source notations of the `railroad` kind. Layout belongs to `spec/layout/railroad.md`.

Authority (paths relative to `.references/mermaid/`):

| File | Lines | Subject |
|---|---|---|
| `packages/parser/src/language/railroad/railroad.langium` | 3–14, 16–113 | Tokens, AST, constructor notation |
| `packages/parser/src/language/railroad-ebnf/railroad-ebnf.langium` | 3–20, 22–166 | Tokens, AST, EBNF notation |
| `packages/parser/src/language/railroad-abnf/railroad-abnf.langium` | 3–17, 19–114 | Tokens, AST, ABNF notation |
| `packages/parser/src/language/railroad-peg/railroad-peg.langium` | 3–14, 16–110 | Tokens, AST, PEG notation |
| `packages/parser/src/language/railroad/tokenBuilder.ts`, and corresponding `railroad-ebnf`, `railroad-abnf`, `railroad-peg` files | 1–7 each | Header token construction |
| `packages/parser/src/language/railroad/valueConverter.ts` | 1–68 | Constructor string and title conversion |
| `packages/parser/src/language/railroad-ebnf/valueConverter.ts` | 1–72 | EBNF string, special, and title conversion |
| `packages/parser/src/language/railroad-abnf/valueConverter.ts` | 1–37 | ABNF string and title conversion |
| `packages/parser/src/language/railroad-peg/valueConverter.ts` | 1–68 | PEG string and title conversion |
| `packages/mermaid/src/diagrams/railroad/parser/railroadParser.ts` | 26–105 | Constructor lowering |
| `packages/mermaid/src/diagrams/railroad/parser/ebnfParser.ts` | 28–162 | EBNF lowering |
| `packages/mermaid/src/diagrams/railroad/parser/abnfParser.ts` | 26–144 | ABNF lowering |
| `packages/mermaid/src/diagrams/railroad/parser/pegParser.ts` | 24–152 | PEG lowering |
| `packages/mermaid/src/diagrams/railroad/railroadDb.ts` | 13–37, 43–49, 56–88, 94–130 | Stored rules and metadata |
| `packages/mermaid/src/schemas/config.schema.yaml` | 476–524, 3196–3305 | Inherited and railroad config keys |

## Scope and detection

- rrgrammar-01: The parser MUST accept `railroad-beta`, `railroad-ebnf-beta`, `railroad-abnf-beta`, and `railroad-peg-beta` with ASCII case folding and the keyword boundary of `spec/detection.md`; each header MUST select only its corresponding notation. [just oracle]
- rrgrammar-02: Preprocessing MUST follow `spec/preprocessing.md`; every span MUST index the repaired source bytes and MUST have an exclusive end. [just parity]
- rrgrammar-03: Each notation MUST accept zero or more metadata tokens followed by zero or more rule definitions; metadata MUST NOT occur after the first rule. [just oracle]

## Lexer modes and first-match order

There is one mode, `INITIAL`, for each notation. A quoted string or comment is one token, not a persistent lexer mode. The tables below give the explicit terminal order from the authority. Grammar literals are reserved tokens: constructor names and punctuation are not identifiers where the grammar requires a literal. Shared preprocessing handles frontmatter and directives before these rules.

- rrgrammar-04: Within `INITIAL`, the lexer MUST take the first matching rule in the following ordered lists; it MUST NOT use a later matching rule to reinterpret a consumed token. [just parity]

| Notation | Explicit terminal order (authority line) |
|---|---|
| Constructor | TITLE (3), ACC_TITLE (4), ACC_DESCR (5), RR_ID (7), RR_STRING (8), RR_WHITESPACE (10), RR_YAML (11), RR_DIRECTIVE (12), RR_SINGLE_LINE_COMMENT (13), RR_BLOCK_COMMENT (14) |
| EBNF | TITLE (3), ACC_TITLE (4), ACC_DESCR (5), EBNF_ID (7), EBNF_STRING (8), EBNF_SPECIAL_SEQUENCE (13), EBNF_WHITESPACE (15), EBNF_YAML (16), EBNF_DIRECTIVE (17), EBNF_SINGLE_LINE_COMMENT (18), EBNF_BLOCK_COMMENT (19), EBNF_ISO_COMMENT (20) |
| ABNF | TITLE (3), ACC_TITLE (4), ACC_DESCR (5), ABNF_RULENAME (7), ABNF_STRING (8), ABNF_NUMVAL (9), ABNF_REPEAT (10), ABNF_EXACT_REPEAT (11), ABNF_WHITESPACE (13), ABNF_YAML (14), ABNF_DIRECTIVE (15), ABNF_SINGLE_LINE_COMMENT (16), ABNF_COMMENT (17) |
| PEG | TITLE (3), ACC_TITLE (4), ACC_DESCR (5), PEG_ID (7), PEG_STRING (8), PEG_WHITESPACE (10), PEG_YAML (11), PEG_DIRECTIVE (12), PEG_SINGLE_LINE_COMMENT (13), PEG_LINE_COMMENT (14) |

- rrgrammar-05: `TITLE` MUST consume `title`, a colon, optional horizontal whitespace, and the rest of that physical line before `%%`; `ACC_TITLE` MUST consume `accTitle`, optional horizontal whitespace, a colon, and that line's value before `%%`. [just oracle]
- rrgrammar-06: `ACC_DESCR` MUST consume `accDescr` followed by either a colon and one line before `%%`, or optional whitespace and a brace-delimited multiline value ending at the first `}`. [just oracle]
- rrgrammar-07: Constructor, EBNF, and PEG identifiers MUST match `[A-Za-z_][\w-]*`, where `\w` is ASCII letters, digits, or underscore; ABNF rule names MUST match `[A-Za-z][A-Za-z0-9-]*`. Identifier comparison MUST be case-sensitive. [just oracle]
- rrgrammar-08: Constructor, EBNF, and PEG strings MUST use matching single or double quotes; a backslash MUST consume the next character, and an unescaped quote of the opening kind MUST close the token; unescaped line endings MUST NOT occur inside a string. [just oracle]
- rrgrammar-09: ABNF strings MUST use double quotes and MUST contain neither double quotes nor line endings; backslash MUST remain ordinary text. [just oracle]
- rrgrammar-10: ABNF numeric values MUST match `%[xXdDbB][0-9A-Fa-f]+(?:[-.][0-9A-Fa-f]+)*`; repeat tokens MUST match `[0-9]*\*[0-9]*` before the exact-count token `[0-9]+`. [just oracle]
- rrgrammar-11: EBNF special sequences MUST start and end with `?`, MUST contain at least one non-whitespace character, and MUST contain neither a semicolon nor an internal `?`; the `?` postfix MUST remain available when this token does not match. [just oracle]
- rrgrammar-12: Whitespace tokens MUST consume spaces, tabs, CR, and LF and MUST be hidden; `%%` comments MUST extend to the next line ending and MUST be hidden in all four notations. [just oracle]
- rrgrammar-13: Constructor and EBNF MUST hide `/* ... */` comments through the first close; EBNF MUST also hide `(* ... *)` comments through the first close; ABNF MUST hide `;` through the line end; PEG MUST hide `#` through the line end. Comments MUST NOT nest. [just oracle]

## Grammar

In this EBNF, braces mean repetition, brackets mean an optional part, and quoted punctuation means a literal. `Meta` is one TITLE, ACC_TITLE, or ACC_DESCR token. Hidden tokens may occur between grammar tokens. `String`, `Id`, and `RuleName` use the corresponding notation's lexer rules.

- rrgrammar-14: The constructor parser MUST accept exactly these productions. [just oracle]

```ebnf
Railroad = Header, { Meta }, { RailroadRule } ;
RailroadRule = Id, "=", RailroadExpression, ";" ;
RailroadExpression = RailroadSequenceExpr | RailroadChoiceExpr | RailroadOptionalExpr
                   | RailroadOneOrMoreExpr | RailroadZeroOrMoreExpr
                   | RailroadTerminalExpr | RailroadNonTerminalExpr | RailroadSpecialExpr ;
RailroadSequenceExpr = "sequence", "(", RailroadExpression, { ",", RailroadExpression }, ")" ;
RailroadChoiceExpr = "choice", "(", RailroadExpression, { ",", RailroadExpression }, ")" ;
RailroadOptionalExpr = "optional", "(", RailroadExpression, ")" ;
RailroadOneOrMoreExpr = "oneOrMore", "(", RailroadExpression, ")" ;
RailroadZeroOrMoreExpr = "zeroOrMore", "(", RailroadExpression, ")" ;
RailroadTerminalExpr = "terminal", "(", String, ")" ;
RailroadNonTerminalExpr = "nonterminal", "(", String, ")" ;
RailroadSpecialExpr = "special", "(", String, ")" ;
```

- rrgrammar-15: The EBNF parser MUST accept exactly these productions; a sequence MUST use commas, not bare juxtaposition. [just oracle]

```ebnf
RailroadEbnf = Header, { Meta }, { EbnfRule } ;
EbnfRule = Id, ("=" | ":" | "::="), EbnfChoice, ";" ;
EbnfChoice = EbnfSequence, { "|", EbnfSequence } ;
EbnfSequence = EbnfTerm, { ",", EbnfTerm } ;
EbnfTerm = EbnfPrimary, { EbnfPostfix } ;
EbnfPrimary = EbnfTerminal | EbnfSpecial | EbnfNonTerminal | EbnfGroup | EbnfOptional | EbnfRepetition ;
EbnfTerminal = String ; EbnfNonTerminal = Id ; EbnfSpecial = SpecialSequence ;
EbnfGroup = "(", EbnfChoice, ")" ;
EbnfOptional = "[", EbnfChoice, "]" ;
EbnfRepetition = "{", EbnfChoice, "}" ;
EbnfPostfix = EbnfOptionalPostfix | EbnfZeroOrMorePostfix | EbnfOneOrMorePostfix | EbnfExceptionPostfix ;
EbnfOptionalPostfix = "?" ; EbnfZeroOrMorePostfix = "*" ; EbnfOneOrMorePostfix = "+" ;
EbnfExceptionPostfix = "-", EbnfPrimary ;
```

- rrgrammar-16: The ABNF parser MUST accept exactly these productions; semicolons MUST start comments and MUST NOT terminate rules. [just oracle]

```ebnf
RailroadAbnf = Header, { Meta }, { AbnfRule } ;
AbnfRule = RuleName, "=", AbnfAlternation ;
AbnfAlternation = AbnfConcatenation, { "/", AbnfConcatenation } ;
AbnfConcatenation = AbnfElement, { AbnfElement } ;
AbnfElement = [ Repeat | ExactRepeat ], AbnfPrimary ;
AbnfPrimary = AbnfStringLiteral | AbnfNumVal | AbnfRuleName | AbnfGroup | AbnfOptionalGroup ;
AbnfStringLiteral = String ; AbnfNumVal = NumVal ; AbnfRuleName = RuleName ;
AbnfGroup = "(", AbnfAlternation, ")" ;
AbnfOptionalGroup = "[", AbnfAlternation, "]" ;
```

- rrgrammar-17: The PEG parser MUST accept exactly these productions; it MUST require the final semicolon and MUST NOT add character classes or actions. [just oracle]

```ebnf
RailroadPeg = Header, { Meta }, { PegRule } ;
PegRule = Id, "<-", PegOrderedChoice, ";" ;
PegOrderedChoice = PegSequence, { "/", PegSequence } ;
PegSequence = PegPrefix, { PegPrefix } ;
PegPrefix = [ "&" | "!" ], PegSuffix ;
PegSuffix = PegPrimary, [ "?" | "*" | "+" ] ;
PegPrimary = PegLiteral | PegIdentifier | PegGroup | PegAny ;
PegLiteral = String ; PegIdentifier = Id ;
PegGroup = "(", PegOrderedChoice, ")" ; PegAny = "." ;
```

## AST and spans

- rrgrammar-18: Every production named in the grammar above MUST have an AST representation with that exact PascalCase name; sum productions MAY use a tagged union without allocating an extra wrapper. Each root MUST retain ordered metadata and rules; each rule MUST retain its name token, definition, and declaration index. [just parity]
- rrgrammar-19: Composition nodes MUST retain their ordered children; unary nodes MUST retain their child; terminals and special nodes MUST retain decoded text; reference nodes MUST retain their name; `AbnfElement`, `EbnfTerm`, `EbnfPostfix`, `PegPrefix`, and `PegSuffix` MUST retain their operators and their token spans. [just parity]
- rrgrammar-20: An AST span MUST run from its first token through its last token, including delimiters and a rule's terminating semicolon when present; hidden leading and trailing tokens MUST NOT extend that span. A root MUST span the header through EOF. Value tokens MUST retain both the original token span and their delimiter-free value. [just parity]
- rrgrammar-21: Constructor, EBNF, and PEG string conversion MUST replace `\n`, `\r`, and `\t` with their control characters and MUST remove the backslash from every other escape; ABNF string conversion MUST remove only the enclosing quotes. EBNF special text MUST remove its two question marks and trim surrounding whitespace. [just oracle]

## Model resolution

- rrgrammar-22: Resolution MUST preserve rule declaration order and MUST lower each definition to terminal, non-terminal, special, sequence, choice, optional, or repetition; it MUST NOT resolve a non-terminal by expanding its referenced rule. [just parity]
- rrgrammar-23: A one-child sequence or choice MUST collapse to that child; a group MUST lower to its content without adding a model element. Constructor terminal, nonterminal, special, optional, oneOrMore, and zeroOrMore MUST lower directly, with repetition bounds respectively `(1, unbounded)` and `(0, unbounded)`. [just parity]
- rrgrammar-24: EBNF terms MUST apply postfixes from left to right; `?` MUST wrap the current element as optional, `*` and `+` MUST wrap it as repetition with minimum 0 and 1, and `- e` MUST lower to a sequence of the current element, terminal `-`, and the lowered `e`. Brace repetition MUST have minimum 0. [just parity]
- rrgrammar-25: ABNF numeric values MUST remain terminal text, including the `%` prefix, rather than becoming decoded characters; absent repeat bounds around `*` MUST mean minimum 0 and unbounded maximum. An exact count MUST set both bounds to that count; `0*1` MUST lower to optional. Other repeat bounds MUST remain repetition even when minimum exceeds maximum. [just oracle]
- rrgrammar-26: PEG `.` MUST lower to special text `.`; suffixes MUST lower before prefixes. A lookahead MUST lower to special text consisting of `&` or `!` and the child's label: a terminal label MUST include double quotes, a non-terminal label MUST be its name, a special label MUST be its text, and any composite label MUST be `(...)`. [just parity]
- rrgrammar-27: Duplicate rule declarations MUST remain separate ordered definitions; lookup by name MUST select the last declaration. Undefined references MUST remain non-terminal elements. Neither condition MUST produce a syntax or semantic error, because the database only logs duplicate names and does not validate references. [just oracle]
- rrgrammar-28: Later metadata MUST replace earlier metadata of the same field; matching outer quotes of a title MUST be removed, with escape conversion in constructor, EBNF, and PEG but not ABNF. Accessibility values MUST follow shared metadata conversion. Model text MUST remain semantic text, not DOM-sanitized markup. [just parity]

## Recovery and diagnostics

- rrgrammar-29: Recovery in constructor, EBNF, and PEG MUST skip through the next semicolon outside strings and comments at the current nesting level, or stop before an enclosing close delimiter; ABNF recovery MUST skip to the next physical line whose first visible tokens are `RuleName =`, or EOF. Recovery MUST NOT create a model rule from the rejected statement. [just go-check]
- rrgrammar-30: Nesting MUST stop before level 65 under the shared nesting-limit diagnostic; this file MUST NOT introduce a railroad alias for that shared code. [just go-check]
- rrgrammar-31: The diagnostic registry MUST contain exactly the railroad rows below; named diagnostics MUST take precedence over generic unterminated errors for the same failure. [just gen-check]

| Code | Severity | Trigger | Message | Span |
|---|---|---|---|---|
| `railroad/unexpected-token` | error | No token alternative fits the current production | `unexpected TOKEN, expected one of: LIST` | Offending token, or zero-width EOF |
| `railroad/unknown-statement` | error | The first token starts no metadata or rule form | `unknown statement TOKEN` | First token through the recovery boundary |
| `railroad/unterminated` | error | EOF inside a string, block comment, description, or expression delimiter | `unterminated TOKEN` | Opening delimiter through EOF |
| `railroad/no-rules` | warning | Resolved document has no rule definitions | `diagram has no railroad rules` | Header keyword |
| `railroad/repeat-max-ignored` | info | A repetition has a finite maximum | `finite repetition maximum MAX is not drawn` | Repeat operator or exact-count token |

- rrgrammar-32: `TOKEN` MUST be the source token text; `LIST` MUST contain accepted token-kind names sorted bytewise and joined by `, `. Repetition notices MUST retain their source operator span after lowering; the maximum notice and no-rules warning MUST NOT invalidate a document. [just parity]

## Authority readings and choices

The four Langium grammars, not a general EBNF, ABNF, or PEG standard, define acceptance. EBNF requires commas; ABNF has no incremental `=/` rule, no case modifiers, and no semantic numeric decoding. Constructor sequence and choice accept one child and then collapse. PEG accepts only one prefix and one suffix per element. The ABNF grammar uses hidden newlines, so a valid next `name =` starts a rule by parser lookahead; physical lines are used only for recovery. Duplicates and unresolved references are accepted, not invented errors. Finite-repeat and no-rules diagnostics are product notices, not upstream parse failures. Config classifications describe this project's readers, not every upstream renderer setting. No layout dimensions or routing rules are defined here.
