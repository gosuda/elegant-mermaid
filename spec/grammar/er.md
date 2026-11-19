# ER grammar

This file fixes the lexical rules, grammar, abstract syntax tree, semantic resolution, and diagnostics of the `er` kind.

## Scope

- er-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/er/parser/erDiagram.jison`; semantic resolution MUST follow `erDb.ts`. [just oracle]
- er-02: The parser MUST cover every reachable statement alternative of the authority. [just oracle]
- er-03: Shared preprocessing MUST run first; spans MUST index repaired-source bytes with exclusive ends. [just parity]

## Header forms

- er-04: The header MUST be `erDiagram`, matched case-sensitively with the shared keyword boundary. [just oracle]
- er-05: Body keyword recognition MUST use ASCII case folding; token values MUST retain source spelling. [just parity]
- er-06: Direction MUST default to `TB`. [just parity]

## Lexer modes

- er-07: The lexer MUST declare the following exclusive modes with these exact names. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| INITIAL | source start | a mode opener |
| block | `{` in INITIAL | `}` |
| block_bq | backtick in block | backtick |
| acc_title | accTitle colon | value token |
| acc_descr | accDescr colon | value token |
| acc_descr_multiline | accDescr brace | closing brace |
| style | style or classDef | newline |

### Lexical rules in first-match order

- er-08: Within each mode the lexer MUST select the first matching rule in the table, not a later longer match; unqualified rules MUST apply only in INITIAL. [just parity]

The Order column gives authority line numbers. Pattern descriptions denote byte patterns unless they name a Unicode range. Mode openers push a mode. Closing rules restore the previous mode.

| Order | Pattern and modes | Action |
|---|---|---|
| 12 | accTitle, whitespace, colon, whitespace | enter acc_title; acc_title |
| 13 | acc_title: all remaining bytes before LF | restore; acc_title_value |
| 14 | accDescr, whitespace, colon, whitespace | enter acc_descr; acc_descr |
| 15 | acc_descr: all remaining bytes before LF | restore; acc_descr_value |
| 16 | accDescr, whitespace, opening brace, whitespace | enter acc_descr_multiline; no token |
| 17 | acc_descr_multiline: closing brace | restore; no token |
| 18 | acc_descr_multiline: bytes other than closing brace | acc_descr_multiline_value |
| 19–22 | greedy same-line prefix, direction, whitespace, TB; then BT; then RL; then LR; same-line suffix | direction_tb, direction_bt, direction_rl, direction_lr respectively |
| 23 | SP, HT, CR run | skip |
| 24 | LF run | NEWLINE |
| 25 | double quotes around a nonempty run excluding quote, percent, CR, LF, VT, backspace, backslash | ENTITY_NAME |
| 26 | double quotes around any run excluding quote | WORD |
| 27 | erDiagram | ER_DIAGRAM |
| 28 | opening brace | enter block; BLOCK_START |
| 29–30 | hash; then the identical hash rule | BRKT |
| 31 | comma | COMMA |
| 32 | three colons | STYLE_SEPARATOR |
| 33 | colon | COLON |
| 34 | block: whitespace run | skip |
| 35 | block: word-bounded PK, FK, or UK | ATTRIBUTE_KEY |
| 36 | block: non-whitespace prefix, tilde, greedy same-line text, tilde, non-whitespace suffix | ATTRIBUTE_WORD |
| 37 | block: first character from star, ASCII letter, underscore, U+00C0–U+FFFF; continuation from those plus digits, hyphen, brackets, parentheses, dot, comma | ATTRIBUTE_WORD |
| 38 | block: backtick | enter block_bq; no token |
| 39 | block_bq: nonempty run excluding backtick | ATTRIBUTE_WORD |
| 40 | block_bq: backtick | restore; no token |
| 41 | block: double quotes around bytes other than quote | COMMENT |
| 42 | block: LF run | skip; shadowed by rule 34 |
| 43 | block: closing brace | restore; BLOCK_STOP |
| 44 | block: one other character | literal character token |
| 45–46 | opening square bracket; closing square bracket | SQS; SQE |
| 48 | style | enter style; STYLE |
| 49 | style: LF run | restore; NEWLINE |
| 50 | style: whitespace run | skip |
| 51–53 | style: colon; comma; hash | COLON; COMMA; BRKT |
| 54 | classDef | enter style; CLASSDEF |
| 55–57 | class; subgraph; word-bounded end and following whitespace | CLASS; SUBGRAPH; END |
| 58–61 | one or zero; one or more; one or many; 1+ | ZERO_OR_ONE; ONE_OR_MORE; ONE_OR_MORE; ONE_OR_MORE |
| 62–63 | vertical bar then o; zero or one | ZERO_OR_ONE |
| 64–70 | zero or more; zero or many; 0+; closing brace then o; many(0); many(1); many | ZERO_OR_MORE except many(1), which gives ONE_OR_MORE |
| 71 | closing brace then vertical bar | ONE_OR_MORE |
| 72–73 | one; only one | ONLY_ONE |
| 74 | digits, dot, digits | DECIMAL_NUM |
| 75–77 | 1 followed by whitespace and letter/underscore/quote; then 1 followed by whitespace and digit; then 1 followed by --, .., .-, or -. | ONLY_ONE; lookahead is not consumed |
| 78–79 | 1; digit run | ENTITY_ONE; NUM |
| 80–83 | two vertical bars; o then vertical bar; o then opening brace; vertical bar then opening brace | ONLY_ONE; ZERO_OR_ONE; ZERO_OR_MORE; ONE_OR_MORE |
| 84 | u before dot, hyphen, or vertical bar | MD_PARENT |
| 85–90 | ..; --; to; optionally to; .-; -. | NON_IDENTIFYING; IDENTIFYING; IDENTIFYING; NON_IDENTIFYING; NON_IDENTIFYING; NON_IDENTIFYING |
| 91 | style: nonempty run of non-ASCII characters, ASCII word characters, hyphen, or star | STYLE_TEXT |
| 92 | style: semicolon | SEMI; remain in style |
| 93 | nonempty run of non-ASCII characters, ASCII word characters, hyphen, star, or dot | UNICODE_TEXT |
| 94 | one other character | literal character token |
| 95 | input end | EOF |

- er-09: Shared line-ending normalization MUST make CRLF, LF, and lone CR equivalent line boundaries without changing source spans. [just parity]
- er-10: Quotes and backticks MUST remain in delimiter spans; entity names, roles, and comments MUST exclude paired double quotes from their values. [just parity]
- er-11: The lexer MUST retain the contextual distinction between ONLY_ONE and ENTITY_ONE; numeric entity names MUST follow the table rather than a numeric coercion. [just oracle]

## Grammar

- er-12: The parser MUST use the following EBNF without backtracking over consumed tokens. [just parity]

```ebnf
start = ER_DIAGRAM, document, EOF ;
document = { line } ;
line = statement | NEWLINE | EOF ;
statement = entityName, [ STYLE_SEPARATOR, idList ], relSpec,
              entityName, [ STYLE_SEPARATOR, idList ], COLON, role
          | entityName, [ SQS, entityName, SQE ],
              [ STYLE_SEPARATOR, idList ], [ BLOCK_START, [ attributes ], BLOCK_STOP ]
          | acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value | direction
          | classDefStatement | classStatement | styleStatement
          | subgraphHeader, document, END ;
subgraphHeader = SUBGRAPH, entityName, [ SQS, subgraphTitle, SQE ], separator ;
subgraphTitle = entityName, { entityName } ;
direction = direction_tb | direction_bt | direction_rl | direction_lr ;
classDefStatement = CLASSDEF, idList, stylesOpt, separator ;
idList = ( UNICODE_TEXT | STYLE_TEXT ), { COMMA, ( UNICODE_TEXT | STYLE_TEXT ) } ;
classStatement = CLASS, idList, idList ;
styleStatement = STYLE, idList, stylesOpt, separator ;
stylesOpt = style, { COMMA, style } ;
style = styleComponent, { styleComponent } ;
styleComponent = STYLE_TEXT | NUM | COLON | BRKT ;
separator = SEMI | NEWLINE | EOF ;
entityName = ENTITY_NAME | UNICODE_TEXT | NUM | DECIMAL_NUM | ENTITY_ONE ;
attributes = attribute, { attribute } ;
attribute = attributeType, attributeName, [ attributeKeyTypeList ], [ attributeComment ] ;
attributeType = ATTRIBUTE_WORD, [ '?' ] ;
attributeName = ATTRIBUTE_WORD ;
attributeKeyTypeList = attributeKeyType, { ',', attributeKeyType } ;
attributeKeyType = ATTRIBUTE_KEY ;
attributeComment = COMMENT ;
relSpec = cardinality, relType, cardinality ;
cardinality = ZERO_OR_ONE | ZERO_OR_MORE | ONE_OR_MORE | ONLY_ONE | MD_PARENT ;
relType = NON_IDENTIFYING | IDENTIFYING ;
role = WORD | ENTITY_NAME | UNICODE_TEXT ;
```

- er-13: An alias MUST occur only in an entity declaration; a relationship endpoint MUST NOT contain an alias clause. [just oracle]
- er-14: Empty entity blocks MUST be valid; attributes MUST NOT require commas, semicolons, or line breaks between records. [just oracle]
- er-15: The parser MUST NOT accept the authority's `title title_value` alternative because neither terminal has a lexer rule. [just oracle]
- er-16: Subgraphs MUST accept nested documents, including an empty document; opening level 65 MUST use the shared nesting-limit diagnostic. [just go-check]

## Statement boundary

- er-17: Successful statements MUST follow grammar boundaries; the parser MUST NOT require a newline between adjacent complete statements. [just oracle]
- er-18: Recovery MUST skip to a physical line end outside quoted text and backticks, a style separator semicolon, or the current scope's matching BLOCK_STOP or END. [just go-check]
- er-19: Recovery MUST preserve a scope close for its owning production; a malformed attribute MUST resume at the next physical line in its block. [just go-check]
- er-20: EOF inside a quoted value, backtick value, attribute block, accessibility block, or subgraph MUST produce one unterminated diagnostic from its opening delimiter. [just go-check]

## Abstract syntax tree

- er-21: AST nodes MUST use the authority production names in PascalCase and MUST span their first through last source token without a trailing separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | header, Document | header through source end |
| Document | ordered Line values | first through last child; empty at current offset |
| Line | Statement or separator | statement span or separator span |
| Statement | entity declaration, relationship, accessibility, Direction, style statement, or subgraph variant | complete statement; include body close |
| SubgraphHeader | EntityName id, optional SubgraphTitle | SUBGRAPH through title or id; omit separator |
| SubgraphTitle | EntityName parts | first through last part |
| Direction | TB, BT, RL, LR | complete direction token including consumed prefix/suffix |
| ClassDefStatement | IdList, StylesOpt | keyword through last style |
| ClassStatement | target IdList, class IdList | keyword through last class id |
| StyleStatement | IdList, StylesOpt | keyword through last style |
| IdList | ordered names | first through last id |
| StylesOpt | ordered Style values | first through last style |
| Style | ordered StyleComponent values | first through last component |
| StyleComponent | token | token span |
| Separator | token | separator span |
| EntityName | raw token, decoded name | token span including quotes |
| Attributes | ordered Attribute values | first through last attribute |
| Attribute | AttributeType, AttributeName, optional AttributeKeyTypeList, optional AttributeComment | type through last present field |
| AttributeType | word, optional question mark | word through question mark; include enclosing backticks |
| AttributeName | word | word span including enclosing backticks |
| AttributeKeyTypeList | ordered AttributeKeyType values | first through last key |
| AttributeKeyType | PK, FK, UK token | key span |
| AttributeComment | text | quote through quote |
| RelSpec | left Cardinality, RelType, right Cardinality | left marker through right marker |
| Cardinality | resolved kind, source token | token span |
| RelType | identifying flag, source token | token span |
| Role | label | token span including quotes |

- er-22: Tokens MUST borrow source text; declaration, alias, attribute-field, endpoint, and marker spans MUST remain available in the model. [just parity]
- er-23: Accessibility alternatives MUST remain Statement variants; the implementation MUST NOT invent upstream production names for them. [just parity]

## Semantic resolution

- er-24: Resolution MUST process declarations and relationships in source order and retain first entity insertion order. [just parity]
- er-25: Entity declarations and relationship endpoints MUST create missing entities; repeated declarations MUST reuse the entity. [just oracle]
- er-26: An entity MUST initially have its name as label, empty attributes and styles, and CSS class `default`; the first nonempty alias MUST win even when it appears after an implicit declaration. [just parity]
- er-27: Display text MUST use a nonempty alias instead of the name; aliases MUST NOT change endpoint lookup identity. [just parity]
- er-28: Attributes MUST append in source order across repeated blocks; absent keys MUST become an empty list and absent comments MUST become an empty string. [just parity]
- er-29: Attribute type and name MUST remain text; PK, FK, and UK MUST remain ordered key values; duplicate attributes and repeated keys MUST NOT be rejected. [just oracle]
- er-30: A nullable type MUST append `?` to its type text; a backtick value MUST remain one ATTRIBUTE_WORD even when it contains spaces or line ends. [just parity]
- er-31: Each relationship MUST retain both endpoint names, both cardinalities, its line kind, its label, and its declaration index; repeated and self relationships MUST remain separate records. [just parity]
- er-32: The left source marker MUST be the start cardinality and the right source marker MUST be the end cardinality; upstream cardB is the start and cardA is the end. [just parity]
- er-33: IDENTIFYING MUST draw a solid relationship; NON_IDENTIFYING MUST draw a dashed relationship. [just parity]
- er-34: The last top-level direction MUST win; a direction inside a subgraph MUST set that subgraph's local direction instead. [just parity]
- er-35: A subgraph MUST collect returned entity and child-subgraph ids in first occurrence order, remove duplicate ids, and exclude direction records. [just parity]
- er-36: The first completed subgraph to claim an id MUST keep that membership; a later subgraph MUST omit the already claimed id without an error. [just oracle]
- er-37: A subgraph id MUST hide an entity of the same name from rendered boxes; a relationship MUST bind to a subgraph only when that subgraph exists when the relationship is resolved. [just parity]
- er-38: class and inline class lists MUST append names only to existing targets; style MUST append declarations only to existing entities or subgraphs; missing targets MUST be ignored. [just oracle]
- er-39: classDef MUST append declarations to its definition; final style compilation MUST resolve attached names against all definitions, including later definitions. [just parity]
- er-40: A classDef declaration containing `color` MUST also supply a text declaration with `fill` replaced by `bgFill`; style text MUST NOT undergo label entity decoding. [just parity]
- er-41: Accessibility values MUST trim surrounding whitespace and replace the preceding value; a subgraph title MUST join name parts with one space. [just parity]
- er-42: The model MUST retain semantic text without browser sanitization artifacts; shared label decoding and static output escaping MUST apply at their specified stages. [just parity]
- er-43: Entity row measurement MUST follow the class compartment-table row rules: each row uses the measured label line height and an empty compartment retains one row. [just parity]
- er-44: Entity width MUST be `max(er.min_width, widest row text + 2 * er.padding)`; entity height MUST be `max(er.min_height, sum of row heights + 2 * er.padding)`. [just validate]
- er-45: `er.min_width` MUST be 100 px or 13 columns; `er.min_height` MUST be 75 px or 5 rows; `er.padding` MUST be 15 px, 2 columns on x, or 1 row on y. [just parity]
- er-46: The adapter MUST preserve the entity header and attribute rows as compartments; shared layered port clearance MUST apply after intrinsic measurement. [just validate]

## Diagnostics

- er-47: The diagnostic registry MUST contain exactly the following ER rows in this order. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `er/unexpected-token` | error | parser | token cannot continue a known production | offending token | `unexpected TOKEN, expected one of: LIST` |
| `er/unknown-statement` | error | parser | first token starts no statement | first token through next boundary | `unknown statement TOKEN` |
| `er/unterminated` | error | parser | EOF inside an open delimiter or subgraph | opener through EOF | `unterminated TOKEN` |

- er-48: LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `; TOKEN MUST contain the offending source text. [just parity]
- er-49: The parser MUST NOT add semantic errors for unknown style targets, duplicate declarations, aliases, attributes, relationships, classes, or subgraph membership; the database accepts those cases. [just oracle]
- er-50: Shared source, configuration, nesting, math, and interaction diagnostics MUST remain in their shared registries rather than the ER registry. [just gen-check]

## Upstream readings

| Reading | Authority fact | Chosen reading |
|---|---|---|
| Lexer case option versus detector | body lexer ignores case; shared header registry is sensitive | keep exact header and ASCII-fold body keywords |
| Direction expressions | greedy prefix and suffix consume the whole matching line; TB rule precedes BT, RL, LR | preserve source precedence, including prefix consumption; no TD alias |
| Title alternative | title and title_value are never returned | do not invent a title statement |
| Attribute recursion | grammar reverses its list and database reverses it again | retain source attribute order once |
| Keys | lexer preserves case but grammar accepts all folded spellings | normalize key identity to PK/FK/UK and retain raw token |
| Subgraph alias actions | alias-only alternatives return no entity list | declare the entity but do not add its id to the enclosing subgraph's returned membership list |
| Repeated subgraph ids | list retains records while lookup overwrites | keep closure-order records and last lookup binding; do not invent duplicate-id errors |
| Empty multiline accessibility | lexer has a potentially empty value rule | accept an empty block as an empty accessibility value without a zero-length token loop |
| Styles | semicolon terminates grammar but does not restore lexer mode | preserve style mode until newline, including after a semicolon |
| Database validation | no semantic action throws for ER data | only the three generic ER errors are required; malformed keys, cardinalities, and attributes use unexpected-token |
| Browser-specific ids and sanitization | database creates rendering ids and sanitizes group text | retain source identity and semantic text; shared scene and escaping contracts replace DOM behavior |

- er-51: Alias-only declarations inside subgraphs MUST follow the returned-membership reading above; declarations with a block MUST return their entity id. [just oracle]
- er-52: No unreachable lexer token or production MUST expand acceptance; Go and Rust MUST retain the same ordered model under both profiles. [just parity]
