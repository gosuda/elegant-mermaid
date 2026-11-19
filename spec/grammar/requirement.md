# Requirement grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `requirement` kind.

## Scope

- requirement-01: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/requirement/parser/requirementDiagram.jison`, with `requirementDb.ts` for resolution. [just oracle]
- requirement-02: The parser MUST accept requirement definitions, element definitions, relationships, directions, accessibility directives, class definitions, class assignments, and style assignments. [just oracle]
- requirement-03: Shared preprocessing and source-position rules MUST apply before this grammar. [just parity]

## Header forms

- requirement-04: Detection MUST accept `requirementDiagram` and `requirement` with the case-sensitive boundary rule of `spec/detection.md`; the shared header adapter MUST supply RD for either spelling. [just oracle]
- requirement-05: The parser MUST require a line end after RD and MUST permit accessibility directives before RD as the start production specifies. [just oracle]

## Lexer modes

- requirement-06: The lexer MUST declare the following exclusive modes with their authority names. [just parity]

| Mode | Entered by | Left by |
|---|---|---|
| INITIAL | source start | mode push |
| string | double quote in INITIAL or style | closing double quote |
| token | no rule | unreachable |
| unqString | no rule | unreachable |
| style | style, classDef, class | LF |
| acc_title | accTitle colon | value token |
| acc_descr | accDescr colon | value token |
| acc_descr_multiline | accDescr opening brace | closing brace |

### Lexical rules in first-match order

Order is the authority line number. An unqualified rule applies in INITIAL. `<*>` applies in every mode. Push saves the current mode. Pop restores it. Pattern descriptions specify matching behavior, not additional productions.

- requirement-07: Within each mode, the lexer MUST apply this table in source order and MUST fold body keyword case with ASCII rules only. [just parity]

| Order | Pattern and modes | Action |
|---|---|---|
| 18 | title, one whitespace, then one or more bytes other than hash, LF, semicolon | title |
| 19 | accTitle, optional whitespace, colon, optional whitespace | push acc_title; acc_title |
| 20 | acc_title: authority value pattern `(?!\n|;|#)*[^\n]*` | pop; acc_title_value |
| 21 | accDescr, optional whitespace, colon, optional whitespace | push acc_descr; acc_descr |
| 22 | acc_descr: same value pattern as line 20 | pop; acc_descr_value |
| 23 | accDescr, optional whitespace, opening brace, optional whitespace | push acc_descr_multiline; skip |
| 24 | acc_descr_multiline: closing brace | pop; skip |
| 25 | acc_descr_multiline: zero or more bytes other than closing brace | acc_descr_multiline_value |
| 26 | any line prefix, direction, whitespace, TB, then line remainder | direction_tb |
| 27 | same with BT | direction_bt |
| 28 | same with RL | direction_rl |
| 29 | same with LR | direction_lr |
| 30 | one or more optional-CR LF pairs | NEWLINE |
| 31 | one or more whitespace characters | skip |
| 32 | hash through line remainder | skip |
| 33 | two percent signs through line remainder | skip |
| 34 | end of input | EOF |
| 36 | requirementDiagram | RD |
| 38 | opening brace | STRUCT_START |
| 39 | closing brace | STRUCT_STOP |
| 40 | three colons | STYLE_SEPARATOR |
| 41 | colon | COLONSEP |
| 43 | id | ID |
| 44 | text | TEXT |
| 45 | risk | RISK |
| 46 | verifyMethod | VERIFYMTHD |
| 48 | requirement | REQUIREMENT |
| 49 | functionalRequirement | FUNCTIONAL_REQUIREMENT |
| 50 | interfaceRequirement | INTERFACE_REQUIREMENT |
| 51 | performanceRequirement | PERFORMANCE_REQUIREMENT |
| 52 | physicalRequirement | PHYSICAL_REQUIREMENT |
| 53 | designConstraint | DESIGN_CONSTRAINT |
| 55 | low | LOW_RISK |
| 56 | medium | MED_RISK |
| 57 | high | HIGH_RISK |
| 59 | analysis | VERIFY_ANALYSIS |
| 60 | demonstration | VERIFY_DEMONSTRATION |
| 61 | inspection | VERIFY_INSPECTION |
| 62 | test | VERIFY_TEST |
| 64 | element | ELEMENT |
| 66 | contains | CONTAINS |
| 67 | copies | COPIES |
| 68 | derives | DERIVES |
| 69 | satisfies | SATISFIES |
| 70 | verifies | VERIFIES |
| 71 | refines | REFINES |
| 72 | traces | TRACES |
| 74 | type | TYPE |
| 75 | docref | DOCREF |
| 77 | style | push style; STYLE |
| 78 | style: one or more ASCII word characters | ALPHA |
| 79 | style: colon | COLON |
| 80 | style: semicolon | SEMICOLON |
| 81 | style: percent | PERCENT |
| 82 | style: minus | MINUS |
| 83 | style: hash | BRKT |
| 84 | style: space | skip |
| 85 | style: double quote | push string; skip |
| 86 | style: LF | pop; skip |
| 88 | classDef | push style; CLASSDEF |
| 89 | class | push style; CLASS |
| 91 | left arrow `<-` | END_ARROW_L |
| 92 | right arrow `->` | END_ARROW_R |
| 93 | minus | LINE |
| 95 | double quote | push string; skip |
| 96 | string: double quote | pop; skip |
| 97 | string: zero or more bytes other than double quote | qString |
| 99 | ASCII word character followed by bytes other than colon, comma, CR, LF, opening brace, angle brackets, minus, equals | trim; unqString |
| 101 | all modes: one or more ASCII word characters | ALPHA |
| 102 | all modes: one or more decimal digits | NUM |
| 103 | all modes: comma | COMMA |

- requirement-08: Quoted values MUST exclude their double quotes from the value and MUST retain them in the token span; backslash MUST NOT escape a quote. [just parity]
- requirement-09: Unquoted values MUST trim whitespace from their value without changing their span. [just parity]
- requirement-10: Shared line handling MUST treat LF, CRLF, and lone CR as physical line ends; mode transitions that name LF MUST use that shared line-end event. [just parity]
- requirement-11: The lexer MUST retain the direction rules' whole-line precedence and the unconditional final ALPHA, NUM, and COMMA rules. [just oracle]

## Grammar

- requirement-12: The parser MUST use the following EBNF without backtracking over consumed tokens. [just parity]

```ebnf
start = { directive, [ NEWLINE ] }, RD, NEWLINE, diagram, EOF ;
diagram = { requirementDef | elementDef | relationshipDef | directive
          | direction | styleStatement | classDefStatement | classStatement | NEWLINE } ;
directive = acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value ;
direction = direction_tb | direction_bt | direction_rl | direction_lr ;
requirementDef = requirementType, requirementName,
                 [ STYLE_SEPARATOR, idList ], STRUCT_START, NEWLINE, requirementBody ;
requirementBody = { ID, COLONSEP, id, NEWLINE
                 | TEXT, COLONSEP, text, NEWLINE
                 | RISK, COLONSEP, riskLevel, NEWLINE
                 | VERIFYMTHD, COLONSEP, verifyType, NEWLINE | NEWLINE }, STRUCT_STOP ;
requirementType = REQUIREMENT | FUNCTIONAL_REQUIREMENT | INTERFACE_REQUIREMENT
                | PERFORMANCE_REQUIREMENT | PHYSICAL_REQUIREMENT | DESIGN_CONSTRAINT ;
riskLevel = LOW_RISK | MED_RISK | HIGH_RISK ;
verifyType = VERIFY_ANALYSIS | VERIFY_DEMONSTRATION | VERIFY_INSPECTION | VERIFY_TEST ;
elementDef = ELEMENT, elementName, [ STYLE_SEPARATOR, idList ],
             STRUCT_START, NEWLINE, elementBody ;
elementBody = { TYPE, COLONSEP, type, NEWLINE | DOCREF, COLONSEP, ref, NEWLINE
             | NEWLINE }, STRUCT_STOP ;
relationshipDef = id, END_ARROW_L, relationship, LINE, id
                | id, LINE, relationship, END_ARROW_R, id ;
relationship = CONTAINS | COPIES | DERIVES | SATISFIES | VERIFIES | REFINES | TRACES ;
classDefStatement = CLASSDEF, idList, stylesOpt ;
classStatement = CLASS, idList, idList | id, STYLE_SEPARATOR, idList ;
idList = ( ALPHA | id ), { COMMA, ( ALPHA | id ) } ;
styleStatement = STYLE, idList, stylesOpt ;
stylesOpt = style, { COMMA, style } ;
style = styleComponent, { styleComponent } ;
styleComponent = ALPHA | NUM | COLON | UNIT | SPACE | BRKT | PCT | MINUS | LABEL | SEMICOLON ;
requirementName = unqString | qString ;
id = unqString | qString ;
text = unqString | qString ;
elementName = unqString | qString ;
type = unqString | qString ;
ref = unqString | qString ;
```

- requirement-13: Grammar terminals with no emitting lexical rule MUST remain unreachable; PERCENT MUST NOT be repaired to PCT. [just oracle]
- requirement-14: The title token MUST produce unexpected-token because no reachable production consumes it. [just oracle]
- requirement-15: The parser MUST permit empty bodies and repeated fields; it MUST NOT require any optional field. [just oracle]

## Statement boundary

- requirement-16: Recovery MUST stop at a physical line end outside string and acc_descr_multiline, or immediately before the current body's closing brace. [just go-check]
- requirement-17: Recovery inside a body MUST resume with its next field or its closing brace; recovery at top level MUST resume with its next statement. [just go-check]
- requirement-18: A semicolon MUST NOT be a general separator; inside style it MUST remain a style component. [just oracle]
- requirement-19: EOF inside an open string, definition body, or accessibility block MUST emit unterminated and MUST stop that construct. [just go-check]

## Abstract syntax tree

- requirement-20: Each AST node MUST use its upstream production name in PascalCase and MUST carry its first-token-through-last-token span, without a trailing separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| Start | header, Diagram, leading Directive list | first directive or header through EOF |
| Diagram | ordered statements | first through last statement; empty at body start |
| Directive | title or description value, multiline flag | keyword through value; multiline includes both braces |
| Direction | TB, BT, RL, LR | complete matched direction token |
| RequirementDef | RequirementType, RequirementName, optional IdList, RequirementBody | type through closing brace |
| RequirementBody | ordered field records and values | first field through closing brace; empty includes closing brace |
| RequirementType | six-way type | keyword |
| RiskLevel | three-way risk | keyword |
| VerifyType | four-way verification method | keyword |
| ElementDef | ElementName, optional IdList, ElementBody | element keyword through closing brace |
| ElementBody | ordered field records and values | first field through closing brace; empty includes closing brace |
| RelationshipDef | two Id values, Relationship, arrow orientation | first endpoint through last endpoint |
| Relationship | seven-way relation | keyword |
| ClassDefStatement | IdList, StylesOpt | classDef through final component |
| ClassStatement | target IdList or Id, class IdList | first token through final class |
| StyleStatement | IdList, StylesOpt | style keyword through final component |
| IdList | ordered names | first through last name |
| StylesOpt | ordered Style list | first through last component |
| Style | ordered StyleComponent list | first through last component |
| StyleComponent | kind and source text | token |
| RequirementName, Id, Text, ElementName, Type, Ref | quoted flag and value | token including quote delimiters |

- requirement-21: Tokens MUST borrow source text; the model MUST retain definition, field, endpoint, style, and delimiter spans. [just parity]

## Semantic resolution

- requirement-22: Resolution MUST retain first insertion order within requirement and element lists and MUST emit requirements before elements, as getData does. [just parity]
- requirement-23: RequirementType MUST map to Requirement, Functional Requirement, Interface Requirement, Performance Requirement, Physical Requirement, or Design Constraint respectively. [just parity]
- requirement-24: A requirement MUST retain its name, type, id, text, risk, and verify method; unset fields MUST be empty. [just parity]
- requirement-25: RiskLevel MUST map to Low, Medium, or High; VerifyType MUST map to Analysis, Demonstration, Inspection, or Test. [just parity]
- requirement-26: Repeated body fields MUST use the first textual value because right-recursive body actions run from the last field to the first. [just oracle]
- requirement-27: An element MUST retain its name, type, and docref with empty defaults. [just parity]
- requirement-28: A duplicate name within one node kind MUST keep the first definition and MUST reset the pending fields after the ignored definition. [just oracle]
- requirement-29: Requirement and element names MUST remain separate namespaces; endpoint and style lookup MUST prefer a requirement when both names exist. [just oracle]
- requirement-30: Each relationship MUST append one record in declaration order; `A <- relation - B` MUST resolve from B to A and `A - relation -> B` MUST resolve from A to B. [just parity]
- requirement-31: All seven relationship kinds MUST be retained, including repeated relationships and self-relations. [just oracle]
- requirement-32: An unresolved endpoint MUST remain unresolved and MUST NOT create an implicit node or a parser error; the database performs no endpoint rejection. [just oracle]
- requirement-33: A contains relation MUST use a solid line and a source requirement_contains marker; every other relation MUST use a dashed line and a target requirement_arrow marker. [just parity]
- requirement-34: A relationship label MUST contain its relation name between two angle brackets on each side, without retaining HTML entity spellings in semantic text. [just parity]
- requirement-35: Direction MUST default to TB for each document and MUST take the final direction statement's value. [just parity]
- requirement-36: Every new node MUST start with class default and an empty direct-style list. [just parity]
- requirement-37: ClassStatement MUST append class names for existing targets and MUST append currently defined class styles; unknown targets and unknown class names MUST NOT raise errors. [just oracle]
- requirement-38: Inline classes MUST apply after inserting their definition and MUST also apply to a retained duplicate definition. [just oracle]
- requirement-39: ClassDefStatement MUST append styles to each named class and MUST append its new styles to existing nodes carrying that class. [just parity]
- requirement-40: Class definition text styles MUST select components containing lowercase color and MUST replace the first lowercase fill with bgFill in that selected component. [just parity]
- requirement-41: StyleStatement MUST append components in order and MUST stop its target loop at the first missing target; embedded commas MUST split into separate components. [just oracle]
- requirement-42: Style MUST concatenate component text without inserting spaces; shared static-output restrictions MUST apply when styles reach a backend. [just parity]
- requirement-43: Accessibility directives MUST trim their values and MUST replace the preceding value of the same accessibility field. [just parity]
- requirement-44: A requirement box MUST have width equal to its widest row text plus requirement.padding and height equal to its row-height sum plus requirement.padding. [just validate]
- requirement-45: requirement.padding MUST be 20 px in vector units, 3 cells on x, and 2 rows on y; each set field among type, id, text, risk, and verify method MUST add one row. [just validate]
- requirement-46: Config keys MUST follow spec/data/config-keys/requirement.json; rect_* keys MUST NOT change this sizing rule. [just gen-check]

## Diagnostics

- requirement-47: Rejected syntax MUST use exactly the following diagnostic rows; resolution MUST NOT invent checks absent from the database. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `requirement/unexpected-token` | error | parser | token fits no current production, including invalid risk or verify method | offending token | `unexpected TOKEN, expected one of: LIST` |
| `requirement/unknown-statement` | error | parser | first token starts no statement | first token through next boundary | `unknown statement TOKEN` |
| `requirement/unterminated` | error | parser | EOF inside a string, definition, or accessibility block | opening delimiter through EOF | `unterminated TOKEN` |

- requirement-48: TOKEN MUST be source text; LIST MUST contain accepted token-kind names sorted bytewise and joined by comma and space. [just parity]
- requirement-49: An unknown first token MUST produce unknown-statement rather than an implicit requirement; a known statement with an invalid field MUST produce unexpected-token. [just go-check]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| Header alias | lexer accepts only requirementDiagram; shared registry also accepts requirement | normalize the shared alias to RD |
| Keyword case | body lexer is case-insensitive; detector is case-sensitive | fold body keywords only |
| Repeated fields | right-recursive actions overwrite from right to left | first textual field wins |
| Title | title token has no production | reject with unexpected-token |
| Percent styles | lexer emits PERCENT; grammar consumes PCT | preserve lexical rejection |
| Unused tokens and modes | token and unqString modes have no entry; several style terminals have no producer | do not add syntax |
| Direction | greedy lexer rules can consume a line prefix and suffix | preserve their ordered whole-line recognition |
| Missing endpoints | addRelationship appends without checking; getData can return undefined ends | retain unresolved references without phantom nodes or invented parser diagnostics |
| Duplicate namespaces | independent maps allow identical requirement and element names | keep separate namespaces and requirement-first lookup |
| Direction reset | clear does not reset direction, but constructor initializes TB | each immutable document starts at TB |
| Line ends | lexer recognizes LF and CRLF inconsistently across modes | apply shared lone-CR handling |
| Empty quoted text | zero-length lexical value can stall some lexer implementations | emit at most one empty qString value and consume the closing quote |
| Geometry keys | legacy rect_* settings do not supply the planned layout rule | accept and ignore them |

- requirement-50: The Go and Rust AST and resolved models MUST agree in declaration order under both metric profiles. [just parity]
