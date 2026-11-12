# Class grammar

This file fixes the lexical rules, the grammar, the abstract syntax tree, the semantic resolution, and the diagnostics of the `class` kind.

## Scope

- class-001: The grammar authority MUST be `.references/mermaid/packages/mermaid/src/diagrams/class/parser/classDiagram.jison`, with `classDb.ts` and `classTypes.ts` for semantic resolution. [just oracle]
- class-002: The parser MUST cover every reachable statement alternative of the authority. [just go-check]
- class-003: Preprocessing MUST follow `spec/preprocessing.md`, and spans MUST index the repaired source bytes with an exclusive end. [just parity]

## Header forms

- class-004: The first header MUST be `classDiagram` or `classDiagram-v2`, case-sensitive, with the keyword boundary of `spec/detection.md`. [just oracle]
- class-005: The header MUST be followed by a line end and at least one statement, as graphConfig and statements require. [just oracle]

## Lexer modes

- class-006: The lexer MUST use the exclusive modes below and MUST take the first matching rule, not the longest later match. [just parity]
- class-007: Quoted word patterns MUST have the word boundary that Jison adds; `classical` MUST NOT start a `CLASS` token. [just oracle]

| Mode | Entered by | Left by |
|---|---|---|
| `INITIAL` | source start | none |
| `string` | double quote in any mode | double quote |
| `bqstring` | backtick in any mode | backtick |
| `generic` | tilde in any mode | tilde |
| `struct` | never | never |
| `href` | never | never |
| `callback_name` | `call` and whitespace in INITIAL | `(` or `()` |
| `callback_args` | `(` in callback_name | `)` |
| `acc_title` | `accTitle:` | value token |
| `acc_descr` | `accDescr:` | value token |
| `acc_descr_multiline` | `accDescr {` | `}` |
| `class` | `class` in INITIAL or namespace-body | newline, or after body closure |
| `class-body` | `{` in class | `}` |
| `namespace` | `namespace` in INITIAL, namespace, namespace-body | newline or enclosing close |
| `namespace-body` | `{` in namespace | `}` |

### Lexical rules in first-match order

The Order column is the authority line number. An unqualified rule applies in INITIAL. A `<*>` rule applies in every mode. `begin` pushes a mode; `popState` restores it. The table retains dead rules to make their precedence visible. The Unicode range rule is one rule, not one rule per source line.

- class-008: The lexer MUST apply the following rules in source order after shared preprocessing. [just parity]

| Order | Pattern and modes | Action |
|---|---|---|
| 24 | `.*direction\s+TB[^\n]*` | `return 'direction_tb';` |
| 25 | `.*direction\s+BT[^\n]*` | `return 'direction_bt';` |
| 26 | `.*direction\s+RL[^\n]*` | `return 'direction_rl';` |
| 27 | `.*direction\s+LR[^\n]*` | `return 'direction_lr';` |
| 28 | `\%\%(?!\{)*[^\n]*(\r?\n?)+` | `/* skip comments */` |
| 29 | `\%\%[^\n]*(\r?\n)*` | `/* skip comments */` |
| 30 | `accTitle\s*":"\s*` | `{ this.begin("acc_title");return 'acc_title'; }` |
| 31 | `<acc_title>(?!\n\|;\|#)*[^\n]*` | `{ this.popState(); return "acc_title_value"; }` |
| 32 | `accDescr\s*":"\s*` | `{ this.begin("acc_descr");return 'acc_descr'; }` |
| 33 | `<acc_descr>(?!\n\|;\|#)*[^\n]*` | `{ this.popState(); return "acc_descr_value"; }` |
| 34 | `accDescr\s*"{"\s*` | `{ this.begin("acc_descr_multiline");}` |
| 35 | `<acc_descr_multiline>[\}]` | `{ this.popState(); }` |
| 36 | `<acc_descr_multiline>[^\}]*` | `return "acc_descr_multiline_value";` |
| 38 | `\s*(\r?\n)+` | `return 'NEWLINE';` |
| 39 | `\s+` | `/* skip whitespace */` |
| 41 | `"classDiagram-v2"` | `return 'CLASS_DIAGRAM';` |
| 42 | `"classDiagram"` | `return 'CLASS_DIAGRAM';` |
| 43 | `"[*]"` | `return 'EDGE_STATE';` |
| 53 | `<INITIAL>"call"[\s]+` | `this.begin("callback_name");` |
| 54 | `<callback_name>\([\s]*\)` | `this.popState();` |
| 55 | `<callback_name>\(` | `this.popState(); this.begin("callback_args");` |
| 56 | `<callback_name>[^(]*` | `return 'CALLBACK_NAME';` |
| 57 | `<callback_args>\)` | `this.popState();` |
| 58 | `<callback_args>[^)]*` | `return 'CALLBACK_ARGS';` |
| 60 | `<string>["]` | `this.popState();` |
| 61 | `<string>[^"]*` | `return "STR";` |
| 62 | `<*>["]` | `this.begin("string");` |
| 63 | `"style"` | `return 'STYLE';` |
| 64 | `"classDef"` | `return 'CLASSDEF';` |
| 66 | `<INITIAL,namespace,namespace-body>"namespace"` | `{ this.begin('namespace'); return 'NAMESPACE'; }` |
| 67 | `<namespace>\s*(\r?\n)+` | `{ this.popState(); return 'NEWLINE'; }` |
| 68 | `<namespace>\s+` | `/* skip whitespace */` |
| 69 | `<namespace>[{]` | `{ this.begin("namespace-body"); return 'STRUCT_START';}` |
| 70 | `<namespace>[}]` | `{ this.popState(); this.less(0); }` |
| 71 | `<namespace-body>[}]` | `{ this.popState(); return 'STRUCT_STOP'; }` |
| 72 | `<namespace-body><<EOF>>` | `return "EOF_IN_STRUCT";` |
| 73 | `<namespace-body>\s*(\r?\n)+` | `return 'NEWLINE';` |
| 74 | `<namespace-body>\s+` | `/* skip whitespace */` |
| 75 | `<namespace-body>"[*]"` | `return 'EDGE_STATE';` |
| 78 | `<class>\s*(\r?\n)+` | `{ this.popState(); return 'NEWLINE'; }` |
| 79 | `<class>\s+` | `/* skip whitespace */` |
| 80 | `<class>[}]` | `{ this.popState(); this.popState(); return 'STRUCT_STOP';}` |
| 81 | `<class>[{]` | `{ this.begin("class-body"); return 'STRUCT_START';}` |
| 82 | `<class-body>[}]` | `{ this.popState(); return 'STRUCT_STOP'; }` |
| 83 | `<class-body><<EOF>>` | `return "EOF_IN_STRUCT";` |
| 84 | `<class-body>"[*]"` | `{ return 'EDGE_STATE';}` |
| 85 | `<class-body>[{]` | `return "OPEN_IN_STRUCT";` |
| 86 | `<class-body>[\n]` | `/* nothing */` |
| 87 | `<class-body>[^{}\n]*` | `{ return "MEMBER";}` |
| 89 | `<*>"cssClass"` | `return 'CSSCLASS';` |
| 90 | `<*>"callback"` | `return 'CALLBACK';` |
| 91 | `<*>"link"` | `return 'LINK';` |
| 92 | `<*>"click"` | `return 'CLICK';` |
| 93 | `<*>"note for"` | `return 'NOTE_FOR';` |
| 94 | `<*>"note"` | `return 'NOTE';` |
| 95 | `<*>"<<"` | `return 'ANNOTATION_START';` |
| 96 | `<*>">>"` | `return 'ANNOTATION_END';` |
| 104 | `<*>"href"` | `return 'HREF';` |
| 106 | `<generic>[~]` | `this.popState();` |
| 107 | `<generic>[^~]*` | `return "GENERICTYPE";` |
| 108 | `<*>"~"` | `this.begin("generic");` |
| 110 | `<bqstring>[&#96;]` | `this.popState();` |
| 111 | `<bqstring>[^&#96;]+` | `return "BQUOTE_STR";` |
| 112 | `<*>[&#96;]` | `this.begin("bqstring");` |
| 114 | `<*>"_self"` | `return 'LINK_TARGET';` |
| 115 | `<*>"_blank"` | `return 'LINK_TARGET';` |
| 116 | `<*>"_parent"` | `return 'LINK_TARGET';` |
| 117 | `<*>"_top"` | `return 'LINK_TARGET';` |
| 119 | `<*>\s*\<\\|` | `return 'EXTENSION';` |
| 120 | `<*>\s*\\|\>` | `return 'EXTENSION';` |
| 121 | `<*>\s*\>` | `return 'DEPENDENCY';` |
| 122 | `<*>\s*\<` | `return 'DEPENDENCY';` |
| 123 | `<*>\s*\*` | `return 'COMPOSITION';` |
| 124 | `<*>\s*o` | `return 'AGGREGATION';` |
| 125 | `<*>\s*\(\)` | `return 'LOLLIPOP';` |
| 126 | `<*>\-\-` | `return 'LINE';` |
| 127 | `<*>\.\.` | `return 'DOTTED_LINE';` |
| 128 | `<*>":"{1}[^:\n;]+` | `return 'LABEL';` |
| 129 | `<*>":"{3}` | `return 'STYLE_SEPARATOR';` |
| 130 | `<*>\-` | `return 'MINUS';` |
| 131 | `<*>"."` | `return 'DOT';` |
| 132 | `<*>\+` | `return 'PLUS';` |
| 133 | `":"` | `return 'COLON';` |
| 134 | `","` | `return 'COMMA';` |
| 135 | `\#` | `return 'BRKT';` |
| 136 | `"#"` | `return 'BRKT';` |
| 137 | `<*>\%` | `return 'PCT';` |
| 138 | `<*>"="` | `return 'EQUALS';` |
| 139 | `<*>\=` | `return 'EQUALS';` |
| 140 | `<*>\w+` | `return 'ALPHA';` |
| 141 | `<*>"["` | `return 'SQS';` |
| 142 | `<*>"]"` | `return 'SQE';` |
| 143 | `<*>[!"#$%&'*+,-.&#96;?\\/]` | `return 'PUNCTUATION';` |
| 144 | `<*>[0-9]+` | `return 'NUM';` |
| 145 | `<*> Unicode letter ranges of authority lines 145–205` | `UNICODE_TEXT` |
| 207 | `<*>\s` | `return 'SPACE';` |
| 208 | `\s` | `return 'SPACE';` |
| 209 | `<*><<EOF>>` | `return 'EOF';` |

- class-009: String, backtick, and generic delimiters MUST NOT be part of their token value, but MUST remain in its span. [just parity]
- class-010: The Unicode letter set MUST be exactly the union of the authority ranges at lines 145–205, not the host language's Unicode letter category. [just parity]
- class-011: The LABEL token MUST consume one colon and a nonempty run excluding colon, LF, and semicolon; a second colon MUST be tokenized separately. [just oracle]
- class-012: A string or backtick value MUST allow line ends, because its authority character class excludes only its closing delimiter. [just oracle]

## Grammar

- class-013: The parser MUST use the following EBNF, whose production names are the authority rule names, without backtracking over consumed tokens. [just parity]

```ebnf
start = mermaidDoc | statements ;
mermaidDoc = graphConfig ;
graphConfig = CLASS_DIAGRAM, NEWLINE, statements, EOF ;
statements = statement, [ NEWLINE, [ statements ] ] ;
statement = relationStatement, [ LABEL ] | namespaceStatement | classStatement
          | memberStatement | annotationStatement | clickStatement | styleStatement
          | cssClassStatement | noteStatement | classDefStatement | direction
          | acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value ;
classLabel = SQS, STR, SQE ;
namespaceName = alphaNumToken, [ DOT, namespaceName | namespaceName ] | classLiteralName ;
className = alphaNumToken, [ DOT, className | className | GENERICTYPE ]
          | classLiteralName, [ GENERICTYPE ] ;
namespaceIdentifier = NAMESPACE, namespaceName, [ classLabel ] ;
namespaceStatement = namespaceIdentifier, STRUCT_START, [ NEWLINE ], classStatements, STRUCT_STOP ;
classStatements = (classStatement | noteStatement | namespaceStatement), [ NEWLINE, [ classStatements ] ] ;
classIdentifier = CLASS, className, [ classLabel ] ;
classStatement = classIdentifier, [ STYLE_SEPARATOR, alphaNumToken, [ STRUCT_START, members, STRUCT_STOP ]
               | STRUCT_START, [ members ], STRUCT_STOP
               | ANNOTATION_START, alphaNumToken, ANNOTATION_END, [ STRUCT_START, [ members ], STRUCT_STOP ] ] ;
annotationStatement = ANNOTATION_START, alphaNumToken, ANNOTATION_END, className ;
members = MEMBER, { MEMBER } ;
memberStatement = className, [ LABEL ] | MEMBER ;
relationStatement = className, [ STR ], relation, [ STR ], className ;
relation = [ relationType ], lineType, [ relationType ] ;
relationType = AGGREGATION | EXTENSION | COMPOSITION | DEPENDENCY | LOLLIPOP ;
lineType = LINE | DOTTED_LINE ;
noteStatement = NOTE_FOR, className, noteText | NOTE, noteText ;
noteText = STR ;
classDefStatement = CLASSDEF, classList, stylesOpt ;
classList = ALPHA, { COMMA, ALPHA } ;
direction = direction_tb | direction_bt | direction_rl | direction_lr ;
clickStatement = CALLBACK, className, STR, [ STR ]
               | LINK, className, STR, [ STR ], [ LINK_TARGET ]
               | CLICK, className, CALLBACK_NAME, [ CALLBACK_ARGS ], [ STR ]
               | CLICK, className, HREF, STR, [ STR ], [ LINK_TARGET ] ;
styleStatement = STYLE, ALPHA, stylesOpt ;
cssClassStatement = CSSCLASS, STR, ALPHA ;
stylesOpt = style, { COMMA, style } ;
style = styleComponent, { styleComponent } ;
styleComponent = ALPHA | NUM | COLON | SPACE | BRKT | STYLE | PCT | LABEL ;
alphaNumToken = UNICODE_TEXT | NUM | ALPHA | MINUS ;
classLiteralName = BQUOTE_STR ;
```

- class-014: A namespace body MUST contain at least one class, note, or nested namespace; relations and standalone member statements MUST NOT occur in it. [just oracle]
- class-015: An empty class body MUST be accepted, but a CSS shorthand followed by a body MUST contain a member token. [just oracle]
- class-016: A bare className MUST parse without creating a class; whitespace between name tokens MUST concatenate them, so `class Service as ServiceInterface` declares `ServiceasServiceInterface`, not an alias. [just oracle]
- class-017: A top-level `title` line MUST parse as a bare className when its tokens fit className; it MUST NOT set the diagram title. [just oracle]
- class-018: A semicolon MUST NOT separate statements; the authority has no semicolon token. [just oracle]

## Statement boundary

- class-019: Recovery MUST skip to the next physical line end outside strings, backticks, and generic values, or to the matching body close at the current scope. [just go-check]
- class-020: Recovery MUST keep the enclosing namespace or class scope and MUST NOT create model objects for the rejected statement. [just go-check]
- class-021: An end of input inside a string, generic value, backtick, class body, namespace body, or accessibility block MUST raise the unterminated diagnostic unless a named code below applies. [just go-check]
- class-022: Namespace and class nesting MUST stop before level 65 and use the shared nesting-limit diagnostic. [just go-check]

## Abstract syntax tree

- class-023: Each AST node MUST take its authority production name in PascalCase and MUST carry a span from the first token through the last token, without a trailing statement separator. [just parity]

| Node | Fields | Span rule |
|---|---|---|
| `Start`, `MermaidDoc`, `GraphConfig` | header, statements | entire source; header through EOF for GraphConfig |
| `Statements`, `ClassStatements` | ordered statements | first through last child |
| `Statement` | selected alternative; accessibility value when present | selected alternative |
| `ClassLabel`, `ClassLiteralName` | decoded delimiter-free value | includes delimiters |
| `ClassName`, `NamespaceName`, `AlphaNumToken` | ordered tokens, joined value, optional generic for ClassName | all consumed tokens |
| `NamespaceIdentifier` | name, optional label | keyword through label or name |
| `NamespaceStatement` | identifier, ordered children | keyword through closing brace |
| `ClassIdentifier` | name, optional label | keyword through label or name |
| `ClassStatement` | identifier, optional CSS class, annotation, members, hasBody | keyword through last field or closing brace |
| `AnnotationStatement` | annotation, class name | opening annotation through class name |
| `Members` | member texts and individual token spans | first through last member |
| `MemberStatement` | class name, optional LABEL, or raw MEMBER | all consumed tokens |
| `RelationStatement` | endpoints, optional multiplicities, relation, optional statement LABEL | first endpoint through last label |
| `Relation`, `RelationType`, `LineType` | start marker, end marker, line kind | marker and line bytes |
| `NoteStatement`, `NoteText` | optional class name, quoted text | keyword through string; NoteText includes quotes |
| `ClickStatement` | action, target, callback or URL, arguments, tooltip, link target | keyword through final argument |
| `StyleStatement`, `CssClassStatement`, `ClassDefStatement` | targets and styles or CSS name | keyword through final value |
| `ClassList` | ordered names | first through last name |
| `StylesOpt`, `Style`, `StyleComponent` | ordered components and raw text | first through last component |
| `Direction` | resolved direction | entire greedy line match |

- class-024: AST tokens MUST borrow the source, and the model MUST retain member, endpoint, and declaration spans for diagnostics. [just parity]

## Semantic resolution

- class-025: Model resolution MUST process statements in declaration order and MUST keep first insertion order for classes, namespaces, notes, and relations. [just parity]
- class-026: Explicit class declarations, relation endpoints, and member assignments MUST create an absent class; bare names MUST NOT create one. [just oracle]
- class-027: A class id with a tilde generic MUST split at the first tilde after its first character; its base is the id and its first generic segment is its type. [just parity]
- class-028: The first declaration MUST set shape `classBox`, label equal to the base id, CSS classes `default`, and empty methods, attributes, annotations, and styles; a later declaration MUST keep those fields except an explicit label replaces the label. [just parity]
- class-029: The display name MUST append the generic as angle-bracket text when the type is nonempty; it MUST NOT store HTML entity escaping as visible text. [just parity]
- class-030: Body members MUST retain source order despite the grammar's reversed reduction list; each trimmed member beginning with `<<` and ending with `>>` MUST add an annotation. [just parity]
- class-031: A nonempty member with a `)` after its first character MUST be a method; every other nonempty member MUST be an attribute; an empty member MUST be ignored. [just parity]
- class-032: Member interpretation MUST follow ClassMember.parseMember: leading `#`, `+`, `~`, or `-` sets visibility, trailing `$` sets static underline, and trailing `*` sets abstract italic. [just parity]
- class-033: A method MUST use the authority regex `([#+~-])?(.+)\((.*)\)([\s$*])?(.*)([$*])?`, with greedy name and parameters; parameters and return type MUST be trimmed, and a trailing classifier on the return type MUST be removed when no classifier follows the closing parenthesis. [just parity]
- class-034: Member display MUST preserve at most one initial name space, convert tilde generic pairs with the shared generic conversion, and show method return text after ` : `. [just parity]
- class-035: A standalone annotation MUST refer to an existing class; it MUST NOT create a class. [just oracle]
- class-036: Relations MUST keep both endpoint multiplicities, trimmed, with absent values `none`; the optional LABEL MUST lose its leading colon and surrounding whitespace. [just parity]
- class-037: Relation marker mapping MUST be aggregation=0, extension=1, composition=2, dependency=3, lollipop=4, absent=none; LINE MUST be solid and DOTTED_LINE MUST be dashed. [just parity]
- class-038: A relation with exactly one lollipop end and no marker at the other end MUST create `interfaceN` at that end, where N is the zero-based interface insertion index, using the original endpoint as its label and the other class as its owner. [just parity]
- class-039: A relation with any other marker pair MUST create both ordinary endpoint classes, including two lollipop markers. [just oracle]
- class-040: A note MUST get id `noteN` with zero-based note insertion index; a note for an absent class MUST remain unattached and MUST NOT create that class. [just parity]
- class-041: Namespace resolution MUST prefix a nested namespace with the current qualified namespace and a dot; dotted segments MUST create missing ancestors with segment labels, ordered from root to leaf. [just parity]
- class-042: An explicit namespace MUST mark its leaf explicit; redeclaration MUST retain its insertion index and replace its label only when the new label is nonempty. [just parity]
- class-043: Namespace closure MUST assign direct class and note children to that namespace; a later assignment MUST replace the child's parent without changing its class id. [just parity]
- class-044: The model MUST retain the hierarchical namespace tree; the `hierarchicalNamespaces` display option MUST be accepted and ignored because the plan supplies one containment layout, not a compact alternative. [just gen-check]
- class-045: CSS assignment MUST append the CSS name only to existing targets; comma-separated ids in cssClass MUST be processed in order, and unknown targets MUST be ignored. [just oracle]
- class-046: Style statements MUST append styles to existing classes only; classDef MUST append to its style definition and apply its styles to existing classes whose CSS class string contains that name. [just parity]
- class-047: A classDef style containing `color` MUST also append a text style after replacing `fill` with `bgFill`; styles MUST retain their source order and MUST NOT decode entity notation. [just parity]
- class-048: Link and callback statements MUST retain their parsed values only on existing targets; the default link target MUST be `_blank`, and callbacks MUST NOT run. [just parity]
- class-049: Callback arguments MUST split on commas outside double quotes, trim outer whitespace, remove paired outer quotes, and default to the class id when no argument exists. [just parity]
- class-050: Accessibility values MUST trim surrounding whitespace and replace the preceding value; direction MUST default to TB and the last recognized direction MUST win. [just parity]
- class-051: The layered adapter MUST size a class as a compartment table: widest row plus twice class.padding, sum of row heights, and one separator row between compartments; an empty compartment MUST retain one row. [just validate]
- class-052: The padding fallback MUST be 16 px, with 2 columns in the cell profile; the separator MUST be 1 px or 1 cell row. [just parity]
- class-053: Notes MUST use note style, namespace frames MUST use group style, and dotted class relations and note connectors MUST use dashed strokes. [just parity]

## Diagnostics

- class-054: A parser rejection MUST produce a code below, and a database action that throws MUST become a model diagnostic rather than a panic. [just oracle]
- class-055: The diagnostic registry MUST contain exactly the following rows in this order. [just gen-check]

| Code | Severity | Raised by | Trigger | Span | Message |
|---|---|---|---|---|---|
| `class/unexpected-token` | error | parser | token fits no current rule, including invalid relation syntax or an unquoted namespace string | offending token | `unexpected TOKEN, expected one of: LIST` |
| `class/unknown-statement` | error | parser | first token starts no statement | first token through next boundary | `unknown statement TOKEN` |
| `class/unterminated` | error | parser | EOF inside a delimiter or block | opening delimiter through EOF | `unterminated TOKEN` |
| `class/nested-member-block` | error | parser | OPEN_IN_STRUCT inside class body | opening brace | `class member cannot contain a block` |
| `class/annotation-target-unknown` | error | model | standalone annotation targets an absent class | target name | `annotation references unknown class ID` |

- class-056: LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; TOKEN MUST be the source token text. [just parity]
- class-057: Named diagnostics MUST take precedence over the generic unterminated diagnostic for the same failure. [just go-check]
- class-058: Syntax diagnostics MUST NOT reject duplicate declarations, duplicate relations, unattached notes, or unknown style targets that upstream accepts; lint owns those checks. [just oracle]

## Upstream readings

| Reading | Authority fact | This file |
|---|---|---|
| Header detector | matches a prefix | keyword boundary follows shared detection, deliberate `keyword-boundary` divergence |
| Unused modes | struct and href are declared but never entered | retain unreachable mode names, no transitions |
| Unreachable productions | emptyBody, commentToken, textToken, textNoTagsToken are not reachable from start | no AST or acceptance extension |
| Undefined lexer tokens | EDGE_STATE, OPEN_IN_STRUCT, EOF_IN_STRUCT have no successful grammar alternative | reject with generic code or named block code |
| Dead grammar terminals | SEPARATOR and UNIT have no returning lexer rule | omitted from reachable EBNF |
| NUM precedence | `\w+` occurs before digits | ASCII numbers normally return ALPHA |
| Quoted identifiers | only backticks are classLiteralName; double quotes are labels or multiplicities | reject `class "Foo"` and `namespace "Foo"` |
| Alias and title prose | no alias or title production exists | bare words concatenate; do not invent semantic alias/title support |
| Label colon | LABEL excludes another colon | `Repo : get(): Result<string,int>` rejects at the second colon |
| HTML entities outside members | ampersand is not a name token | reject `&lt;&lt;interface&gt;&gt; A`; do not decode before lexing |
| Namespaces | classStatements excludes relations, empty namespace, standalone members | reject these forms, even when a renderer might draw them |
| Annotation action | addAnnotation dereferences an existing class | report unknown target, not an implicit declaration |
| Direction regex | greedy `.*direction` can consume a preceding prefix and line suffix | reproduce the INITIAL rule order; no TD direction |
| HTML and DOM | database sanitizes text and creates DOM ids and event handlers | retain semantic text, apply static escaping and URL/callback rules at shared stages; no DOM in core |
| Numeric CSS targets | database prefixes ids starting with a digit with classId- | reproduce lookup for CSS assignment and links; do not rename declared ids |

- class-059: No unreachable authority helper MUST expand the accepted language. [just oracle]
- class-060: The Go and Rust AST and resolved relations MUST agree in declaration order under both metric profiles. [just parity]
