# Event modeling grammar

This file fixes syntax and model resolution for `eventmodeling`.

## Scope

- eventmodeling-01: The authority MUST be `.references/mermaid/packages/parser/src/language/eventmodeling/event-modeling.langium:9-70`; resolution MUST follow `.references/mermaid/packages/mermaid/src/diagrams/eventmodeling/db.ts:87-151,189-396,448-538,541-642` and record fields in `types.ts:67-101`. [just oracle]
- eventmodeling-02: The implementation MUST accept every statement below; layout coordinates MUST follow `spec/layout/lanes.md`, not the upstream DOM measurements. [just parity]

## Header forms

- eventmodeling-03: The header MUST be the case-sensitive keyword `eventmodeling`, with the boundary and preprocessing rules of `spec/detection.md`. [just oracle]

## Lexer modes

- eventmodeling-04: The lexer MUST use one mode, `INITIAL`; it MUST retain byte spans over the original source and MUST NOT add jison start conditions to this Langium grammar. [just parity]

### Lexical rules in first-match order

- eventmodeling-05: The lexer MUST recognise reserved literals before identifiers at equal matches; the literal inventory in grammar occurrence order is `eventmodeling`, `rmo`, `readmodel`, `ui`, `cmd`, `command`, `evt`, `event`, `pcr`, `processor`, `json`, `jsobj`, `figma`, `salt`, `uri`, `md`, `html`, `text`, backtick, `.`, `tf`, `timeframe`, `->>`, `[[`, `]]`, `rf`, `resetframe`, `entity`, `data`, `note`, `gwt`, `given`, `when`, `then`. A longer identifier MUST remain an identifier rather than a keyword prefix. [just oracle]
- eventmodeling-06: Terminal rules MUST keep the following authority order; `EM_EID` and `EM_FI` are parser wrappers, not extra lexer rules. A hidden token MUST consume input without entering the AST. [just parity]

| Order (authority line) | Token | Match or action |
|---|---|---|
|54|EM_ID|ASCII `_` or letter, then zero or more ASCII word characters (`A-Z a-z 0-9 _`)|
|55|EM_FID|One to three decimal digits; retain leading zeros|
|57|EM_DATA_INLINE|One physical line enclosed in `{…}`, double quotes, or single quotes; each alternative is greedy through its last matching close on that line; no escape syntax|
|58|EM_DATA_BLOCK|`{`, optional SP/HT, LF or CRLF, optional arbitrary content ending in LF or CRLF, `}`, then LF/CRLF or a position not followed by a non-whitespace byte|
|60|EM_ACC_DESCR|Optional SP/HT, `accDescr`, then optional SP/HT and `:` with text to comment or line end, or whitespace and a brace body through its first `}`|
|61|EM_ACC_TITLE|Optional SP/HT, `accTitle`, optional SP/HT, `:`, text to `%%` or line end|
|62|EM_TITLE|Optional SP/HT, `title`, then optional horizontal-whitespace-prefixed text to `%%` or line end|
|64|EM_WS (hidden)|One or more whitespace characters|
|65|EM_YAML (hidden)|Opening `---` line, body, closing `---` line|
|66|EM_DIRECTIVE (hidden)|Optional SP/HT, `%%{` through first `}%%`, then line end or whitespace boundary|
|67|EM_SINGLE_LINE_COMMENT (hidden)|Optional SP/HT, `%%`, text to line end|
|69|EM_ML_COMMENT (hidden)|`/*` through first `*/`, including line ends|
|70|EM_SL_COMMENT (hidden)|`//` through line end|

- eventmodeling-07: Shared preprocessing MUST handle frontmatter, directives, Mermaid comments, and line endings before this grammar; block and inline payloads MUST remain opaque text, not JSON or executable HTML. [just parity]

## Grammar

- eventmodeling-08: The parser MUST implement this EBNF; spaces between tokens include hidden whitespace and comments, so a physical newline is not a required separator. [just oracle]

```ebnf
EventModel = "eventmodeling", { EM_ACC_DESCR | EM_ACC_TITLE | EM_TITLE
           | EmModelEntity | EmFrame | EmDataEntity | EmNoteEntity | EmGwt } ;
EmModelEntityType = "rmo" | "readmodel" | "ui" | "cmd" | "command"
                  | "evt" | "event" | "pcr" | "processor" ;
EmDataType = "json" | "jsobj" | "figma" | "salt" | "uri" | "md" | "html" | "text" ;
EmDataInline = [ "`", EmDataType, "`" ], EM_DATA_INLINE ;
EmDataBlock = [ "`", EmDataType, "`" ], EM_DATA_BLOCK ;
QualifiedName = EM_EID, { ".", EM_EID } ;
EmFrame = EmTimeFrame | EmResetFrame ;
EmTimeFrame = ("tf" | "timeframe"), EM_FI, EmModelEntityType, QualifiedName,
              { "->>", EM_FI }, [ "[[", EM_EID, "]]" ], [ EmDataInline ] ;
EmResetFrame = ("rf" | "resetframe"), EM_FI, EmModelEntityType, QualifiedName,
               { "->>", EM_FI }, [ "[[", EM_EID, "]]" ], [ EmDataInline ] ;
EmModelEntity = "entity", QualifiedName ;
EmDataEntity = "data", EM_EID, EmDataBlock ;
EmNoteEntity = "note", EM_FI, EmDataBlock ;
EmGwt = "gwt", EM_FI, "given", EmGwtStatement, { EmGwtStatement },
        [ "when", EmGwtStatement, { EmGwtStatement } ],
        "then", EmGwtStatement, { EmGwtStatement } ;
EmGwtStatement = EmModelEntityType, EM_EID ;
EM_EID = EM_ID ;
EM_FI = EM_FID ;
```

## Statement boundary

- eventmodeling-09: Recovery MUST skip to a physical line end outside a payload or block comment, or to a recognised top-level statement opener outside those tokens; it MUST NOT consume that opener. A semicolon MUST NOT become a statement separator. [just go-check]
- eventmodeling-10: A statement with a known opener and an invalid continuation MUST raise `eventmodeling/unexpected-token`; an unrecognised top-level statement MUST raise `eventmodeling/unknown-statement` and MUST NOT create a frame. [just oracle]

## Abstract syntax tree

- eventmodeling-11: AST nodes MUST use authority production names in PascalCase and MUST span their first through last consumed token, excluding trailing hidden text; an absent optional field MUST have no fabricated span. [just parity]

| Node | Fields |
|---|---|
|EventModel|accDescr, accTitle, title; ordered modelEntities, frames, dataEntities, noteEntities, gwtEntities|
|EmTimeFrame, EmResetFrame|name (EM_FI text), modelEntityType, entityIdentifier (QualifiedName text), ordered sourceFrames reference texts, optional dataReference, dataType, dataInlineValue|
|EmModelEntity|name (QualifiedName)|
|EmDataEntity|name, optional dataType, dataBlockValue|
|EmNoteEntity|sourceFrame reference text, optional dataType, dataBlockValue|
|EmGwt|sourceFrame reference text; ordered givenStatements, whenStatements, thenStatements|
|EmGwtStatement|modelEntityType, entityIdentifier reference text|

- eventmodeling-12: EmFrame MUST be a union of EmTimeFrame and EmResetFrame; EmDataInline and EmDataBlock MUST contribute fields to their owning node rather than independent AST nodes. QualifiedName, EmModelEntityType, EmDataType, EM_EID, and EM_FI MUST be scalar productions. Reference and identifier spans MUST cover only their text; payload spans MUST include delimiters. [just parity]

## Semantic resolution

- eventmodeling-13: Resolution MUST retain each of the nine entity-type spellings; its semantic categories MUST be read model (`rmo`, `readmodel`), UI (`ui`), command (`cmd`, `command`), event (`evt`, `event`), and processor (`pcr`, `processor`). Data type tags MUST retain all eight spellings without validating payload contents. [just parity]
- eventmodeling-14: Frames MUST become boxes in frame declaration order; frame names MUST remain strings, so `01` and `1` are different names. A reused exact frame name across either frame kind MUST raise `eventmodeling/duplicate-frame-id` at the later name, with the earlier name as a related span. [just oracle]
- eventmodeling-15: A QualifiedName with exactly two components MUST use its first component as namespace and its second as display name; a one-component name or a name with three or more components MUST have no namespace and MUST display its full name. Frames MUST NOT require an `entity` declaration. [just oracle]
- eventmodeling-16: Lane assignment MUST process frames in declaration order and use the table below; lane indices MUST sort numerically for model output. A new namespace lane MUST take one plus the maximum occupied index strictly inside its category interval, or one plus the interval's lower bound when none exists. [just parity]

| Frame category | Unqualified lane index and label | Namespace interval | New namespace label |
|---|---|---|---|
|UI or processor|0, `UI/Automation`|(0,100)|`UI/A: ` + namespace|
|Command or read model|100, `Command/Read Model`|(100,200)|`C/RM: ` + namespace|
|Event|200, `Events`|(200,300)|`Stream: ` + namespace|

- eventmodeling-17: The implementation MUST preserve the database's namespace-storage behaviour: its namespace lookup searches existing lane `namespace` fields, but newly created lanes store index and label only, not namespace. Thus repeating a qualified namespace MUST allocate another lane, even in the same category; equal namespace text MUST NOT merge those lanes. If allocation reaches an already occupied boundary index, the stored lane at that index MUST be reused without replacing its label. [just oracle]
- eventmodeling-18: A frame with explicit `->>` references MUST suppress inferred relations, even when no reference resolves. Resolution MUST filter the complete frame list by referenced name in frame declaration order, not reference order; repeated references to one name MUST produce at most one candidate. Each resolved candidate MUST create a relation only if its box already exists, including the current frame's box. Forward references MUST therefore produce no relation. [just parity]
- eventmodeling-19: A time frame without explicit sources MUST infer a relation from the nearest earlier box with a different lane index; earlier boxes in the same lane MUST be skipped. The first frame MUST have no inferred relation. A reset frame without explicit sources MUST have no inferred relation. A reset frame with explicit sources MUST use only those sources. [just parity]
- eventmodeling-20: Every stored relation MUST have sourceBox and targetBox references, source and target coordinate records, and visual properties; sourceBox MUST be the referenced or inferred earlier box and targetBox MUST be the current frame box. There MUST be no separate relation type, label, multiplicity, or GWT edge. The arrow text points from the current declaration to a source identifier syntactically, but the stored relation runs from that source box to the current box. [just parity]
- eventmodeling-21: `entity`, `data`, `note`, and `gwt` declarations MUST remain in their separate AST lists. The database MUST use only frames to create boxes and relations; notes and GWT statements MUST NOT create displayed nodes or relations. A data reference MUST select the first data declaration with that exact name. An unresolved data reference MUST leave inline data unchanged, or contribute no data when inline data is absent. [just oracle]
- eventmodeling-22: Text resolution MUST retain the database's extraction order: inline data first, referenced data second when found. For inline data it MUST apply JavaScript `substring(indexOf('{') + 1)`, then `substring(0, lastIndexOf('}') - 1)` to that result. For referenced data it MUST apply `substring(indexOf('{\n') + 2)`, then the same second operation, and append a line break. JavaScript substring MUST clamp negative bounds to zero and exchange reversed bounds. The model MUST store the resulting text, not upstream HTML wrappers. [just parity]
- eventmodeling-23: Accessibility and title tokens MUST populate common metadata through the shared metadata rules; later assignments MUST replace earlier values. Geometry, text wrapping, theme paint, and static escaping MUST follow their shared specifications. [just parity]
- eventmodeling-24: Acceptance MUST follow `packages/parser/src/parse.ts:133-149` and `diagrams/eventmodeling/parser.ts:8-14`: lexer/parser errors and duplicate frame IDs reject input. The editor validator in `language/eventmodeling/event-modeling-validator.ts:23-65` MUST NOT add rejection rules to this entry point; it is not run by `parse`. Missing references and disallowed source-type pairs MUST NOT become error diagnostics here. [just oracle]

## Diagnostics

- eventmodeling-25: The implementation MUST emit exactly the kind diagnostics below; it MUST use the common nesting diagnostic from `spec/preprocessing.md` for shared depth limits rather than invent a kind code. [just gen-check]

| Code | Severity | Message | Span |
|---|---|---|---|
|eventmodeling/unexpected-token|error|`unexpected TOKEN, expected one of: LIST`|Offending token; zero-width at EOF|
|eventmodeling/unknown-statement|error|`unknown statement TOKEN`|First token through recovery boundary, excluding boundary|
|eventmodeling/unterminated|error|`unterminated TOKEN`|Opening payload quote, brace, metadata brace, backtick, reference bracket, or block-comment delimiter through EOF|
|eventmodeling/duplicate-frame-id|error|`duplicate event modeling frame ID ID`|Later frame name; related earlier name with message `first declared here`|

- eventmodeling-26: LIST MUST contain accepted token-kind names sorted bytewise and joined with `, `; TOKEN MUST be source text. Diagnostic help MUST be empty, and these diagnostics MUST have no fixes. [just parity]
- eventmodeling-27: EOF inside an open delimiter MUST produce only `eventmodeling/unterminated` for that opening, not an additional unexpected-token for the same failure. [just parity]

## Upstream readings

| Reading | Consequence |
|---|---|
|event-modeling.langium:27-49|Both frame kinds accept the same payload and source-reference fields; GWT has required given and then lists|
|db.ts:139-150|Only frame IDs are checked for duplicates|
|db.ts:189-287,448-465|Exactly two name components create a namespace; lane construction omits namespace storage|
|db.ts:96-129,541-642|Explicit sources are filtered in frame order; missing or forward boxes are ignored; resets stop inference|
|parse.ts:133-149; event-modeling-validator.ts:23-65|The parser entry does not run linking or editor validation|
|config.schema.yaml:476-525,2818-2833|Config consists of inherited base keys plus padding and rowHeight|

- eventmodeling-28: Config classification MUST use `spec/data/config-keys/eventmodeling.json`; `padding` and `rowHeight` MUST be accepted but ignored because the project fixes family geometry in `spec/layout/lanes.md`. [just gen-check]
