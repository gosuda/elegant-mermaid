# Preprocessing

This file fixes line endings, frontmatter, directives, comments, entity decoding, and the config-value grammar.

## Reader inputs and interface

- preprocessing-001: The config-value reader MUST parse three inputs: the frontmatter body, the body of a directive, and the `Config` text of the layout options. [just go-check]
- preprocessing-002: The reader MUST be recursive-descent, MUST NOT backtrack, and MUST fail at the first byte that the current rule does not accept. [just go-check]
- preprocessing-003: Go MUST expose `syntax.ParseConfigYAML(src, start, end)` and `syntax.ParseConfigJSON(src, start, end)`. [just go-check]
- preprocessing-004: Rust MUST expose `parse_config_yaml` and `parse_config_json` in the `syntax` module, file `crates/elegant-mermaid/src/syntax/config_value.rs`, with the same arguments. [just rust-check]
- preprocessing-005: Each call MUST return one `ConfigValue` and an ordered list of diagnostics. [just go-check]
- preprocessing-006: `start` and `end` MUST be byte offsets into `src`, and every span MUST be a byte offset into `src`. [just go-check]

## Preprocessing order

- preprocessing-007: Preprocessing order MUST be fixed: line ends, frontmatter, directives, comments. [just go-check]
- preprocessing-008: The reader MUST read directives only after frontmatter is removed. [just go-check]
- preprocessing-009: CRLF, LF, and a lone CR MUST each end a line. [just go-check]
- preprocessing-010: The CR of a CRLF MUST NOT be part of the line text. [just go-check]
- preprocessing-011: The reader MUST scan the original bytes. [just go-check]
- preprocessing-012: A TAB MUST NOT end a line. [just go-check]
- preprocessing-013: A line whose text after optional spaces or tabs starts with `%%`, and that does not start a directive, MUST be an ordinary comment. [just go-check]
- preprocessing-177: A comment line MUST take with it the blank lines directly before it, back to the previous line that holds text, so its removed span MUST start at the first of those blank lines. A blank line holds only SP, HT, or bytes of a removed directive or frontmatter. Blank lines with no comment line after them MUST stay in the text. [just go-check: TestCommentLineAbsorbsBlankLinesBeforeIt]
- preprocessing-178: Rust MUST return the same removed spans as Go for a comment line and the blank lines before it. [just rust-check: comment_line_absorbs_blank_lines_before_it]

## Nesting depth

- preprocessing-014: Each open block mapping, flow sequence, flow mapping, JSON object, and JSON array MUST count as one nesting level, and the outermost MUST be level 1. [just go-check]
- preprocessing-015: Opening level 65 MUST raise `limit/nesting-depth` (error) at the opening token, and the reader MUST stop. [just go-check]
- preprocessing-016: The opening token MUST be `[`, `{`, or the first byte of a nested block key. [just go-check]
- preprocessing-017: `Config` text that is not valid UTF-8 MUST NOT parse. [just go-check]

## Config values

- preprocessing-018: `ConfigValue` MUST be one of `Null`, `Bool`, `Integer`, `Decimal`, `String`, `Sequence`, or `Mapping`. [just go-check]
- preprocessing-019: `Integer` and `Decimal` MUST keep the source text, sign included. [just go-check]
- preprocessing-020: A `Mapping` MUST keep its entries in source order, and each entry MUST have a key string, the key span, and a value. [just go-check]
- preprocessing-021: Keys MUST be `String`, and the reader MUST NOT resolve them. [just go-check]

## Frontmatter

- preprocessing-022: Line 1 MUST be `---` with optional SP (U+0020) or HT (U+0009) bytes before and after it, the line MUST start at byte 0, and it MUST end with a line end. [just go-check]
- preprocessing-023: The closing line MUST be the first later line with the identical SP/HT byte prefix as the opening line, then `---`, optional trailing SP or HT bytes, and a line end; equal indentation columns with different bytes MUST NOT match. This prefix rule matches the capture and backreference in upstream `frontMatterRegex` (`packages/mermaid/src/diagram-api/regexes.ts`). [just go-check]
- preprocessing-024: Without a closing line there MUST be no frontmatter, and line 1 MUST be ordinary text. [just go-check]
- preprocessing-025: The body MUST be the lines between the two fence lines. [just go-check]
- preprocessing-026: Text after the closing line MUST stay diagram text, and blank lines there MUST stay in it. [just go-check]
- preprocessing-027: An empty body MUST be valid and MUST give no config. [just go-check]
- preprocessing-028: A frontmatter root that is a scalar or a flow sequence MUST give no config and no diagnostic. [just go-check]
- preprocessing-029: The frontmatter key `config` MUST hold a `Mapping`, and any other value MUST raise `config/malformed` at the value's token. [just go-check]

## YAML grammar

- preprocessing-030: The frontmatter body and the `Config` text MUST parse by this grammar. [just go-check]

  ```
  document     = { blank | comment-line } , [ block-node ] , { blank | comment-line } ;
  block-node   = block-map | block-seq | flow | scalar ;
  block-map    = entry , { entry } ;                 entries of one map start at column n
  entry        = key , ':' , [ SP , value ] , [ SP , comment ] , EOL , [ nested-node ] ;
  block-seq    = sequence-item , { sequence-item } ; items of one sequence share a dash column
  sequence-item = '-' , ( SP | EOL ) , [ value | compact-map | compact-seq ] ;
  nested-node  = block-node | block-body ;           starts deeper than its owning map or dash
  key          = plain-key | dquoted | squoted ;
  value        = flow | block-header | scalar ;
  flow         = flow-seq | flow-map ;
  flow-seq     = '[' , [ item , { ',' , item } ] , ']' ;
  flow-map     = '{' , [ pair , { ',' , pair } ] , '}' ;
  pair         = scalar , ':' , item ;
  item         = flow | scalar ;
  scalar       = dquoted | squoted | plain ;
  block-header = ( '|' | '>' ) , [ '-' | '+' ] ;
  blank        = { SP } , EOL ;
  comment-line = { SP } , comment , EOL ;
  comment      = '#' , text to EOL ;                 only after SP or HT, or at the start of a token
  ```

- preprocessing-031: Blank lines MUST hold only SP bytes, and a comment line MUST have `#` as its first byte that is not SP. [just go-check]
- preprocessing-032: The reader MUST NOT allow comments inside a flow collection. [just go-check]
- preprocessing-033: Indentation MUST be SP only. [just go-check]
- preprocessing-034: A HT before the first non-SP byte of a line MUST raise `config/malformed`. [just go-check]
- preprocessing-035: The first entry of a block map MUST set its column `n`. [just go-check]
- preprocessing-036: A line at a column smaller than `n` MUST end the map. [just go-check]
- preprocessing-037: The root column MAY be greater than 0. [just go-check]
- preprocessing-038: With no value on the key line, a deeper node MUST supply the value. It MAY be a mapping, sequence, flow value, or scalar. [just go-check]
- preprocessing-039: When no such nested node follows, the value MUST be `Null`. [just go-check]
- preprocessing-040: A `-` followed by separation or a line end MUST open a block-sequence item. Items MUST preserve declaration order and MAY be null, scalars, flow values, nested sequences, or compact mappings. Collection openings MUST count toward the existing depth limit. [just go-check]
- preprocessing-041: A `?` followed by SP, HT, or a line end MUST raise `config/malformed`. [just go-check]
- preprocessing-042: A line that starts at column 0 with `---` or `...`, followed by SP, HT, a line end, or the end of the reader's range, MUST raise `config/malformed`. [just go-check]

## Plain scalars

- preprocessing-043: In block context the first byte of a plain scalar MUST NOT be one of `[ ] { } , # & * ! | > '`, a double quote, `%`, `@`, or a backtick. [just go-check]
- preprocessing-044: A `-`, `?`, or `:` first byte MUST be allowed only when the next byte is not SP, HT, or a line end. [just go-check]
- preprocessing-045: A plain YAML value MAY continue on deeper lines until a comment or a mapping or sequence boundary ends it. Implicit keys MUST remain on one line. [just go-check]
- preprocessing-046: It MUST stop before SP or HT followed by `#`. [just go-check]
- preprocessing-047: Trailing SP and HT MUST be removed. [just go-check]
- preprocessing-048: In a key a plain scalar MUST stop before `:` followed by SP, HT, or a line end. [just go-check]
- preprocessing-049: Scalar continuation MUST follow YAML 1.2.2 line folding: one ordinary break becomes one space; each empty line between nonempty lines contributes one LF. Continuation indentation and trailing separation MUST NOT enter the value. Scalar resolution MUST run once on the complete folded text. [just go-check]
- preprocessing-050: In flow context the first-byte rule MUST be the same. [just go-check]
- preprocessing-051: In flow context a plain scalar MUST stop before `,`, `[`, `]`, `{`, `}`, and `:`. [just go-check]
- preprocessing-052: A YAML flow-context value MAY contain folded line breaks under preprocessing-049. Flow keys MUST remain on one line. JSON strings and numbers MUST retain their separate strict grammar. [just go-check]
- preprocessing-053: A TAB inside a plain scalar MUST be text. [just go-check]

## Quoted scalars

- preprocessing-054: In a single-quoted scalar `''` MUST stand for one `'`, and no other escape MUST exist. [just go-check]
- preprocessing-055: A single-quoted YAML value MAY span lines and MUST fold them under preprocessing-049. A single-quoted implicit key MUST remain on one line. [just go-check]
- preprocessing-056: A double-quoted scalar MUST use the escape table under Escapes. [just go-check]
- preprocessing-057: A double-quoted YAML value MAY span lines and MUST fold ordinary breaks under preprocessing-049. A backslash immediately before a line ending MUST suppress that break and continuation indentation. A double-quoted implicit key MUST remain on one line. [just go-check]
- preprocessing-058: Raw bytes U+0000 to U+001F MUST be malformed inside a quoted scalar, TAB included, except physical YAML value line endings handled by preprocessing-055 and preprocessing-057. JSON MUST NOT gain this exception. [just go-check]
- preprocessing-059: `&` or `*` at the start of a node MUST raise `config/unsupported-anchor`. [just go-check]
- preprocessing-060: `!` at the start of a node MUST raise `config/unsupported-tag`. [just go-check]
- preprocessing-061: Inside plain text, `&`, `*`, and `!` MUST be ordinary characters. [just go-check]

## Plain scalar resolution

- preprocessing-062: Plain scalar resolution MUST apply the first matching rule of this list. [just go-check]

  1. An empty value, `null`, `Null`, `NULL`, or `~` gives `Null`.
  2. `true`, `True`, or `TRUE` gives `Bool` true. `false`, `False`, or `FALSE` gives `Bool` false.
  3. `[-+]?[0-9]+` gives `Integer`.
  4. `[-+]?[0-9]+\.[0-9]+` gives `Decimal`.
  5. Anything else gives `String` with the plain text.

- preprocessing-063: A quoted scalar MUST resolve to `String`. [just go-check]
- preprocessing-064: Exponent forms, `.inf`, `.nan`, and hexadecimal forms MUST resolve to `String`. [just go-check]

## Escapes

- preprocessing-065: Double-quoted scalars and JSON strings MUST use this escape table. [just go-check]

  |Escape|Code point|
  |---|---|
  |`\"`|U+0022|
  |`\\`|U+005C|
  |`\/`|U+002F|
  |`\b`|U+0008|
  |`\f`|U+000C|
  |`\n`|U+000A|
  |`\r`|U+000D|
  |`\t`|U+0009|
  |`\u` plus four hex digits, either case|the code point|

- preprocessing-066: Any other backslash form MUST be malformed. [just go-check]
- preprocessing-067: In YAML every surrogate escape (U+D800 to U+DFFF) MUST be malformed. [just go-check]
- preprocessing-068: In JSON a high surrogate escape immediately followed by a low surrogate escape MUST form one code point. [just go-check]
- preprocessing-069: In JSON any other surrogate escape MUST be malformed. [just go-check]

## Block scalars

- preprocessing-070: The block scalar header MUST be `|` or `>`, then `-` (strip), `+` (keep), or nothing (clip), then optional SP and a comment, then a line end. [just go-check]
- preprocessing-071: A digit after the header MUST raise `config/malformed`. [just go-check]
- preprocessing-072: A block-scalar header MUST be a mapping value or sequence item, including a deeper value after an omitted key-line value. A standalone root block-scalar header MUST remain malformed. [just go-check]
- preprocessing-073: With `n` the key's column, the first non-blank line after the header MUST set the content indentation `m` to its count of leading SP bytes. [just go-check]
- preprocessing-074: If that line's column is `n` or less, the scalar MUST be empty, and the line MUST belong to the parent. [just go-check]
- preprocessing-075: The scalar MUST continue over blank lines and over lines with at least `m` leading SP bytes. [just go-check]
- preprocessing-076: The scalar MUST end at the first non-blank line with fewer than `m` leading SP bytes, or at the end of the reader's range. [just go-check]
- preprocessing-077: The TAB rule MUST apply to that line. [just go-check]
- preprocessing-078: A content line MUST be its bytes after the first `m` SP bytes, and an empty line MUST have no bytes after them. [just go-check]
- preprocessing-079: A line with more than `m` leading SP bytes MUST keep the extra SP bytes as content. [just go-check]
- preprocessing-080: Literal: between two non-empty lines with `e` empty lines between them, the output MUST contain `e + 1` LF. [just go-check]
- preprocessing-081: Folded: between two non-empty lines with `e` empty lines between them, if either line starts with SP or HT, the output MUST contain `e + 1` LF. [just go-check]
- preprocessing-082: Folded: otherwise, if `e` is 0, the output MUST contain one SP. [just go-check]
- preprocessing-083: Folded: otherwise the output MUST contain `e` LF. [just go-check]
- preprocessing-084: Each empty line before the first non-empty line MUST give one LF. [just go-check]
- preprocessing-085: With `t` the count of empty lines after the last non-empty line, and `V` the text from the first to the last non-empty line, joined as above with no final LF, the output MUST be the leading LFs, then `V`, then the tail. [just go-check]
- preprocessing-086: The clip tail MUST add one LF. [just go-check]
- preprocessing-087: The strip tail MUST add nothing. [just go-check]
- preprocessing-088: The keep tail MUST add one LF and `t` LF. [just go-check]
- preprocessing-089: With no non-empty line, the output MUST be empty for clip and strip, and one LF per empty line for keep. [just go-check]

## Flow collections

- preprocessing-090: `[]` and `{}` MUST be valid. [just go-check]
- preprocessing-091: A missing item, a trailing comma, a missing `:`, or a missing closing bracket MUST be malformed. [just go-check]
- preprocessing-092: SP and HT MUST separate tokens, and a line end inside a flow collection MUST separate tokens. [just go-check]
- preprocessing-093: The next line MUST have more leading SP bytes than `n`, where `n` is the column of the key that owns the collection. [just go-check]

## Duplicate keys

- preprocessing-094: A duplicate key MUST NOT stop the reader, and the mapping MUST keep the first key's position and the later entry's value. [just go-check]
- preprocessing-095: `config/malformed` (duplicate key) MUST be raised once per duplicate, at the later key's span. [just go-check]

## JSON bodies

- preprocessing-096: A directive body MUST parse by this JSON grammar. [just go-check]

  ```
  json      = WS , object , WS ;
  object    = '{' , WS , [ member , { WS , ',' , WS , member } ] , WS , '}' ;
  member    = string , WS , ':' , WS , value ;
  value     = object | array | string | number | 'true' | 'false' | 'null' ;
  array     = '[' , WS , [ value , { WS , ',' , WS , value } ] , WS , ']' ;
  WS        = { SP | HT | CR | LF } ;
  ```

- preprocessing-097: Literals MUST be lowercase. [just go-check]
- preprocessing-098: A number with no fraction and no exponent MUST be `Integer`, any other number MUST be `Decimal`, and both MUST keep their text. [just go-check]
- preprocessing-099: A JSON array MUST be a `Sequence`, and a JSON object MUST be a `Mapping`. [just go-check]
- preprocessing-100: JSON strings MUST use the escape table under Escapes. [just go-check]
- preprocessing-101: Before the JSON grammar runs, every `'` byte of the directive body MUST be read as `"`. [just go-check]
- preprocessing-102: With the quote rewrite, `%%{init: {'theme': 'dark'}}%%` MUST parse, and a `'` inside a double-quoted string MUST end that string. [just go-check]
- preprocessing-103: Duplicate keys in a JSON body MUST follow the duplicate-key rule. [just go-check]

## Directives

- preprocessing-104: A directive MUST match this grammar. [just go-check]

  ```
  directive = '%%{' , WS , name , WS , [ ':' , body ] , '}%%' ;
  name      = { ASCII letter | ASCII digit | '_' } ;      may be empty
  body      = all bytes after ':' up to the first '}%%' ;
  ```

- preprocessing-105: Every `%%{` in the text after frontmatter removal MUST start a directive, including a `%%{` on a comment line. [just go-check]
- preprocessing-106: A name other than `init`, `initialize`, or `wrap` MUST be unknown, including an empty name. [just go-check]
- preprocessing-107: A name that contains `init` or `initialize` MUST be unknown; the two exact names MUST match. [just go-check]
- preprocessing-108: An unknown directive MUST be removed from `%%{` through the first `}%%` after it, or through the end of the source when there is none; its body MUST NOT be read, and it MUST raise no diagnostic. [just go-check]
- preprocessing-109: A known directive MUST be removed from `%%{` through its closing `}%%`, whether it is valid or not. [just go-check]
- preprocessing-110: For `init` or `initialize`, the next byte after the name and WS MUST be `:` or the start of `}%%`; otherwise the directive MUST be malformed. [just go-check]
- preprocessing-111: With `:`, the body MUST be one JSON object, or only WS, which has no effect; any other body MUST be malformed. [just go-check]
- preprocessing-112: Without `:`, an `init` or `initialize` directive MUST have no effect. [just go-check]
- preprocessing-113: `wrap` without `:` MUST set the wrap flag. [just go-check]
- preprocessing-114: `wrap` with `:` MUST raise `config/malformed`. [just go-check]
- preprocessing-115: A known directive with no closing `}%%` MUST raise `config/malformed`, and MUST be removed through the end of the source. [just go-check]
- preprocessing-116: Several `init` bodies MUST merge in source order, to depth 2: a top-level key of a later body replaces the same key of an earlier body; when both values are mappings their keys merge one level; a deeper value is replaced whole. [just go-check]
- preprocessing-117: A malformed known directive MUST raise its diagnostic and MUST be removed; other directives MUST apply. [just go-check]
- preprocessing-118: An `init` body key `config` MUST stay an ordinary key of the merged mapping. [just go-check]

## Entities

- preprocessing-119: The model stage MUST decode entities when it resolves a label. [just go-check]
- preprocessing-120: For each match of `#[A-Za-z0-9_]+;` in label text, when the inner text matches `\+?[0-9]+` and its decimal value is a Unicode scalar value other than 0, the match MUST become that scalar. [just go-check]
- preprocessing-121: Otherwise, when `&<inner>;` is a key of `spec/data/entities.json`, the match MUST become that entry's code points. [just go-check]
- preprocessing-122: Otherwise the match MUST stay literal text. [just go-check]
- preprocessing-123: Decoding MUST NOT change the source text or any span. [just go-check]
- preprocessing-124: Decoding MUST apply to label text only, and MUST NOT apply to `style`, `classDef`, or `linkStyle` values, where `#` starts a colour. [just go-check]
- preprocessing-125: `spec/data/entities.json` MUST hold the WHATWG named character references, and the reader MUST use keys that end in `;` only. [just gen-check]

## Config diagnostics

- preprocessing-126: Every code of the table below MUST have severity error. [just gen-check]
- preprocessing-127: The span of a config diagnostic MUST follow the token rule. [just go-check]

  Let `p` be the byte where the reader fails. If the byte at `p` is SP, HT, CR, or LF, the span is that byte, or both bytes of a CRLF. If `p` is the end of the reader's range, the span is zero-width there. Otherwise the span is the run of bytes from `p` that are not SP, HT, CR, or LF.

- preprocessing-128: Each construct MUST raise its code, message, and span as this table states. [just go-check]

  |Construct|Code|Message|Span|
  |---|---|---|---|
  |Tab before the first non-SP byte of a line|`config/malformed`|`tab in indentation`|the TAB|
  |Complex key `?`|`config/malformed`|`complex keys are not supported`|the `?`|
  |Multi-document marker|`config/malformed`|`multi-document streams are not supported`|the three bytes|
  |Digit in a block scalar header|`config/malformed`|`block scalar indentation indicator is not supported`|the digit|
  |Invalid escape|`config/malformed`|`invalid escape`|the backslash and the next byte|
  |Surrogate escape (see Escapes)|`config/malformed`|`invalid unicode escape`|the escape's six bytes, or fewer if the range ends|
  |Duplicate key|`config/malformed`|`duplicate key`|the later key|
  |Frontmatter `config` not a mapping|`config/malformed`|`frontmatter config must be a mapping`|token rule at the value|
  |Known directive with a malformed form, or with no closing `}%%`|`config/malformed`|`malformed directive`|`%%{`|
  |`wrap` with `:`|`config/malformed`|`wrap takes no body`|`%%{`|
  |Directive body that is not a JSON object|`config/malformed`|`directive body must be a JSON object`|token rule at the first non-WS byte|
  |Any other syntax failure|`config/malformed`|`malformed config value`|token rule|
  |Anchor `&` or alias `*`|`config/unsupported-anchor`|`anchors and aliases are not supported`|the `&` or `*` and following ASCII letters, digits, `_`, `-`|
  |Tag `!`|`config/unsupported-tag`|`tags are not supported`|the `!` and following bytes up to SP, HT, CR, LF, or any of `,[]{}`|
  |Nesting level 65|`limit/nesting-depth`|`nesting depth exceeds 64`|the opening token|

- preprocessing-129: Help text MUST be empty for every config diagnostic. [just go-check]
- preprocessing-130: The registry rows of the config codes MUST be rows of `spec/data/diagnostics/common.json`, and `spec/diagnostics.md` fixes their rendering. [just gen-check]

## Stop errors and results

- preprocessing-131: A stop error MUST end the reading of its block, and the block MUST give no value: the frontmatter contributes no config, one directive contributes nothing, or the `Config` text contributes nothing. [just go-check]
- preprocessing-132: Other directives MUST apply. [just go-check]
- preprocessing-133: The diagram body MUST parse despite config diagnostics, and `Layout` MUST return the invalid-document error (`ErrInvalidDocument` in Go, `RenderError::InvalidDocument` in Rust), because every config diagnostic has error severity. [just go-check]
- preprocessing-134: `LayoutOptions.Config` MUST return `ErrBadConfig` in Go, or `RenderError::InvalidConfig` in Rust, when its text fails to parse, or when its root is a scalar or a sequence. [just go-check]
- preprocessing-135: Empty `Config` text MUST be an empty mapping. [just go-check]
- preprocessing-136: Duplicate keys MUST NOT be stop errors; the block keeps its value, and the diagnostic makes the document invalid. [just go-check]

## Thousandths conversion

- preprocessing-137: A consumer that needs a number in thousandths MUST apply this rule, and all arithmetic MUST be integer. [just go-check]

  Let `s` be the sign. Let `D` be the mantissa digits, integer digits then fraction digits, with leading zeros removed. `D` is `0` when no digit is non-zero. Let `k` be the fraction digit count. Let `E` be the exponent, `0` when absent, clamped to the range -999999999 to 999999999. Let `P = E - k + 3`.
  1. If `D` is `0`, `T = 0`.
  2. Otherwise, if `P > 10`, the value overflows.
  3. Otherwise, if `P >= 0`, `T` is `D` followed by `P` zero digits.
  4. Otherwise let `r = -P`. If `len(D) < r`, `T = 0`. Otherwise `T` is the first `len(D) - r` digits of `D`, or `0` when there are none. If the digit `D[len(D) - r]` (zero-based) is 5 to 9, add 1 to `T` with decimal carry.
  5. If `T` is greater than 2147483647, the value overflows. Otherwise the thousandths are `s * T`, and zero has no sign.

- preprocessing-138: An overflow in a config value MUST raise `ErrBadConfig` in Go, or `RenderError::InvalidConfig` in Rust. [just go-check]
- preprocessing-139: The worked examples MUST hold: `0.75` gives 750; `0.0005` gives 1; `1` gives 1000. [just go-check]

## Settled readings

The requirements below fix the cases that the grammar above leaves open. Where one of them and an earlier requirement both apply, the requirement below decides.

- preprocessing-140: The document root MUST be one of a block map, a flow collection, a quoted scalar, or a plain scalar. [just parity]
- preprocessing-141: A block scalar header (`|` or `>`) at the document root MUST raise `config/malformed` at the header byte, because the first byte rule for plain scalars rejects it and a header is valid only as the value of a key. [just parity]
- preprocessing-142: Leading SP before a root scalar MUST be indentation and MUST NOT be part of the scalar text. [just parity]
- preprocessing-143: The multi-document marker rule MUST apply at column 0 only; `---` or `...` at any other column MUST be read by the plain scalar rules. [just parity]
- preprocessing-144: A map colon MUST be a `:` followed by SP, HT, a line end, or the end of the reader's range, outside a quoted scalar and outside a flow collection. A block line MUST be a map entry exactly when it holds a map colon, and its key MUST be the text before the first map colon. [just parity]
- preprocessing-145: A plain key MUST obey the first byte rules for plain scalars, so the line `-x:` MUST be an entry with key `-x`, and a line whose first byte is a map colon MUST raise `config/malformed` at that byte. [just parity]
- preprocessing-146: A `-` or `?` at the end of the reader's range with no line end MUST be read as a plain scalar. [just parity]
- preprocessing-147: Every invalid escape, including `\u` with fewer than four hexadecimal digits, MUST have the span of the backslash and the next byte, clamped to the end of the reader's range. [just parity]
- preprocessing-148: An HT met while the reader scans the leading whitespace of a line MUST raise `config/malformed` at that HT, in the document, in a block map, in a block scalar, and in a flow continuation line. [just parity]
- preprocessing-149: After a value and after a map colon, the reader MUST skip SP and HT before a comment or a line end. [just parity]
- preprocessing-150: The continuation column of a flow collection with no owning key MUST be the start column of the collection. [just parity]
- preprocessing-151: A block scalar with no non-empty line MUST give the empty string under clip and strip, and one LF for each blank line under keep. [just parity]
- preprocessing-152: The duplicate key rule MUST apply to block maps, flow maps, and JSON objects. [just parity]
- preprocessing-153: A `%%` comment line MUST allow leading SP and HT, and a `#` comment line inside a config value MUST allow leading SP only. [just parity]
- preprocessing-154: In a flow collection the reader MUST report the first byte that the current rule rejects, and MUST NOT read to the end of a token before it reports. [just parity]
- preprocessing-155: A reader range that is empty, or that holds only blank lines and comment lines, MUST give an empty mapping and no diagnostic. [just parity]
- preprocessing-156: Inside a flow collection a `#` that is not the first byte of a plain scalar MUST be text of that scalar, with or without SP or HT before it, so `[a #b]` MUST hold the one string `a #b`. [just parity]
- preprocessing-157: A `|` or `>` that starts a line at the column of a block map MUST raise `config/malformed` at that byte, and MUST NOT be read as an empty block scalar. [just parity]
- preprocessing-158: A `config/malformed` diagnostic at a byte that is not SP, HT, CR, or LF MUST have the token rule span, which runs from that byte to the next SP, HT, CR, LF, or the end of the reader's range; it MUST NOT be a zero-width span at the end of the range. [just parity]
- preprocessing-159: When the next line of an open flow collection is not blank and does not start at a column greater than the continuation column, the reader MUST raise `config/malformed` at the first byte of that line that is not SP. [just parity]
- preprocessing-160: Inside a single- or double-quoted YAML value, continuation lines MUST allow any indentation column, including a column at or left of the owning key. Leading SP and HT on continuation lines and trailing SP and HT before an ordinary physical break MUST NOT enter the value. This rule overrides preprocessing-034, preprocessing-058, and preprocessing-148 for continuation indentation only. These cases match Mermaid 12.3.0's bundled js-yaml `load` with `JSON_SCHEMA`. [just go-check: TestConfigQuotedClosingLine]
- preprocessing-161: Inside a quoted YAML value, `#`, `{`, `}`, `[`, `]`, `,`, `:`, and `;` MUST be ordinary text. Between nonempty physical lines, one ordinary break MUST fold to one SP; with `e` empty intervening lines, the breaks MUST give `e` LF. A double-quoted backslash immediately before a physical break MUST suppress that break and continuation indentation; further empty lines MUST each give one LF. Escapes MUST otherwise follow preprocessing-065, and single quotes MUST use only the doubled-quote escape. Implicit keys and JSON strings MUST retain their one-line rule. [just go-check: TestYAMLMultilineValueFolding]
- preprocessing-162: Inside a quoted YAML value a column-zero `---` or `...` followed by SP, HT, a physical line end, or the reader's end MUST raise `config/malformed` with message `malformed config value` at that marker under the token-span rule. An unterminated quoted value without such a marker MUST fail at the reader's end with a zero-width span. [just go-check: TestConfigQuotedDocumentMarker]
- preprocessing-163: Continuation lines of a root plain scalar MUST start at or right of the root scalar's column. A line that is not blank, not a comment line, and starts left of that column MUST end the scalar, and the reader MUST then raise `config/malformed` at the first byte of that line that is not SP. [just go-check: TestConfigRootPlainScalarContinuesAtColumnZero]
    The column of the root scalar is its count of leading SP bytes on its line (preprocessing-142). Examples: the lines `a`, `b`, an empty line, and `c` give the string `a b` LF `c`; the lines `   a` and `b` raise `config/malformed` at `b`.
- preprocessing-164: A JSON number MUST fail at the first byte that the number grammar rejects: the byte after a leading `-`, the byte after the `.` of a fraction, and the byte after `e` or `E` and its optional sign, when that byte is not a digit. The `config/malformed` span MUST follow the token rule at that byte. [just go-check: TestConfigJSONNumberFailsAtTheFirstRejectedByte]
- preprocessing-165: Inside a directive, the WS before the name, between the name and `:`, and before the first body byte MUST be SP, HT, CR, or LF, as the WS of the JSON grammar is and as the upstream directive pattern reads `\s*`. [just go-check: TestDirectiveWhitespaceIncludesLineEnds]
- preprocessing-166: A block line that starts with `'` or `"` MUST be a map entry exactly when its quoted token closes on that line and only SP or HT, then a `:`, follow the closing quote. A `:` inside the quoted token MUST NOT make the line an entry. Any other line that starts with a quote MUST be read as a quoted value. [just go-check: TestConfigQuotedColonLineIsAScalar]
- preprocessing-167: After a quoted key, the first byte that is not SP, HT, or the map colon MUST raise `config/malformed` at that byte under the token rule. [just go-check: TestConfigQuotedKeyFollowedByNonColon]
- preprocessing-168: Truncating a quoted YAML value at any byte MUST give one of three results. When the kept text holds the closing quote under preprocessing-161, the scalar MUST be closed and the reader MUST raise no diagnostic. When the kept text ends inside an escape, the reader MUST raise `config/malformed` (`invalid escape`) over the backslash and the next byte, clamped to the reader's end. Otherwise the reader MUST raise the zero-width diagnostic of preprocessing-162 at the reader's end. [just go-check: TestConfigQuotedValueTruncation]
- preprocessing-169: A plain value that starts on the line after its owning key MUST continue on lines that start at a column greater than the column of that key. A non-blank line at or left of that column MUST end the scalar. Preprocessing-150 and preprocessing-163 MUST apply only to a value with no owning key. [just go-check: TestConfigNextLinePlainValueColumn]
- preprocessing-170: A flow collection that starts on the line after its owning key MUST use the column of that key as its continuation column under preprocessing-159. [just go-check: TestConfigNextLineFlowValueColumn]
- preprocessing-171: A line at the column of a block map that is not blank, is not a comment line, and holds no map colon MUST raise `config/malformed` at the end of its line content, which is the CR or LF that ends the line or the end of the reader's range. A comment on that line MUST NOT move the failure. [just go-check: TestConfigKeylessLineFailsAtLineEnd]
- preprocessing-172: While the reader probes the lines after a plain YAML value for continuation lines, an HT in the leading whitespace of a probed line MUST raise `config/malformed` (`tab in indentation`) at that HT, and the entry that owns the value MUST NOT be committed, so it raises no duplicate-key diagnostic. [just go-check: TestConfigTabDuringContinuationProbe]
- preprocessing-173: A column-zero `---` or `...` that follows a complete root value, with only blank lines and comment lines between, and that is followed by SP, HT, a line end, or the reader's end MUST raise `config/malformed` with message `multi-document streams are not supported` over its three bytes. Without that boundary the byte run MUST fail under the token rule with message `malformed config value`. [just go-check: TestConfigMarkerAfterRootValue]
- preprocessing-174: A `[` or `{` that starts a block sequence item MUST open a flow collection even when the item's line holds a map colon. [just go-check: TestConfigFlowValueInSequenceItem]
- preprocessing-175: An anchor or a tag inside a flow collection that is a block sequence item MUST raise `config/unsupported-anchor` or `config/unsupported-tag` under preprocessing-059 and preprocessing-060, over the span of the table under Config diagnostics. [just go-check: TestConfigNodePrefixInsideFlowSequenceItem]
- preprocessing-176: A line that starts with `|` or `>` and holds a map colon MUST raise `config/malformed` at that first byte under the token rule, both as a line at the column of a block map and as the first line of a value that follows its key. Preprocessing-072 MUST apply only to a header line that holds no map colon. [just go-check: TestConfigNextLinePipeLineWithMapColon]
