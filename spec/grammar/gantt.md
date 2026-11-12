# Gantt grammar

This file fixes syntax and model resolution for the `gantt` kind. Layout belongs to `spec/layout/charts.md`.

## Scope

- gantt-01: Implementations MUST use `.references/mermaid/packages/mermaid/src/diagrams/gantt/parser/gantt.jison:6-97,107-173` as the syntax authority and `ganttDb.js:24-214,227-475,536-635,658-704,712-822,885-899` in the same directory as the resolution authority. [just oracle]
- gantt-02: Implementations MUST use `schemas/config.schema.yaml:476-525,2089-2209` for configuration keys and `ganttRenderer.js:650-755` for axis directives; paths in this clause are relative to `.references/mermaid/packages/mermaid/src/`. [just gen-check]
- gantt-03: The model MUST preserve source order, raw date-format text, task data, spans, sections, tags, references, and interaction statements; unreachable `addTaskOrg`, `compileData`, `clickStatementDebug`, `date`, and `accDescription` productions MUST NOT add statement forms. [just parity]

## Header forms

- gantt-04: The header MUST be `gantt`, case-sensitive, with the boundary and preprocessing rules of `spec/detection.md`; the body lexer MUST fold ASCII keyword case as the authority's case-insensitive lexer does. [just oracle]

## Lexer modes

- gantt-05: The lexer MUST use INITIAL and exclusive modes `click`, `href`, `callbackname`, `callbackargs`, `acc_title`, `acc_descr`, and `acc_descr_multiline`, and MUST choose the first matching rule in the following table. [just parity]

### Lexical rules in first-match order

Order is the authority line number. Mode changes push and pop the current state. Shared preprocessing removes directives before this table runs.

| Order | Mode and pattern | Action |
|---|---|---|
|18|INITIAL `%%{`|Shared directive reader; the authority's undeclared `open_directive` state is not a new grammar mode.|
|20-21|INITIAL `accTitle` plus optional whitespace, colon, whitespace; acc_title through line end|Emit introducer, push acc_title; emit value and pop.|
|22-23|INITIAL `accDescr` plus optional whitespace, colon, whitespace; acc_descr through line end|Emit introducer, push acc_descr; emit value and pop.|
|24-26|INITIAL `accDescr` plus whitespace and `{`; multiline `}`; multiline non-`}` run|Push acc_descr_multiline without emitting opener; pop at close; emit value run.|
|28-30|INITIAL comment patterns, in order: `%%` with non-directive tail; non-`}` byte followed by percent run and tail; percent run and optional newlines|Discard. Shared comment handling takes precedence.|
|32|INITIAL LF run|Emit NL. CRLF and lone CR use the shared line-end rule.|
|33-34|INITIAL whitespace run; percent comment tail|Discard.|
|42-44|INITIAL `href` whitespace double quote; href double quote; href non-quote run|Push href; pop; emit href value.|
|54-59|INITIAL `call` whitespace; callbackname empty parentheses; callbackname `(`; callbackname non-`(` run; callbackargs `)`; callbackargs non-`)` run|Push callbackname; pop on empty arguments; switch to callbackargs on `(`; emit name; pop at `)`; emit arguments.|
|67-69|INITIAL `click` whitespace; click whitespace or newline; click non-whitespace run|Push click; pop; emit id list.|
|71|INITIAL `gantt`|Emit header.|
|72|INITIAL `dateFormat` whitespace then non-`#`, non-line-end, non-semicolon run|Emit dateFormat.|
|73-74|INITIAL `inclusiveEndDates`; `topAxis`|Emit matching token.|
|75-78|INITIAL `axisFormat`, `tickInterval`, `includes`, `excludes`, each whitespace then non-`#`, non-line-end, non-semicolon run|Emit matching token.|
|79|INITIAL `todayMarker` whitespace then non-line-end, non-semicolon run|Emit todayMarker, including any `#` colour.|
|80-86|INITIAL `weekday` whitespace then monday, tuesday, wednesday, thursday, friday, saturday, sunday, in that order|Emit distinct weekday token.|
|87-88|INITIAL `weekend` whitespace then friday, saturday|Emit distinct weekend token.|
|89|INITIAL four digits, hyphen, two digits, hyphen, two digits|Emit date; no statement consumes it alone.|
|90|INITIAL `title` whitespace then non-line-end run|Emit title.|
|91|INITIAL `accDescription` whitespace then non-`#`, non-line-end, non-semicolon run|Emit accDescription; no statement consumes it.|
|92|INITIAL `section` whitespace then non-line-end run|Emit section.|
|93|INITIAL non-colon, non-line-end run|Emit taskTxt, including trailing spaces.|
|94|INITIAL colon then non-`#`, non-line-end, non-semicolon run|Emit taskData.|
|95-97|INITIAL colon; end of input; any remaining byte|Emit colon; EOF; INVALID.|

- gantt-06: Token values MUST omit interaction and accessibility delimiters but token spans MUST include them; directive values MUST use the authority's fixed prefix offsets, then the database's trimming rules, not an extra global trim. [just parity]
- gantt-07: A semicolon MUST NOT be treated as a general statement separator: taskData and most directive tokens stop before it, but no separator production consumes it; title and section tokens can contain it. [just oracle]

## Grammar

- gantt-08: The parser MUST implement the following EBNF with source-borrowing tokens and no backtracking. [just parity]

```ebnf
start = gantt, document, EOF ;
document = { line } ;
line = statement | NL | EOF ;
statement = dateFormat | inclusiveEndDates | topAxis | axisFormat
          | tickInterval | excludes | includes | todayMarker | weekday | weekend
          | title | acc_title, acc_title_value | acc_descr, acc_descr_value
          | acc_descr_multiline_value | section | clickStatement | taskTxt, taskData ;
weekday = weekday_monday | weekday_tuesday | weekday_wednesday | weekday_thursday
        | weekday_friday | weekday_saturday | weekday_sunday ;
weekend = weekend_friday | weekend_saturday ;
clickStatement = click, (callbackname, [callbackargs], [href]
                       | href, [callbackname, [callbackargs]]) ;
```

- gantt-09: The callback form MUST require `call NAME(...)`, even though the parentheses emit no grammar token; a link MUST require `href "URL"`, and a click MUST contain at least one of those commands. [just oracle]

## Statement boundary

- gantt-10: Recovery MUST discard the rejected statement through the next physical line end outside href, callback, or multiline accessibility text; it MUST then continue without adding a task for that rejected statement. [just parity]
- gantt-11: EOF inside an interaction delimiter or accessibility block MUST raise `gantt/unterminated` from its opening delimiter through EOF; an ordinary unknown line MUST raise `gantt/unknown-statement` over the line without its ending. [just oracle]

## Abstract syntax tree

- gantt-12: AST nodes MUST use the authority production names `Start`, `Document`, `Line`, `Statement`, `Weekday`, `Weekend`, and `ClickStatement`; directive and task alternatives MUST be variants of `Statement`, not invented production names. [just parity]

| Node | Fields | Span |
|---|---|---|
|Start|header, document|Header start through EOF.|
|Document|ordered lines|First body token through last body token, or zero-width after header.|
|Line|statement or blank|Statement span or line-ending span.|
|Statement|alternative, raw value; task text and raw data; accessibility value|First token through last token, excluding line ending.|
|Weekday / Weekend|selected token|Whole directive.|
|ClickStatement|raw id list, optional callback name and arguments, optional URL, command order|`click` through final closing delimiter.|

- gantt-13: The model MUST retain spans for each task id, date operand, reference id, tag, URL, callback, and directive, even when the AST stores them as slices of one token. [just parity]

## Semantic resolution

- gantt-14: Initial state MUST have empty dateFormat and axisFormat, absent tickInterval, no sections, empty current section, false inclusiveEndDates and topAxis, weekday sunday, weekend saturday, and an empty ordered task list; the documented default dateFormat `YYYY-MM-DD` MUST NOT replace the database's empty string. [just parity]
- gantt-15: Repeated dateFormat, axisFormat, tickInterval, weekday, weekend, title, and accessibility statements MUST replace the earlier value; inclusiveEndDates and topAxis MUST only enable their flags; each section MUST append its name and set the current section without resetting task dependencies. [just oracle]
- gantt-16: Includes and excludes MUST lowercase text, split on whitespace or commas, remove empty tokens, and append only new tokens in first-seen order across all statements. [just parity]
- gantt-17: Task data MUST drop its leading colon, split on every comma without quote protection, consume leading fields that exactly match lowercase `active`, `done`, `crit`, `milestone`, or `vert` after whitespace trimming, and then trim all remaining fields; tag matching MUST remain case-sensitive despite keyword folding. [just oracle]
- gantt-18: One remaining field MUST mean generated id, predecessor end, and end operand; two MUST mean generated id, explicit start operand, and end operand; three MUST mean explicit id, start operand, and end operand; other arities MUST raise `gantt/task-data-invalid` rather than reproducing the database's later undefined-property exception. [just oracle]
- gantt-19: Generated ids MUST be `task1`, `task2`, and so on, increasing only for tasks without explicit ids; explicit ids MUST remain unrestricted trimmed field text, and duplicate ids MUST resolve references to the last declared task, without a duplicate-id error. [just parity]
- gantt-20: Each task MUST retain the current section and all independent tag flags; the syntax model MUST preserve upstream's vert order -1 and non-vert zero-based order as metadata, but layout MUST follow the plan's declaration-order rows, with one row per task and one header row per section, including vert tasks. [just parity]
- gantt-21: Date compilation MUST use the final dateFormat, includes, excludes, weekend, and inclusiveEndDates state for all tasks; it MUST scan tasks in declaration order and repeat up to eleven full scans, matching the initial compile plus ten retries in getTasks. [just parity]
- gantt-22: Predecessor lookup MUST use the preceding task's id through the final id table; a first task with only an end operand MUST raise `gantt/predecessor-missing`, because the database dereferences a missing predecessor. [just oracle]
- gantt-23: Start `after` and end `until` MUST match the case-sensitive prefix `^after\s+([\d\w- ]+)` or `^until\s+([\d\w- ]+)`, split its captured text on ASCII space, ignore empty ids, and use the latest referenced end or earliest referenced start respectively; suffixes outside the captured run MUST NOT become references. [just parity]
- gantt-24: Missing reference ids MUST raise `gantt/unknown-task-reference` as a warning and MUST NOT reject the diagram; known ids MUST still participate, and ties MUST keep the first reference. [just oracle]
- gantt-25: Model Start and End MUST be signed integer seconds since 1970-01-01 00:00:00 with no zone, computed from proleptic Gregorian civil days as `days * 86400 + hh * 3600 + mm * 60 + ss`; no parser, resolver, or layout MUST read the wall clock or host timezone. [just parity]
- gantt-26: Where upstream uses today's midnight for an unresolved after or until, implementations MUST use epoch midnight 0; where a format omits year, month, or day, implementations MUST supply values from 1970-01-01 using the database's missing-field rule (day 1 if year or month is supplied, otherwise anchor day; January if year but no month is supplied, otherwise anchor month). The plan supplies no missing-date fallback, so this deterministic replacement MUST remain an explicit ambiguity. [just parity]
- gantt-27: Date parsing MUST use English names and a naive civil calendar with no zone; offset tokens MUST be consumed and validated but MUST NOT shift the civil fields, and no host timezone MUST be read. The plan supplies no offset-token conversion rule, so ignoring the offset after validation MUST remain an explicit ambiguity. [just parity]
- gantt-28: dateFormat MUST retain case and MUST recognize the Dayjs 1.11.21 customParseFormat token inventory `Y YY YYYY Q M MM MMM MMMM D DD Do H HH h hh m mm s ss S SS SSS A a Z ZZ w ww z`, square-bracket literals, separator runs, and localized expansions `LT LTS L LL LLL LLLL l ll lll llll`; this inventory MUST NOT be replaced with the inaccurate documentation claim that DDD and DDDD are day-of-year tokens. [just oracle]
- gantt-29: YYYY MUST read four digits; YY MUST map 69..99 to 1969..1999 and 00..68 to 2000..2068; Y MUST read a signed year; Q MUST select the quarter's first month; month and ordinal names MUST use English; H/h, minute and second tokens MUST read one or two digits except fixed-width DD, MM, YY and YYYY; S, SS, SSS MUST scale fractional seconds by 100, 10 and 1 respectively. [just parity]
- gantt-30: Strict date parsing MUST require that formatting the parsed date with the same format returns the input exactly; unsupported output tokens such as Y, S and SS MUST therefore keep their Dayjs round-trip consequences rather than silently gain support; w/ww MUST NOT call an unavailable weekOfYear plugin, and z MUST NOT call an unavailable timezone plugin. [just oracle]
- gantt-31: A numeric unsigned start with the exact trimmed format x or X MUST first use the upstream millisecond interpretation in both cases, because getStartDate bypasses Dayjs; end parsing MUST retain Dayjs's x milliseconds and X seconds distinction and strict round-trip check; every resolved instant MUST then become integer seconds by floor division by 1000. The plan supplies no sub-second rounding rule, so floor conversion MUST remain an explicit ambiguity, including for pre-epoch input. [just parity]
- gantt-32: An explicit start that fails strict parsing MUST try deterministic ISO/civil Date-compatible parsing; a non-date or a fallback year outside -10000..10000 MUST raise `gantt/invalid-date`; environment-dependent natural-language Date parsing MUST be treated as an ambiguity and MUST NOT consult the host runtime. [just oracle]
- gantt-33: End resolution MUST first handle until, then strict date parsing, then duration; inclusiveEndDates MUST add one calendar day only to an explicitly parsed end date, not to until or a duration. [just parity]
- gantt-34: A duration MUST match `^(\d+(?:\.\d+)?)([Mdhmswy]|ms)$` after trimming; M MUST mean calendar months, m minutes, y years, w weeks, d days, h hours, s seconds, and ms milliseconds; negative values, exponents, whitespace within a value, and other unit spellings MUST NOT match. [just oracle]
- gantt-35: Duration arithmetic MUST use exact decimal operands: days and weeks MUST round their day increment half up (weeks multiply by seven first); month and year addition MUST truncate the resulting calendar field toward zero and clamp the day to the new month's final day; smaller units MUST add exact durations in seconds with factors 3600, 60, 1, or 1/1000 for h, m, s, or ms, then floor the resulting absolute instant to integer seconds before publishing it or using it as a dependency. The plan supplies no sub-second duration rule, so this floor conversion MUST remain an explicit ambiguity rather than reproduce Date TimeClip. [just parity]
- gantt-36: An end operand that is neither a strict date nor a duration MUST raise `gantt/invalid-end` as a warning and MUST resolve to the task start, not reject the diagram; an out-of-range duration result MUST likewise leave the end at the start. [just oracle]
- gantt-37: manualEndTime MUST be true exactly when the raw end operand strictly parses as YYYY-MM-DD, regardless of dateFormat; such tasks and tasks with no excludes MUST skip exclusion extension. [just parity]
- gantt-38: Exclusion checks MUST first accept a date whose YYYY-MM-DD rendering occurs in includes; otherwise they MUST exclude the configured weekend only when excludes contains `weekends`, an English lowercase weekday name in excludes, or its YYYY-MM-DD rendering in excludes. Saturday MUST select ISO days 6 and 7; friday MUST select days 5 and 6. The plan's ISO-date matching MUST replace the database's additional current-dateFormat matching. [just parity]
- gantt-39: Duration extension MUST scan calendar days from start plus one day through the evolving end inclusively, preserve time of day, add one day to end for each excluded day, and update renderEndTime to the current end before testing a day only when the preceding day was not excluded; renderEndTime MUST remain absent when no day is scanned. [just parity]
- gantt-40: Exclusion extension beyond the original end plus 10000 days MUST raise `gantt/exclusion-limit` as an error; a dependency still unresolved after eleven scans MUST raise `gantt/unresolved-task` instead of emitting invalid time coordinates. [just oracle]
- gantt-41: axisFormat MUST remain raw output-format text, separate from dateFormat; tickInterval MUST remain raw text and MUST select an explicit interval only when it matches `^([1-9][0-9]*)(millisecond|second|minute|hour|day|week|month)$`; other values MUST fall back to automatic ticks without a syntax error. [just oracle]
- gantt-42: Axis formatting MUST use non-empty AxisFormat first, else `%d` only for exact case-sensitive DateFormat `D`, else `%Y-%m-%d`; only `%Y %m %d %H %M %S %a %b %%` MUST render, and any other code MUST emit `gantt/axis-format-unsupported` (warning) and use `%Y-%m-%d`. A millisecond tickInterval MUST emit `gantt/tick-interval-unsupported` (warning) and use automatic ticks; automatic tick selection and weekday alignment MUST follow `spec/layout/charts.md`, including its 18-entry second-duration table and exact squared comparisons. Syntax MUST accept unsupported axisFormat text without a parse error. [just parity]
- gantt-43: todayMarker MUST be parsed and retained but MUST draw nothing, including when absent or set to a style; a present statement MUST emit `gantt/today-marker-ignored` as info at its statement span. [just parity]
- gantt-44: Click id lists MUST split only on commas, without an additional id trim; href and callback effects MUST apply only to tasks already declared at that statement; missing tasks MUST be ignored, and a later href for one id MUST replace its link. [just oracle]
- gantt-45: Callback arguments MUST split on commas outside balanced double-quoted pairs, trim each argument, and remove a double quote at each end when both exist; absent or empty arguments MUST default to the task id; callbacks MUST be retained but never executed, with shared `interaction/callback-ignored` reporting. [just parity]
- gantt-46: Static links MUST follow the shared safe-scheme rule and MUST NOT reproduce window.open, JavaScript callbacks, or upstream securityLevel-dependent executable behavior; a standalone link statement MUST NOT be accepted because only clickStatement reaches setLink. [just parity]
- gantt-47: title and section values MUST preserve their authority substring text; accTitle, accDescr colon form, and accDescr brace form MUST trim their values and set shared accessibility metadata; accDescription without a colon or braces MUST NOT be accepted as an accessibility alias. [just oracle]

## Diagnostics

- gantt-48: Implementations MUST emit the codes in this table with these severities; shared source, limit, config, and interaction codes MUST remain in their common registries. [just gen-check]

| Code | Severity | Message | Span |
|---|---|---|---|
|gantt/unexpected-token|error|unexpected TOKEN, expected one of: LIST|Offending token; EOF is zero-width.|
|gantt/unknown-statement|error|unknown statement TOKEN|Rejected statement without line ending.|
|gantt/unterminated|error|unterminated TOKEN|Opening delimiter through EOF.|
|gantt/task-data-invalid|error|task requires one, two, or three data fields after tags|Task data.|
|gantt/predecessor-missing|error|task has no preceding task|Single end operand.|
|gantt/invalid-date|error|invalid date VALUE|Start operand.|
|gantt/unknown-task-reference|warning|KEYWORD references unknown task id ID|Missing reference token.|
|gantt/invalid-end|warning|VALUE is neither a date nor a duration; task has zero duration|End operand.|
|gantt/exclusion-limit|error|cannot find a non-excluded end within 10000 days|Task end operand.|
|gantt/unresolved-task|error|task dates remain unresolved after eleven passes|Task data.|
|gantt/today-marker-ignored|info|today marker is ignored|todayMarker statement.|
|gantt/tick-interval-unsupported|warning|millisecond tick interval is not supported; using automatic ticks|tickInterval value.|
|gantt/axis-format-unsupported|warning|axis format contains unsupported code CODE; using %Y-%m-%d|axisFormat value.|

- gantt-49: LIST MUST contain accepted token-kind names sorted bytewise and joined by `, `; diagnostics MUST keep source spans and MUST NOT invent a task as recovery. [just parity]

## Upstream readings

| Reading | Authority fact | Decision |
|---|---|---|
|ganttDb.js:305-375,409-466|Date fallback and unresolved references can read current date.|Use epoch anchor and naive civil integer seconds; flag missing dates, offset handling, sub-second flooring, and host parsing as ambiguities.|
|ganttDb.js:169-180,658-704|Compilation can stop with unresolved dates.|Keep eleven scans; report unresolved tasks rather than serialize undefined dates.|
|gantt.jison:141; ganttDb.js:113-119,835-878|Grammar calls TopAxis but database exports enableTopAxis.|Resolve the directive to enableTopAxis; this is an upstream naming defect, not an intended rejection.|
|Dayjs 1.11.21 plugin/customParseFormat.js and dayjs.min.js, fetched from https://unpkg.com/dayjs@1.11.21/|Strict parsing uses a token table and format round-trip; missing fields use current date; core calendar arithmetic has distinct rounding paths.|Apply clauses 25-35, not the documentation's larger token promises.|
|ganttDb.js:299-302,455-458|Unknown references and invalid end operands warn and continue.|Keep warning severity and deterministic fallback.|
|ganttDb.js:712-822|Interactions resolve against tasks present when the action runs.|Keep declaration-time lookup; static output never executes callbacks.|

- gantt-50: Implementations MUST document the epoch anchor, naive offset-token handling, sub-second flooring, fallback parsing restriction, TopAxis naming repair, and unresolved-date diagnostics as explicit ambiguities where the plan gives no rule; the plan's integer-second model, ISO exclusion matching, diagnostic names and severities, and declaration-order rows MUST override upstream behavior. No accepted corpus mismatch MUST be hidden without a parent-owned oracle divergence decision. [just oracle]
