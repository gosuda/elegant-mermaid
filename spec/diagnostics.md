# Diagnostics

This file fixes the diagnostic model, the severity and fix safety values, the registry rows, and the four output formats: text, JSON schema v1, SARIF 2.1.0, and GitHub workflow commands.

## Diagnostic model

- diagnostics-01: A diagnostic MUST carry a code, a severity, a message, a span, related spans, help text, and fixes, with the field set of spec/library-surface.md. [just parity]
- diagnostics-02: The severity of a diagnostic MUST be `error`, `warning`, or `info`, with the wire value of the same name. [just parity]
- diagnostics-03: The safety of a fix MUST be `safe` or `unsafe`, and the wire value `none` MUST appear only in a registry row. [just parity]
- diagnostics-04: A diagnostic without fixes MUST carry an empty `fixes` array. [just parity]
- diagnostics-05: A span MUST hold byte offsets with an exclusive `end`, and `line`, `column`, `end_line`, and `end_column` MUST be derived by the position rules of spec/source-and-positions.md. [just parity]
- diagnostics-06: Each entry of `related` MUST hold a `span` and a `message`, and the JSON output MUST add `line` and `column` at `span.start`. [just parity]
- diagnostics-07: A diagnostic code MUST be a stable identifier, a renamed code MUST keep its old name as an alias in the registry, and a code MUST NOT be reused. [just gen-check]
- diagnostics-08: Every emitted diagnostic MUST satisfy `0 <= span.start <= span.end <= len(source)`. [just go-check: TestDiagnosticSpansAndFixes]
- diagnostics-09: In every output format, files MUST be ordered byte-wise by `path`, with stdin as the one file `<stdin>`, and diagnostics MUST be ordered by `span.start`, then `code` byte-wise, then emission order. [just parity]

## Registry rows

- diagnostics-10: A row of `spec/data/diagnostics/<kind>.json` or `spec/data/lint-rules/<kind>.json` MUST have the fields `code`, `severity`, `summary`, `help`, `rationale`, `fix_safety`, and `aliases`, with the keys in that order. [just gen-check]
- diagnostics-11: The severity of a row MUST be `error`, `warning`, or `info`, and a lint row MAY also have severity `off`. [just gen-check]
- diagnostics-12: The `fix_safety` of a row MUST be `none`, `safe`, or `unsafe`. [just gen-check]
- diagnostics-13: A lint row MUST also have `source` (`mermaid-lint:<rule>`, `maid:<CODE>`, or `own`) and `status` (`adopted` or `rejected`), with the keys after `aliases` in the order `source`, `status`, `reason`, and `reason` MUST be present only when `status` is `rejected`. [just gen-check]
- diagnostics-14: The rows of the table below MUST be the content of `spec/data/diagnostics/common.json`, except the lint rows `common/acc-title-missing`, `common/acc-descr-missing`, and `common/no-experimental` and the `meta/` rows, which are the content of `spec/data/lint-rules/common.json`, and per-kind rows MUST follow the same fields. [just gen-check]

    |Code|Severity|Message|Help|
    |---|---|---|---|
    |`common/unknown-diagram-kind`|error|unknown diagram kind TOKEN|Start the source with a supported diagram header, for example flowchart.|
    |`common/empty-source`|error|source is empty|add a diagram header, for example flowchart|
    |`common/no-experimental`|warning|KIND is a beta diagram type|Beta syntax may break on a Mermaid upgrade.|
    |`common/acc-title-missing`|off (`warning` when selected)|diagram has no accTitle line|Add an accTitle line that names the diagram.|
    |`common/acc-descr-missing`|off (`warning` when selected)|diagram has no accDescr line|Add an accDescr line that describes the diagram.|
    |`meta/unknown-rule`|warning|unknown rule CODE|Use a code from the lint rule registry.|
    |`meta/unused-suppression`|warning|suppression of CODE suppresses nothing|Remove the directive, or move it to the line it should cover.|
    |`meta/malformed-suppression`|warning|malformed suppression directive|Write the directive with a code list and a reason, as in `%% emd-disable-next-line CODES: reason`.|
    |`config/malformed`|error|invalid config value VALUE for KEY|Write a value that the config key accepts.|
    |`config/unsupported-anchor`|error|anchor or alias TOKEN is not supported|Write the value without anchors or aliases.|
    |`config/unsupported-tag`|error|tag TOKEN is not supported|Write the value without a tag.|
    |`config/unknown-key`|warning|unknown config key KEY|Check the spelling of the key, or remove it.|
    |`config/unsupported-key`|warning|config key KEY is not supported by this project|Remove the key; this project cannot produce the output it asks for.|
    |`config/font-metrics-approximate`|info|text width is measured with Inter; fontFamily is VALUE|Text widths may differ from the font named in fontFamily.|
    |`limit/nesting-depth`|error|nesting depth exceeds 64|Reduce the nesting to 64 levels or fewer.|
    |`limit/max-text-size`|error|source has SIZE bytes; the limit is LIMIT bytes|Shorten the source, or raise maxTextSize.|
    |`limit/max-edges`|error|diagram has COUNT edges; the limit is LIMIT|Reduce the number of edges, or raise maxEdges.|
    |`layout/budget-exhausted`|info|layout stopped at its iteration cap in PHASE|The diagram uses the best feasible result found so far.|
    |`math/unsupported-command`|warning|unsupported math command COMMAND|The source text is shown as written.|
    |`math/syntax`|error|invalid math syntax: REASON|The source text is shown as written.|
    |`icon/pack-missing`|info|icon NAME is not available|The diagram draws the unknown icon in its place.|
    |`interaction/unsafe-url`|warning|link URL is not allowed|Use an http, https, or mailto link.|
    |`interaction/callback-ignored`|info|callback FUNCTION is ignored|Static output never runs callbacks.|
    |`source/invalid-utf8`|error|invalid UTF-8 at byte OFFSET|Save the source as UTF-8.|

- diagnostics-15: In the table of diagnostics-14, the `Message` column MUST be the `summary` field, the `Help` column MUST be the `help` field, an empty `Help` MUST be the empty string, and an emitted diagnostic MUST carry its row summary with the placeholders filled. [just gen-check]
- diagnostics-16: A row whose default severity is `off` MUST run with severity `warning` when `--select` or `lint.select` names it, unless `lint.severity` gives it another value. [just go-check]

## JSON output

- diagnostics-17: A schema v1 diagnostic object MUST have the keys `code`, `severity`, `message`, `span`, `line`, `column`, `end_line`, `end_column`, `related`, `help`, and `fixes`, in that order. [just parity]
- diagnostics-18: In schema v1, `span` MUST be `{"start","end"}` in byte offsets with an exclusive `end`, each `related` item MUST be `{span,line,column,message}`, and each `fixes` item MUST be `{title,safety,edits:[{span,new_text}]}` with `safety` `safe` or `unsafe`. [just parity]
- diagnostics-19: All JSON output MUST follow the byte rules of the canonical layout dump of spec/layout-dump.md. [just parity]
- diagnostics-20: The `check` and `lint` JSON output MUST be the document below. [just parity]

    ```
    {"version":1,"files":[{"path","kind","diagnostics":[..]}],"summary":{"files","errors","warnings","info"}}
    ```

- diagnostics-21: In that document, `kind` MUST be the kind id or `null`; `summary.files` MUST count every entry of `files`, including files with no diagnostics; and the other `summary` counts MUST be the diagnostics of this output. [just parity]

## Text output

- diagnostics-22: The text format MUST be fixed to the byte: UTF-8 with LF only, the path printed as given except for terminal control replacement under diagnostics-28, and `<stdin>` as the path for stdin in every format. [just parity]
- diagnostics-23: One diagnostic MUST print in the form below. [just parity]

    ```
    path:line:column: error[code]: message
      |
    L | source line
      | ^~~~
      = help: HELP
      = fix: TITLE
    ```

- diagnostics-24: The severity word MUST be `error`, `warning`, or `info`, the `help` and `fix` lines MUST be omitted when empty, and fixes MUST print in fix order. [just parity]
- diagnostics-25: The gutter MUST be as wide as the line number, and a tab MUST expand to 8-column stops. [just parity]
- diagnostics-26: The underline MUST cover the span in terminal cells, at least one cell (`^` then `~`), and a multi-line span MUST underline to the end of its first line. [just parity]
- diagnostics-27: Each related span MUST append `  = note: MESSAGE at path:line:column`. [just parity]
- diagnostics-28: Every untrusted text field in terminal diagnostics MUST replace U+0000 to U+001F, U+007F, and U+0080 to U+009F with U+FFFD. This rule MUST cover paths, codes, messages, related messages, help, and fix titles. Source-line tabs MUST instead expand under diagnostics-25. Formatter-owned line breaks and colour sequences MUST remain unchanged. Machine-readable formats MUST retain their own escaping rules and original field values. [just parity]
- diagnostics-29: A blank line MUST separate diagnostics. [just parity]
- diagnostics-30: Colour, when on, MUST wrap only the severity word and the underline. [just go-check]

## SARIF output

- diagnostics-31: The SARIF 2.1.0 output MUST hold one run whose `tool.driver.name` is `emd` and whose `tool.driver.version` is the `Version` constant. [just go-check: TestLintGolden]
- diagnostics-32: Each diagnostic MUST be one result with `ruleId` set to the code, `level` set by the table under diagnostics-36, `message.text` set to the message, and `locations[0].physicalLocation` holding `artifactLocation.uri` (the path as given, or `<stdin>`) and `region` with `startLine`, `startColumn`, `endLine`, and `endColumn`. [just go-check: TestLintGolden]
- diagnostics-33: SARIF columns MUST be 1-based UTF-16 code units, and `endColumn` MUST be exclusive. [just go-check: TestLintGolden]
- diagnostics-34: Related spans MUST go to `relatedLocations`, and `help` and fixes MUST NOT be emitted. [just go-check: TestLintGolden]
- diagnostics-35: `tool.driver.rules` MUST list the distinct codes of the output in this order: the lint rule rows in the registry order of spec/lint.md, then the diagnostic rows in registry order, then codes with no registry row in ascending byte order; `shortDescription.text` MUST be the summary and `help.text` MUST be the help. [just go-check: TestLintGolden]
- diagnostics-36: The severity mapping of the machine formats MUST be the table below, and severity `off` MUST NOT be emitted. [just go-check: TestLintGolden]

    |severity|`json`|`sarif` `level`|`github` command|
    |---|---|---|---|
    |`error`|`error`|`error`|`::error`|
    |`warning`|`warning`|`warning`|`::warning`|
    |`info`|`info`|`note`|`::notice`|

## GitHub workflow commands

- diagnostics-37: Each diagnostic MUST print one workflow command in the form below, where `<command>` is `error`, `warning`, or `notice` for `info`, and `L`, `C`, `L2`, and `C2` are the JSON `line`, `column`, `end_line`, and `end_column` values. [just go-check: TestLintGolden]

    ```
    ::<command> file=PATH,line=L,col=C,endLine=L2,endColumn=C2,title=CODE::MESSAGE
    ```

- diagnostics-38: In MESSAGE, `%`, CR, and LF MUST be written as `%25`, `%0D`, and `%0A`, and in property values `:` and `,` MUST also be written as `%3A` and `%2C`. [just go-check: TestLintGolden]
