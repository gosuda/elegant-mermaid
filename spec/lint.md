# Lint

This file fixes the lint rule model, the registry and its seeding, the engine pipeline, suppression comments, configuration, fix safety, and fix application; the byte formats of the output are fixed in spec/diagnostics.md.

## Rules and registry

- lint-01: A lint rule MUST be one function over the resolved model of its kind plus its registry row. [just gen-check]
- lint-02: A rule code MUST be `<kind>/<name>` or `common/<name>`. [just gen-check]
- lint-03: The registry MUST be the directory `spec/data/lint-rules/`, with one file per kind (`<kind>.json`) and `common.json`, whose rows follow spec/diagnostics.md. [just gen-check]
- lint-04: A rule MUST read only its argument, MUST NOT read the file system or the clock, and MUST NOT read another kind's model. [just go-check]
- lint-05: A rule MUST emit diagnostics with its own row's code, in a fixed order, and MUST NOT set a severity; the engine sets the effective severity and drops `off` diagnostics. [just go-check]
- lint-06: A kind rule and a common rule MUST have the signatures below in each language, where `M` is the resolved model of that kind (`internal/model/<kind>`; Rust `model::<kind>`); a common rule takes the internal `Block` view of one block (its source bytes, its host offset, and its header token) and runs for every kind. [just gen-check]

    ```
    Go kind rule:     func(m M, row Row) []diag.Diagnostic
    Go common rule:   func(b *Block, row Row) []diag.Diagnostic
    Rust kind rule:   fn(m: &M, row: &Row) -> Vec<diag::Diagnostic>
    Rust common rule: fn(b: &Block, row: &Row) -> Vec<diag::Diagnostic>
    ```

## Ownership and generation

- lint-07: A kind rule and its row MUST belong to that kind's packet files: `internal/lint/<kind>.go`, `crates/elegant-mermaid/src/lint/<kind>.rs`, and `spec/data/lint-rules/<kind>.json`. [just gen-check]
- lint-08: The common rules, their rows, and the engine MUST belong to `internal/lint/common.go`, `crates/elegant-mermaid/src/lint/common.rs`, and `spec/data/lint-rules/common.json`. [just gen-check]
- lint-09: A row with `source` `maid:<CODE>` MUST be emitted by the parser of its kind under its code, a row with `source` `mermaid-lint:suppression-*` MUST be emitted by the suppression pass, and neither kind of row MUST have a rule function. [just gen-check]
- lint-10: `tools/specgen` MUST write adopted rows only, in registry order, to `internal/gen/lintrules.go` and `crates/elegant-mermaid/src/gen/lintrules.rs`, where the registry order is the rows of `common.json`, then each kind file in the order of `spec/data/kinds.json`, rows in file order. [just gen-check]
- lint-11: `gen-check` MUST fail when an adopted row whose `source` is `own` or `mermaid-lint:<rule>`, other than the three suppression rows, has no function; when a function has no row; when a code is duplicated; or when a row sits in the file of another kind. [just gen-check]

## Engine pipeline

- lint-12: For each block, the engine MUST run the steps below in order. [just go-check]

    1. The parser reports its syntax diagnostics; they are always on and keep their row severity.
    2. For each enabled lint row, in registry order, the engine runs its function.
    3. The engine sets each diagnostic's severity to its effective severity and drops `off` diagnostics.
    4. The suppression pass removes suppressed diagnostics and adds the `meta/*` diagnostics.
    5. Output is sorted as spec/diagnostics.md orders it.

- lint-13: `Lint(d, cfg)` MUST return the diagnostics of steps 2 to 4, `Document.Diagnostics()` MUST be step 1, and the `lint` command MUST print both lists in one sorted output. [just go-check]
- lint-14: `check` MUST run step 1 only, and suppressions and lint rules MUST apply only in `lint`. [just go-check]

## Registry seeding

- lint-15: The registry MUST be seeded from `.references/mermaid-lint/docs/semantic-rules.md` (MIT, 101 rows at lines 24 to 124) by porting every row with its default severity. [just gen-check]
- lint-16: The registry MUST be seeded from `.references/maid/docs/errors.md` (ISC) by porting every code as a syntax diagnostic with its fix where maid marks one Safe or All. [just gen-check]
- lint-17: Each source row MUST be recorded as `adopted` with the code of this project or `rejected` with the reason, and nothing MUST be copied from `.references/mermaid-linter`. [just gen-check]
- lint-18: A mermaid-lint row MUST be adopted when its predicate reads only the block source, the header token, and the model of its kind, and a row whose predicate needs anything else MUST be rejected. [just gen-check]
- lint-19: The mermaid-lint row `click-target-not-found` MUST be rejected because it reads files beside the input and the core does no I/O. [just gen-check]
- lint-20: The mermaid-lint severities MUST map `warn` to `warning`, `error` to `error`, and `off` to `off`, and the four rows with `error` MUST be `duplicate-ids`, `eventmodeling-undefined-frame`, `venn-no-sets`, and `frontmatter-must-be-first`. [just gen-check]
- lint-21: A mermaid-lint code MUST map its scope column to a kind through the `aliases` arrays of `spec/data/kinds.json`: a single-kind scope gives `<kind>/<name>`, `flowchart / graph` and `graph` give `flowchart/<name>`, `all` gives `common/<name>`, and `<name>` is the upstream id without its leading `<kind>-` when the id starts with the kind id and a hyphen. [just gen-check]

    - `duplicate-ids` (flowchart / graph) gives `flowchart/duplicate-ids`
    - `xychart-missing-x-axis` gives `xychart/missing-x-axis`
    - `gitgraph-duplicate-commit-id` gives `gitgraph/duplicate-commit-id`
    - `no-experimental` (all) gives `common/no-experimental`

- lint-22: The mermaid-lint suppression rows MUST map `suppression-unknown-rule` to `meta/unknown-rule`, `suppression-unused` to `meta/unused-suppression`, and `suppression-malformed` to `meta/malformed-suppression`; all three MUST be `warning` with fix `none` and live in `common.json`. [just gen-check]
- lint-23: When a mapped code already exists, the later row MUST be `rejected` with the reason `duplicate of <code>`. [just gen-check]
- lint-24: Every maid code that is a bullet under a heading of `errors.md` MUST be adopted as a syntax row, including codes that the autofix matrix does not list; the `When` line MUST become `summary`, the `Hint` line MUST become `help`, and a one-line reason in the words of this project MUST become `rationale`. [just gen-check]
- lint-25: A maid code prefix MUST map `FL` to `flowchart`, `PI` to `pie`, `SE` to `sequence`, `ST` to `state`, `CL` to `class`, and `GEN` to `common`; the rest of the code MUST be lower-cased and keep its hyphens; `source` MUST be `maid:<CODE>`. [just gen-check]

    - `FL-ARROW-INVALID` gives `flowchart/arrow-invalid`
    - `SE-QUOTE-UNCLOSED` gives `sequence/quote-unclosed`

- lint-26: A maid row MUST have severity `error`, except `SE-QUOTE-UNCLOSED`, `SE-LABEL-ESCAPED-QUOTE`, and `SE-LABEL-DOUBLE-IN-DOUBLE`, which MUST have severity `warning`, and `--deny-warnings` MUST be the only escalation because there is no strict mode. [just gen-check]
- lint-27: The maid autofix column MUST map `Safe` to `fix_safety` `safe`, `All` to `unsafe`, and `None` or a missing matrix row to `none`; a code listed twice MUST use `All`; the fix title MUST be the "What maid changes" text, written as an imperative. [just gen-check]
- lint-28: The maid rows `GEN-HEADER-INVALID`, `SE-HEADER-MISSING`, `CL-HEADER-MISSING`, and `ST-HEADER-MISSING` MUST be `rejected` because a missing or unknown header is `common/unknown-diagram-kind`, and `FL-STRICT-LABEL-QUOTES-REQUIRED` MUST be `rejected` because it applies in strict mode only. [just gen-check]
- lint-29: The registry MUST add `common/acc-title-missing` and `common/acc-descr-missing` with `source` `own` and default severity `off`; `common/acc-title-missing` MUST report a block with no `accTitle:` line and `common/acc-descr-missing` MUST report a block with no `accDescr:` line, each with the header keyword as its span. [just go-check]
- lint-30: Each maid invalid fixture under `corpus/<kind>/maid/invalid/` MUST produce at least one diagnostic: error severity when the upstream verdict is reject, else a lint warning. [just go-check: TestMaidInvalidDiagnosed]

## Suppression comments

- lint-31: A suppression directive MUST be one per line, after optional spaces or tabs, in one of the four Mermaid forms below or the `emd-disable-file` form in a Markdown host outside fenced blocks, and any other `%%` line MUST be an ordinary comment. [just go-check: TestSuppression]

    ```
    %% emd-disable-next-line CODES: reason
    %% emd-disable CODES: reason
    %% emd-enable CODES
    %% emd-disable-diagram CODES: reason
    ```

    ```
    <!-- emd-disable-file CODES: reason -->
    ```

- lint-32: `CODES` MUST be one or more registry codes separated by `,`, with one space after a comma allowed; the list MUST end at the `:`; wildcards MUST NOT be used; directives MUST sit below any YAML frontmatter. [just go-check: TestSuppression]
- lint-33: `reason` MUST be the text after `:` with spaces trimmed, it MUST be present and MUST NOT be empty, and `emd-enable` MUST take no reason. [just go-check: TestSuppression]
- lint-34: The scope of each directive MUST be as follows. [just go-check: TestSuppression]

    - `emd-disable-next-line` covers the physical line right after the directive line; blank and comment lines are not skipped; for a multi-line statement it covers only diagnostics whose span starts on that first line.
    - `emd-disable` covers from the directive to the `emd-enable` that lists the same code, or to the end of the diagram block.
    - `emd-disable-diagram` covers the whole diagram block.
    - `emd-disable-file` covers the whole Markdown document.

- lint-35: A code MUST have at most one open `emd-disable`; `emd-enable` MUST close the open disable of each code it lists; an `emd-enable` for a code that is not open, and an `emd-disable` for a code that is already open, MUST be malformed. [just go-check: TestSuppression]
- lint-36: A well-formed directive MUST be used when it suppresses at least one diagnostic whose span starts inside its scope, and a well-formed directive that suppresses nothing MUST be reported as `meta/unused-suppression` (warning) with its directive line as span. [just go-check: TestSuppression]
- lint-37: `meta/unknown-rule` (warning) MUST be reported on each unknown code token, and the other codes of that directive MUST still apply. [just go-check: TestSuppression]
- lint-38: `meta/malformed-suppression` (warning) MUST be reported on the directive line for a missing reason, an empty code list, a code that cannot be suppressed, or an `emd-enable` or `emd-disable` that breaks the rule of lint-35, and a malformed directive MUST apply nothing. [just go-check: TestSuppression]
- lint-39: Error-severity syntax rows (diagnostics from the parser) and every `meta/*` diagnostic MUST NOT be suppressible, and a directive that names one of them MUST be malformed. [just go-check: TestSuppression]

## Configuration file

- lint-40: `emd.json` MUST have the shape below, and only the `lint` object MUST be read in this version. [just go-check: TestEmdJSON]

    ```
    {"lint":{"select":[..],"ignore":[..],"severity":{"code":"error|warning|info|off"}},"mermaid":{...upstream config...}}
    ```

- lint-41: Any other top-level key, invalid JSON, or a wrong type MUST exit 2 with the `invalid emd.json PATH: MESSAGE` message of spec/cli.md. [just go-check: TestEmdJSON]
- lint-42: Precedence per key MUST be that a flag replaces the file value of the same key and the file replaces the default; `--select` and `--ignore` MUST replace the file's lists; a missing key MUST take its default. [just go-check: TestEmdJSON]
- lint-43: The effective rule set MUST be built as follows. [just go-check: TestEmdJSON]

    - Start from `select` when present, otherwise from every rule whose default severity is not `off`.
    - Add each code in `severity` whose value is not `off`.
    - Remove each code whose `severity` value is `off`, and each code in `ignore`.
    - A `severity` value replaces the row's default severity for that code.

- lint-44: Syntax rows MUST ignore `select`, `ignore`, and `severity`. [just go-check]
- lint-45: An unknown code in any list MUST exit 2 with the unknown-code message of spec/cli.md. [just go-check: TestEmdJSON]
- lint-46: The `mermaid` key MUST stay reserved for the upstream config object and no command MAY read it in this version; `render -c FILE` MUST be the only input for `LayoutOptions.Config`, and `render` MUST NOT read `emd.json`. [just go-check: TestEmdJSON]
- lint-47: The JSON keys `lint.select`, `lint.ignore`, and `lint.severity` MUST fill `LintConfig.Select`, `LintConfig.Ignore`, and `LintConfig.Severity`; an empty or nil `Select` MUST mean absent, so `select: []` selects the default set; `Off` MUST have no JSON key, the loader MUST fill it with the codes whose `severity` value is `off`, and no flag sets it; a library caller MAY set `Off` directly; Rust uses the same fields in snake_case. [just go-check: TestEmdJSON]

## Fix safety

- lint-48: A `safe` fix MUST NOT change the meaning of the rendered diagram, an `unsafe` fix MAY change it, and a row with `fix_safety` `none` MUST have no fix. [just go-check]
- lint-49: `--fix` MUST apply safe fixes, and `--unsafe-fixes` MUST apply safe and unsafe fixes and MUST require `--fix`; without `--fix` it MUST be a usage error with the message of spec/cli.md. [just go-check]
- lint-50: A suppressed diagnostic MUST NOT be fixed. [just go-check: TestSuppression]

## Fix application

- lint-51: `ApplyFixes(src, cfg, max)` (Rust `apply_fixes`) MUST take `max` as `FixSafe` for `--fix` and `FixUnsafe` for `--unsafe-fixes`; each pass MUST parse `Document.Source()`, MUST compute the step 1 diagnostics and the step 2 to 4 diagnostics with the same `cfg`, MUST read suppressions from the text of that pass, and MUST take fixes from both lists. [just rust-check: apply_fixes]
- lint-52: For each diagnostic in output order, the engine MUST choose the first Fix in fix order whose safety is within `max`; fix order MUST be the order in which the rule function emits the fixes of one diagnostic, and the registry MUST NOT reorder fixes. [just rust-check: apply_fixes]
- lint-53: The engine MUST sort the chosen fixes' edits by span start, then span end, then fix order; it MUST drop every fix that has an edit starting before the end of an earlier kept edit; it MUST apply the kept edits in one step and then re-lint. [just rust-check: apply_fixes]
- lint-54: Fixing MUST repeat until a pass applies no fix, with a limit of 10 passes. [just rust-check: apply_fixes]
- lint-55: The engine MUST compare the multiset of `(code, span start)` over the error-severity diagnostics after a pass with the multiset before it; when the after-multiset holds an element the before-multiset does not hold, that pass MUST be discarded, fixing MUST stop, and the output MUST be the text before the pass. [just rust-check: apply_fixes]
- lint-56: `applied` MUST count the fixes applied in accepted passes. [just rust-check: apply_fixes]
- lint-57: For every registry row whose `fix_safety` is not `none`, at least one golden case MUST produce a fix, and applying that fix MUST remove the diagnostic. [just go-check: TestDiagnosticSpansAndFixes]

## Output formats

- lint-58: The output formats MUST be `text`, `json`, `sarif`, and `github`, selected by `--output-format` with default `text`, and each format MUST report the diagnostics after suppression and fixes. [just go-check]
- lint-59: The `json` output MUST be the document of spec/diagnostics.md (schema v1). [just go-check: TestLintGolden]
- lint-60: The `sarif` output MUST follow spec/diagnostics.md, including its level mapping. [just go-check: TestLintGolden]
- lint-61: The `github` output MUST follow spec/diagnostics.md, including its level mapping. [just go-check: TestLintGolden]

## Golden cases

- lint-62: The golden cases MUST be exactly the five rows of the table below, with no other case; each case MUST be `spec/golden/lint/<case>.mmd` with expected `<case>.text`, `<case>.json`, `<case>.sarif`, and `<case>.github`; in a Source, `\n` is a line break. [just go-check: TestLintGolden]

    |Case|Source|Rule code|Severity|Covers|
    |---|---|---|---|---|
    |`error-duplicate-ids`|`flowchart LR\n  A[Start] --> B[End]\n  A[Begin] --> C[End]`|`flowchart/duplicate-ids`|`error`|Error severity. Fix: none.|
    |`warning-quote-unclosed`|`sequenceDiagram\n  participant "Bob\n  A->>Bob: hi`|`sequence/quote-unclosed`|`warning`|Warning severity. Fix: unsafe. `--fix` skips it; `--fix --unsafe-fixes` applies it.|
    |`safe-fix-arrow-invalid`|`flowchart LR\n  A -> B`|`flowchart/arrow-invalid`|`error`|Error severity. Safe fix: `->` becomes `-->`.|
    |`unsafe-fix-end-without-subgraph`|`flowchart TD\n  A --> B\n  end`|`flowchart/end-without-subgraph`|`error`|Error severity. Unsafe fix: the stray `end` line is removed.|
    |`suppressed-duplicate-ids`|`flowchart LR\n  A[Start] --> B[End]\n  %% emd-disable-next-line flowchart/duplicate-ids: ids collide upstream\n  A[Begin] --> C[End]`|`flowchart/duplicate-ids`|none (suppressed)|Suppression: the directive removes the duplicate-ids error on line 4.|

- lint-63: The Go and Rust golden tests MUST compare their output with the golden files byte for byte. [just rust-check: lint_golden]
- lint-64: `flowchart/duplicate-ids` MUST report the later declaration, with its span on the id token of the later node statement and one related span on the id token of the first declaration with the message `first declared here`, and the first and last golden cases MUST cover a related span this way. [just go-check: TestLintGolden]
- lint-65: A golden run MUST be `emd lint --no-config --color never --output-format text <case>.mmd`, run inside the golden directory. [just go-check: TestLintGolden]
- lint-66: No rule MUST have the default severity `info`, so no golden case has it; `TestSeverityOverride` and `severity_override` MUST set one rule to `info` through an `emd.json` and compare the output with `<case>.info.txt` of the `error-duplicate-ids` case. [just go-check: TestSeverityOverride]
- lint-67: The golden case `warning-quote-unclosed` MUST get its diagnostic from the sequence parser under seqgrammar-55, in `check` and in `lint`, and its text, json, sarif, and github outputs MUST be byte-identical in Go and Rust. [just go-check: TestLintGolden]
