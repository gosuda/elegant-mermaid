# Command line interface

This file fixes the `emd` command line: the subcommands, invocation, help, defaults, streams, exact messages, output rules, the `explain` subcommand, configuration files, and file handling.

## Subcommands

- cli-01: The CLI MUST expose the six subcommands with the synopsis below. [just go-check]

    ```
    emd render  [INPUT] [-i INPUT] [-o OUTPUT] [-e svg|png|text] [-t THEME] [-b BACKGROUND] [-s SCALE]
                [--charset unicode|ascii] [--color auto|always|never] [--width COLS]
                [--svg-text font|paths] [--icon-pack FILE]... [-c CONFIG] [-a ARTEFACT_DIR]
    emd check   [PATH...] [--output-format text|json|sarif|github] [--color auto|always|never]
    emd lint    [PATH...] [--fix] [--unsafe-fixes] [--select CODES] [--ignore CODES]
                [--deny-warnings] [--output-format text|json|sarif|github] [--lint-config FILE] [--no-config]
                [--color auto|always|never]
    emd view    INPUT [-t THEME] [--graphics auto|kitty|iterm|sixel|cells] [--color auto|always|never]
    emd layout  [INPUT] [--profile vector|cell] [--stage model|layout] [--metrics]
    emd explain CODE [--output-format text|json]
    ```

## Invocation

- cli-02: `emd` without a subcommand MUST print help to stderr and exit 2. [just go-check]
- cli-03: `-h` and `--help` MUST print help to stdout and exit 0. [just go-check]
- cli-04: `--version` MUST print `emd VERSION`, for example `emd 0.1.0`, to stdout and exit 0. [just parity]
- cli-05: Flags MAY come before or after positionals, and `--` MUST end flags. [just go-check]
- cli-06: `render` MUST accept `-i INPUT`, listed in `emd render --help`; a positional `INPUT` and `-i INPUT` MUST be mutually exclusive, with the message `pass input either as INPUT or with -i, not both` and exit 2. [just go-check]
- cli-07: `render` and `layout` without `INPUT`, or with `-`, MUST read stdin; when stdin is a terminal they MUST print `missing INPUT; pass a path or pipe Mermaid source` to stderr and exit 2. [just go-check]
- cli-08: `view` MUST need an existing readable path and MUST reject stdin with `view requires a readable file path; stdin is not supported` and exit 2. [just go-check]
- cli-09: `check` and `lint` without paths MUST scan `.` recursively for `.mmd` and `.mermaid` files and for `.md`, `.markdown`, and `.mdx` hosts, skipping hidden directories, `node_modules`, and `target`. [just go-check]
- cli-10: An explicit `-` MUST read Mermaid source from stdin. [just go-check]
- cli-11: An explicit path, file or directory, that holds no supported file MUST make `check` and `lint` print `no Mermaid files found in PATH` to stderr and exit 2, and the implicit scan of `.` that finds no supported file MUST print `no Mermaid files found in .` to stderr and exit 0. [just go-check]
- cli-12: The hidden forms below MUST exist and MUST be omitted from help output; `--stage` MUST appear in the synopsis and MUST be omitted from `emd layout --help`, and `--stage layout` MUST be the default. [just go-check]

    - `emd kernel-eval FILE` evaluates kernel cases for `just kernel-diff`; the case format is fixed in spec/geometry-kernel.md.
    - `emd layout --metrics --dump FILE` reads one canonical layout dump of any origin and prints the metric line; the keys are fixed in spec/quality-metrics.md.
    - `emd view INPUT --script FILE` replays a script; the grammar is fixed in spec/viewer.md.
    - `emd layout --stage model` prints the model-stage dump of spec/model-dump.md.

## Help

- cli-13: Root help MUST print one line per subcommand, with the wording below. [just go-check]

    - `render`, Render Mermaid as SVG, PNG, or terminal text
    - `check`, Check syntax and semantics without changing files
    - `lint`, Check lint rules and optionally apply fixes
    - `view`, Watch and display a diagram in the terminal
    - `layout`, Print canonical layout data
    - `explain`, Explain a diagnostic code

- cli-14: Each subcommand help MUST state the purpose, the accepted values and default of every flag except the hidden forms, and one example from the list below. [just go-check]

    - `emd render demo.mmd -e text`
    - `emd check docs/`
    - `emd lint --fix demo.mmd`
    - `emd view demo.mmd`
    - `emd layout demo.mmd --profile cell`
    - `emd explain flowchart/unexpected-token`

## Defaults

- cli-15: The flag defaults MUST be as follows. [just go-check]

    - `-e` follows the output format rule of cli-23.
    - Without `-t`, the theme is `elegant-light`, with one exception: for text output (`-e text` and `view`) it is `elegant-dark` when `COLORFGBG` parses and its background field is 0 to 6 or 8; the terminal is never queried; a given `-t` always wins.
    - `-s` defaults to 2.
    - `-b` defaults to the theme `bg` token.
    - `--charset` defaults to `unicode`.
    - `--color` defaults to `auto`.
    - `--width` defaults to 0.
    - `--svg-text` defaults to `font`.
    - `--graphics` defaults to `auto`.
    - `layout --profile` defaults to `vector`.
    - `render -e text` uses the `cell` profile.
    - `check`, `lint`, and `explain` default to `--output-format text`.
    - `--select`, `--ignore`, `-c`, `--lint-config`, `-a`, and `--icon-pack` have no default.
    - Without `--select`, `lint` uses the default rule set.

- cli-16: An invalid flag value MUST exit 2 with `invalid value VALUE for FLAG; expected one of: LIST`; for a numeric flag, LIST is the accepted range: `1..8` for `-s`, and `non-negative integers` for `--width`. [just go-check]
- cli-17: `--select` and `--ignore` MUST take comma-separated codes. [just go-check]

## Streams

- cli-18: `render` and `layout` MUST write their result to stdout unless an output option writes files, and MUST write diagnostics to stderr; `check` and `lint` MUST write diagnostics to stdout in the selected format, except `lint --fix -`, which MUST write the fixed source to stdout and text diagnostics to stderr. [just go-check]
- cli-19: Usage errors, I/O errors, and notes MUST go to stderr, and stdout MUST NOT mix a result with diagnostics. [just go-check]
- cli-20: `--color` MUST control terminal text and text diagnostics only, never SVG, PNG, or machine formats; `layout` MUST have no `--color`; `layout --metrics` MUST write the metric line whose keys, order, and meaning are fixed in spec/quality-metrics.md. [just go-check]

## Exact messages

- cli-21: The messages below MUST be printed to stderr with the exact text shown. [just go-check]

    - `missing INPUT; pass a path or pipe Mermaid source`
    - `pass input either as INPUT or with -i, not both`
    - `view requires a readable file path; stdin is not supported`
    - `cannot write PNG to a terminal; use -o FILE.png or redirect stdout to a file`
    - `rendering Markdown input requires -o OUTPUT or -a ARTEFACT_DIR`
    - `lint --fix - supports only text diagnostics; remove --output-format or pass a file path`
    - `no Mermaid blocks found in INPUT; add a fenced code block labelled mermaid`
    - `unknown diagnostic code: CODE; use a code printed by emd check or emd lint`
    - `no Mermaid files found in PATH`, for an explicit path, and `no Mermaid files found in .`, for the implicit scan of `.`
    - `invalid value VALUE for FLAG; expected one of: LIST`
    - `--unsafe-fixes requires --fix`
    - `invalid emd.json PATH: MESSAGE`
    - `cannot read FILE: OS error text`
    - `--metrics needs --profile vector`
    - `unknown flag FLAG; run emd COMMAND --help`
    - `bad case line N`, for `emd kernel-eval`; the case format is fixed in spec/geometry-kernel.md
    - `cannot infer the output format from PATH; pass -e`

- cli-22: `no Mermaid blocks found in INPUT; add a fenced code block labelled mermaid` MUST exit 1, the two `no Mermaid files found` messages MUST follow the empty scan rule of cli-11, and every other message in the list of cli-21 MUST exit 2. [just go-check]

## Output

- cli-23: The output format MUST be `-e` when given; else the extension of `-o` (`.svg`, `.png`, `.txt`); else `text` when stdout is a terminal and `svg` otherwise. [just go-check]
- cli-24: `-o` with no `-e`, with any other extension, or with no extension MUST exit 2 with `cannot infer the output format from PATH; pass -e`, and PNG to a terminal stdout MUST be refused with exit 2. [just go-check]
- cli-25: `--width 0` MUST be the natural canvas width; a positive width MUST be a wrapping and packing target, never a crop, and the output MAY exceed it. [just go-check]
- cli-26: A path ending `.md`, `.markdown`, or `.mdx` MUST be a host document, and `check` and `lint` MUST map every diagnostic to host positions. [just go-check]
- cli-27: `render` of a host MUST need `-o` or `-a`, and the output naming MUST be as follows. [just go-check]

    - `-o IMAGE` writes `<stem>-N<ext>` per block.
    - `-a DIR` alone writes `<input-stem>-N.<ext>` into `DIR`.
    - `-o HOST.md` writes a copy of the host in which each block is an image link (alt text is the diagram `accTitle`, else `diagram`), with images in `-a`, default `<HOST-stem>.assets`; the image format is `svg` or `png`, default `svg`.

- cli-28: A host with zero Mermaid blocks MUST exit 1 with `no Mermaid blocks found in INPUT; add a fenced code block labelled mermaid` and MUST write nothing. [just go-check]
- cli-29: `check` MUST report syntax and semantic diagnostics, and `lint` MUST report those plus lint rules. [just go-check]
- cli-30: `lint --fix` with file paths MUST rewrite the files and print the remaining diagnostics; `lint --fix -` MUST write the fixed source to stdout and text diagnostics to stderr, and MUST reject other output formats with exit 2. [just go-check]
- cli-31: `--fix` MUST apply safe fixes, and `--unsafe-fixes` MUST apply safe and unsafe fixes; without `--fix` it MUST be a usage error. [just go-check]
- cli-32: `--output-format json` MUST write the document of spec/diagnostics.md (schema v1). [just parity]
- cli-33: The exit codes MUST be as follows. [just go-check]

    - `0`: no error-severity diagnostic.
    - `1`: at least one error-severity diagnostic, or any warning under `--deny-warnings`.
    - `2`: usage error or I/O failure.

- cli-34: A `render` or `layout` whose document has error-severity diagnostics MUST write them to stderr as text and exit 1, and `TooLarge`, `Overflow`, and raster pixel-size or encode errors MUST print the error text to stderr and exit 1; the texts are `model exceeds the limit of LIMIT; actual ACTUAL`, `arithmetic overflow`, `image is too large: WxH pixels`, and `PNG encoding failed: MESSAGE`, and the Go and Rust binaries MUST print the same bytes. [just go-check: TestErrorPaths]
- cli-35: Invalid option values MUST print the error text to stderr and exit 2: an unknown theme name (`-t`), an invalid `-b` colour, `-c` text that does not parse, and a malformed `--icon-pack` file. [just go-check]
- cli-36: Colour MUST be resolved as follows. If a caller supplies terminal environment values, the CLI MUST use those values for colour and theme decisions. The CLI MUST NOT replace them with process environment values. [just go-check]

    - `--color always` wins.
    - Under `auto`, in order: non-empty `NO_COLOR` turns colour off; `CLICOLOR_FORCE=1` or non-empty, non-zero `FORCE_COLOR` turns it on; `CLICOLOR=0` or `TERM=dumb` turns it off; else colour is on only when stdout is a terminal.
    - Machine formats never carry colour.
    - Depth: `COLORTERM=truecolor` or `24bit` gives truecolor; `TERM` ending `256color` gives 256; else 16.
    - `NO_COLOR` does not change SVG or PNG.

## Explain

- cli-37: `emd explain CODE` MUST print the registry row for `CODE` to stdout and exit 0, and the text output MUST have one `key: value` line for each key in the order below. [just go-check]

    - `code`
    - `kind`, the kind id from the code prefix, or `common` when the prefix is not a kind id (for example `common`, `meta`, `config`, or `source`)
    - `severity`
    - `fix_safety`
    - `summary`
    - `help` (may be empty)
    - `rationale`
    - `suppression`, the comment template `%% emd-disable-next-line CODE: reason` with `CODE` replaced by the code

- cli-38: `--output-format json` MUST print one object with the same keys in the same order. [just go-check]
- cli-39: An alias MUST print the row of its current code, and an unknown code MUST print `unknown diagnostic code: CODE; use a code printed by emd check or emd lint` and exit 2. [just go-check]

## Configuration

- cli-40: `emd.json` MUST be a JSON object whose `lint` member holds the lint settings `select` (list of codes), `ignore` (list of codes), and `severity` (map from code to `error`, `warning`, `info`, or `off`); entries valued `off` MUST go to `LintConfig.Off` and the other entries to `LintConfig.Severity`; the `mermaid` key MUST stay reserved for the upstream config object; the file format and the handling of other top-level keys are fixed in spec/lint.md. [just go-check: TestEmdJSON]
- cli-41: `lint` MUST find `emd.json` by walking up from the input's directory to the first `emd.json` or the filesystem root; for stdin the walk MUST start in the working directory; `--no-config` MUST skip the search; `--lint-config FILE` on `lint` MUST name the file and skip the search. [just go-check: TestEmdJSON]
- cli-42: On `render`, `-c FILE` MUST read upstream config text into `LayoutOptions.Config`, and `render` MUST NOT read `emd.json`. [just go-check]
- cli-43: Precedence per key MUST be that a flag replaces the file value of the same key and the file replaces the default; `select` MUST replace the default rule set, and `ignore` MUST remove codes from it. [just go-check: TestEmdJSON]

## Files

- cli-44: Outputs MUST overwrite existing files, and each output MUST be written to a temporary file in the same directory and then renamed over the target. [just go-check]
- cli-45: Directory walks MUST visit paths in byte-wise path order and MUST NOT follow symbolic links. [just go-check]

## Failures

- cli-46: When the CLI cannot read a file, it MUST print `cannot read FILE: TEXT` to stderr and MUST exit 2. [just go-check: TestErrorPaths]
- cli-47: In cli-46, FILE MUST be the path as given, or `<stdin>` for standard input. [just go-check: TestErrorPaths]
- cli-48: In cli-46, TEXT MUST be the message of the operating system for the failure, in lower case, without the operation, the path, or the error number, for example `no such file or directory`, `permission denied`, or `is a directory`. [just go-check: TestErrorPaths]
- cli-49: When the CLI cannot write a file, it MUST print `cannot write FILE: TEXT` to stderr and MUST exit 2. [just go-check: TestErrorPaths]
- cli-50: In cli-49, FILE MUST be the target path as given, MUST NOT be the temporary file, and TEXT MUST follow cli-48; a target that is a directory MUST give `is a directory`. [just go-check: TestErrorPaths]
- cli-51: When `render`, `layout`, `view`, or `kernel-eval` receives more than one INPUT, it MUST print `COMMAND accepts one INPUT` to stderr, with the name of the command in place of `COMMAND`, and MUST exit 2. [just go-check: TestErrorPaths]
- cli-52: `emd kernel-eval -h` and `emd kernel-eval --help` MUST print `Usage: emd kernel-eval FILE` and one LF to stdout and MUST exit 0. [just go-check: TestErrorPaths]
- cli-53: `emd kernel-eval` with a flag it does not know MUST print `unknown flag FLAG; run emd kernel-eval --help` and MUST exit 2. [just go-check: TestErrorPaths]
- cli-54: `emd kernel-eval` MUST read stdin when it has no FILE or when FILE is `-`. [just go-check: TestKernelEvalInputs]
- cli-55: When `emd layout --metrics --dump FILE` cannot decode FILE as a canonical layout dump, it MUST print `FILE: malformed layout dump: REASON` to stderr and MUST exit 2, with REASON as spec/layout-dump.md fixes it. [just go-check: TestErrorPaths]
- cli-56: When `render -c FILE` finds config text that fails, it MUST print `FILE: invalid config: MESSAGE` to stderr and MUST exit 2. [just go-check: TestErrorPaths]
- cli-57: In cli-56, MESSAGE MUST be `invalid UTF-8 at byte OFFSET` when the text is not valid UTF-8, else the message of the first diagnostic of the config reader, else `config must be a mapping` when the root is not a mapping, else the message of the first diagnostic of the look reader; blank text MUST be valid. [just go-check: TestErrorPaths]
- cli-58: When `render --icon-pack FILE` finds a pack that is not valid, it MUST print `FILE: malformed icon pack: REASON` to stderr and MUST exit 2, with REASON as spec/library-surface.md fixes it. [just go-check: TestErrorPaths]
- cli-59: `emd view` MUST check its arguments in this order: the number of paths, the stdin rule of cli-08, the value of `--graphics`, the value of `--color`, the theme, and then it MUST read FILE. [just go-check: TestErrorPaths]
- cli-60: The Rust tests `error_paths` and `view_script_errors` MUST check the same cases, with the same messages, as `TestErrorPaths` and `TestViewScriptErrors`. [just rust-check: error_paths]
- cli-61: Every command except `kernel-eval` MUST read an argument as a flag when it starts with `-` and is neither `-` nor `--`; one leading dash and two leading dashes MUST name the same flag, so `-t`, `--t`, `-color` and `--color` are all flags, and an argument with three or more leading dashes MUST print `unknown flag ARG; run emd COMMAND --help` and exit 2. [just go-check: TestFlagSpellings]
- cli-62: A flag that takes a value MUST take it from the text after the first `=` of its argument, even when that text is empty, and else from the next argument whatever that argument looks like; when no next argument exists, it MUST print `missing value for ARG`, with ARG as written, and exit 2. A flag that is not in the command MUST be rejected with the message of cli-61 before any value is read. [just go-check: TestFlagSpellings]
- cli-63: A switch (`lint --fix`, `--unsafe-fixes`, `--deny-warnings`, `--no-config`, and `layout --metrics`) MUST take no next argument, MUST mean true without `=`, and MUST accept after `=` exactly `1`, `t`, `T`, `true`, `TRUE`, `True`, `0`, `f`, `F`, `false`, `FALSE`, and `False`; any other text MUST print `invalid value TEXT for --NAME; expected one of: true, false`, with the long spelling of the name, and exit 2. [just go-check: TestFlagSpellings]
- cli-64: `view --script` and `view --script=` with an empty value MUST name a script with an empty path, and so MUST print `cannot read : no such file or directory` and exit 2, and an empty value of any other flag MUST follow the rule of that flag. [just go-check: TestFlagSpellings]
- cli-65: The Rust test `flag_spellings` MUST check the same spellings and failures, with the same messages, as `TestFlagSpellings`. [just rust-check: flag_spellings]
- cli-66: A `layout`, `render`, or `view` failure that comes from the model, a limit, arithmetic, or the raster back end MUST exit 1 in both binaries, and a failure that comes from an option value or from a file the command reads MUST exit 2 in both binaries. [just go-check: TestErrorPaths]
