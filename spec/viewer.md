# Viewer

This file fixes the terminal viewer: its keys, its states, its pixel geometry, its pure frame function, its script replay, and its pseudo-terminal check.

## Invocation

- viewer-01: `emd view FILE` MUST reject stdin with `view requires a readable file path; stdin is not supported` on stderr and exit 2. [just go-check]
- viewer-02: When `FILE` cannot be read at startup, `emd view` MUST exit 2 with `cannot read FILE: OS error text`. [just go-check]
- viewer-03: The viewer MUST re-render when `FILE` changes. [just go-check: TestViewPTY]

## Keys

- viewer-04: The viewer MUST read the keys of this table, and Escape and the arrow keys MUST be read in raw mode, where a lone ESC byte is Escape when no byte follows within 50 ms. [just go-check]

  |Key|Effect|
  |---|---|
  |arrows, `h` `j` `k` `l`|Pan one step: left, down, up, right. Cells: one column or one row. Pixel modes: `cell_w` px horizontally or `cell_h` px vertically, in scaled image pixels (Geometry). Offsets are clamped.|
  |`+`, `-`|Pixel modes only. `z` is the zoom percent, limits 10 to 800. `+` sets `z = min(800, floor(z * 5 / 4))`. `-` sets `z = max(10, floor(z * 4 / 5))`. Either key leaves fit mode. Cells ignore both keys.|
  |`0`|Pixel modes: enter fit mode and compute `z` (Geometry). Cells: set both offsets to 0.|
  |`n`, `p`|Next and previous block of a Markdown host. `n` after the last block goes to the first; `p` before the first goes to the last. The block index is 1-based in the status. Non-Markdown input: no effect. Emits `Edited`. A Markdown host with no Mermaid block shows `no Mermaid blocks found in PATH; add a fenced code block labelled mermaid` in place of the empty message.|
  |`t`|Cycle the nine built-in themes in this order: `elegant-light`, `elegant-dark`, `github-light`, `github-dark`, `catppuccin-latte`, `catppuccin-mocha`, `nord`, `solarized-light`, `solarized-dark`, then back to `elegant-light`. Each press moves to the next name after the current theme. An upstream theme set with `-t` is not in the cycle, so the next press moves to `elegant-light`. The order does not come from `spec/data/themes.json`. Emits `Edited`.|
  |`c`|Toggle `unicode` and `ascii`. Emits `Edited`.|
  |`g`|Cycle `cells`, `kitty`, `iterm`, `sixel`, then `cells`. Emits `Edited`.|
  |`d`|Toggle the diagnostics panel.|
  |`?`|Toggle the key reference panel.|
  |`r`|Read `FILE` again and emit `Edited`. If `FILE` is missing, set watch lost.|
  |Escape|Close the open panel.|
  |`q`, Ctrl-C|Quit.|

- viewer-05: The key table MUST be closed: it holds every key the viewer accepts and no other. [just go-check]
- viewer-06: Opening one panel MUST close the other. [just go-check]
- viewer-07: The start values MUST be: the theme is the `-t` value, the charset is `unicode`, the graphics mode is the probe result or `--graphics`, pixel modes start in fit mode, and cells start with both offsets at 0. [just go-check]

## Viewer states

- viewer-08: The viewer MUST draw a status row at row `H - 2` and a key row at row `H - 1`, with the parts, the text, and the layout that `## Frame` fixes. [just go-check]
- viewer-09: An empty input MUST show `Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes`, where the source is empty when it holds only whitespace, frontmatter, directives, or comments as the `common/empty-source` rule states, and the displayed revision of an empty source MUST carry the diagnostic `common/empty-source` as an error with span 0..0. [just go-check: TestViewScripts]
- viewer-10: An unknown kind MUST open the diagnostics panel with `common/unknown-diagram-kind` as an error. [just go-check: TestViewScripts]
- viewer-11: A parse error on the first load MUST show the diagnostics panel and `No valid revision yet; fix the source or press r`. [just go-check: TestViewScripts]
- viewer-12: An error on a later revision MUST keep the last good frame and mark the status `STALE revision N; latest revision M has errors`, where N is the revision of the last good frame and M is the displayed revision, which equals the latest revision when the scheduler is idle. [just go-check: TestViewScripts]
- viewer-13: Pixel modes MUST start fitted and cells MUST start at the origin, and a diagram larger than the viewport MUST add `NxM cells; pan available` to the status. [just go-check: TestViewScripts]
- viewer-14: Panning MUST be clamped so that content cannot be lost. [just go-check]
- viewer-15: A resize MUST keep the centre and the zoom, MUST re-clamp the offsets, and MUST recompute the fit only in fit mode; it MUST NOT emit an event and MUST NOT start a render. [just go-check: TestViewScripts]
- viewer-16: Without colour the viewer MUST keep textual severities and every control, and colour MUST be applied by the terminal writer only, never to frame text. [just go-check]
- viewer-17: The watcher MUST watch the parent directory so that an atomic replace is seen, MUST ignore events for other names in that directory, and MUST coalesce file changes for 50 ms before it emits `Edited`. [just go-check: TestViewPTY]
- viewer-18: After a deletion the frame MUST stay, the status MUST show `WATCH LOST: recreate {path}; retrying` with `PATH` as given, and the viewer MUST poll every 500 ms until the file returns; that poll MUST emit `Edited` when the file is back. [just go-check: TestViewScripts]

## Geometry

- viewer-19: Pixel modes MUST compute these integers, where every division is integer division with truncation toward zero and all operands are non-negative: [just go-check]

  - `cell_w` and `cell_h` are the pixel size of one cell, which the probe sets, with the fallback 8 and 16.
  - `src_w` by `src_h` is the RGBA8 buffer of the displayed revision, rendered by `raster` at scale `-s`, and the viewer keeps it with the last good frame.
  - `W` and `H` are the terminal size in cells, `V = H - 2` is the viewport row count, `VW = W * cell_w`, and `VH = V * cell_h`.

- viewer-20: Fit MUST set `z = clamp(min(VW * 100 / src_w, VH * 100 / src_h), 10, 800)`. [just go-check]
- viewer-21: The scaled size MUST be `SW = (src_w * z + 99) / 100` and `SH = (src_h * z + 99) / 100`. [just go-check]
- viewer-22: The offsets in scaled pixels MUST satisfy `ox` in `0 .. max(0, SW - VW)` and `oy` in `0 .. max(0, SH - VH)`, and every change MUST clamp both. [just go-check]
- viewer-23: An axis where `SW < VW` or `SH < VH` MUST have offset 0 and MUST centre the image with `x0 = (VW - SW) / 2` or `y0 = (VH - SH) / 2`; every other axis MUST use `x0 = 0` or `y0 = 0`. [just go-check]
- viewer-24: The composite buffer MUST be one `VW` by `VH` RGBA8 buffer filled with the theme `bg` colour, where for output pixel `(x, y)` with `X = x - x0 + ox` and `Y = y - y0 + oy`, the pixel MUST be `src` at `(X * 100 / z, Y * 100 / z)` when `0 <= X < SW` and `0 <= Y < SH`, and MUST be `bg` otherwise. [just go-check]
- viewer-25: Sampling MUST be nearest-neighbour only. [just go-check]
- viewer-26: A resize MUST keep the centre with `ox' = ox + VW_old / 2 - VW_new / 2` and `oy'` by the same rule, then clamp, and cells MUST use the same rule with `W` and `V` in cells. [just go-check]
- viewer-27: The size text `NxM` MUST use `N` = content columns and `M` = content lines of the cell-profile text for cells, and `N = (SW + cell_w - 1) / cell_w` and `M = (SH + cell_h - 1) / cell_h` for pixel modes. [just go-check]
- viewer-28: The content MUST count as larger than the viewport when `N > W` or `M > V`, or in pixel modes when `SW > VW` or `SH > VH`. [just go-check]

## Frame

- viewer-29: `frame(state)` MUST be a pure function of the `ViewState` fields of this section, and it MUST read no clock, file, environment variable, or terminal. [just go-check: TestViewScripts]
- viewer-30: Go and Rust MUST return the same bytes for the same state and size. [just go-check: TestViewScripts]
- viewer-31: `ViewState` MUST hold the fields of this list, with these names in Go and their snake_case forms in Rust: [just go-check]

  - `path`: the path as given on the command line.
  - `width`, `height`: terminal size in cells, with `width >= 20` and `height >= 5`.
  - `kind`: the displayed revision's kind id, `unknown`, or none.
  - `block`: 1-based index and count for Markdown hosts, or none.
  - `mode`: `cells`, `kitty`, `iterm`, or `sixel`.
  - `fit`: boolean. `zoom`: integer percent.
  - `errors`, `warnings`: counts for the displayed revision.
  - `empty`: boolean.
  - `displayed`: revision number, 0 for none.
  - `frame_rev`: revision of the last good frame, 0 for none.
  - `panel`: `none`, `diagnostics`, or `keys`. `auto_panel`: boolean.
  - `diagnostics`: formatted lines of the displayed revision, as this section defines them.
  - `watch_lost`: boolean.
  - `text`: cell-profile lines of the last good frame in cells mode.
  - `content_w`, `content_h`, `offset_x`, `offset_y`: content size and offsets, in cells in cells mode.

- viewer-32: The frame MUST have `H` rows, each row MUST be exactly `W` Unicode scalar values, a row longer than `W` MUST be cut, a shorter row MUST be padded with spaces, and the output MUST be the rows in order each followed by one LF, with no CR byte and no escape byte. [just go-check: TestViewScripts]
- viewer-33: Rows `0` to `H - 3` MUST be the viewport of `V = H - 2` rows, row `H - 2` MUST be the status row, and row `H - 1` MUST be the key row. [just go-check: TestViewScripts]

### Viewport

- viewer-34: The viewport MUST use the first matching rule of this list: [just go-check]

  1. A panel is open: the panel rows.
  2. `empty` is set: the message `Empty diagram: add a Mermaid header such as flowchart TD; waiting for changes`, word-wrapped at `W`, where a word longer than `W` is split at `W`, in the first rows, and the other rows are blank.
  3. `mode` is `cells` and `frame_rev` is not 0: viewport row `r` shows line `offset_y + r` of `text`, from scalar `offset_x` for `W` scalars, and missing lines are empty.
  4. Otherwise: `V` blank rows, over which the terminal writer draws the pixel image.

### Status row

- viewer-35: The status row MUST hold these parts separated by ` | `, in this order: `PATH`, `MSG`, `KIND`, `MODE`, `ZOOM`, `E e errors W w warnings`, `REV r`. [just go-check: TestViewScripts]
- viewer-36: `KIND` MUST be `-` when `displayed` is 0 or `empty` is set, `unknown` for an unknown kind, and the kind id otherwise, and for a Markdown host the kind MUST be followed by ` k/n`. [just go-check: TestViewScripts]
- viewer-37: `MODE` MUST be the mode name. [just go-check]
- viewer-38: `ZOOM` MUST be `-` in cells, `fit` in fit mode, and `z%` with the zoom percent otherwise. [just go-check]
- viewer-39: `REV r` MUST be `r` equal to `displayed`, and `REV -` when `displayed` is 0. [just go-check]
- viewer-40: `MSG` MUST be omitted when empty, and otherwise MUST hold these parts in this order joined by ` | `: [just go-check]

  1. `WATCH LOST: recreate {path}; retrying` when `watch_lost` is set.
  2. When `displayed` is not 0 and `errors` is greater than 0: `No valid revision yet; fix the source or press r` if `frame_rev` is 0, otherwise `STALE revision {frame_rev}; latest revision {displayed} has errors`.
  3. `NxM cells; pan available` when the content is larger than the viewport.

- viewer-41: When the row has more than `W` scalars, the PATH field MUST be replaced by `...` followed by the last `k` scalars of `path`, where `k = W - (scalars in the row without PATH) - 3`, if `k >= 1`, and the row MUST then be cut to `W`. [just go-check: TestViewScripts]
- viewer-42: When `k` is below 1, the PATH field MUST be replaced by `...`. [just go-check: TestViewScripts]
- viewer-43: The key row MUST be `? help  q quit  d diagnostics  arrows/hjkl pan  0 fit`, cut or padded to `W`. [just go-check: TestViewScripts]

### Panels

- viewer-44: A panel of `W` columns and `V` rows with `V >= 3` MUST use these rows: [just go-check: TestViewScripts]

  - Row 0: `+- `, then the title, then ` `, then `-` repeated `W - len(title) - 5` times, then `+`. The titles are `Diagnostics` and `Keys`.
  - Rows `1` to `V - 2`: `| `, then the content padded to `W - 4`, then ` |`.
  - Row `V - 1`: `+`, then `-` repeated `W - 2` times, then `+`.

- viewer-45: The content MUST be cut to `W - 4` and MUST have `V - 2` slots; when it has more lines than slots, the first `V - 3` lines MUST be shown and the last slot MUST be `... N more`, where `N` is the number of lines not shown; unused slots MUST be blank. [just go-check: TestViewScripts]
- viewer-46: The diagnostics content MUST hold one line per diagnostic of the displayed revision, in JSON order, formatted `{severity} {code} {line}:{column} {message}` with the severity in lower case, and `No diagnostics` when there is none. [just go-check: TestViewScripts]
- viewer-47: The keys content MUST hold these lines in this order, one per line, verbatim: [just go-check: TestViewScripts]

  ```text
  arrows, hjkl    pan
  + -             zoom (pixel modes)
  0               fit / origin
  n, p            next, previous block
  t               cycle theme
  c               toggle charset
  g               cycle graphics mode
  d               diagnostics panel
  r               reload INPUT
  ?               this key reference
  Esc             close panel
  q, Ctrl-C       quit
  ```

### Display effect

- viewer-48: `Display(v)` MUST apply these steps in this order: [just go-check: TestViewScripts]

  1. `displayed = v`; `errors`, `warnings`, `diagnostics`, `kind`, `block`, and `empty` are set from `v`.
  2. If the result has a frame: `text`, `content_w`, `content_h`, and the pixel buffer are replaced, `frame_rev = v`, `z` is recomputed in fit mode, offsets are clamped, and the panel closes when `auto_panel` is set.
  3. If the result has no frame and `watch_lost` is clear, the diagnostics panel opens with `auto_panel` set when `v` has `common/unknown-diagram-kind`, or when `frame_rev` is 0 and `v` has an error other than `common/empty-source`.

## Script replay

- viewer-49: `emd view INPUT --script FILE` MUST replay scripted events without a terminal and without the watcher, then print the final frame to stdout with one row per line and exit 0. [just go-check: TestViewScripts]
- viewer-50: Replay MUST start at size 80 by 24, with graphics mode `cells`, the theme from `-t` or its default, and charset `unicode`, and it MUST read `INPUT` as the in-memory source and emit `Edited` once as the startup event. [just go-check: TestViewScripts]
- viewer-51: The script MUST use this grammar, one event per line, with lines ending in LF or CRLF, where a blank line and a line whose first non-space character is `#` MUST be ignored: [just go-check: TestViewScripts]

  ```text
  event     = "resize" SP W SP H
            / "key" SP KEY
            / "file-change" SP SRC
            / "file-create" SP SRC
            / "file-delete"
            / "settle"
  KEY       = one printable ASCII character other than space
            / "up" / "down" / "left" / "right" / "esc" / "ctrl-c"
  W, H      = 1*DIGIT, decimal, W >= 20, H >= 5
  SRC       = a path, relative to the directory of FILE unless absolute
  ```

- viewer-52: `resize W H` MUST set the size and emit no event. [just go-check: TestViewScripts]
- viewer-53: `key K` MUST have the same effect as the key table, and `key q` and `key ctrl-c` MUST end the replay so that later lines are not read. [just go-check: TestViewScripts]
- viewer-54: `file-change SRC` MUST replace the in-memory source with the bytes of `SRC` and MUST emit `Edited`. [just go-check: TestViewScripts]
- viewer-55: `file-create SRC` MUST do the same as `file-change` and MUST clear `watch_lost`. [just go-check: TestViewScripts]
- viewer-56: `file-delete` MUST set `watch_lost`, MUST leave the source unchanged, and MUST emit no event. [just go-check: TestViewScripts]
- viewer-57: `settle` MUST run renders until `inflight = 0`. [just go-check: TestViewScripts]
- viewer-58: Replay MUST bypass the watcher, so each `file-change` line MUST be one `Edited` with no 50 ms coalescing. [just go-check: TestViewScripts]
- viewer-59: Renders MUST run synchronously on the replay thread when a `settle` line is reached or the script ends, and a settle MUST loop while `inflight != 0`, where a set `cancelled` makes the pending render return `RenderAborted` without work and otherwise the render MUST read the in-memory source at that moment and return `RenderDone`. [just go-check: TestViewScripts]
- viewer-60: A `file-change A` then `file-change B` then `settle` MUST abort revision 1 and render revision 2. [just go-check: TestViewScripts]
- viewer-61: At the end of the script, replay MUST perform an implicit `settle` and MUST print `frame(state)` to stdout. [just go-check: TestViewScripts]
- viewer-62: An unknown verb, bad arguments, an unreadable `SRC`, or a size below the minimum MUST print `FILE:LINE: MESSAGE` to stderr and exit 2. [just go-check: TestViewScripts]
- viewer-63: The script matrix at 80 by 24 MUST compare the Go and Rust final frames byte for byte against `internal/cli/testdata/view/<case>.txt` for these cases: empty file; unknown kind; parse error on first load; parse error after a good revision; a diagram larger than the viewport; `resize 40 12`; `file-delete` then `file-create`; `key ?`. [just go-check: TestViewScripts]
- viewer-64: The Rust test `view_scripts` MUST compare the same cases with the same files byte for byte. [just rust-check: view_scripts]

## Pseudo-terminal check

- viewer-65: The pseudo-terminal check MUST use `script(1)` from util-linux, which is an ordinary test in `go-check` and in `rust-check`, and it MUST fail rather than skip when `script` is not on `PATH`. [just go-check: TestViewPTY]
- viewer-66: The check MUST create a temporary directory holding `a.mmd` with `flowchart LR` and `  A[alpha] --> B`. [just go-check: TestViewPTY]
- viewer-67: The check MUST start `script -q -e -f -c 'stty cols 80 rows 24; exec "$EMD_BIN" view --graphics cells --color never "$FILE"' /dev/null` with `FILE` in the environment and the pty input as stdin of the process. [just go-check: TestViewPTY]
- viewer-68: The check MUST wait up to 10 s for `alpha` on the output. [just go-check: TestViewPTY]
- viewer-69: The check MUST rewrite `a.mmd` with `A[beta]` and then with `A[gamma]`, two writes within 50 ms, and MUST wait up to 10 s for `gamma` on the output written after that rewrite. [just go-check: TestViewPTY]
- viewer-70: The check MUST write `q` to the process stdin, and the process MUST exit with status 0 within 10 s. [just go-check: TestViewPTY]
- viewer-71: The check MUST NOT run the probe, because `--graphics cells` is set. [just go-check: TestViewPTY]
- viewer-72: The Rust test `view_pty` MUST run the same steps with the same conditions. [just rust-check: view_pty]
