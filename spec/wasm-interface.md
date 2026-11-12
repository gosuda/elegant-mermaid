# WebAssembly interface

This file fixes the single entry point that both WebAssembly engines expose, the shape of its request and response, and the worker protocol that the playground uses to call it.

## Entry point

- wasm-interface-01: Both engines MUST expose one entry `emdCall(op, source, optionsJson) -> responseJson`, so the page never branches on the engine. [just wasm-parity]
- wasm-interface-02: The Go engine MUST define `emdCall` as a global function through `syscall/js` in `cmd/emd-wasm/main.go`, and it MUST then block with `select {}`. [just wasm-parity]
- wasm-interface-03: The Rust crate `elegant-mermaid-wasm` MUST export `emdCall` with `#[wasm_bindgen(js_name = emdCall)]`. [just wasm-parity]
- wasm-interface-04: `op` MUST be one of `check`, `lint`, `fix`, `render_svg`, `render_text`, `layout`, `version`. [just wasm-parity]
- wasm-interface-05: `source` MUST be the Mermaid text, passed unchanged. [just wasm-parity]

## Options

- wasm-interface-06: `optionsJson` MUST be a JSON object with snake_case keys, and each key MUST mirror a Public API option or a CLI flag; an absent key MUST take the value that the CLI takes when its flag is omitted. [just wasm-parity]
- wasm-interface-07: The keys of `optionsJson` MUST be the closed list of this table, with the default of each row: [just wasm-parity]

  |Key|Value|Default|
  |---|---|---|
  |`theme`|string, the `-t` value. The CLI's COLORFGBG rule does not apply: wasm never reads the environment.|`elegant-light`|
  |`background`|a colour string accepted by `-b`, or `null` for the theme `bg`|`null`|
  |`charset`|`unicode` or `ascii`|`unicode`|
  |`profile`|`vector` or `cell`; read by `layout` only.|`vector`|
  |`stage`|`layout` or `model`; read by `layout` only.|`layout`|
  |`max_width`|integer, or `null` for no width; read by `render_svg` and `render_text`.|`null`|
  |`lint`|object with the shape of the `lint` object of `emd.json`: `select` and `ignore` (arrays of codes) and `severity` (object mapping a code to `error`, `warning`, `info`, or `off`). Read by `lint` and `fix`.|every rule at its default severity|
  |`max`|`safe` or `unsafe`, where `unsafe` is `--unsafe-fixes`; read by `fix`.|`safe`|

- wasm-interface-08: A key outside the closed list, or a value of the wrong type, MUST return `ok` `false`, `output` `invalid option: KEY`, `diagnostics` `[]`, and `applied` `0`. [just wasm-parity]
- wasm-interface-09: A key that the op does not read MUST be ignored. [just wasm-parity]

## Response

- wasm-interface-10: The response MUST be `{"ok":bool,"output":string,"diagnostics":[…],"applied":n}` with the keys in that order. [just wasm-parity]
- wasm-interface-11: Each element of `diagnostics` MUST be a schema v1 object with the keys `code`, `severity`, `message`, `span`, `line`, `column`, `end_line`, `end_column`, `related`, `help`, and `fixes`, in that order, as `spec/diagnostics.md` defines them. [just wasm-parity]
- wasm-interface-12: `applied` MUST be the number of fixes that `fix` applied, and `0` for every other op. [just wasm-parity]

## Output and status

- wasm-interface-13: `output` MUST equal the stdout of the CLI command of this section for the same input, byte for byte. [just wasm-parity]
- wasm-interface-14: Wasm-parity MUST compare `output` with the native binaries. [just wasm-parity]
- wasm-interface-15: Each command MUST read `source` from stdin with `INPUT` omitted, except `check` and `lint`, which MUST take `-`, and the command MUST match its row of this table: [just wasm-parity]

  |Op|CLI command|
  |---|---|
  |`check`|`emd check --output-format json -`, where stdin is reported with the path `<stdin>`|
  |`lint`|`emd lint --output-format json -`, with an `emd.json` holding `{"lint": OPTIONS.lint}` in the working directory|
  |`fix`|`emd lint --fix -`, plus `--unsafe-fixes` when `max` is `unsafe`, with the same `emd.json`; its stdout is the fixed source|
  |`render_svg`|`emd render -e svg -t THEME`, plus `-b BACKGROUND` when `background` is not `null` and `--width N` when `max_width` is not `null`|
  |`render_text`|`emd render -e text --charset CHARSET --color never -t THEME`, plus `--width N` when `max_width` is not `null`|
  |`layout`|`emd layout --profile PROFILE --stage STAGE`|
  |`version`|`emd --version`|

- wasm-interface-16: Wasm-parity MUST run each command in an empty temporary directory, so that no ambient `emd.json` applies. [just wasm-parity]
- wasm-interface-17: `ok` MUST be `true` when no diagnostic has severity `error` for `check` and `lint`, MUST be always `true` for `fix` and `version`, and MUST be `true` when the CLI command exits 0 for `render_svg`, `render_text`, and `layout`. [just wasm-parity]
- wasm-interface-18: `output` for `check` and `lint` MUST be the stdout even when `ok` is `false`, because their stdout is the diagnostics. [just wasm-parity]
- wasm-interface-19: `output` for `fix` MUST always be the fixed source. [just wasm-parity]
- wasm-interface-20: `output` for `render_svg`, `render_text`, and `layout` MUST be `""` when `ok` is `false`. [just wasm-parity]
- wasm-interface-21: `diagnostics` MUST be `files[0].diagnostics` from `emd check --output-format json -` on the same source for `check`, `render_svg`, `render_text`, and `layout`; from `emd lint --output-format json -` for `lint`; and from `emd lint --output-format json -` run on the fixed source for `fix`; and it MUST be `[]` for `version`. [just wasm-parity]

## Worker protocol

- wasm-interface-22: Each engine MUST run in its own Web Worker, `playground/src/lib/engine.worker.ts`, created with `{ type: 'classic' }` so that the Go worker calls `importScripts` and the Rust worker loads its module with `import()`. [just playground-check]
- wasm-interface-23: The first message MUST give the worker its built URLs: `asset('wasm/wasm_exec.js')` and `asset('wasm/emd-go.wasm')` for Go, and `asset('wasm/emd-rs/elegant_mermaid_wasm.js')` and `asset('wasm/emd-rs/elegant_mermaid_wasm_bg.wasm')` for Rust. [just playground-check]
- wasm-interface-24: The worker MUST read the `.wasm` response as a stream and MUST post `progress` messages with the bytes loaded and the `Content-Length` total, or `null` when the total is absent. [just playground-check]
- wasm-interface-25: The worker MUST instantiate the bytes with `WebAssembly.instantiate` for Go and MUST pass them to the generated `init` for Rust. [just playground-check]
- wasm-interface-26: The Go worker MUST call `go.run(instance)` without awaiting it and MUST post `ready` once `globalThis.emdCall` is a function. [just playground-check]
- wasm-interface-27: The Rust worker MUST post `ready` after `init` resolves. [just playground-check]
- wasm-interface-28: A call message MUST carry `{id, revision, op, source, optionsJson}`, and the reply MUST carry the same `id` and `revision` and the response string. [just playground-check]
- wasm-interface-29: Requests MUST be debounced by 150 ms. [just playground-check]
- wasm-interface-30: The page MUST keep a revision counter and MUST drop a response that is older than the newest request, so the displayed revision never goes backwards. [just playground-check]
- wasm-interface-31: The wasm-parity script `playground/scripts/wasm-parity.mjs` MUST load both `.wasm` files, Go through `wasm_exec.js` and Rust through the generated module initialised from bytes, MUST run `check`, `render_text`, and `layout` on every tenth corpus file in sorted order, and MUST compare four ways: Go wasm with `bin/emd-go`, Rust wasm with `bin/emd-rs`, and the two wasm engines with each other. [just wasm-parity]
- wasm-interface-32: Those four outputs MUST be byte-identical for every compared file. [just wasm-parity]
