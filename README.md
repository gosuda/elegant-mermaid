# elegant-mermaid

Render, check, and lint Mermaid diagrams as SVG, PNG, or terminal text, without a browser.

[![ci](https://github.com/gosuda/elegant-mermaid/actions/workflows/ci.yml/badge.svg)](https://github.com/gosuda/elegant-mermaid/actions/workflows/ci.yml) [![crates.io](https://img.shields.io/crates/v/emd-cli?style=flat)](https://crates.io/crates/emd-cli) [![license](https://img.shields.io/github/license/gosuda/elegant-mermaid?style=flat)](LICENSE)

elegant-mermaid gives you the `emd` command and libraries for Go, Rust, and Node.js. Use it to draw a diagram in your terminal, render SVG or PNG in a build, or check every diagram in a docs folder in CI. Unlike the upstream Mermaid stack, no browser or JavaScript runtime is in the render path: `emd` is a single binary. It reads no network, host fonts, clock, or randomness, so the same input always gives the same bytes.

```sh
printf 'flowchart LR\n  A[Start] --> B[Choice]\n  B --> C[Done]\n' | emd render -e text
#
#  ┌───────┐   ┌────────┐   ┌──────┐
#  │ Start ├───▶ Choice ├───▶ Done │
#  └───────┘   └────────┘   └──────┘
#
```

The three diagram rows are the same bytes the repository ships as the text-render golden at [`internal/cells/testdata/render/demo.txt`](internal/cells/testdata/render/demo.txt); the command adds one blank line on each side and one leading space on each row.

## Why use it

- **One binary, no browser:** `emd` renders without a JavaScript runtime or a DOM; the npm package ships the compiled binary behind a small Node launcher, so the npm command still needs Node.js.
- **Two engines, one output:** the Go and Rust implementations produce byte-identical output. `just parity` compares them over a corpus of 3,566 diagrams.
- **33 diagram kinds:** from flowchart and sequence to gantt, sankey, and railroad. The full list is under [Diagram kinds](#diagram-kinds).
- **Checker and linter:** stable diagnostic codes, safe automatic fixes, and text, JSON, SARIF, or GitHub annotation output.
- **Integer geometry:** layout uses no floating point. A Lean 4 model in [`proofs/`](proofs) checks layouts against hard geometry constraints.

## Quick start

The fastest way to run `emd` is the npm package (GNU/Linux x64 with glibc, Node.js 26 or later):

```sh
npm install --global emd-cli
printf 'flowchart LR\n  A[Write] --> B[Check]\n  B --> C[Render]\n' > demo.mmd
emd check demo.mmd        # no output and exit 0 mean the diagram is valid
emd render demo.mmd -e text
emd render demo.mmd -o demo.svg
```

The published package is version 0.1.0, which is older than this repository: it has no `lint` or `explain` command, no PNG output, and no `--svg-text paths`. For those commands install from source, as the next section shows.

## Install

From a checkout of this repository (Rust 1.99 or later):

```sh
git clone https://github.com/gosuda/elegant-mermaid.git
cd elegant-mermaid
cargo install --path crates/elegant-mermaid-cli --locked
```

This puts `emd` in `~/.cargo/bin`. To build the Go implementation instead, run `go build -o emd ./cmd/emd` in the same folder.

Published packages exist for both registries, each at version 0.1.0 with the limits noted above:

```sh
cargo install emd-cli --locked     # any platform with Rust 1.99 or later
npm install --global emd-cli       # GNU/Linux x64 with glibc, Node.js 26 or later
```

## Usage

Check a whole docs folder and fail CI on warnings:

```sh
emd lint docs/ --deny-warnings --output-format github
```

A problem is reported with its code, position, and a fix when one exists:

```sh
printf 'flowchart LR\n  A[Start --> B\n' | emd check -
# <stdin>:2:4: error[flowchart/unclosed-node-bracket]: node bracket [ is never closed
#   |
# 2 |   A[Start --> B
#   |    ^~~~~~~~~~~~
#   = help: Add the closing bracket that matches the opening bracket.
#   = fix: Add the closing bracket
```

Apply safe fixes in place:

```sh
emd lint --fix demo.mmd
```

Render with a dark theme in ASCII, for terminals without Unicode:

```sh
emd render demo.mmd -e text -t elegant-dark --charset ascii
```

Watch a diagram while you edit it:

```sh
emd view demo.mmd
```

`emd` has six subcommands:

|Command|What it does|Example|
|---|---|---|
|`render`|Render Mermaid as SVG, PNG, or terminal text|`emd render demo.mmd -o demo.svg`|
|`check`|Check syntax and semantics without changing files|`emd check docs/`|
|`lint`|Check lint rules and optionally apply fixes|`emd lint --fix demo.mmd`|
|`view`|Watch and display a diagram in the terminal|`emd view demo.mmd`|
|`layout`|Print canonical layout data|`emd layout demo.mmd --profile cell`|
|`explain`|Explain a diagnostic code|`emd explain flowchart/unexpected-token`|

Main `render` options:

- `-o OUTPUT` sets the output file. The format follows its extension (`.svg`, `.png`, `.txt`).
- `-e svg|png|text` sets the format explicitly.
- `-t THEME` picks a theme. The default is `elegant-light`, or `elegant-dark` on a dark terminal for text output.
- `-s SCALE` sets PNG pixels per CSS pixel, from 1 to 8. The default is 2.
- `--charset unicode|ascii` and `--color auto|always|never` control terminal text.

Run `emd COMMAND --help` for every option and its default. The full contract is in [`spec/cli.md`](spec/cli.md).

## Configuration

- Diagram config: `emd` reads Mermaid frontmatter `config` and `%%{init}%%` directives. `emd render -c FILE` adds config text from a file.
- Icons: `emd render --icon-pack FILE` loads an Iconify JSON icon pack. Repeat the option to load more packs.
- Lint rules: `emd lint` uses the first `emd.json` it finds, walking up from each input file's folder. `--lint-config FILE` names a file, and `--no-config` ignores config files.

The config keys are described in [`spec/config.md`](spec/config.md) and the lint rules in [`spec/lint.md`](spec/lint.md).

## Libraries

Go, from a checkout of this repository next to your module:

```sh
go mod edit -require=github.com/gosuda/elegant-mermaid@v0.0.0 \
  -replace=github.com/gosuda/elegant-mermaid=../elegant-mermaid
```

```go
package main

import (
	"context"
	"fmt"
	"log"

	mermaid "github.com/gosuda/elegant-mermaid"
)

func main() {
	src := []byte("pie\n  \"Go\" : 2\n  \"Rust\" : 3\n")
	text, err := mermaid.RenderTextSource(context.Background(), src, mermaid.TextOptions{})
	if err != nil {
		log.Fatal(err)
	}
	fmt.Print(string(text))
}
```

The Go package imports only the standard library. `RenderSVGSource` returns SVG the same way.

Rust:

```sh
cargo add elegant-mermaid
```

```rust
use elegant_mermaid::{RenderError, TextOptions, render_text_str};

fn main() -> Result<(), RenderError> {
    let text = render_text_str("flowchart LR\n  A --> B\n", &TextOptions::default())?;
    print!("{text}");
    Ok(())
}
```

The crate forbids `unsafe` code and builds for `wasm32-unknown-unknown`.

Node.js (GNU/Linux x64 with glibc, Node.js 26 or later):

```sh
npm install elegant-mermaid
```

```js
import { renderSvg, renderText } from "elegant-mermaid";

const svg = await renderSvg("flowchart LR\n  A --> B\n");
```

The library surface is described in [`spec/library-surface.md`](spec/library-surface.md).

## Diagram kinds

The registry in [`spec/data/kinds.json`](spec/data/kinds.json) defines these kind IDs:

<!-- kinds:start -->
- `flowchart`
- `swimlane`
- `agentflow`
- `class`
- `state`
- `er`
- `requirement`
- `usecase`
- `c4`
- `sequence`
- `block`
- `architecture`
- `kanban`
- `packet`
- `mindmap`
- `treeview`
- `ishikawa`
- `gitgraph`
- `eventmodeling`
- `timeline`
- `journey`
- `gantt`
- `xychart`
- `quadrant`
- `treemap`
- `wardley`
- `pie`
- `radar`
- `sankey`
- `venn`
- `cynefin`
- `railroad`
- `info`
<!-- kinds:end -->

## Contributing

Open an issue or a pull request on [GitHub](https://github.com/gosuda/elegant-mermaid). CI runs `just gen-check`, `go-check`, `rust-check`, `build`, and `parity`, so run them before you push.

You need:

- Go, at the toolchain version in [`go.mod`](go.mod).
- Rust, at the version in [`rust-toolchain.toml`](rust-toolchain.toml). `rustup` installs it on first use.
- [just](https://github.com/casey/just).
- For the full gate: Lean 4 through `elan` (version in [`proofs/lean-toolchain`](proofs/lean-toolchain)), a Java runtime for the TLA+ model check, and Node.js with pnpm for the upstream oracle.

Build and test:

```sh
just build        # bin/emd-go and bin/emd-rs
just go-check     # Go format, vet, lint, race tests, vulnerability check
just rust-check   # Rust format, clippy, tests, cargo-deny, docs
just parity       # Go and Rust output must match byte for byte
just verify       # every gate, including Lean proofs and the oracle
```

Generated files come from `tools/specgen`. Edit the sources under [`spec/`](spec), then run `just gen`. `just gen-check` fails when a generated file is stale. Maintainer rules and file ownership are in [`AGENTS.md`](AGENTS.md).

## License

Apache-2.0. See [`LICENSE`](LICENSE). The bundled Inter fonts are under OFL-1.1 and the Unicode data under Unicode-3.0; [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) lists every bundled work.
