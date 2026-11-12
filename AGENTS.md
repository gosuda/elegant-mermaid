# AGENTS.md

This is the maintainer register. MUST, SHOULD, and MAY have the meanings of RFC 2119.

## Gates

Run the gates from the repository root:

- `just go-check`
- `just rust-check`
- `just slop`
- `just verify`

A step that creates a gate MUST add its recipe to the `Justfile` and MUST add the gate to `verify` in the same commit.

## CI split

CI runs `gen-check go-check rust-check build parity`.

`pages.yml` runs `playground-wasm`.

Every other recipe is local only. The local-only recipes are `gen`, `proofs`, `model`, `oracle`, `kernel-diff`, `validate`, `lean-parity`, `quality`, `theme-check`, `d3-check`, `fuzz-smoke`, `slop`, `playground-check`, `playground-e2e`, `wasm-parity`, `verify`, `check-fast`, `mutants`, `coverage`, and `bench`.

The reasons are:

- `slop` needs the house sloplint.
- `proofs` needs the Lean toolchain.
- `model` needs a JDK.
- The rest would exceed the 30-minute job limit.

## Write sets

The parent owns these shared files:

- `go.mod`
- `Cargo.toml`
- `Cargo.lock`
- `Justfile`
- the lint configs
- `corpus/MANIFEST.json`
- `corpus/divergences.json`
- `proofs/theorems.txt`
- `spec/data/SOURCES.json`
- `THIRD_PARTY_NOTICES.md`

The parent also writes `proofs/ElegantGeometry/` and `proofs/Main.lean`.

Workers get disjoint write sets:

- A Go worker owns Go paths.
- A Rust worker owns `crates/` and `fuzz/`.
- A spec worker owns `spec/`.
- A Lean worker owns `proofs/Elegant/` (kind adapters, family modules, and phase modules).

Registries are split per kind: `spec/data/diagnostics/<kind>.json`, `spec/data/lint-rules/<kind>.json`, and `spec/data/config-keys/<kind>.json`.

Kind workers MUST NOT share a registry file.

Workers MUST NOT run repository-wide gates. The parent runs the `verify` recipe after each step.

Only the parent writes `corpus/divergences.json`.

You MUST NOT copy text from `.references/mermaid-linter`.

Only `tools/specgen` writes generated files.
