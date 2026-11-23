# AGENTS.md

This is the maintainer register. MUST, SHOULD, and MAY have the meanings of RFC 2119.

## Gates

Run the gates from the repository root:

- `just go-check`
- `just rust-check`
- `just slop`
- `just verify`

A step that creates a gate MUST add its recipe to the `Justfile` and MUST add the gate to `verify` in the same commit.

The Go and Rust engines MUST give byte-identical output. A change to the output of one engine MUST change the other engine in the same commit.

You MUST NOT rebuild `bin/emd-go`, `bin/emd-rs`, or `proofs/.lake/build/bin/geomcheck` while `parity`, `validate`, `lean-parity`, or `kernel-diff` runs. These recipes read the binaries from disk.

The corpus recipes list their files with `git ls-files`. Run them in a git checkout or a git worktree. They fail in an exported tree.

## CI split

The core CI workflow runs `gen-check go-check rust-check build parity`.

The verification workflow also runs the house linter, Lean proof audit,
scheduler model, corpus oracle, random graphs, geometry validation, Lean
parity, quality comparisons, and theme checks. Its independent jobs install
the pinned gate dependencies and have longer time limits than core CI.
Failures in one independent gate MUST NOT suppress the other gate results.

`just verify` remains the complete local entry point. Both workflows MUST
pass before the repository is described as fully verified.

## Lean proofs

`just proofs` rejects `sorry`, `axiom`, `native_decide`, `partial def`, `unsafe`, `implemented_by`, and `extern` in every `.lean` file below `proofs/Elegant/` and `proofs/ElegantGeometry/`. The scan includes files that git does not track.

The audit checks only the theorems that `proofs/theorems.txt` lists. A theorem is proved only when `proofs/Elegant.lean` imports its module and `proofs/theorems.txt` lists its full name.

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

Only `tools/specgen` writes generated files. This includes the kinds list in `README.md` between the `kinds:start` and `kinds:end` markers.
