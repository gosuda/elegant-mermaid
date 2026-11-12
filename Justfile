set shell := ["bash", "-euo", "pipefail", "-c"]

# Generate the shared tables, font copies, and README kinds block from spec/data
gen:
    go run ./tools/specgen

# Regenerate into a temporary directory and fail on any difference
gen-check:
    go run ./tools/specgen -check

# Go checks: gofmt, go vet, golangci-lint, race tests, govulncheck
go-check PKG='./...':
    {{ if PKG != './...' { "go test -list '.*' " + PKG + " | grep '^Test' >/dev/null" } else { "true" } }}
    test -z "$(gofmt -l $(go list -f '{{{{.Dir}}' ./...))"
    go vet {{PKG}}
    go tool golangci-lint run
    go test -race {{PKG}}
    go tool govulncheck ./...

# Rust checks: fmt, clippy, nextest, cargo-deny, doc tests
rust-check FILTER='':
    cargo fmt --check
    cargo clippy --all-targets --all-features --locked -- -D warnings
    cargo nextest run --all-features --locked {{FILTER}} {{ if FILTER == '' { '--no-tests=pass' } else { '--no-tests=fail' } }}
    cargo deny --locked check
    cargo test --doc --locked -p elegant-mermaid

# House lint: sloplint over the repository
slop:
    sloplint check . --format agent --strictness standard --mode threshold --fail-on deny

# TLC model check of the preview scheduler
model:
    java -cp .tools/tla2tools.jar tlc2.TLC -config models/PreviewScheduler.cfg -workers auto models/PreviewScheduler.tla

# Format check on the staged content of Go and Rust files; the pre-commit hook runs it
staged-format:
    #!/usr/bin/env bash
    set -euo pipefail
    index="$(mktemp -d)"
    trap 'rip -f "$index"' EXIT
    git checkout-index --all --prefix="$index/"
    cd "$index"
    mapfile -t go_files < <(git -C "{{justfile_directory()}}" diff --cached --name-only --diff-filter=ACMR -- '*.go')
    mapfile -t rs_files < <(git -C "{{justfile_directory()}}" diff --cached --name-only --diff-filter=ACMR -- '*.rs')
    test "${#go_files[@]}" -eq 0 || test -z "$(gofmt -l "${go_files[@]}")"
    test "${#rs_files[@]}" -eq 0 || rustfmt --check --edition 2024 "${rs_files[@]}"

# Run every gate whose subject exists, in order
verify:
    just gen-check
    just go-check
    just rust-check
    just slop
    just model
