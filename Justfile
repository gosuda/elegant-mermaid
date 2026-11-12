set shell := ["bash", "-euo", "pipefail", "-c"]

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

# Run every gate whose subject exists, in order
verify:
    just go-check
    just rust-check
    just slop
