set shell := ["bash", "-euo", "pipefail", "-c"]

# Generate the shared tables, font copies, and README kinds block from spec/data
gen:
    go run ./tools/specgen

# Regenerate into a temporary directory and fail on any difference
gen-check:
    go run ./tools/specgen -check

# Go checks: gofmt, go vet, golangci-lint, race tests, govulncheck; accepts `just go-check PKG='./x/...'`
go-check PKG='./...':
    {{ if trim_start_match(PKG, 'PKG=') != './...' { "go test -list '.*' " + trim_start_match(PKG, 'PKG=') + " | grep '^Test' >/dev/null" } else { "true" } }}
    test -z "$(gofmt -l $(go list -f '{{{{.Dir}}' ./...))"
    go vet {{ trim_start_match(PKG, 'PKG=') }}
    go tool golangci-lint run
    go test -race {{ trim_start_match(PKG, 'PKG=') }}
    go tool govulncheck ./...

# Rust checks: fmt, clippy, nextest, cargo-deny, doc tests; accepts `just rust-check FILTER=name`
rust-check FILTER='':
    cargo fmt --check
    cargo clippy --all-targets --all-features --locked -- -D warnings
    cargo nextest run --all-features --locked {{ trim_start_match(FILTER, 'FILTER=') }} {{ if trim_start_match(FILTER, 'FILTER=') == '' { '--no-tests=pass' } else { '--no-tests=fail' } }}
    cargo deny --locked check
    cargo test --doc --locked -p elegant-mermaid

# House lint: sloplint over the repository
slop:
    sloplint check . --format agent --strictness standard --mode threshold --fail-on deny

# Build both binaries: bin/emd-go and bin/emd-rs
build:
    go build -trimpath -o bin/emd-go ./cmd/emd
    cargo build --release --locked -p elegant-mermaid-cli
    cp "${CARGO_TARGET_DIR:-target}/release/emd" bin/emd-rs

# Lean build with warnings as errors, then the proof hygiene audit
proofs:
    cd proofs && lake build --wfail
    bash proofs/scripts/audit.sh

# TLC model check of the preview scheduler
model:
    java -cp .tools/tla2tools.jar tlc2.TLC -config models/PreviewScheduler.cfg -workers auto models/PreviewScheduler.tla

# Go, Rust, and Lean kernels agree on the generated cases
kernel-diff: build proofs
    mkdir -p corpus/.cache/kernel
    go run ./tools/kernelgen > corpus/.cache/kernel/cases.txt
    proofs/.lake/build/bin/geomcheck eval corpus/.cache/kernel/cases.txt > corpus/.cache/kernel/lean.out
    bin/emd-go kernel-eval corpus/.cache/kernel/cases.txt > corpus/.cache/kernel/go.out
    bin/emd-rs kernel-eval corpus/.cache/kernel/cases.txt > corpus/.cache/kernel/rust.out
    cmp corpus/.cache/kernel/lean.out corpus/.cache/kernel/go.out
    cmp corpus/.cache/kernel/lean.out corpus/.cache/kernel/rust.out

geomcheck := "proofs/.lake/build/bin/geomcheck"

# Print the selected corpus paths; accepts KIND=<kind> SAMPLE=<n> JOBS=<n> FILES=<list file>
_corpus *ARGS:
    #!/usr/bin/env bash
    set -euo pipefail
    kind="" sample=1 files=""
    for arg in {{ ARGS }}; do
      case "$arg" in
        KIND=*) kind="${arg#KIND=}" ;;
        SAMPLE=*) sample="${arg#SAMPLE=}" ;;
        FILES=*) files="${arg#FILES=}" ;;
        JOBS=*) ;;
        *) echo "unknown argument $arg; expected KIND=, SAMPLE=, JOBS=, or FILES=" >&2; exit 2 ;;
      esac
    done
    if [ -n "$files" ]; then cat "$files"; else git ls-files -- 'corpus/*.mmd' ':!corpus/_out-of-scope/*'; fi \
      | awk -v kind="$kind" 'kind == "" || index($0, "corpus/" kind "/") == 1' \
      | LC_ALL=C sort \
      | awk -v n="$sample" '(NR - 1) % n == 0'

# Print the worker count: JOBS=<n>, else the processor count
_jobs *ARGS:
    #!/usr/bin/env bash
    set -euo pipefail
    jobs="$(nproc)"
    for arg in {{ ARGS }}; do
      case "$arg" in JOBS=*) jobs="${arg#JOBS=}" ;; esac
    done
    echo "$jobs"

# Run one private per-file recipe over the selected corpus paths in parallel
_each RECIPE *ARGS:
    #!/usr/bin/env bash
    set -uo pipefail
    list="$(mktemp)"
    trap 'rm -f -- "$list"' EXIT
    just _corpus {{ ARGS }} > "$list" || exit 2
    jobs="$(just _jobs {{ ARGS }})"
    xargs -d '\n' -P "$jobs" -n 1 just {{ RECIPE }} < "$list"
    status=$?
    echo "{{ RECIPE }}: $(wc -l < "$list") files, xargs status $status"
    test "$status" -eq 0

_oracle-one FILE:
    #!/usr/bin/env bash
    set -uo pipefail
    f={{ quote(FILE) }}
    report="$(bin/emd-go check --output-format json "$f" 2>/dev/null)"
    printf '%s\n' "$report" | jaq -c --arg path "$f" '{path: $path, accept: (.summary.errors == 0), kind: .files[0].kind}'

# Compare accept, reject, and kind with corpus/verdicts.json and corpus/divergences.json
oracle *ARGS:
    #!/usr/bin/env bash
    set -euo pipefail
    list="$(mktemp)" ours="$(mktemp)"
    trap 'rm -f -- "$list" "$ours"' EXIT
    just _corpus {{ ARGS }} > "$list"
    jobs="$(just _jobs {{ ARGS }})"
    xargs -d '\n' -P "$jobs" -n 1 just _oracle-one < "$list" > "$ours"
    test "$(wc -l < "$ours")" -eq "$(wc -l < "$list")" || { echo "oracle: a check run printed no verdict"; exit 1; }
    report="$(jaq -rn --slurpfile ours "$ours" --slurpfile upstream corpus/verdicts.json --slurpfile rows corpus/divergences.json '
      ($upstream[0]) as $up
      | ($rows[0] | map({key: .path, value: .}) | from_entries) as $div
      | $ours[]
      | . as $o
      | {accept: $o.accept, kind: $o.kind} as $mine
      | (if $up | has($o.path) then ($up[$o.path] | {accept, kind}) else null end) as $theirs
      | if $theirs == null then "oracle: no upstream verdict: \($o.path)"
        elif $div | has($o.path) then
          (if $div[$o.path].upstream_verdict == $theirs and $div[$o.path].our_verdict == $mine then empty
           else "oracle: stale divergence row: \($o.path)" end)
        elif $theirs == $mine then empty
        else "oracle: verdict differs: \($o.path) upstream \($theirs | tojson) ours \($mine | tojson)" end')"
    echo "oracle: $(wc -l < "$list") files, $(jaq 'length' corpus/divergences.json) divergence rows"
    test -z "$report" || { echo "$report"; exit 1; }

# Format check on the staged content of Go and Rust files; the pre-commit hook runs it
staged-format:
    #!/usr/bin/env bash
    set -euo pipefail
    index="$(mktemp -d)"
    trap 'rm -rf -- "$index"' EXIT
    git ls-files -z -- '*.go' '*.rs' | git checkout-index -z --stdin --prefix="$index/"
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
    just build
    just proofs
    just model
    just oracle
    just kernel-diff
