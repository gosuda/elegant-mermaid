set shell := ["bash", "-euo", "pipefail", "-c"]

# Generate the shared tables, font copies, and README kinds block from spec/data
gen:
    go run ./tools/specgen

# Regenerate into a temporary directory and fail on any difference
gen-check:
    go run ./tools/specgen -check

# Go checks: gofmt, go vet, golangci-lint, race tests, govulncheck; accepts `just go-check PKG='./x/...'`
go-check PKG='./...': build
    {{ if trim_start_match(PKG, 'PKG=') != './...' { "go test -list '.*' " + trim_start_match(PKG, 'PKG=') + " | grep '^Test' >/dev/null" } else { "true" } }}
    test -z "$(gofmt -l $(go list -f '{{{{.Dir}}' ./...))"
    go vet {{ trim_start_match(PKG, 'PKG=') }}
    go tool golangci-lint run
    EMD_BIN="{{ justfile_directory() }}/bin/emd-go" go test -race {{ trim_start_match(PKG, 'PKG=') }}
    go tool govulncheck ./...

# Rust checks: fmt, clippy, nextest, cargo-deny, doc tests; accepts `just rust-check FILTER=name`
rust-check FILTER='': build
    cargo fmt --check
    cargo clippy --all-targets --all-features --locked -- -D warnings
    EMD_BIN="{{ justfile_directory() }}/bin/emd-rs" cargo nextest run --all-features --locked --no-fail-fast {{ trim_start_match(FILTER, 'FILTER=') }} {{ if trim_start_match(FILTER, 'FILTER=') == '' { '--no-tests=pass' } else { '--no-tests=fail' } }}
    cargo deny --locked check
    cargo test --doc --locked -p elegant-mermaid

# House lint: upstream standard profile, failing on major findings
slop:
    sloplint check . --jobs 1 --format agent --strictness standard --mode threshold --fail-on major

# Build both binaries: bin/emd-go and bin/emd-rs
build:
    go build -trimpath -o bin/emd-go ./cmd/emd
    cargo build --release --locked -p emd-cli
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
    if [ -n "$files" ]; then cat "$files"; else git ls-files -- 'corpus/*.mmd' ':!corpus/_out-of-scope/*' ':!corpus/termgfx/*'; fi \
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
    report="$(bin/emd-go check --output-format json "$f")"
    status=$?
    case "$status" in
      0|1) ;;
      *) echo "oracle: check failed with exit $status: $f" >&2; exit 1 ;;
    esac
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

_parity-one FILE:
    #!/usr/bin/env bash
    set -uo pipefail
    f={{ quote(FILE) }}
    same() {
      cmp -s <(bin/emd-go "$@" 2>/dev/null; echo "exit=$?") <(bin/emd-rs "$@" 2>/dev/null; echo "exit=$?") && return 0
      echo "parity: differs: emd $*"
      return 1
    }
    same check --output-format json "$f" || exit 1
    same check --output-format text --color never "$f" || exit 1
    bin/emd-go check --output-format json "$f" >/dev/null 2>&1; status=$?
    case "$status" in 0) ;; 1) exit 0 ;; *) echo "parity: check failed with exit $status: $f"; exit 1 ;; esac
    works() {
      bin/emd-go "$@" >/dev/null 2>&1 || { echo "parity: go fails on an accepted file: emd $*"; return 1; }
      same "$@"
    }
    works layout --profile vector "$f" || exit 1
    works layout --profile cell "$f" || exit 1
    works layout --stage model "$f" || exit 1
    works render -e svg "$f" || exit 1
    works render -e text --charset unicode --color never "$f" || exit 1
    works render -e text --charset ascii --color never "$f" || exit 1

# Go and Rust outputs equal on every selected corpus file
parity *ARGS:
    go_version="$(bin/emd-go --version)"; rs_version="$(bin/emd-rs --version)"; test "$go_version" = "$rs_version"
    just _each _parity-one {{ ARGS }}

# Compare actual Markdown assets, rewritten hosts, diagnostics, and path handling
markdown-parity: build
    go run ./tools/markdown-parity

_accept-one FILE:
    #!/usr/bin/env bash
    set -euo pipefail
    f={{ quote(FILE) }}
    for engine in bin/emd-go bin/emd-rs; do
      if report="$("$engine" check --output-format json "$f")"; then continue; fi
      printf '%s\n%s\n' "acceptance: $engine check failed for $f" "$report" >&2
      exit 1
    done

layered-random-check JOBS='2': build
    go run ./tools/randgraph
    test "$(wc -l < corpus/.cache/random/layered.txt)" -eq 2000
    test "$(LC_ALL=C sort -u corpus/.cache/random/layered.txt | wc -l)" -eq 2000
    just _each _accept-one FILES=corpus/.cache/random/layered.txt JOBS={{ quote(trim_start_match(JOBS, 'JOBS=')) }}
    just parity FILES=corpus/.cache/random/layered.txt JOBS={{ quote(trim_start_match(JOBS, 'JOBS=')) }}
    echo "layered-random-check: 2000 accepted and parity-checked cases"

_validate-one FILE:
    #!/usr/bin/env bash
    set -uo pipefail
    f={{ quote(FILE) }}
    bin/emd-go check --output-format json "$f" >/dev/null 2>&1; status=$?
    case "$status" in 0) ;; 1) exit 0 ;; *) echo "validate: check failed with exit $status: $f"; exit 1 ;; esac
    for engine in bin/emd-go bin/emd-rs; do
      for profile in vector cell; do
        verdict="$("$engine" layout --profile "$profile" "$f" 2>/dev/null | proofs/.lake/build/bin/geomcheck validate 2>&1)"
        test "$verdict" = "valid" && continue
        echo "validate: $engine $profile $f: $verdict"
        exit 1
      done
    done

# Every layout dump of every accepted corpus file passes geomcheck validate
validate *ARGS:
    just _each _validate-one {{ ARGS }}

_lean-parity-one FILE:
    #!/usr/bin/env bash
    set -uo pipefail
    f={{ quote(FILE) }}
    geomcheck=proofs/.lake/build/bin/geomcheck
    bin/emd-go check --output-format json "$f" >/dev/null 2>&1; status=$?
    case "$status" in 0) ;; 1) exit 0 ;; *) echo "lean-parity: check failed with exit $status: $f"; exit 1 ;; esac
    for profile in vector cell; do
      bin/emd-go layout --profile "$profile" "$f" >/dev/null 2>&1 || { echo "lean-parity: go layout fails: $profile $f"; exit 1; }
      cmp -s <(bin/emd-go layout --stage model --profile "$profile" "$f" 2>/dev/null | "$geomcheck" layout 2>/dev/null; echo "exit=$?") \
             <(bin/emd-go layout --profile "$profile" "$f" 2>/dev/null; echo "exit=$?") && continue
      echo "lean-parity: layout differs: $profile $f"
      exit 1
    done
    for charset in unicode ascii; do
      bin/emd-go render -e text --charset "$charset" --color never "$f" >/dev/null 2>&1 || { echo "lean-parity: go render fails: $charset $f"; exit 1; }
      cmp -s <(bin/emd-go layout --stage model --profile cell "$f" 2>/dev/null | "$geomcheck" text --charset "$charset" 2>/dev/null; echo "exit=$?") \
             <(bin/emd-go render -e text --charset "$charset" --color never "$f" 2>/dev/null; echo "exit=$?") && continue
      echo "lean-parity: text differs: $charset $f"
      exit 1
    done

# Lean reference output equals the Go output on every accepted corpus file
lean-parity *ARGS:
    just _each _lean-parity-one {{ ARGS }}

# Quality gates against the dagre and ELK baselines; accepts JOBS=<n>
quality *ARGS:
    #!/usr/bin/env bash
    set -euo pipefail
    jobs="$(just _jobs {{ ARGS }})"
    fixtures="$(mktemp)"
    trap 'rm -f -- "$fixtures"' EXIT
    go run ./tools/quality -list > "$fixtures"
    EMD_BIN=bin/emd-go node tools/upstream-oracle/baseline.mjs "$fixtures" "$jobs"
    go run ./tools/quality -emd bin/emd-go -jobs "$jobs"

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

# Contributor loop: generated tables, Go and Rust checks, and parity on every tenth corpus file
check-fast:
    just gen-check
    just go-check
    just rust-check
    just parity KIND=flowchart FILES=corpus/flat-flowchart.txt SAMPLE=10

# Contrast for built-in themes, no hex colour literal in back-end code, SVG titles, config-key coverage
theme-check: build
    go test -count=1 -run '^TestBuiltInThemeContrast$' ./internal/theme
    cargo nextest run --locked -p elegant-mermaid --all-features -E 'test(built_in_theme_contrast)'
    ! git grep -nE '#([0-9A-Fa-f]{3,4}|[0-9A-Fa-f]{6}|[0-9A-Fa-f]{8})\b' -- '*.go' '*.rs' ':!*_test.go' ':!*_gen.go' ':!*/gen/*' ':!tools/*' ':!**/tests/**' ':!**/tests.rs' ':!**/*_tests.rs'
    go test -count=1 -run '^TestCorpusSVGTitles$' ./internal/svg
    cargo nextest run --locked -p elegant-mermaid --all-features -E 'test(corpus_svg_titles)'
    node tools/upstream-oracle/config-keys.mjs --missing spec/data/config-keys


# Build the two browser engines from the pinned native toolchains
playground-wasm:
    mkdir -p playground/static/wasm/emd-rs
    GOOS=js GOARCH=wasm go build -trimpath -o playground/static/wasm/emd-go.wasm ./cmd/emd-wasm
    cp "$(go env GOROOT)/lib/wasm/wasm_exec.js" playground/static/wasm/wasm_exec.js
    cargo build --locked --release --target wasm32-unknown-unknown -p elegant-mermaid-wasm
    wasm-bindgen --target web --out-dir playground/static/wasm/emd-rs --out-name elegant_mermaid_wasm "${CARGO_TARGET_DIR:-target}/wasm32-unknown-unknown/release/elegant_mermaid_wasm.wasm"

# Browser types, formatting, lint, and unit regressions
playground-check:
    pnpm --dir playground check
    pnpm --dir playground exec biome check .
    pnpm --dir playground exec vitest run

# Prerender the browser application, including its worker assets
playground-build: build playground-wasm
    node playground/scripts/initial-text.mjs
    pnpm --dir playground build

# Compare tracked corpus fixtures across native and browser engines
wasm-parity: build playground-wasm
    node --test playground/scripts/wasm-parity.test.mjs
    node playground/scripts/wasm-parity.mjs

# Exercise production output and the classic worker served by Vite development mode
playground-e2e: playground-build
    pnpm --dir playground exec playwright test
    PLAYGROUND_SERVER_MODE=dev pnpm --dir playground exec playwright test --grep 'both engines render the default source'

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
    just parity
    just markdown-parity
    just layered-random-check
    just kernel-diff
    just validate
    just lean-parity
    just quality
    just theme-check
    just playground-check
    just wasm-parity
    just playground-e2e
