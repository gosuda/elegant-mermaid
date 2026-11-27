"""Focused native Windows proof for the paired Markdown path repair."""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final
from receipt_reuse import authenticate, require_test_only_delta

WORKSPACE: Final = Path(sys.argv[1]).absolute()
PROOF: Final = Path(sys.argv[2]).absolute()
OUTPUT: Final = Path(sys.argv[3]).absolute()
OUTPUT.mkdir(parents=True, exist_ok=True)
BUILDS: Final = OUTPUT.parent / "emd-paired-windows-builds"
BUILDS.mkdir(parents=True, exist_ok=True)
LINKS: Final = "crates/elegant-mermaid-cli/src/render/markdown/links.rs"
RUST_OWNED: Final = (LINKS, "crates/elegant-mermaid-cli/src/render/markdown/output.rs")
GO_OWNED: Final = (
    "internal/cli/output_path.go", "internal/cli/output_path_other.go",
    "internal/cli/output_path_windows.go", "internal/cli/output_path_windows_test.go",
    "internal/cli/render_markdown_output.go", "internal/tui/read_windows.go",
)
OWNED: Final = (*RUST_OWNED, *GO_OWNED)
MANIFEST: Final = json.loads((PROOF / "manifest.json").read_text(encoding="utf-8"))
RECEIPTS: list[dict[str, str | int | list[str]]] = []


@dataclass(frozen=True)
class Snapshot:
    name: str
    root: Path
    head: str
    tree: str
    index: str
    controls: int
    exits: tuple[int, ...]


def snapshot(name: str) -> Snapshot:
    record = MANIFEST["sources"][name]
    head, tree = record["head"], record["tree"]
    if not isinstance(head, str) or not re.fullmatch("[0-9a-f]{40}", head):
        raise RuntimeError(f"{name}: exact source commit is not bound")
    if not isinstance(tree, str) or not re.fullmatch("[0-9a-f]{40}", tree):
        raise RuntimeError(f"{name}: exact source tree is not bound")
    return Snapshot(name, WORKSPACE / name, head, tree, f"{name}-index.json",
                    record["controls"], tuple(record["exits"]))


def digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def git_blob(content: bytes) -> str:
    return hashlib.sha1(f"blob {len(content)}\0".encode() + content,
                       usedforsecurity=False).hexdigest()


def run(name: str, command: list[str], source: Snapshot, expected: int = 0) -> str:
    environment = dict(os.environ)
    environment.update({
        "GOENV": "off", "GOCACHEPROG": "", "CARGO_INCREMENTAL": "0",
        "RUSTC_WRAPPER": "", "RUSTC_WORKSPACE_WRAPPER": "",
        "CARGO_TARGET_DIR": str(BUILDS / f"cargo-{source.name}"),
        "GOCACHE": str(BUILDS / f"gocache-{source.name}"),
    })
    result = subprocess.run(
        command, cwd=source.root, env=environment, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, encoding="utf-8", errors="replace", check=False,
    )
    (OUTPUT / f"{name}.log").write_text(result.stdout, encoding="utf-8")
    record: dict[str, str | int | list[str]] = {
        "name": name, "command": command, "exit": result.returncode,
        "expected": expected, "log_sha256": digest(result.stdout.encode()),
    }
    RECEIPTS.append(record)
    print("COMMAND_RECEIPT " + json.dumps(record), flush=True)
    print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
    if result.returncode != expected:
        raise RuntimeError(f"{name}: actual exit {result.returncode}, expected {expected}")
    return result.stdout


def expected_index(source: Snapshot) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = json.loads((PROOF / source.index).read_text(encoding="utf-8"))
    if len({row["path"] for row in rows}) != len(rows):
        raise RuntimeError("duplicate frozen source paths")
    if any(row["mode"] not in ("100644", "100755") for row in rows):
        raise RuntimeError("unsupported source mode")
    return rows


def identity(source: Snapshot, expected: list[dict[str, str]] | None = None) -> list[dict[str, str]]:
    if expected is None:
        expected = expected_index(source)
    rows: list[dict[str, str]] = []
    for row in expected:
        content = (source.root / row["path"]).read_bytes()
        if git_blob(content) != row["sha"]:
            raise RuntimeError(f"{source.name}: source blob mismatch: {row['path']}")
        rows.append({**row, "sha256": digest(content)})
    process = subprocess.run(
        ["git", "ls-files", "-s", "-z"], cwd=source.root,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    )
    entries: dict[str, tuple[str, str]] = {}
    for item in process.stdout.decode().rstrip("\0").split("\0"):
        meta, path = item.split("\t", 1)
        mode, blob, stage = meta.split()
        if stage != "0":
            raise RuntimeError("unmerged source index")
        entries[path] = (mode, blob)
    if entries != {row["path"]: (row["mode"], row["sha"]) for row in expected}:
        raise RuntimeError(f"{source.name}: tracked index differs")
    record = {
        "snapshot": source.name, "head": source.head, "tracked_blobs": len(rows),
        "index_sha256": digest(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()),
    }
    print("SOURCE_IDENTITY " + json.dumps(record), flush=True)
    return rows


def path_witnesses(source: Snapshot, tests: bytes) -> None:
    path = source.root / LINKS
    original = path.read_bytes()
    try:
        path.write_bytes(original + tests)
        binary = BUILDS / f"{source.name}-path-tests.exe"
        run(f"{source.name}-compile-path-tests",
            ["rustc", "--edition=2024", "--test", LINKS, "-o", str(binary)], source)
        controls = run(f"{source.name}-permanent-path-controls",
                       [str(binary), "--nocapture", "--skip", "review_windows_tests"], source)
        wanted = f"test result: ok. {source.controls} passed; 0 failed;"
        if wanted not in controls:
            raise RuntimeError(f"{source.name}: permanent Windows control count differs")
        cases = [
            ("mixed-prefixes", "review_mixed_windows_prefixes_form_relative_urls", "NATIVE_WITNESS mixed-prefixes"),
            ("literal-link", "review_ordinary_link_preserves_literal_target", "NATIVE_WITNESS literal-target"),
            ("normalized-urls", "review_ordinary_trailing_components_use_normalized_urls", "NATIVE_WITNESS ordinary-normalization"),
            ("unc-normalization", "review_unc_components_use_ordinary_normalization", "NATIVE_WITNESS unc-normalization"),
        ]
        if len(source.exits) != len(cases):
            raise RuntimeError("wrong frozen outcome count")
        for (label, test, marker), expected in zip(cases, source.exits, strict=True):
            log = run(f"{source.name}-{label}",
                      [str(binary), "--exact", f"review_windows_tests::{test}", "--nocapture"],
                      source, expected)
            if marker not in log:
                raise RuntimeError(f"{source.name}/{label}: native prerequisite missing")
    finally:
        path.write_bytes(original)


def namespace_go_mutation(source: Snapshot, formatted_index: list[dict[str, str]]) -> None:
    go_path = source.root / "internal/cli/output_path_windows.go"
    go_test_path = source.root / "internal/cli/output_path_windows_test.go"
    go_fixed, go_tests = go_path.read_bytes(), go_test_path.read_bytes()
    go_anchor = b'return strings.HasPrefix(path, "\\\\\\\\?\\\\")'
    go_old = go_anchor + b' || strings.HasPrefix(path, "\\\\\\\\.\\\\")'
    if go_fixed.count(go_anchor) != 1 or go_old in go_fixed:
        raise RuntimeError("Go namespace mutation is not uniquely bound")
    go_mutant = go_fixed.replace(go_anchor, go_old)
    if go_mutant.replace(go_old, go_anchor) != go_fixed:
        raise RuntimeError("Go mutation changed more than its prefix predicate")
    mutant = Snapshot("candidate-namespace-mutant", source.root, source.head,
                      source.tree, source.index, source.controls, source.exits)
    go_binary = BUILDS / "candidate-namespace-mutant-go.exe"
    test_name = "TestMarkdownWindowsNamespaceNormalization"
    try:
        go_path.write_bytes(go_mutant)
        if go_test_path.read_bytes() != go_tests:
            raise RuntimeError("Go namespace regression bytes changed")
        run("namespace-go-mutant-compile", [
            "go", "test", "-c", "-o", str(go_binary), "./internal/cli",
        ], mutant)
        go_log = run("namespace-go-mutant-red", [
            str(go_binary), "-test.v", "-test.count=1",
            "-test.run", f"^{test_name}$",
        ], mutant, 1)
        failed = set(re.findall(r"^\s*--- FAIL: (" + test_name + r"/[^ ]+) ",
                                go_log, flags=re.MULTILINE))
        expected = {f"{test_name}/{case}" for case in (
            "device-dot-final", "device-dot-intermediate", "device-space-final",
        )}
        passed = set(re.findall(r"^\s*--- PASS: (" + test_name + r"/[^ ]+) ",
                                go_log, flags=re.MULTILINE))
        if failed != expected or len(passed) != 9:
            raise RuntimeError("Go mutation failure identities differ from the raw native witness")
        if "directory identity for " not in go_log:
            raise RuntimeError("Go mutation lacks its native file identity assertion")
    finally:
        go_path.write_bytes(go_fixed)
    if go_path.read_bytes() != go_fixed or go_test_path.read_bytes() != go_tests:
        raise RuntimeError("Go namespace mutation was not restored")
    identity(source, formatted_index)
    print("GO_NAMESPACE_MUTATION_RECEIPT " + json.dumps({
        "go_fixed_sha256": digest(go_fixed), "go_mutant_sha256": digest(go_mutant),
        "go_test_file_sha256": digest(go_tests), "go_exit": 1,
        "go_failed_subtests": sorted(failed), "go_passed_subtests": sorted(passed),
        "exact_source_restored": True,
    }), flush=True)


def format_owned_source(source: Snapshot) -> tuple[list[dict[str, str]], str]:
    before = {path: (source.root / path).read_bytes() for path in OWNED}
    run("candidate-format-owned", ["rustfmt", "--edition", "2024", *RUST_OWNED], source)
    run("candidate-format-check", ["rustfmt", "--edition", "2024", "--check", *RUST_OWNED], source)
    run("candidate-format-go-owned", ["gofmt", "-w", *GO_OWNED], source)
    changed = []
    payload = []
    for path in OWNED:
        content = (source.root / path).read_bytes()
        payload.append({"path": path, "sha256": digest(content), "blob": git_blob(content),
                        "content": content.decode("utf-8")})
        if content != before[path]:
            changed.append(path)
    (OUTPUT / "formatted-source.json").write_text(json.dumps(payload, ensure_ascii=True) + "\n")
    for item in payload:
        content = item["content"]
        chunks = [content[at:at + 16000] for at in range(0, len(content), 16000)]
        for number, chunk in enumerate(chunks):
            print("CANDIDATE_SOURCE_CHUNK " + json.dumps({
                "path": item["path"], "sha256": item["sha256"], "blob": item["blob"],
                "number": number, "chunks": len(chunks), "content": chunk,
            }, ensure_ascii=True), flush=True)
    run("candidate-stage-owned-format", ["git", "add", "--", *OWNED], source)
    tree = run("candidate-formatted-tree", ["git", "write-tree"], source).strip()
    expected = expected_index(source)
    actual = {item["path"]: item["blob"] for item in payload}
    expected = [{**row, "sha": actual.get(row["path"], row["sha"])} for row in expected]
    rows = identity(source, expected)
    (OUTPUT / "compiled-source-index.json").write_text(json.dumps(rows, sort_keys=True, separators=(",", ":")) + "\n", encoding="utf-8")
    print("CANDIDATE_FORMATTED_SOURCE " + json.dumps({
        "authored_head": source.head, "authored_tree": source.tree,
        "compiled_tree": tree, "format_changed": changed,
        "payload_sha256": digest((OUTPUT / "formatted-source.json").read_bytes()),
        "paths": [{key: value for key, value in item.items() if key != "content"} for item in payload],
    }), flush=True)
    return expected, tree


def literal(path: Path) -> Path:
    spelling = str(path)
    if spelling.startswith("\\\\?\\"):
        return path
    if spelling.startswith("\\\\"):
        return Path("\\\\?\\UNC\\" + spelling[2:])
    return Path("\\\\?\\" + spelling)


@dataclass(frozen=True)
class Case:
    name: str
    host: str
    assets: str
    actual_directory: Path
    wanted_url: str
    directory: Path


def observe_engine(binary: Path, engine: str) -> list[dict[str, str | int | bool]]:
    cases: list[Case] = []
    local = Path(os.environ["EMD_TEST_LOCAL_ROOT"])
    network = Path(os.environ["EMD_TEST_UNC_ROOT"])
    for kind, parent in [("local", local), ("unc", network)]:
        for suffix, label, escaped in [(".", "dot", "."), (" ", "space", "%20")]:
            directory = parent / f"{engine}-{kind}-{label}"
            directory.mkdir()
            (directory / "assets").mkdir()
            ordinary = directory / f"assets{suffix}"
            resolved_operand = ordinary.resolve(strict=True)
            (resolved_operand / "native.svg").write_bytes(b"native")
            if (directory / "assets/native.svg").read_bytes() != b"native":
                raise RuntimeError("ordinary native directory normalization mismatch")
            cases.append(Case(f"{kind}-{label}", "report.md", str(ordinary),
                              directory / "assets", "assets/report-1.svg", directory))
            missing = directory / "future."
            cases.append(Case(f"{kind}-{label}-missing", "future.md", str(missing),
                              directory / "future", "future/future-1.svg", directory))
            explicit = literal(directory) / f"literal{suffix}"
            explicit.mkdir()
            cases.append(Case(f"{kind}-{label}-literal", str(literal(directory) / "literal.md"),
                              str(explicit), explicit,
                              f"literal{escaped}/literal-1.svg", directory))
        directory = parent / f"{engine}-{kind}-mixed"
        directory.mkdir()
        (directory / "assets").mkdir()
        cases.extend([
            Case(f"{kind}-mixed-assets", "assets.md", str(literal(directory) / "assets"),
                 directory / "assets", "assets/assets-1.svg", directory),
            Case(f"{kind}-mixed-host", str(literal(directory) / "host.md"), "assets",
                 directory / "assets", "assets/host-1.svg", directory),
        ])
    for suffix, label, escaped in [(" ", "space", "%20"), (".", "dot", ".")]:
        directory = local / f"{engine}-symlink-{label}"
        directory.mkdir()
        target = literal(directory) / f"literal{suffix}"
        target.mkdir()
        link = directory / "linked"
        os.symlink(target, link, target_is_directory=True)
        (link / "native.svg").write_bytes(b"native")
        if (target / "native.svg").read_bytes() != b"native":
            raise RuntimeError("native symlink identity mismatch")
        cases.append(Case(f"symlink-{label}", "report.md", "linked", target,
                          f"literal{escaped}/report-1.svg", directory))
        (target / "child").mkdir()
        cases.append(Case(f"symlink-{label}-child-dot", "child.md", str(link / "child."),
                          target / "child", f"literal{escaped}/child/child-1.svg", directory))
    observations: list[dict[str, str | int | bool]] = []
    for case in cases:
        (case.directory / "input.md").write_bytes(b"\x60\x60\x60mermaid\nflowchart LR\nA --> B\n\x60\x60\x60\n")
        command = [str(binary), "render", "input.md", "-o", case.host, "-a", case.assets]
        result = subprocess.run(command, cwd=case.directory, capture_output=True, check=False)
        host = Path(case.host)
        if not host.is_absolute():
            host = case.directory / host
        host_bytes = host.read_bytes() if host.is_file() else b""
        expected = f"![diagram]({case.wanted_url})\n".encode()
        image = case.actual_directory / f"{Path(case.host).stem}-1.svg"
        record: dict[str, str | int | bool] = {
            "id": case.name, "exit": result.returncode, "stderr": result.stderr.decode("utf-8", "replace"),
            "host": host_bytes.decode("utf-8", "replace"), "expected_host": expected.decode(),
            "image_exists": image.is_file(), "image_sha256": digest(image.read_bytes()) if image.is_file() else "",
            "matches": result.returncode == 0 and host_bytes == expected and image.is_file(),
        }
        observations.append(record)
        if image.is_file():
            (OUTPUT / f"{engine}-{case.name}.svg").write_bytes(image.read_bytes())
        print("CANDIDATE_WINDOWS_OBSERVATION " + json.dumps({"engine": engine, **record}, ensure_ascii=True), flush=True)
    if len(observations) != 20:
        raise RuntimeError("expected exactly twenty frozen CLI observations")
    (OUTPUT / f"{engine}-observations.json").write_text(json.dumps(observations, indent=2) + "\n")
    print("CANDIDATE_WINDOWS_OBSERVATION_COUNT " + json.dumps({"engine": engine, "count": len(observations)}), flush=True)
    return observations


def final_filename_observations(binary: Path, engine: str) -> list[dict[str, str | int | bool]]:
    root = Path(os.environ["EMD_TEST_LOCAL_ROOT"])
    observations: list[dict[str, str | int | bool]] = []
    cases = [
        ("ordinary-dot", "image.svg.", False, "image.svg-1"),
        ("ordinary-space", "image.svg ", False, "image-1.svg"),
        ("verbatim-dot", "image.svg.", True, "image.svg-1."),
        ("verbatim-space", "image.svg ", True, "image-1.svg "),
    ]
    for label, output_name, explicit, expected_name in cases:
        directory = root / f"{engine}-final-{label}"
        directory.mkdir()
        native = directory / "native"
        native.mkdir()
        raw_native = (literal(native) if explicit else native) / output_name
        raw_native.write_bytes(b"native")
        native_name = output_name if explicit else output_name.rstrip(". ")
        native_files = sorted(path.name for path in literal(native).iterdir())
        if native_files != [native_name]:
            raise RuntimeError(f"{label}: native final filename boundary differs")
        if (literal(native) / native_name).read_bytes() != b"native":
            raise RuntimeError("native filename identity mismatch")
        source = b"\x60\x60\x60mermaid\nflowchart LR\nA --> B\n\x60\x60\x60\n"
        (directory / "input.md").write_bytes(source)
        output = (literal(directory) if explicit else directory) / output_name
        command = [str(binary), "render", "input.md", "-e", "svg", "-o", str(output)]
        process = subprocess.run(command, cwd=directory, capture_output=True, check=False)
        names = sorted(path.name for path in literal(directory).iterdir()
                       if path.name not in ("input.md", "native"))
        target = literal(directory) / expected_name
        record: dict[str, str | int | bool] = {
            "id": label, "exit": process.returncode, "stderr": process.stderr.decode("utf-8", "replace"),
            "native_name": native_name, "expected_name": expected_name,
            "actual_names_json": json.dumps(names, ensure_ascii=True),
            "image_sha256": digest(target.read_bytes()) if target.is_file() else "",
            "matches": process.returncode == 0 and names == [expected_name] and target.is_file(),
        }
        observations.append(record)
        if target.is_file():
            (OUTPUT / f"{engine}-final-{label}.svg").write_bytes(target.read_bytes())
        print("FINAL_FILENAME_OBSERVATION " + json.dumps({"engine": engine, **record}, ensure_ascii=True), flush=True)
    if len(observations) != 4:
        raise RuntimeError(f"{engine}: final filename observation count differs")
    return observations


def compare_engines(left: list[dict[str, str | int | bool]],
                    right: list[dict[str, str | int | bool]], label: str) -> None:
    if [item["id"] for item in left] != [item["id"] for item in right]:
        raise RuntimeError(f"{label}: engine case identities differ")
    for go, rust in zip(left, right, strict=True):
        if not go["matches"] or not rust["matches"]:
            raise RuntimeError(f"{label}/{go['id']}: native expected placement or URL differs")
        if go.get("host") != rust.get("host") or go["image_sha256"] != rust["image_sha256"]:
            raise RuntimeError(f"{label}/{go['id']}: engine output bytes differ")
    print("ENGINE_PARITY " + json.dumps({"scope": label, "cases": len(left), "matches": True}), flush=True)


def restore_owned(source: Snapshot, original: dict[str, bytes]) -> None:
    index = {row["path"]: row for row in expected_index(source)}
    for path, content in original.items():
        (source.root / path).write_bytes(content)
        row = index[path]
        run(f"restore-index-{Path(path).stem}",
            ["git", "update-index", "--cacheinfo", row["mode"], row["sha"], path], source)


def main() -> None:
    candidate = snapshot("candidate")
    original = {path: (candidate.root / path).read_bytes() for path in OWNED}
    report: dict[str, object] = {
        "candidate": candidate.head, "authored_tree": candidate.tree,
        "publication_eligible": False, "source_restored": False,
        "focused_verification_passed": False, "repository_wide_gates_run": False,
        "prior_run_conclusion": "failure", "reused_commands": [], "executed_commands": [],
    }
    try:
        for name, wanted in MANIFEST["proof_sha256"].items():
            if digest((PROOF / name).read_bytes()) != wanted:
                raise RuntimeError(f"proof hash mismatch: {name}")
        workflow = WORKSPACE / "proof" / ".github/workflows/elegant-paired-windows-r35.yml"
        if digest(workflow.read_bytes()) != MANIFEST["workflow_sha256"]:
            raise RuntimeError("producer workflow hash mismatch")
        if run("candidate-head", ["git", "rev-parse", "HEAD"], candidate).strip() != candidate.head:
            raise RuntimeError("wrong frozen source commit")
        if run("candidate-tree", ["git", "rev-parse", "HEAD^{tree}"], candidate).strip() != candidate.tree:
            raise RuntimeError("wrong frozen source tree")
        identity(candidate)
        rust_version = run("rust-version", ["rustc", "--version"], candidate)
        go_version = run("go-version", ["go", "version"], candidate)
        rust_lines = [line for line in rust_version.splitlines() if line.startswith("rustc ")]
        if len(rust_lines) != 1 or not rust_lines[0].startswith("rustc 1.100.0 "):
            raise RuntimeError("Rust toolchain identity differs")
        if go_version.strip() != "go version go1.27.4 windows/amd64":
            raise RuntimeError("Go toolchain identity differs")
        if run("go-cache-disabled", ["go", "env", "GOCACHEPROG"], candidate).strip():
            raise RuntimeError("external Go cache is active")
        prior = authenticate(PROOF, OUTPUT, MANIFEST["receipt_reuse"])
        report["authenticated_prior_evidence"] = prior.provenance
        report["reused_commands"] = prior.reused
        allowed = "internal/cli/output_path_windows_test.go"
        require_test_only_delta(candidate.root, prior, allowed)
        formatted_index, tree = format_owned_source(candidate)
        report["compiled_tree"] = tree
        report["test_only_delta"] = require_test_only_delta(candidate.root, prior, allowed)
        namespace_go_mutation(candidate, formatted_index)
        go_files = sorted(str(path.relative_to(candidate.root))
                          for path in (candidate.root / "internal/cli").glob("*.go"))
        if not go_files:
            raise RuntimeError("scoped Go source files missing")
        if run("candidate-go-format", ["gofmt", "-l", *go_files], candidate).strip():
            raise RuntimeError("candidate Go formatting differs")
        run("candidate-go-vet", ["go", "vet", "./internal/cli"], candidate)
        run("candidate-go-lint", ["go", "tool", "golangci-lint", "run", "./internal/cli"], candidate)
        go_binary = BUILDS / "emd-go.exe"
        run("candidate-go-cli", ["go", "build", "-trimpath", "-o", str(go_binary), "./cmd/emd"], candidate)
        go_tests: list[str] = MANIFEST["go_test_names"]
        if len(go_tests) != 6 or any(not re.fullmatch("Test[A-Za-z0-9_]+", name) for name in go_tests):
            raise RuntimeError("six targeted Go test names are not bound")
        pattern = "^(" + "|".join(go_tests) + ")$"
        os.environ["EMD_BIN"] = str(go_binary)
        go_log = run("candidate-go-ownership-tests",
                     ["go", "test", "-count=1", "-v", "-run", pattern, "./internal/cli"], candidate)
        passed = set(re.findall(r"^--- PASS: (Test[A-Za-z0-9_]+) ", go_log, flags=re.MULTILINE))
        if passed != set(go_tests):
            raise RuntimeError("one or more required native Go ownership tests did not pass")
        run("candidate-rust-cli",
            ["cargo", "build", "-p", "emd-cli", "--bin", "emd", "--all-features", "--locked", "--release"],
            candidate)
        rust_binary = BUILDS / "cargo-candidate/release/emd.exe"
        if not rust_binary.is_file():
            raise RuntimeError("fresh Rust CLI missing")
        print("BUILT_BINARIES " + json.dumps({
            "go_sha256": digest(go_binary.read_bytes()),
            "rust_sha256": digest(rust_binary.read_bytes()),
        }), flush=True)
        go_observations = observe_engine(go_binary, "go")
        rust_observations = observe_engine(rust_binary, "rust")
        go_final = final_filename_observations(go_binary, "go")
        rust_final = final_filename_observations(rust_binary, "rust")
        compare_engines(go_observations, rust_observations, "frozen-Windows-paths")
        compare_engines(go_final, rust_final, "final-filenames")
        identity(candidate, formatted_index)
        run("candidate-whitespace", ["git", "diff", "--check", "HEAD"], candidate)
        report["focused_verification_passed"] = True
    finally:
        restore_owned(candidate, original)
        identity(candidate)
        run("candidate-final-restoration", ["git", "diff", "--exit-code", "HEAD"], candidate)
        report["source_restored"] = True
        report["executed_commands"] = RECEIPTS
        (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("FOCUSED_WINDOWS_FOLLOWUP_REPORT " + json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
