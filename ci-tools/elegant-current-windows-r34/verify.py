"""Observe current Elegant Mermaid PR28 against frozen native Windows witnesses."""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Final

SOURCE: Final = Path(sys.argv[1]).absolute()
PROOF: Final = Path(sys.argv[2]).absolute()
OUTPUT: Final = Path(sys.argv[3]).absolute()
OUTPUT.mkdir(parents=True, exist_ok=True)
RELATIVE: Final = Path("crates/elegant-mermaid-cli/src/render/markdown/links.rs")
MANIFEST: Final = json.loads((PROOF / "manifest.json").read_text())
HEAD: Final = MANIFEST["source"]
TREE: Final = MANIFEST["source_tree"]
if not isinstance(HEAD, str) or len(HEAD) != 40 or not isinstance(TREE, str) or len(TREE) != 40:
    raise RuntimeError("Parent must bind the exact current-head plus timeout-only source before launch")
RECEIPTS: list[dict[str, str | int | list[str] | tuple[int, ...]]] = []


def digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def run(name: str, command: list[str], expected: int | tuple[int, ...] = 0, cwd: Path = SOURCE) -> str:
    result = subprocess.run(
        command, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        encoding="utf-8", errors="replace", check=False,
    )
    log = result.stdout
    (OUTPUT / f"{name}.log").write_text(log, encoding="utf-8")
    record: dict[str, str | int | list[str] | tuple[int, ...]] = {
        "name": name, "command": command, "exit": result.returncode,
        "expected": expected, "log_sha256": digest(log.encode("utf-8")),
    }
    RECEIPTS.append(record)
    print("COMMAND_RECEIPT " + json.dumps(record), flush=True)
    print(log, end="" if log.endswith("\n") else "\n", flush=True)
    accepted = (expected,) if isinstance(expected, int) else expected
    if result.returncode not in accepted:
        raise RuntimeError(f"{name}: actual exit {result.returncode}, expected {expected}")
    return log


def identity() -> list[dict[str, str]]:
    expected: list[dict[str, str]] = json.loads((PROOF / "source-index.json").read_text())
    rows: list[dict[str, str]] = []
    for row in expected:
        content = (SOURCE / row["path"]).read_bytes()
        header = f"blob {len(content)}\0".encode("ascii")
        blob = hashlib.sha1(header + content, usedforsecurity=False).hexdigest()
        if blob != row["sha"]:
            raise RuntimeError(f"source blob mismatch: {row['path']}")
        rows.append({**row, "sha256": digest(content)})
    actual = subprocess.run(
        ["git", "ls-files", "-s", "-z"], cwd=SOURCE, stdout=subprocess.PIPE, check=True,
    ).stdout.decode("utf-8")
    entries: dict[str, tuple[str, str]] = {}
    for item in actual.rstrip("\0").split("\0"):
        meta, path = item.split("\t", 1)
        mode, blob, stage = meta.split()
        if stage != "0":
            raise RuntimeError("unmerged source index")
        entries[path] = (mode, blob)
    wanted = {row["path"]: (row["mode"], row["sha"]) for row in expected}
    if entries != wanted:
        raise RuntimeError("tracked source index differs from frozen manifest")
    print("SOURCE_IDENTITY " + json.dumps({
        "head": HEAD, "tracked_blobs": len(rows),
        "index_sha256": digest(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()),
    }), flush=True)
    return rows


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


def observe_go(binary: Path) -> None:
    cases: list[Case] = []
    local = Path(os.environ["EMD_TEST_LOCAL_ROOT"])
    network = Path(os.environ["EMD_TEST_UNC_ROOT"])
    for kind, parent in [("local", local), ("unc", network)]:
        for suffix, label, escaped in [(".", "dot", "."), (" ", "space", "%20")]:
            directory = parent / f"go-{kind}-{label}"
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
        directory = parent / f"go-{kind}-mixed"
        directory.mkdir()
        (directory / "assets").mkdir()
        cases.extend([
            Case(f"{kind}-mixed-assets", "assets.md", str(literal(directory) / "assets"),
                 directory / "assets", "assets/assets-1.svg", directory),
            Case(f"{kind}-mixed-host", str(literal(directory) / "host.md"), "assets",
                 directory / "assets", "assets/host-1.svg", directory),
        ])
    for suffix, label, escaped in [(" ", "space", "%20"), (".", "dot", ".")]:
        directory = local / f"go-symlink-{label}"
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
            "image_exists": image.is_file(), "matches": result.returncode == 0 and host_bytes == expected and image.is_file(),
        }
        observations.append(record)
        print("GO_WINDOWS_OBSERVATION " + json.dumps(record, ensure_ascii=True), flush=True)
    if len(observations) != 20:
        raise RuntimeError("expected exactly twenty frozen Go CLI observations")
    (OUTPUT / "go-observations.json").write_text(json.dumps(observations, indent=2) + "\n")
    print("GO_WINDOWS_OBSERVATION_COUNT " + str(len(observations)), flush=True)


def main() -> None:
    original = (SOURCE / RELATIVE).read_bytes()
    report: dict[str, str | int | bool | list[dict[str, str | int | list[str] | tuple[int, ...]]]] = {
        "source": HEAD, "publication_eligible": False, "source_restored": False,
    }
    try:
        if run("source-head", ["git", "rev-parse", "HEAD"]).strip() != HEAD:
            raise RuntimeError("wrong source commit")
        if run("source-tree", ["git", "rev-parse", "HEAD^{tree}"]).strip() != TREE:
            raise RuntimeError("wrong source tree")
        identity()
        rust_output = run("rust-version", ["rustc", "--version"])
        rust_versions = [line for line in rust_output.splitlines() if line.startswith("rustc ")]
        if len(rust_versions) != 1 or not rust_versions[0].startswith("rustc 1.100.0 "):
            raise RuntimeError("unexpected Rust version")
        if not run("go-version", ["go", "version"]).startswith("go version go1.27.4 windows/amd64"):
            raise RuntimeError("unexpected Go version")
        workflow = PROOF.parents[1] / ".github/workflows/elegant-current-windows-r34.yml"
        if digest(workflow.read_bytes()) != MANIFEST["workflow_sha256"]:
            raise RuntimeError("workflow identity mismatch")
        manifest = MANIFEST
        for name, expected in manifest["proof_sha256"].items():
            if digest((PROOF / name).read_bytes()) != expected:
                raise RuntimeError(f"proof identity mismatch: {name}")
        tests = (PROOF / "windows-regressions.rs").read_bytes()
        (SOURCE / RELATIVE).write_bytes(original + tests)
        binary = OUTPUT / "windows-regressions.exe"
        run("compile-regressions", ["rustc", "--edition=2024", "--test", str(RELATIVE), "-o", str(binary)])
        controls = run("existing-path-controls", [str(binary), "--nocapture", "--skip", "review_windows_tests"])
        if "test result: ok. 8 passed; 0 failed;" not in controls:
            raise RuntimeError("the eight current-source Windows path controls did not all pass")
        cases = [
            ("mixed-prefixes", "review_mixed_windows_prefixes_form_relative_urls", "NATIVE_WITNESS mixed-prefixes"),
            ("literal-link", "review_ordinary_link_preserves_literal_target", "NATIVE_WITNESS literal-target"),
            ("normalized-urls", "review_ordinary_trailing_components_use_normalized_urls", "NATIVE_WITNESS ordinary-normalization"),
            ("unc-normalization", "review_unc_components_use_ordinary_normalization", "NATIVE_WITNESS unc-normalization"),
        ]
        for name, test, marker in cases:
            log = run(name, [str(binary), "--exact", f"review_windows_tests::{test}", "--nocapture"], expected=(0, 101))
            if marker not in log:
                raise RuntimeError(f"{name}: native filesystem witness did not finish")
        (SOURCE / RELATIVE).write_bytes(original)
        normalization = OUTPUT / "normalization.exe"
        run("compile-native-normalization", ["rustc", "--edition=2024", str(PROOF / "normalization.rs"), "-o", str(normalization)])
        normalization_log = run("native-normalization", [str(normalization)])
        if sum(line.startswith("WINDOWS_NORMALIZE ") for line in normalization_log.splitlines()) != 19:
            raise RuntimeError("expected exactly nineteen native normalization observations")
        go_binary = OUTPUT / "emd-go.exe"
        run("build-go-observer", ["go", "build", "-trimpath", "-o", str(go_binary), "./cmd/emd"])
        observe_go(go_binary)
        report["frozen_witness_observations_complete"] = True
        report["candidate_verified"] = False
    finally:
        (SOURCE / RELATIVE).write_bytes(original)
        identity()
        run("source-restoration", ["git", "diff", "--exit-code"])
        report["source_restored"] = True
        report["commands"] = RECEIPTS
        (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print("CURRENT_HEAD_OBSERVATION_REPORT " + json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
