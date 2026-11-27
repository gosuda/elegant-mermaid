"""Observe raw Windows namespace identity without changing product source."""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Final

SOURCE: Final = Path(sys.argv[1]).absolute()
PROOF: Final = Path(sys.argv[2]).absolute()
OUTPUT: Final = Path(sys.argv[3]).absolute()
OUTPUT.mkdir(parents=True, exist_ok=True)
BUILDS: Final = OUTPUT.parent / "emd-namespace-r36-builds"
BUILDS.mkdir(parents=True, exist_ok=True)
LINKS: Final = "crates/elegant-mermaid-cli/src/render/markdown/links.rs"
MANIFEST: Final = json.loads((PROOF / "manifest.json").read_text(encoding="utf-8"))
RECEIPTS: list[dict[str, object]] = []


def digest(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def run(name: str, command: list[str], environment: dict[str, str] | None = None) -> str:
    result = subprocess.run(
        command, cwd=SOURCE, env=environment, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False, timeout=600,
    )
    raw = result.stdout
    (OUTPUT / f"{name}.log").write_bytes(raw)
    record: dict[str, object] = {
        "name": name, "command": command, "exit": result.returncode,
        "expected": 0, "log_sha256": digest(raw),
    }
    RECEIPTS.append(record)
    print("COMMAND_RECEIPT " + json.dumps(record), flush=True)
    text = raw.decode("utf-8", errors="strict")
    print(text, end="" if text.endswith("\n") else "\n", flush=True)
    if result.returncode != 0:
        raise RuntimeError(f"{name}: actual exit {result.returncode}")
    return text


def identity(label: str) -> dict[str, object]:
    rows: list[dict[str, str]] = json.loads((PROOF / "candidate-index.json").read_text(encoding="utf-8"))
    if len(rows) != 6714 or len({row["path"] for row in rows}) != 6714:
        raise RuntimeError("wrong frozen candidate source count")
    actual: list[dict[str, str]] = []
    for row in rows:
        content = (SOURCE / row["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
        if blob != row["sha"]:
            raise RuntimeError(f"source blob mismatch: {row['path']}")
        actual.append({**row, "sha256": digest(content)})
    process = subprocess.run(
        ["git", "ls-files", "-s", "-z"], cwd=SOURCE, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, check=True, timeout=120,
    )
    entries: dict[str, tuple[str, str]] = {}
    for entry in process.stdout.decode("utf-8").rstrip("\0").split("\0"):
        metadata, path = entry.split("\t", 1)
        mode, blob, stage = metadata.split()
        if stage != "0":
            raise RuntimeError("unmerged source entry")
        entries[path] = (mode, blob)
    if entries != {row["path"]: (row["mode"], row["sha"]) for row in rows}:
        raise RuntimeError("tracked index/mode mismatch")
    record: dict[str, object] = {
        "label": label, "commit": MANIFEST["source"]["commit"],
        "tree": MANIFEST["source"]["tree"], "tracked_blobs": len(rows),
        "content_index_sha256": digest(json.dumps(actual, sort_keys=True, separators=(",", ":")).encode()),
    }
    (OUTPUT / f"{label}-source-index.json").write_text(
        json.dumps(actual, sort_keys=True, indent=2) + "\n", encoding="utf-8",
    )
    print("SOURCE_IDENTITY " + json.dumps(record), flush=True)
    return record


def decode_utf16_hex(value: str) -> str:
    if len(value) % 4 or not re.fullmatch(r"[0-9a-f]*", value):
        raise RuntimeError("malformed exact UTF-16 record")
    return bytes.fromhex(value).decode("utf-16-be", errors="strict")


def main() -> None:
    for path, expected in MANIFEST["files"].items():
        if digest((PROOF / path).read_bytes()) != expected:
            raise RuntimeError(f"frozen proof hash mismatch: {path}")
    head = run("source-head", ["git", "rev-parse", "HEAD"]).strip()
    tree = run("source-tree", ["git", "rev-parse", "HEAD^{tree}"]).strip()
    if head != MANIFEST["source"]["commit"] or tree != MANIFEST["source"]["tree"]:
        raise RuntimeError("unexpected checkout identity")
    original = (SOURCE / LINKS).read_bytes()
    restored = False
    before = identity("before")
    failure: str | None = None
    try:
        run("native-namespace", [
            "pwsh", "-NoProfile", "-File", str(PROOF / "native.ps1"),
            "-Evidence", str(OUTPUT), "-Phase", "native",
        ])
        native = json.loads((OUTPUT / "native.json").read_text(encoding="utf-8"))
        cases = native["cases"]
        expected_ids = {
            f"{prefix}-{suffix}-{position}"
            for prefix in ("ordinary", "device", "verbatim")
            for suffix in ("dot", "space")
            for position in ("final", "intermediate")
        }
        if {case["id"] for case in cases} != expected_ids or len(cases) != 12:
            raise RuntimeError("native matrix identity mismatch")
        for case in cases:
            if case["input"].endswith("\\") or case["input"] != case["native"]["Input"]:
                raise RuntimeError("native operand was normalized or gained a trailing separator")
            if decode_utf16_hex(case["native"]["InputUtf16"]) != case["input"]:
                raise RuntimeError("native exact input encoding mismatch")
        versions = run("rust-version", ["rustc", "--version"])
        rust_lines = [line for line in versions.splitlines() if line.startswith("rustc ")]
        if len(rust_lines) != 1 or not rust_lines[0].startswith("rustc 1.100.0 "):
            raise RuntimeError("unexpected Rust compiler")
        binary = BUILDS / "candidate-namespace.exe"
        (SOURCE / LINKS).write_bytes(original + (PROOF / "namespace-observer.rs").read_bytes())
        run("candidate-standalone-compile", [
            "rustc", "--edition=2024", "--test", LINKS, "-o", str(binary),
        ])
        environment = dict(os.environ)
        environment["EMD_NAMESPACE_CASES"] = str(OUTPUT / "cases.tsv")
        observed = run("candidate-standalone-observe", [
            str(binary), "--exact", "namespace_observer_r36::raw_namespace_paths",
            "--nocapture", "--test-threads=1",
        ], environment)
        results: list[dict[str, object]] = []
        for line in observed.splitlines():
            if "RUST_NAMESPACE\t" not in line:
                continue
            fields = line[line.index("RUST_NAMESPACE\t"):].split("\t")
            if len(fields) != 6:
                raise RuntimeError("incomplete Rust observation")
            _, case_id, input_hex, status, payload, error = fields
            if status not in ("ok", "err"):
                raise RuntimeError("invalid Rust observation status")
            results.append({
                "id": case_id, "input": decode_utf16_hex(input_hex), "status": status,
                "resolved": decode_utf16_hex(payload) if status == "ok" else "",
                "error_kind": payload if status == "err" else "", "os_error": int(error),
            })
        if len(results) != 12 or {row["id"] for row in results} != expected_ids:
            raise RuntimeError("incomplete or duplicated Rust observations")
        (OUTPUT / "rust-results.json").write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
        run("candidate-native-identity", [
            "pwsh", "-NoProfile", "-File", str(PROOF / "native.ps1"),
            "-Evidence", str(OUTPUT), "-Phase", "candidate",
        ])
        comparison = json.loads((OUTPUT / "candidate-observations.json").read_text(encoding="utf-8"))
        summary = {
            "cases": 12,
            "raw_native_open_failures": sum(not case["native"]["Success"] for case in cases),
            "candidate_resolver_errors": sum(row["status"] == "err" for row in results),
            "candidate_same_native_identity": sum(row["same_native_identity"] for row in comparison),
            "candidate_comparison_is_observational": True,
            "binary_sha256": digest(binary.read_bytes()),
        }
        (OUTPUT / "observation-summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print("NAMESPACE_OBSERVATION_SUMMARY " + json.dumps(summary), flush=True)
    except Exception as error:
        failure = f"{type(error).__name__}: {error}"
        raise
    finally:
        (SOURCE / LINKS).write_bytes(original)
        after = identity("after")
        if before["content_index_sha256"] != after["content_index_sha256"]:
            raise RuntimeError("source identity changed after restoration")
        restored = True
        report = {
            "source": MANIFEST["source"], "producer": os.environ["GITHUB_SHA"],
            "run_id": os.environ["GITHUB_RUN_ID"], "attempt": os.environ["GITHUB_RUN_ATTEMPT"],
            "source_restored": restored, "source_identity": after,
            "failure": failure, "commands": RECEIPTS,
            "scope": "native namespace observation and standalone Rust resolver; no repository gates",
        }
        (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("NAMESPACE_PROOF_REPORT " + json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
