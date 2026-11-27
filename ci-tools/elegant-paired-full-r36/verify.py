"""Run the repository's complete verification on one immutable paired source."""
from __future__ import annotations

import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Final

from resource_support import ResourceTrace, abort_process_group

SOURCE: Final = Path(sys.argv[1]).absolute()
PROOF: Final = Path(sys.argv[2]).absolute()
OUTPUT: Final = Path(sys.argv[3]).absolute()
OUTPUT.mkdir(parents=True, exist_ok=True)
TEMP: Final = OUTPUT.parent / "elegant-full-builds"
TEMP.mkdir(parents=True, exist_ok=True)
EXPECTED_GATES: Final = (
    "gen-check", "go-check", "rust-check", "markdown-paths", "slop", "build",
    "proofs", "model", "oracle", "parity", "markdown-parity", "wasm-parity",
    "playground-check", "playground-e2e", "layered-random-check", "kernel-diff",
    "validate", "lean-parity", "quality", "theme-check",
)


@dataclass(frozen=True)
class SourceEntry:
    path: str
    mode: str
    sha: str


@dataclass(frozen=True)
class Receipt:
    name: str
    command: tuple[str, ...]
    raw_exit: int | None
    timed_out: bool
    seconds: float
    log_sha256: str
    accepted: bool
    monitor_errors: tuple[str, ...]


RECEIPTS: Final[list[Receipt]] = []
RESOURCE_REPORTS: Final[list[dict[str, object]]] = []


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def object_value(value: object, context: str) -> dict[str, object]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise ValueError(f"{context} must be a JSON object")
    return value


def text_value(value: object, context: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{context} must be text")
    return value


def read_object(path: Path) -> dict[str, object]:
    value: object = json.loads(path.read_bytes())
    return object_value(value, str(path))


def checked_sha(value: object, width: int, context: str) -> str:
    text = text_value(value, context)
    if not re.fullmatch(f"[0-9a-f]{{{width}}}", text):
        raise ValueError(f"Invalid {context}")
    return text


def source_entries(path: Path) -> list[SourceEntry]:
    value: object = json.loads(path.read_bytes())
    if not isinstance(value, list):
        raise ValueError("Source index must be a JSON array")
    entries: list[SourceEntry] = []
    seen: set[str] = set()
    for raw in value:
        row = object_value(raw, "source entry")
        name = text_value(row.get("path"), "source path")
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or not name or name in seen:
            raise ValueError(f"Unsafe or duplicate source path: {name}")
        mode = text_value(row.get("mode"), "source mode")
        if mode not in ("100644", "100755"):
            raise ValueError(f"Unsupported source mode: {mode}")
        entries.append(SourceEntry(name, mode, checked_sha(row.get("sha"), 40, "Git blob")))
        seen.add(name)
    return sorted(entries, key=lambda entry: entry.path)


def environment() -> dict[str, str]:
    env = os.environ.copy()
    env.update({
        "GOENV": "off", "GOCACHEPROG": "", "GOTOOLCHAIN": "local",
        "GOCACHE": str(TEMP / "go"), "GOMAXPROCS": "8",
        "CARGO_TARGET_DIR": str(TEMP / "cargo"), "CARGO_BUILD_JOBS": "4",
        "CARGO_INCREMENTAL": "0", "RUSTC_WRAPPER": "", "RUSTC_WORKSPACE_WRAPPER": "",
        "RUSTUP_TOOLCHAIN": "1.100.0", "LEAN_NUM_THREADS": "4",
        "BASE_PATH": "/elegant-mermaid", "NO_COLOR": "1", "CLICOLOR": "0",
        "CI": "true", "PYTHONUNBUFFERED": "1",
    })
    return env


def run(name: str, command: list[str], timeout: int = 300,
        measure_resources: bool = False) -> Path:
    log = OUTPUT / f"{name}.log"
    started = time.monotonic()
    timed_out = False
    raw_exit: int | None = None
    trace: ResourceTrace | None = None
    process: subprocess.Popen[bytes] | None = None
    original_error: BaseException | None = None
    monitor_errors: list[str] = []
    phase = "start"
    print("FULL_COMMAND_START " + json.dumps({"name": name, "command": command}), flush=True)
    try:
        if measure_resources:
            phase = "monitor-start"
            trace = ResourceTrace(OUTPUT)
        with log.open("wb") as stream:
            phase = "spawn"
            if trace is None:
                process = subprocess.Popen(
                    command, cwd=SOURCE, env=environment(), stdout=stream,
                    stderr=subprocess.STDOUT, start_new_session=True,
                )
            else:
                process = trace.spawn(command, SOURCE, environment(), stream)
            deadline = started + timeout
            next_progress = started + 30
            while True:
                if trace is not None:
                    phase = "monitor-sample"
                    trace.sample(process.pid)
                phase = "wait"
                remaining = deadline - time.monotonic()
                try:
                    raw_exit = process.wait(timeout=max(0.001, min(2 if trace is not None else 30, remaining)))
                    break
                except subprocess.TimeoutExpired:
                    if time.monotonic() < deadline:
                        if time.monotonic() >= next_progress:
                            print("FULL_COMMAND_PROGRESS " + json.dumps({
                                "name": name, "seconds": round(time.monotonic() - started, 1),
                                "log_bytes": log.stat().st_size,
                            }), flush=True)
                            next_progress = time.monotonic() + 30
                        continue
                    timed_out = True
                    raw_exit = abort_process_group(process)
                    break
    except BaseException as error:
        original_error = error
        monitor_errors.append(f"{phase}: {type(error).__name__}: {error}")
        owned_child = process if process is not None else (trace.child if trace is not None else None)
        if owned_child is not None:
            raw_exit = abort_process_group(owned_child)
    finally:
        if trace is not None:
            try:
                measured = trace.finish()
            except BaseException as error:
                if original_error is None:
                    original_error = error
                monitor_errors.append(f"monitor-finish: {type(error).__name__}: {error}")
                measured = trace.known_report()
            measured["monitor_errors"] = list(monitor_errors)
            RESOURCE_REPORTS.append(measured)
            print("FULL_RESOURCE_REPORT " + json.dumps(measured), flush=True)
    accepted = raw_exit == 0 and not timed_out and not monitor_errors
    receipt = Receipt(
        name, tuple(command), raw_exit, timed_out, time.monotonic() - started,
        file_digest(log) if log.exists() else "", accepted, tuple(monitor_errors),
    )
    RECEIPTS.append(receipt)
    print("FULL_COMMAND_RESULT " + json.dumps(asdict(receipt)), flush=True)
    if not accepted:
        if log.exists():
            with log.open("rb") as stream:
                stream.seek(max(0, log.stat().st_size - 120_000))
                print(stream.read().decode("utf-8", errors="replace"), flush=True)
        raise RuntimeError(
            f"{name} failed with actual exit {raw_exit}; timeout={timed_out}; monitor_errors={monitor_errors}"
        ) from original_error
    return log


def git_output(arguments: list[str]) -> bytes:
    result = subprocess.run(
        ["git", *arguments], cwd=SOURCE, env=environment(),
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(f"git {arguments} failed: {result.stderr.decode('utf-8', errors='replace')}")
    return result.stdout


def identity(entries: list[SourceEntry], expected_tree: str, label: str) -> str:
    actual: list[SourceEntry] = []
    for record in git_output(["ls-files", "--stage", "-z"]).split(b"\0"):
        if not record:
            continue
        metadata, raw_path = record.split(b"\t", 1)
        mode, blob, stage = metadata.decode("ascii").split()
        if stage != "0":
            raise RuntimeError("Unmerged source index")
        actual.append(SourceEntry(raw_path.decode("utf-8"), mode, blob))
    actual.sort(key=lambda entry: entry.path)
    if actual != entries:
        raise RuntimeError("Complete tracked source index differs")
    for entry in entries:
        path = SOURCE / entry.path
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"Expected a regular source file: {entry.path}")
        content = path.read_bytes()
        blob = hashlib.sha1(f"blob {len(content)}\0".encode("ascii") + content).hexdigest()
        executable = bool(path.stat().st_mode & 0o111)
        if blob != entry.sha or executable != (entry.mode == "100755"):
            raise RuntimeError(f"Source content or mode differs: {entry.path}")
    tree = git_output(["write-tree"]).decode("ascii").strip()
    if tree != expected_tree:
        raise RuntimeError(f"Source tree differs: {tree}")
    encoded = json.dumps([asdict(entry) for entry in entries], separators=(",", ":")).encode("utf-8")
    digest = sha256(encoded)
    print("FULL_SOURCE_IDENTITY " + json.dumps({
        "label": label, "tree": tree, "blobs": len(entries), "index_sha256": digest,
    }), flush=True)
    return digest


def verify_version(name: str, command: list[str], pattern: str) -> None:
    output = run(name, command).read_text(encoding="utf-8")
    if not re.search(pattern, output, flags=re.MULTILINE):
        raise RuntimeError(f"{name} does not match the pinned tool version")
    print("FULL_TOOL_VERSION " + json.dumps({"name": name, "output": output.strip()}), flush=True)


def main() -> None:
    manifest = read_object(PROOF / "manifest.json")
    source = object_value(manifest.get("source"), "source")
    head = checked_sha(source.get("head"), 40, "source head")
    tree = checked_sha(source.get("tree"), 40, "source tree")
    proof_hashes = object_value(manifest.get("proof_sha256"), "proof hashes")
    for name, expected in proof_hashes.items():
        if Path(name).name != name:
            raise ValueError("Proof filenames must be local")
        if file_digest(PROOF / name) != checked_sha(expected, 64, "proof digest"):
            raise RuntimeError(f"Proof digest differs: {name}")
    entries = source_entries(PROOF / "source-index.json")
    if len(entries) != source.get("blobs"):
        raise RuntimeError("Source blob count differs")
    if git_output(["rev-parse", "HEAD"]).decode("ascii").strip() != head:
        raise RuntimeError("Wrong immutable source checkout")
    if git_output(["rev-parse", "HEAD^{tree}"]).decode("ascii").strip() != tree:
        raise RuntimeError("Wrong committed source tree")
    report: dict[str, object] = {
        "schema": 1, "manifest": manifest, "source_gates_passed": False,
        "source_restored": False, "publication_eligible": False,
    }
    try:
        report["initial_index_sha256"] = identity(entries, tree, "before")
        verify_version("rust-version", ["rustc", "--version"], r"^rustc 1\.100\.0 ")
        verify_version("go-version", ["go", "version"], r"^go version go1\.27\.4 linux/amd64$")
        verify_version("node-version", ["node", "--version"], r"^v26\.13\.1$")
        verify_version("pnpm-version", ["pnpm", "--version"], r"^12\.23\.0$")
        verify_version("just-version", ["just", "--version"], r"^just 1\.59\.0$")
        verify_version("nextest-version", ["cargo", "nextest", "--version"], r"^cargo-nextest 0\.9\.151(?:\s|$)")
        verify_version("deny-version", ["cargo", "deny", "--version"], r"^cargo-deny 0\.20\.2(?:\s|$)")
        verify_version("jaq-version", ["jaq", "--version"], r"^jaq 3\.2\.0(?:\s|$)")
        verify_version("wasm-bindgen-version", ["wasm-bindgen", "--version"], r"^wasm-bindgen 0\.2\.130(?:\s|$)")
        verify_version("lean-version", ["lean", "--version"], r"Lean \(version 4\.35\.0,")
        if run("go-cache-disabled", ["go", "env", "GOCACHEPROG"]).read_text(encoding="utf-8").strip():
            raise RuntimeError("External Go cache is active")
        if file_digest(SOURCE / ".tools/tla2tools.jar") != "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88":
            raise RuntimeError("Pinned TLC archive differs")
        install_metadata = Path(os.environ["EMD_HOUSE_ROOT"]) / ".crates2.json"
        if "72f29bae0ba1187da854e080c998b8a21f1e4640" not in install_metadata.read_text(encoding="utf-8"):
            raise RuntimeError("House linter source pin differs")
        house_binary = Path(os.environ["EMD_HOUSE_ROOT"]) / "bin/sloplint"
        report["house_linter"] = {
            "source": "72f29bae0ba1187da854e080c998b8a21f1e4640",
            "binary_sha256": file_digest(house_binary),
            "install_metadata_sha256": file_digest(install_metadata),
        }
        full_log = run("just-verify", ["just", "verify"], timeout=9600, measure_resources=True)
        markers = {
            line.strip()[5:]
            for line in full_log.read_text(encoding="utf-8", errors="strict").splitlines()
            if line.startswith("just ") and line.strip()[5:] in EXPECTED_GATES
        }
        if markers != set(EXPECTED_GATES):
            raise RuntimeError(f"Missing complete verification recipe markers: {set(EXPECTED_GATES) - markers}")
        report["completed_recipes"] = list(EXPECTED_GATES)
        whole_log = full_log.read_text(encoding="utf-8", errors="strict")
        summaries = [line for line in whole_log.splitlines() if line.startswith("summary: strictness=")]
        if len(summaries) != 1:
            raise RuntimeError("Missing or ambiguous required house-linter summary")
        parsed = dict(re.findall(r"([a-z_]+)=([a-z0-9]+)", summaries[0]))
        if parsed.get("strictness") != "standard" or not parsed.get("files", "").isdigit():
            raise RuntimeError("Invalid house-linter coverage summary")
        record_pattern = re.compile(r"^(?P<path>\S.*):(?P<line>[0-9]+):(?P<column>[0-9]+): (?P<severity>blocker|critical|major|minor|info)/(?P<confidence>low|medium|high): (?P<message>.*) \[(?P<rule>meta/parse-error)\]$")
        incomplete = [match.groupdict() for line in whole_log.splitlines()
                      if (match := record_pattern.fullmatch(line)) is not None]
        timed_out_files = [row for row in incomplete
                           if row["message"] == "parse timed out; other rules skipped for this file"]
        report["lint_coverage"] = {
            "summary": summaries[0], "fields": parsed,
            "parse_error_records": incomplete, "timeout_records": timed_out_files,
            "scope": "The original severity gate is unchanged. Existing syntax/generated-file exclusions remain visible; an affinity-sensitive parser timeout makes this proof ineligible.",
        }
        if timed_out_files:
            raise RuntimeError("House linter timed out on files under the recorded CPU mask")
        if not RESOURCE_REPORTS or not RESOURCE_REPORTS[-1].get("linter_processes"):
            raise RuntimeError("No actual pinned house-linter process was observed")
        run("whitespace", ["git", "diff", "--check", "HEAD"])
        report["final_index_sha256"] = identity(entries, tree, "after")
        run("source-unchanged", ["git", "diff", "--exit-code", "HEAD"])
        report["source_gates_passed"] = True
    finally:
        try:
            run("restore-isolated-source", ["git", "restore", "--source", head, "--staged", "--worktree", "--", "."])
            report["restored_index_sha256"] = identity(entries, tree, "restored")
            run("source-restoration", ["git", "diff", "--exit-code", "HEAD"])
            report["source_restored"] = True
        finally:
            report["publication_eligible"] = bool(report["source_gates_passed"] and report["source_restored"])
            report["commands"] = [asdict(receipt) for receipt in RECEIPTS]
            report["resource_reports"] = RESOURCE_REPORTS
            (OUTPUT / "report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            print("FULL_VERIFY_REPORT " + json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
