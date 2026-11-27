"""Inactive paired quality diagnostic. The parent owns activation and gate execution."""
from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Final

from archive import authenticate
from support import Entry, Runner, digest, entry, git, identity, object_value
from support import read_entries, read_object, text_value, write_json

PROOF: Final = Path(sys.argv[1]).resolve(strict=True)
ROOTS: Final = {"maintained": Path(sys.argv[2]).resolve(strict=True),
               "candidate": Path(sys.argv[3]).resolve(strict=True)}
OUTPUT: Final = Path(sys.argv[4]).absolute()
TEMP: Final = Path(sys.argv[5]).absolute()
KINDS: Final = frozenset("flowchart,class,state,er,requirement,usecase,c4,agentflow,swimlane".split(","))
METRIC_FIELDS: Final = ("schema", "hard_ok", "nodes", "mean_node_extent", "crossings",
                       "bends", "against_flow_edges", "total_route_length", "canvas_area", "soft_cost")
GATE_NAMES: Final = ("hard constraints", "total crossings", "total soft cost", "exceptions <= 5 percent")
ROW: Final = re.compile(r"^(corpus/.+) ours=([0-9]+)/([0-9]+) dagre=([0-9]+)/([0-9]+) elk=([0-9]+)/([0-9]+) exception=(true|false)$")

def environment(lane: str) -> dict[str, str]:
    env = os.environ.copy()
    work = TEMP / lane
    env.update({
        "GOENV": "off", "GOCACHEPROG": "", "GOTOOLCHAIN": "local", "GOMAXPROCS": "8",
        "GOCACHE": str(work / "go-cache"), "GOMODCACHE": str(work / "go-modules"),
        "CARGO_TARGET_DIR": str(work / "cargo"), "CARGO_BUILD_JOBS": "4",
        "CARGO_INCREMENTAL": "0", "RUSTC_WRAPPER": "", "RUSTC_WORKSPACE_WRAPPER": "",
        "RUSTUP_TOOLCHAIN": "1.100.0", "NO_COLOR": "1", "CLICOLOR": "0",
        "CI": "true", "PYTHONUNBUFFERED": "1", "BASE_PATH": "/elegant-mermaid",
        "PNPM_HOME": str(work / "pnpm-home"),
    })
    for key in ("GH_TOKEN", "GITHUB_TOKEN", "EMD_BIN", "EMD_QUALITY_REAL", "EMD_QUALITY_RECORDS", "EMD_QUALITY_TEMP",
                "EMD_QUALITY_STAT", "EMD_QUALITY_LANE", "EMD_QUALITY_BINARY_SHA256"):
        env.pop(key, None)
    return env

def expected_indexes(manifest: dict[str, object]) -> dict[str, list[Entry]]:
    names = manifest["maintained_index_parts"]
    if not isinstance(names, list):
        raise TypeError("Index parts must be an array")
    base = read_entries(PROOF, [text_value(name) for name in names])
    candidate = {item.path: item for item in base}
    raw: object = json.loads((PROOF / "candidate-delta.json").read_bytes())
    if not isinstance(raw, list) or len(raw) != 8:
        raise ValueError("Expected exactly eight candidate paths")
    seen: set[str] = set()
    for value in raw:
        row = object_value(value)
        name = text_value(row["path"])
        if name in seen:
            raise ValueError("Duplicate candidate delta path")
        seen.add(name)
        prior = None if row["before"] is None else entry(row["before"])
        following = entry(row["after"])
        if name != following.path or candidate.get(name) != prior:
            raise ValueError(f"Candidate delta precondition differs: {name}")
        candidate[name] = following
    return {"maintained": base, "candidate": sorted(candidate.values(), key=lambda item: item.path)}

def checked_versions(runner: Runner) -> None:
    root = ROOTS["maintained"]
    env = environment("maintained")
    versions = (
        ("go", ["go", "version"], r"^go version go1\.27\.4 linux/amd64$"),
        ("node", ["node", "--version"], r"^v26\.13\.1$"),
        ("pnpm", ["pnpm", "--version"], r"^12\.23\.0$"),
        ("just", ["just", "--version"], r"^just 1\.59\.0$"),
        ("rust", ["rustc", "--version"], r"^rustc 1\.100\.0 "),
        ("nextest", ["cargo", "nextest", "--version"], r"^cargo-nextest 0\.9\.151(?:\s|$)"),
    )
    for name, command, pattern in versions:
        log = runner.checked(f"version-{name}", command, root, env, 120)
        if re.search(pattern, log.read_text(encoding="utf-8"), re.MULTILINE) is None:
            raise RuntimeError(f"Pinned {name} version differs")

def selected_paths(root: Path) -> list[str]:
    verdicts = read_object(root / "corpus/verdicts.json")
    paths = sorted(name for name, value in verdicts.items()
                   if object_value(value).get("accept") is True
                   and object_value(value).get("kind") in KINDS)
    if not paths or any(not path.startswith("corpus/") or ".." in Path(path).parts for path in paths):
        raise ValueError("Invalid selected corpus paths")
    return paths

def install_capture(lane: str, real: Path, binary_sha: str, env: dict[str, str]) -> Path:
    root = ROOTS[lane]
    target = root / "bin/emd-go"
    if target.exists() or target.is_symlink():
        raise RuntimeError(f"{lane}: unexpected preexisting quality executable")
    if git(root, ["ls-files", "--", "bin/emd-go"]):
        raise RuntimeError("Refusing to replace a tracked source file")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(f"#!{sys.executable}\n".encode("utf-8") + (PROOF / "capture.py").read_bytes())
    target.chmod(0o755)
    stat = real.stat()
    env.update({
        "EMD_QUALITY_REAL": str(real),
        "EMD_QUALITY_RECORDS": str(OUTPUT / lane / "cli-calls.jsonl"),
        "EMD_QUALITY_TEMP": str(TEMP / lane / "capture"),
        "EMD_QUALITY_STAT": json.dumps([stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_mode]),
        "EMD_QUALITY_LANE": lane, "EMD_QUALITY_BINARY_SHA256": binary_sha,
    })
    return target

def classify(argv: list[str], allowed: set[str]) -> tuple[str, str]:
    if len(argv) == 4 and argv[:3] == ["layout", "--profile", "vector"]:
        kind, path = "vector", argv[3]
    elif len(argv) == 3 and argv[:2] == ["layout", "--metrics"]:
        kind, path = "ours", argv[2]
    elif len(argv) == 4 and argv[:3] == ["layout", "--metrics", "--dump"]:
        prefix = "corpus/.cache/quality/"
        if not argv[3].startswith(prefix):
            raise ValueError("Unexpected baseline path")
        rest = argv[3][len(prefix):]
        if rest.endswith(".dagre.json"):
            kind, path = "dagre", rest[:-len(".dagre.json")]
        elif rest.endswith(".elk.json"):
            kind, path = "elk", rest[:-len(".elk.json")]
        else:
            raise ValueError("Unexpected baseline suffix")
    else:
        raise ValueError(f"Unexpected measured command: {argv}")
    if path not in allowed:
        raise ValueError(f"Unexpected measured fixture: {path}")
    return kind, path

def metric(record: dict[str, object]) -> dict[str, object]:
    encoded = text_value(record["stdout_base64"])
    data = base64.b64decode(encoded, validate=True)
    if hashlib.sha256(data).hexdigest() != record["stdout_sha256"]:
        raise ValueError("Captured metric byte digest differs")
    value: object = json.loads(data)
    result = object_value(value)
    if any(name not in result for name in METRIC_FIELDS):
        raise ValueError("Incomplete native metric")
    if type(result["hard_ok"]) is not bool or result["schema"] != 1:
        raise ValueError("Invalid native metric schema/hard_ok")
    for key in METRIC_FIELDS:
        if key in ("schema", "hard_ok"):
            continue
        if type(result[key]) is not int or result[key] < 0:
            raise ValueError(f"Invalid native metric: {key}")
    if result["mean_node_extent"] < 1:
        raise ValueError("Invalid native metric mean")
    return result

def numeric(value: dict[str, object], field: str) -> int:
    result = value[field]
    if type(result) is not int:
        raise TypeError(f"Expected integer metric: {field}")
    return result

def collect(lane: str, log: Path, binary_sha: str, runner: Runner) -> dict[str, object]:
    root = ROOTS[lane]
    paths = selected_paths(root)
    allowed = set(paths)
    captured: dict[tuple[str, str], dict[str, object]] = {}
    for line in (OUTPUT / lane / "cli-calls.jsonl").read_bytes().splitlines():
        raw: object = json.loads(line)
        record = object_value(raw)
        args = record["argv"]
        if not isinstance(args, list):
            raise TypeError("Captured argv must be an array")
        kind, path = classify([text_value(arg) for arg in args], allowed)
        key = (path, kind)
        if key in captured:
            raise ValueError(f"Duplicate measured invocation: {key}")
        if record["lane"] != lane or record["cwd"] != str(root) or record["binary_sha256"] != binary_sha:
            raise ValueError("Captured invocation identity differs")
        if record["raw_exit"] != 0 or record["affinity"] != list(runner.selected_affinity):
            raise ValueError(f"Native metric command failed or used a different CPU mask: {key}")
        captured[key] = record
    expected = {(path, kind) for path in paths for kind in ("vector", "ours", "dagre", "elk")}
    if set(captured) != expected:
        raise ValueError(f"Missing/unexpected native captures: {len(expected - set(captured))}/{len(set(captured) - expected)}")
    rows: list[dict[str, object]] = []
    expected_lines: list[str] = []
    hard_failures: list[str] = []
    crossings = {"ours": 0, "dagre": 0, "elk": 0}
    costs = {"ours": 0, "dagre": 0, "elk": 0}
    exceptions = 0
    for path in paths:
        measurements = {kind: metric(captured[(path, kind)]) for kind in ("ours", "dagre", "elk")}
        ours, dagre, elk = (measurements[kind] for kind in ("ours", "dagre", "elk"))
        if not ours["hard_ok"]:
            hard_failures.append(path)
        for kind in measurements:
            crossings[kind] += numeric(measurements[kind], "crossings")
            costs[kind] += numeric(measurements[kind], "soft_cost")
        exceptional = numeric(ours, "soft_cost") * 100 > min(numeric(dagre, "soft_cost"), numeric(elk, "soft_cost")) * 120
        exceptions += int(exceptional)
        expected_lines.append(
            f"{path} ours={numeric(ours, 'crossings')}/{numeric(ours, 'soft_cost')} "
            f"dagre={numeric(dagre, 'crossings')}/{numeric(dagre, 'soft_cost')} "
            f"elk={numeric(elk, 'crossings')}/{numeric(elk, 'soft_cost')} exception={str(exceptional).lower()}")
        hashes = {kind: digest(root / "corpus/.cache/quality" / f"{path}.{kind}.json") for kind in ("dagre", "elk")}
        rows.append({
            "path": path, "metrics": measurements,
            "stdout_sha256": {kind: captured[(path, kind)]["stdout_sha256"] for kind in ("vector", "ours", "dagre", "elk")},
            "baseline_sha256": hashes,
        })
    text = log.read_text(encoding="utf-8")
    actual_lines = [line for line in text.splitlines() if ROW.fullmatch(line)]
    if actual_lines != expected_lines:
        raise ValueError("Actual quality rows differ from the captured native metrics")
    gates = [not hard_failures, crossings["ours"] <= min(crossings["dagre"], crossings["elk"]),
             costs["ours"] <= min(costs["dagre"], costs["elk"]), exceptions * 20 <= len(paths)]
    gate_lines = [f"gate {index + 1} {name}: {'PASS' if gates[index] else 'FAIL'}" for index, name in enumerate(GATE_NAMES)]
    actual_gates = [line for line in text.splitlines() if re.fullmatch(r"gate [1-4] .+: (PASS|FAIL)", line)]
    if actual_gates != gate_lines:
        raise ValueError("Actual gate verdicts differ from the captured native metrics")
    normalized = "\n".join(actual_lines + actual_gates) + "\n"
    result: dict[str, object] = {
        "fixtures": len(paths), "native_invocations": len(captured), "crossings": crossings,
        "soft_cost": costs, "exceptions": exceptions, "hard_failure_paths": hard_failures,
        "gate_passed": gates, "normalized_report_sha256": hashlib.sha256(normalized.encode()).hexdigest(),
        "committed_fixture_list_matches": (root / "corpus/quality-corpus.txt").read_bytes() == ("\n".join(paths) + "\n").encode(),
        "committed_exception_report": {"fixtures": read_object(root / "corpus/quality-exceptions.json")["fixtures"],
                                      "sha256": digest(root / "corpus/quality-exceptions.json")},
        "reported_mismatches": [line for line in text.splitlines() if "differs from computed" in line],
        "rows": rows,
    }
    write_json(OUTPUT / lane / "measurements.json", result)
    (OUTPUT / lane / "normalized-quality-report.txt").write_text(normalized, encoding="utf-8")
    return result

def prepare_lane(lane: str, runner: Runner) -> tuple[dict[str, str], Path, str]:
    root, env = ROOTS[lane], environment(lane)
    work = TEMP / lane
    work.mkdir(parents=True, exist_ok=True)
    out = OUTPUT / lane
    out.mkdir(parents=True, exist_ok=True)
    for path in (root / "tools/upstream-oracle/node_modules", root / "corpus/.cache/quality"):
        if path.exists():
            raise RuntimeError(f"{lane}: baseline/dependency directory was not fresh: {path}")
    disabled = runner.checked(f"{lane}-cache-disabled", ["go", "env", "GOCACHEPROG"], root, env, 30)
    if disabled.read_text(encoding="utf-8").strip():
        raise RuntimeError("External Go cache is active")
    runner.checked(f"{lane}-dependencies",
                   ["pnpm", "--dir", "tools/upstream-oracle", "install", "--frozen-lockfile",
                    "--store-dir", str(work / "pnpm-store")], root, env, 600)
    real = work / "emd-real"
    if real.exists():
        raise RuntimeError("Real binary path was not fresh")
    runner.checked(f"{lane}-build-go", ["go", "build", "-trimpath", "-o", str(real), "./cmd/emd"],
                   root, env, 900)
    binary_sha = digest(real)
    build_info = runner.checked(f"{lane}-build-identity", ["go", "version", "-m", str(real)], root, env, 30)
    expected_head = git(root, ["rev-parse", "HEAD"]).decode("ascii").strip()
    if re.search(r"\bvcs\.revision=" + re.escape(expected_head) + r"\s", build_info.read_text(encoding="utf-8")) is None:
        raise RuntimeError(f"{lane}: Go build revision does not match the immutable checkout")
    write_json(out / "binary.json", {"path": str(real), "sha256": binary_sha,
                                   "go_build_info_sha256": digest(build_info)})
    install_capture(lane, real, binary_sha, env)
    return env, real, binary_sha

def compare(measurements: dict[str, dict[str, object]]) -> dict[str, object]:
    if set(measurements) != {"maintained", "candidate"}:
        return {"complete": False, "reason": "One or both quality lanes lacked complete authenticated measurements"}
    left, right = measurements["maintained"], measurements["candidate"]
    if not isinstance(left["rows"], list) or not isinstance(right["rows"], list):
        raise TypeError("Expected complete row arrays")
    old = {text_value(object_value(row)["path"]): object_value(row) for row in left["rows"]}
    new = {text_value(object_value(row)["path"]): object_value(row) for row in right["rows"]}
    common = sorted(old.keys() & new.keys())
    changed = [{"path": path, "maintained": old[path], "candidate": new[path]}
               for path in common if old[path] != new[path]]
    return {
        "complete": True, "same_fixture_set": old.keys() == new.keys(),
        "maintained_only": sorted(old.keys() - new.keys()), "candidate_only": sorted(new.keys() - old.keys()),
        "native_metric_vector_baseline_differences": changed,
        "exact_measurements_equal": old == new,
        "exact_quality_report_equal": left["normalized_report_sha256"] == right["normalized_report_sha256"],
        "maintained_gate_passed": left["gate_passed"], "candidate_gate_passed": right["gate_passed"],
        "publication_eligible": False,
    }

def main() -> int:
    if ROOTS["maintained"] == ROOTS["candidate"]:
        raise ValueError("Source checkouts must be separate")
    for root in ROOTS.values():
        if OUTPUT.is_relative_to(root) or TEMP.is_relative_to(root) or PROOF.is_relative_to(root):
            raise ValueError("Proof, evidence and build directories must be outside both source roots")
    OUTPUT.mkdir(parents=True, exist_ok=True)
    TEMP.mkdir(parents=True, exist_ok=True)
    manifest = read_object(PROOF / "manifest.json")
    for name, expected in object_value(manifest["proof_sha256"]).items():
        if Path(name).name != name or digest(PROOF / name) != expected:
            raise RuntimeError(f"Proof digest differs: {name}")
    repository = PROOF.parent.parent
    active = repository / ".github/workflows/elegant-quality-r39.yml"
    if not active.is_file() or digest(active) != manifest["workflow_sha256"]:
        raise RuntimeError("The parent has not activated the exact reviewed workflow")
    if git(repository, ["rev-parse", "HEAD"]).decode().strip() != os.environ["GITHUB_SHA"]:
        raise RuntimeError("Producer checkout differs from the workflow commit")
    indexes = expected_indexes(manifest)
    sources = object_value(manifest["sources"])
    runner = Runner(OUTPUT, 9000)
    report: dict[str, object] = {
        "schema": 1, "manifest": manifest, "producer": os.environ["GITHUB_SHA"],
        "run": os.environ["GITHUB_RUN_ID"], "source_gates_passed": False,
        "publication_eligible": False, "source_restored": False,
        "lanes": {}, "theme": {"attempted": False}, "errors": [],
        "original_affinity": list(runner.original_affinity), "selected_affinity": list(runner.selected_affinity),
    }
    lanes: dict[str, dict[str, object]] = {}
    measurements: dict[str, dict[str, object]] = {}
    errors: list[str] = []
    initialized: set[str] = set()
    theme_passed = False
    versions_ok = False
    try:
        for lane in ROOTS:
            source = object_value(sources[lane])
            if len(indexes[lane]) != source["blobs"]:
                raise RuntimeError(f"{lane}: source count differs")
            observed = identity(ROOTS[lane], indexes[lane], text_value(source["head"]),
                                text_value(source["tree"]), f"{lane}-before")
            if observed["index_sha256"] != source["index_sha256"]:
                raise RuntimeError(f"{lane}: complete source-index digest differs")
            initialized.add(lane)
            lanes[lane] = {"initial_identity": observed, "quality_passed": False}
            write_json(OUTPUT / f"{lane}-source-index.json", [asdict(item) for item in indexes[lane]])
        report["prior_artifact"] = authenticate(PROOF, OUTPUT, object_value(manifest["prior_artifact"]))
        checked_versions(runner)
        versions_ok = True
        for lane in ROOTS:
            try:
                env, real, binary_sha = prepare_lane(lane, runner)
                source = object_value(sources[lane])
                identity(ROOTS[lane], indexes[lane], text_value(source["head"]), text_value(source["tree"]),
                         f"{lane}-after-dependencies")
                receipt, log = runner.run(f"{lane}-quality", ["just", "quality", "JOBS=1"],
                                          ROOTS[lane], env, 2700)
                lanes[lane]["quality_receipt"] = asdict(receipt)
                lanes[lane]["quality_passed"] = receipt.child_success
                if digest(real) != binary_sha:
                    raise RuntimeError(f"{lane}: real binary changed during measurement")
                if receipt.timed_out or receipt.cleanup_errors:
                    raise RuntimeError(f"{lane}: quality command did not complete cleanly")
                measurements[lane] = collect(lane, log, binary_sha, runner)
                lanes[lane]["measurements_sha256"] = digest(OUTPUT / lane / "measurements.json")
                lanes[lane]["final_identity"] = identity(
                    ROOTS[lane], indexes[lane], text_value(source["head"]), text_value(source["tree"]),
                    f"{lane}-after-quality")
            except (OSError, RuntimeError, ValueError, TypeError, KeyError) as error:
                errors.append(f"{lane}: {type(error).__name__}: {error}")
            finally:
                runner.quiesce()
                launcher = ROOTS[lane] / "bin/emd-go"
                if launcher.exists() and launcher.read_bytes().startswith(f"#!{sys.executable}\n".encode()):
                    launcher.unlink()
        comparison = compare(measurements)
        write_json(OUTPUT / "comparison.json", comparison)
        report["comparison"] = {key: value for key, value in comparison.items()
                                if key != "native_metric_vector_baseline_differences"}
        differences = comparison.get("native_metric_vector_baseline_differences", [])
        if not isinstance(differences, list):
            raise TypeError("Invalid comparison differences")
        report["comparison_difference_count"] = len(differences)
        report["comparison_sha256"] = digest(OUTPUT / "comparison.json")
        # Independent missed recipe. Its only Justfile dependency is build, not verify.
        if versions_ok and "candidate" in initialized and (ROOTS["candidate"] / "tools/upstream-oracle/node_modules").is_dir():
            receipt, _ = runner.run("candidate-theme-check", ["just", "theme-check"],
                                    ROOTS["candidate"], environment("candidate"), 1800)
            report["theme"] = {"attempted": True, "receipt": asdict(receipt)}
            theme_passed = receipt.child_success
        else:
            report["theme"] = {"attempted": False, "reason": "Required source/tool/dependency setup did not complete"}
    except BaseException as error:
        errors.append(f"supervisor: {type(error).__name__}: {error}")
    finally:
        restored: dict[str, bool] = {}
        try:
            runner.quiesce()
            for lane in ROOTS:
                if lane not in initialized:
                    restored[lane] = False
                    continue
                source = object_value(sources[lane])
                try:
                    try:
                        lanes[lane]["pre_restore_identity"] = identity(
                            ROOTS[lane], indexes[lane], text_value(source["head"]),
                            text_value(source["tree"]), f"{lane}-before-restoration")
                    except (OSError, RuntimeError, ValueError, TypeError) as error:
                        errors.append(f"source changed before restoration: {lane}: {error}")
                    receipt, _ = runner.run(
                        f"{lane}-restore", ["git", "restore", "--source", text_value(source["head"]),
                                            "--staged", "--worktree", "--", "."],
                        ROOTS[lane], environment(lane), 30, emergency=True)
                    if not receipt.child_success:
                        raise RuntimeError(f"{lane}: restoration command failed")
                    lanes[lane]["restored_identity"] = identity(
                        ROOTS[lane], indexes[lane], text_value(source["head"]),
                        text_value(source["tree"]), f"{lane}-restored")
                    if git(ROOTS[lane], ["diff", "--name-only", "HEAD"]):
                        raise RuntimeError(f"{lane}: restored source has a tracked diff")
                    restored[lane] = True
                except (OSError, RuntimeError, ValueError, TypeError) as error:
                    restored[lane] = False
                    errors.append(f"restoration: {type(error).__name__}: {error}")
        except (OSError, RuntimeError, ValueError) as error:
            errors.append(f"quiescence: {type(error).__name__}: {error}")
        report["lanes"] = lanes
        report["restored_lanes"] = restored
        report["source_restored"] = set(restored) == set(ROOTS) and all(restored.values())
        report["errors"] = errors
        report["commands"] = [asdict(receipt) for receipt in runner.receipts]
        report["diagnostic_complete"] = set(measurements) == set(ROOTS) and not errors and report["source_restored"]
        report["source_gates_passed"] = all(lanes.get(lane, {}).get("quality_passed") is True for lane in ROOTS) and theme_passed
        report["publication_eligible"] = False
        write_json(OUTPUT / "report.json", report)
        print("PAIRED_QUALITY_REPORT " + json.dumps(report, ensure_ascii=False), flush=True)
    # A complete diagnostic may still fail: inherited gate failures remain actual failures.
    return 0 if report["diagnostic_complete"] and report["source_gates_passed"] else 1

if __name__ == "__main__":
    raise SystemExit(main())
