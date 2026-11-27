"""Require a durable known-exit receipt when final log hashing fails."""
from __future__ import annotations

import json
import os
import sys
import tempfile
from dataclasses import asdict
from pathlib import Path

import support


def main() -> None:
    proof = Path(__file__).resolve().parent
    output = Path(sys.argv[1]).resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = support.read_object(proof / "manifest.json")
    hashes = support.object_value(manifest["proof_sha256"])
    for name in ("support.py", "runner_receipt_control.py"):
        if support.digest(proof / name) != hashes[name]:
            raise RuntimeError("control source digest differs: " + name)
    runner = support.Runner(output / "receipt-control", 60)
    original_digest = support.digest
    target = runner.output / "known-exit-digest-error.log"
    injections = 0
    result: dict[str, object] = {"schema": 1, "passed": False, "publication_eligible": False}

    def fail_final_digest(path: Path) -> str:
        nonlocal injections
        if path == target:
            injections += 1
            raise OSError("injected final command log read error")
        return original_digest(path)

    try:
        with tempfile.TemporaryDirectory(prefix="quality-receipt-control-", dir=output.parent) as temporary:
            env = os.environ.copy()
            for name in ("GH_TOKEN", "GITHUB_TOKEN"):
                env.pop(name, None)
            support.digest = fail_final_digest
            try:
                receipt, log = runner.run(
                    "known-exit-digest-error",
                    [sys.executable, "-c", "import os\nprint(os.getpid(), flush=True)\nraise SystemExit(23)\n"],
                    Path(temporary), env, 10,
                )
            finally:
                support.digest = original_digest
            pid = int(log.read_text(encoding="ascii").strip())
            result["child_pid"] = pid
            if (injections != 1 or len(runner.receipts) != 1 or receipt.raw_exit != 23
                    or receipt.timed_out or receipt.log_sha256 != "" or receipt.child_success
                    or receipt.cleanup_errors != (
                        "log digest: OSError: injected final command log read error",
                    )):
                raise RuntimeError("known exit or fatal observer error was not preserved")
            try:
                os.waitpid(pid, os.WNOHANG)
            except ChildProcessError:
                result["child_reaped"] = True
            else:
                raise RuntimeError("child was not reaped before receipt")
            try:
                os.killpg(pid, 0)
            except ProcessLookupError:
                result["process_group_absent"] = True
            else:
                raise RuntimeError("child process group remains")
            runner.quiesce()
            if tuple(sorted(os.sched_getaffinity(0))) != runner.original_affinity:
                raise RuntimeError("supervisor affinity differs")
            result["affinity_restored"] = True
            result["passed"] = True
    finally:
        support.digest = original_digest
        result["injections"] = injections
        result["commands"] = [asdict(row) for row in runner.receipts]
        support.write_json(output / "runner-receipt-control.json", result)
        print("QUALITY_RUNNER_RECEIPT_CONTROL " + json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
