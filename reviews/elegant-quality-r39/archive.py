"""Authenticate the failed r36 receipt before comparing any new quality measurements."""
from __future__ import annotations

import hashlib
import io
import json
import os
import zipfile
from pathlib import Path, PurePosixPath

from artifact_support import download
from support import object_value, read_object, write_json

def authenticate(proof: Path, output: Path, specification: dict[str, object]) -> dict[str, object]:
    artifact = download(specification, os.environ["GH_TOKEN"])
    prior = output / "prior"
    prior.mkdir(parents=True, exist_ok=True)
    (prior / "artifact.zip").write_bytes(artifact.data)
    with zipfile.ZipFile(io.BytesIO(artifact.data)) as archive:
        members = archive.infolist()
        if len(members) > 64 or sum(item.file_size for item in members) > 64 * 1024 * 1024:
            raise ValueError("Frozen artifact exceeds its uncompressed bound")
        names: set[str] = set()
        for item in members:
            path = PurePosixPath(item.filename)
            if (path.is_absolute() or ".." in path.parts or "\\" in item.filename
                    or item.filename in names or item.file_size > 16 * 1024 * 1024):
                raise ValueError("Invalid or oversized frozen artifact member")
            names.add(item.filename)
        if "report.json" not in names or "just-verify.log" not in names:
            raise ValueError("Frozen artifact is missing its report or complete command log")
        report_bytes = archive.read("report.json")
        log = archive.read("just-verify.log")
    if hashlib.sha256(log).hexdigest() != specification["log_sha256"]:
        raise RuntimeError("Complete prior command log differs")
    report: object = json.loads(report_bytes)
    expected = read_object(proof / "prior-report.json")
    if object_value(report) != expected:
        raise RuntimeError("Prior report differs from the frozen reviewed receipt")
    if (expected["source_gates_passed"] is not False or expected["source_restored"] is not True
            or expected["publication_eligible"] is not False):
        raise RuntimeError("Prior failed outcome was relabeled")
    commands = expected["commands"]
    if not isinstance(commands, list):
        raise TypeError("Invalid prior command receipts")
    actual = [object_value(row) for row in commands if object_value(row).get("name") == "just-verify"]
    if (len(actual) != 1 or actual[0]["raw_exit"] != 1 or actual[0]["timed_out"] is not False
            or actual[0]["monitor_errors"] != [] or actual[0]["log_sha256"] != specification["log_sha256"]):
        raise RuntimeError("Prior actual root exit differs")
    (prior / "report.json").write_bytes(report_bytes)
    (prior / "just-verify.log").write_bytes(log)
    result: dict[str, object] = {
        **artifact.receipt,
        "report_sha256": hashlib.sha256(report_bytes).hexdigest(),
        "log_sha256": hashlib.sha256(log).hexdigest(),
        "prior_actual_exit": 1, "prior_conclusion": "failure",
        "source_restored": True, "previous_gate_results_reused_as_new_success": False,
        "complete_prior_log_preserved": True,
    }
    write_json(prior / "authentication.json", result)
    print("QUALITY_PRIOR_ARTIFACT " + json.dumps(result), flush=True)
    return result
