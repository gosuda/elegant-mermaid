"""Authenticate prior Windows receipts and restrict reuse to unchanged source."""
from __future__ import annotations

import hashlib
import http.client
import io
import json
import os
import urllib.parse
import urllib.request
import zipfile
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class PriorEvidence:
    index: list[dict[str, str]]
    reused: list[dict[str, object]]
    provenance: dict[str, object]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def api(path: str, token: str) -> tuple[int, dict[str, str], bytes]:
    connection = http.client.HTTPSConnection("api.github.com", timeout=60)
    try:
        connection.request("GET", path, headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "elegant-mermaid-frozen-receipt-proof",
        })
        response = connection.getresponse()
        return response.status, dict(response.getheaders()), response.read()
    finally:
        connection.close()


def api_json(path: str, token: str) -> dict[str, object]:
    status, _, data = api(path, token)
    if status != 200:
        raise RuntimeError(f"GitHub evidence metadata returned status {status}")
    return json.loads(data)


def records(log: str, marker: str) -> list[dict[str, object]]:
    prefix = marker + " {"
    return [
        json.loads(line[line.index(prefix) + len(marker) + 1:])
        for line in log.splitlines() if prefix in line
    ]


def authenticate(proof: Path, output: Path, specification: dict[str, object]) -> PriorEvidence:
    token = os.environ.pop("GH_ARTIFACT_TOKEN")
    base = "/repos/gosuda/elegant-mermaid"
    artifact_id = specification["artifact_id"]
    run_id = specification["run_id"]
    producer = specification["producer"]
    run = api_json(f"{base}/actions/runs/{run_id}", token)
    job = api_json(f"{base}/actions/jobs/{specification['job_id']}", token)
    artifact = api_json(f"{base}/actions/artifacts/{artifact_id}", token)
    if (run["id"] != run_id or run["head_sha"] != producer
            or run["status"] != "completed" or run["conclusion"] != "failure"):
        raise RuntimeError("prior failed workflow identity differs")
    if job["id"] != specification["job_id"] or job["run_id"] != run_id or job["conclusion"] != "failure":
        raise RuntimeError("prior failed job identity differs")
    if (artifact["id"] != artifact_id or artifact["expired"]
            or artifact["workflow_run"]["id"] != run_id
            or artifact["workflow_run"]["head_sha"] != producer
            or artifact["digest"] != "sha256:" + specification["zip_sha256"]
            or artifact["size_in_bytes"] != specification["zip_bytes"]):
        raise RuntimeError("prior artifact producer or ZIP digest differs")
    status, headers, archive = api(f"{base}/actions/artifacts/{artifact_id}/zip", token)
    token = ""
    if status == 302:
        location = next((value for key, value in headers.items() if key.lower() == "location"), "")
        parsed = urllib.parse.urlsplit(location)
        if parsed.scheme != "https" or not parsed.hostname or parsed.username or parsed.password:
            raise RuntimeError("artifact redirect is not an authenticated HTTPS download")
        # Authorization is never forwarded to the artifact storage host.
        with urllib.request.urlopen(location, timeout=120) as response:
            archive = response.read(specification["zip_bytes"] + 1)
    elif status != 200:
        raise RuntimeError(f"artifact download returned status {status}")
    if len(archive) != specification["zip_bytes"] or digest(archive) != specification["zip_sha256"]:
        raise RuntimeError("downloaded artifact ZIP bytes differ")

    frozen = json.loads((proof / "previous-failure.json").read_text(encoding="utf-8"))
    full_log = json.loads((proof / "previous-job-log.json").read_text(encoding="utf-8"))
    payload = json.loads((proof / "previous-formatted-source.json").read_text(encoding="utf-8"))
    if digest(full_log["content"].encode("utf-8")) != specification["job_log_sha256"]:
        raise RuntimeError("archived full job log differs")
    reports = records(full_log["content"], "FOCUSED_WINDOWS_REPORT")
    formats = records(full_log["content"], "CANDIDATE_FORMATTED_SOURCE")
    if reports != [frozen["report"]] or formats != [frozen["formatted_source"]]:
        raise RuntimeError("archived full log does not bind the frozen report/source")
    if records(full_log["content"], "COMMAND_RECEIPT") != frozen["report"]["commands"]:
        raise RuntimeError("archived full log command sequence differs")
    if frozen["report"]["compiled_tree"] != specification["compiled_tree"]:
        raise RuntimeError("prior compiled tree differs")

    with zipfile.ZipFile(io.BytesIO(archive)) as bundle:
        report = json.loads(bundle.read("report.json"))
        if report != frozen["report"] or not report["source_restored"]:
            raise RuntimeError("artifact report differs or source was not restored")
        unexpected = [item["name"] for item in report["commands"] if item["exit"] != item["expected"]]
        if unexpected != ["candidate-go-lint"]:
            raise RuntimeError("prior failure is not the one frozen lint failure")
        for item in report["commands"]:
            raw = bundle.read(item["name"] + ".log")
            # The original driver hashes subprocess text after universal-newline
            # decoding, then writes that text using Windows native line endings.
            with io.TextIOWrapper(io.BytesIO(raw), encoding="utf-8", newline=None) as stream:
                normalized = stream.read()
            if digest(normalized.encode("utf-8")) != item["log_sha256"]:
                raise RuntimeError(f"prior command log differs: {item['name']}")
        raw_payload = bundle.read("formatted-source.json")
        if digest(raw_payload) != frozen["formatted_source"]["payload_sha256"]:
            raise RuntimeError("native formatted source payload bytes differ")
        native_payload = json.loads(raw_payload)
        if native_payload != payload or len(payload) != 8:
            raise RuntimeError("archived eight-file source payload differs")
        for item in payload:
            content = item["content"].encode("utf-8")
            blob = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content,
                                usedforsecurity=False).hexdigest()
            if digest(content) != item["sha256"] or blob != item["blob"]:
                raise RuntimeError(f"prior source content differs: {item['path']}")
        index: list[dict[str, str]] = json.loads(bundle.read("compiled-source-index.json"))
        if len(index) != 6714 or len({item["path"] for item in index}) != 6714:
            raise RuntimeError("prior compiled index is incomplete")
        index_hash = digest(json.dumps(index, sort_keys=True, separators=(",", ":")).encode())
        if index_hash != specification["compiled_index_sha256"]:
            raise RuntimeError("prior complete compiled index differs")
        by_path = {item["path"]: item for item in index}
        for item in payload:
            if by_path[item["path"]]["sha"] != item["blob"] or by_path[item["path"]]["sha256"] != item["sha256"]:
                raise RuntimeError("prior complete index does not bind the source payload")

    by_name = {item["name"]: item for item in frozen["report"]["commands"]}
    reused = [by_name[name] for name in specification["reused_command_names"]]
    if any(item["exit"] != item["expected"] for item in reused):
        raise RuntimeError("a failing prior gate cannot be reused")
    provenance = {
        "producer": producer, "run": run_id, "job": specification["job_id"],
        "artifact": artifact_id, "zip_sha256": specification["zip_sha256"],
        "compiled_tree": specification["compiled_tree"],
        "compiled_index_sha256": specification["compiled_index_sha256"],
        "full_job_log_sha256": specification["job_log_sha256"],
        "prior_run_conclusion": "failure", "all_archived_command_logs_verified": len(by_name),
        "source_payloads_verified": 8, "source_blobs": len(index),
        "reused_commands": reused,
    }
    (output / "authenticated-prior-evidence.json").write_text(
        json.dumps(provenance, indent=2) + "\n", encoding="utf-8",
    )
    print("AUTHENTICATED_PRIOR_EVIDENCE " + json.dumps(provenance), flush=True)
    return PriorEvidence(index, reused, provenance)


def require_test_only_delta(source: Path, prior: PriorEvidence, allowed: str) -> dict[str, object]:
    changed: list[str] = []
    for item in prior.index:
        content = (source / item["path"]).read_bytes()
        if digest(content) != item["sha256"]:
            changed.append(item["path"])
    if changed != [allowed]:
        raise RuntimeError(f"receipt reuse requires exactly the one Go test delta: {changed}")
    record = {
        "prior_compiled_tree": prior.provenance["compiled_tree"],
        "changed_paths": changed, "unchanged_source_blobs": len(prior.index) - 1,
        "new_test_sha256": digest((source / allowed).read_bytes()),
    }
    print("TEST_ONLY_SOURCE_DELTA " + json.dumps(record), flush=True)
    return record
