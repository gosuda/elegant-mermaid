"""Bounded process ownership and exact tracked-source identity for the r39 draft."""
from __future__ import annotations

import hashlib
import json
import os
import signal
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path

@dataclass(frozen=True)
class Entry:
    path: str
    mode: str
    sha: str

@dataclass(frozen=True)
class Receipt:
    name: str
    command: tuple[str, ...]
    cwd: str
    raw_exit: int | None
    timed_out: bool
    seconds: float
    log_sha256: str
    selected_affinity: tuple[int, ...]
    cleanup_errors: tuple[str, ...]
    child_success: bool

def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def object_value(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise TypeError("Expected a JSON object with text keys")
    return value

def text_value(value: object) -> str:
    if not isinstance(value, str):
        raise TypeError("Expected text")
    return value

def read_object(path: Path) -> dict[str, object]:
    value: object = json.loads(path.read_bytes())
    return object_value(value)

def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def entry(value: object) -> Entry:
    row = object_value(value)
    name = text_value(row["path"])
    mode = text_value(row["mode"])
    sha = text_value(row["sha"])
    if not name or Path(name).is_absolute() or ".." in Path(name).parts:
        raise ValueError(f"Unsafe tracked path: {name}")
    if mode not in ("100644", "100755") or len(sha) != 40 or any(c not in "0123456789abcdef" for c in sha):
        raise ValueError(f"Invalid source entry: {name}")
    return Entry(name, mode, sha)

def read_entries(proof: Path, parts: list[str]) -> list[Entry]:
    result: list[Entry] = []
    for name in parts:
        value: object = json.loads((proof / name).read_bytes())
        if not isinstance(value, list):
            raise TypeError("Source-index part must be an array")
        result.extend(entry(item) for item in value)
    result.sort(key=lambda item: item.path)
    if len({item.path for item in result}) != len(result):
        raise ValueError("Duplicate source-index path")
    return result

def git(root: Path, arguments: list[str]) -> bytes:
    done = subprocess.run(["git", *arguments], cwd=root, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=30, check=False)
    if done.returncode != 0:
        raise RuntimeError(f"git {arguments} exited {done.returncode}: {done.stderr.decode('utf-8', errors='replace')}")
    return done.stdout

def identity(root: Path, expected: list[Entry], head: str, tree: str, label: str) -> dict[str, object]:
    if git(root, ["rev-parse", "HEAD"]).decode("ascii").strip() != head:
        raise RuntimeError(f"{label}: wrong source commit")
    if git(root, ["rev-parse", "HEAD^{tree}"]).decode("ascii").strip() != tree:
        raise RuntimeError(f"{label}: wrong committed tree")
    actual: list[Entry] = []
    for row in git(root, ["ls-files", "--stage", "-z"]).split(b"\0"):
        if not row:
            continue
        metadata, path = row.split(b"\t", 1)
        mode, sha, stage = metadata.decode("ascii").split()
        if stage != "0":
            raise RuntimeError(f"{label}: unmerged index")
        actual.append(Entry(path.decode("utf-8"), mode, sha))
    actual.sort(key=lambda item: item.path)
    if actual != expected:
        raise RuntimeError(f"{label}: complete tracked index differs")
    for item in expected:
        path = root / item.path
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"{label}: not a regular tracked file: {item.path}")
        data = path.read_bytes()
        blob = hashlib.sha1(f"blob {len(data)}\0".encode("ascii") + data).hexdigest()
        if blob != item.sha or bool(path.stat().st_mode & 0o111) != (item.mode == "100755"):
            raise RuntimeError(f"{label}: tracked bytes/mode differ: {item.path}")
    if git(root, ["write-tree"]).decode("ascii").strip() != tree:
        raise RuntimeError(f"{label}: staged tree differs")
    encoded = json.dumps([asdict(item) for item in expected], separators=(",", ":")).encode("utf-8")
    result = {"label": label, "head": head, "tree": tree, "blobs": len(expected),
              "index_sha256": hashlib.sha256(encoded).hexdigest()}
    print("QUALITY_SOURCE_IDENTITY " + json.dumps(result), flush=True)
    return result

def live_group(group: int) -> list[int]:
    found: list[int] = []
    for directory in Path("/proc").iterdir():
        if not directory.name.isdigit():
            continue
        try:
            raw = (directory / "stat").read_text(encoding="ascii")
        except (FileNotFoundError, ProcessLookupError):
            continue
        fields = raw[raw.rindex(")") + 2:].split()
        # fields: state, ppid, pgrp, session. Zombies cannot execute source.
        if fields[0] != "Z" and int(fields[2]) == group and int(fields[3]) == group:
            found.append(int(directory.name))
    return sorted(found)

def kill_group(group: int) -> None:
    try:
        os.killpg(group, signal.SIGKILL)
    except ProcessLookupError:
        pass

class Runner:
    def __init__(self, output: Path, seconds: int) -> None:
        self.output = output
        self.output.mkdir(parents=True, exist_ok=True)
        self.deadline = time.monotonic() + seconds
        self.receipts: list[Receipt] = []
        self.groups: set[int] = set()
        self.original_affinity = tuple(sorted(os.sched_getaffinity(0)))
        if not self.original_affinity:
            raise RuntimeError("No available CPU")
        self.selected_affinity = self.original_affinity[:1]

    def drain(self, group: int) -> None:
        if live_group(group):
            kill_group(group)
        deadline = time.monotonic() + 5
        while live_group(group) and time.monotonic() < deadline:
            time.sleep(0.05)
        if live_group(group):
            raise RuntimeError(f"Owned process group remains active: {group}")
        self.groups.discard(group)

    def quiesce(self) -> None:
        errors: list[str] = []
        for group in tuple(self.groups):
            try:
                self.drain(group)
            except (OSError, RuntimeError) as error:
                errors.append(str(error))
        if errors or self.groups:
            raise RuntimeError(f"Cannot restore sources while processes remain: {errors}")
        if tuple(sorted(os.sched_getaffinity(0))) != self.original_affinity:
            raise RuntimeError("Supervisor affinity was not restored")

    def run(self, name: str, command: list[str], root: Path, env: dict[str, str],
            timeout: int, emergency: bool = False) -> tuple[Receipt, Path]:
        log = self.output / f"{name}.log"
        started = time.monotonic()
        deadline = started + timeout if emergency else min(started + timeout, self.deadline)
        raw: int | None = None
        timed_out = False
        errors: list[str] = []
        child: subprocess.Popen[bytes] | None = None
        print("QUALITY_COMMAND_START " + json.dumps({"name": name, "command": command, "cwd": str(root)}), flush=True)
        try:
            if deadline <= started:
                timed_out = True
                raise TimeoutError("Diagnostic command budget exhausted before spawn")
            with log.open("wb") as stream:
                try:
                    os.sched_setaffinity(0, self.selected_affinity)
                    child = subprocess.Popen(command, cwd=root, env=env, stdout=stream,
                                             stderr=subprocess.STDOUT, start_new_session=True)
                    self.groups.add(child.pid)
                finally:
                    os.sched_setaffinity(0, self.original_affinity)
                if tuple(sorted(os.sched_getaffinity(0))) != self.original_affinity:
                    raise RuntimeError("Supervisor affinity restoration failed after spawn")
                while True:
                    try:
                        raw = child.wait(timeout=max(0.001, min(30, deadline - time.monotonic())))
                        break
                    except subprocess.TimeoutExpired:
                        print("QUALITY_PROGRESS " + json.dumps({"name": name,
                              "seconds": round(time.monotonic() - started, 1),
                              "log_bytes": log.stat().st_size}), flush=True)
                        if time.monotonic() < deadline:
                            continue
                        timed_out = True
                        kill_group(child.pid)
                        raw = child.wait(timeout=10)
                        break
        except BaseException as error:
            errors.append(f"{type(error).__name__}: {error}")
            if child is not None:
                kill_group(child.pid)
                raw = child.wait(timeout=10)
        finally:
            if child is not None:
                try:
                    active = live_group(child.pid)
                    if active and raw == 0:
                        errors.append(f"Successful child left active descendants: {active}")
                    self.drain(child.pid)
                except (OSError, RuntimeError) as error:
                    errors.append(f"cleanup: {error}")
            record = Receipt(name, tuple(command), str(root), raw, timed_out,
                             time.monotonic() - started, digest(log) if log.exists() else "",
                             self.selected_affinity, tuple(errors),
                             raw == 0 and not timed_out and not errors)
            self.receipts.append(record)
            print("QUALITY_COMMAND_RESULT " + json.dumps(asdict(record)), flush=True)
        return record, log

    def checked(self, name: str, command: list[str], root: Path, env: dict[str, str],
                timeout: int) -> Path:
        receipt, log = self.run(name, command, root, env, timeout)
        if not receipt.child_success:
            raise RuntimeError(f"{name}: raw exit {receipt.raw_exit}; timed_out={receipt.timed_out}; errors={receipt.cleanup_errors}")
        return log
