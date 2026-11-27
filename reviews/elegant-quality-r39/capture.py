"""Observe the real quality CLI once and relay its byte streams unchanged."""
from __future__ import annotations

import base64
import fcntl
import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

def file_digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def main() -> int:
    real = Path(os.environ["EMD_QUALITY_REAL"]).resolve(strict=True)
    record_path = Path(os.environ["EMD_QUALITY_RECORDS"])
    temporary = Path(os.environ["EMD_QUALITY_TEMP"])
    temporary.mkdir(parents=True, exist_ok=True)
    expected: object = json.loads(os.environ["EMD_QUALITY_STAT"])
    info = real.stat()
    actual = [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_mode]
    if actual != expected:
        raise RuntimeError("The bound real binary identity changed")
    arguments = sys.argv[1:]
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="call-", dir=temporary) as directory:
        stdout = Path(directory) / "stdout.bin"
        stderr = Path(directory) / "stderr.bin"
        with stdout.open("wb") as out, stderr.open("wb") as err:
            done = subprocess.run([str(real), *arguments], stdin=subprocess.DEVNULL,
                                  stdout=out, stderr=err, check=False)
        # Preserve the actual result and byte streams before any observer validation.
        with stdout.open("rb") as out:
            shutil.copyfileobj(out, sys.stdout.buffer)
        with stderr.open("rb") as err:
            shutil.copyfileobj(err, sys.stderr.buffer)
        sys.stdout.buffer.flush()
        sys.stderr.buffer.flush()
        record: dict[str, object] = {
            "lane": os.environ["EMD_QUALITY_LANE"], "argv": arguments,
            "cwd": str(Path.cwd()), "real_binary": str(real),
            "binary_sha256": os.environ["EMD_QUALITY_BINARY_SHA256"],
            "raw_exit": done.returncode, "seconds": time.monotonic() - started,
            "affinity": sorted(os.sched_getaffinity(0)),
            "stdout_sha256": file_digest(stdout), "stderr_sha256": file_digest(stderr),
            "stdout_bytes": stdout.stat().st_size, "stderr_bytes": stderr.stat().st_size,
            "stderr_base64": base64.b64encode(stderr.read_bytes()).decode("ascii"),
        }
        if arguments[:2] == ["layout", "--metrics"]:
            record["stdout_base64"] = base64.b64encode(stdout.read_bytes()).decode("ascii")
        encoded = (json.dumps(record, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8")
        with record_path.open("ab") as stream:
            fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
    if done.returncode < 0:
        caught = -done.returncode
        if caught not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(caught, signal.SIG_DFL)
        os.kill(os.getpid(), caught)
        return 128 + caught
    return done.returncode

if __name__ == "__main__":
    raise SystemExit(main())
