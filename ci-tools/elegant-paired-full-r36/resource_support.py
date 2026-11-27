"""Measure one unchanged root command under a recorded CPU affinity mask."""
from __future__ import annotations

import json
import os
import resource
import signal
import subprocess
import time
from pathlib import Path
from typing import BinaryIO


def memory_snapshot() -> dict[str, object]:
    raw = Path("/proc/self/cgroup").read_text(encoding="ascii")
    groups: set[Path] = {Path("/sys/fs/cgroup")}
    for line in raw.splitlines():
        fields = line.split(":", 2)
        if len(fields) == 3 and fields[0] == "0":
            groups.add(Path("/sys/fs/cgroup") / fields[2].lstrip("/"))
    values: dict[str, object] = {}
    for group in sorted(groups):
        files: dict[str, str] = {}
        for name in ("memory.current", "memory.peak", "memory.max",
                     "memory.events", "memory.events.local", "memory.pressure"):
            path = group / name
            if path.is_file():
                files[name] = path.read_text(encoding="ascii").strip()
        values[str(group)] = files
    return {
        "proc_cgroup": raw,
        "groups": values,
        "proc_meminfo": Path("/proc/meminfo").read_text(encoding="ascii"),
    }


def process_sample(pid: int) -> dict[str, object] | None:
    root = Path("/proc") / str(pid)
    try:
        status = root.joinpath("status").read_text(encoding="ascii")
        command = root.joinpath("cmdline").read_bytes().replace(b"\0", b" ").decode("utf-8", errors="replace")
        executable = os.readlink(root / "exe")
        affinity = sorted(os.sched_getaffinity(pid))
        children = [int(value) for value in root.joinpath("task", str(pid), "children").read_text().split()]
    except (FileNotFoundError, ProcessLookupError):
        return None
    fields: dict[str, int] = {}
    for line in status.splitlines():
        if line.startswith(("VmRSS:", "VmHWM:", "Threads:")):
            name, value, *_ = line.split()
            fields[name.rstrip(":")] = int(value)
    return {"pid": pid, "rss_kib": fields.get("VmRSS", 0),
            "hwm_kib": fields.get("VmHWM", 0), "threads": fields.get("Threads", 0),
            "command": command, "executable": executable,
            "affinity": affinity, "children": children}


def abort_process_group(child: subprocess.Popen[bytes]) -> int:
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    return child.wait()


class ResourceTrace:
    def __init__(self, output: Path) -> None:
        self.path = output / "resource-samples.jsonl"
        self.house_binary = str((Path(os.environ["EMD_HOUSE_ROOT"]) / "bin/sloplint").resolve(strict=True))
        self.before = memory_snapshot()
        self.original_affinity = sorted(os.sched_getaffinity(0))
        if not self.original_affinity:
            raise RuntimeError("No allowed CPU for the immutable command")
        self.selected_affinity = self.original_affinity[:1]
        self.peak_tree_rss_kib = 0
        self.peak_linter_rss_kib = 0
        self.linter_observations: dict[int, dict[str, object]] = {}
        self.samples = 0
        self.started = time.monotonic()
        self.parent_affinity_restored = False
        self.child: subprocess.Popen[bytes] | None = None

    def spawn(self, command: list[str], cwd: Path, env: dict[str, str],
              stream: BinaryIO) -> subprocess.Popen[bytes]:
        try:
            try:
                os.sched_setaffinity(0, self.selected_affinity)
                self.child = subprocess.Popen(
                    command, cwd=cwd, env=env, stdout=stream,
                    stderr=subprocess.STDOUT, start_new_session=True,
                )
            finally:
                os.sched_setaffinity(0, self.original_affinity)
                self.parent_affinity_restored = sorted(os.sched_getaffinity(0)) == self.original_affinity
            if not self.parent_affinity_restored:
                raise RuntimeError("Supervisor CPU affinity did not restore")
            print("FULL_AFFINITY " + json.dumps({
                "argv": command, "original": self.original_affinity,
                "selected": self.selected_affinity, "supervisor_restored": True,
            }), flush=True)
            if self.child is None:
                raise RuntimeError("Child creation returned no owned process")
            return self.child
        except BaseException:
            if self.child is not None:
                abort_process_group(self.child)
            raise

    def sample(self, root_pid: int) -> None:
        waiting = [root_pid]
        seen: set[int] = set()
        rows: list[dict[str, object]] = []
        while waiting:
            pid = waiting.pop()
            if pid in seen:
                continue
            seen.add(pid)
            row = process_sample(pid)
            if row is None:
                continue
            rows.append(row)
            children = row["children"]
            if not isinstance(children, list):
                raise TypeError("Invalid process child list")
            waiting.extend(int(value) for value in children)
        total = 0
        for row in rows:
            rss = row["rss_kib"]
            if not isinstance(rss, int):
                raise TypeError("Invalid RSS sample")
            total += rss
            if row.get("executable") == self.house_binary:
                if row["affinity"] != self.selected_affinity:
                    raise RuntimeError("House linter did not retain the recorded CPU mask")
                self.peak_linter_rss_kib = max(self.peak_linter_rss_kib, rss)
                pid = row["pid"]
                if not isinstance(pid, int):
                    raise TypeError("Invalid process ID")
                self.linter_observations[pid] = row
        self.peak_tree_rss_kib = max(self.peak_tree_rss_kib, total)
        self.samples += 1
        record = {"seconds": round(time.monotonic() - self.started, 3),
                  "tree_rss_kib": total, "processes": rows}
        with self.path.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(record) + "\n")

    def known_report(self) -> dict[str, object]:
        report: dict[str, object] = {
            "before": self.before,
            "original_affinity": self.original_affinity,
            "selected_affinity": self.selected_affinity,
            "supervisor_affinity_restored": self.parent_affinity_restored,
            "samples": self.samples,
            "peak_sampled_observed_subtree_rss_kib": self.peak_tree_rss_kib,
            "peak_sampled_linter_rss_kib": self.peak_linter_rss_kib,
            "linter_processes": list(self.linter_observations.values()),
            "scope": "The CPU mask applies to the entire unchanged just verify process and descendants. RSS is sampled from process-leader child lists, which can omit children forked by other threads; it is an observed subtree, not an exhaustive total. Cgroup counters retain their recorded kernel scope.",
        }
        return report

    def finish(self) -> dict[str, object]:
        report = self.known_report()
        report["after"] = memory_snapshot()
        report["children_ru_maxrss_kib"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        return report
