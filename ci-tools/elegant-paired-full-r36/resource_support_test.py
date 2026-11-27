"""Fault-inject monitor failures around real owned native child processes."""
from __future__ import annotations

import contextlib
import io
import json
import os
import signal
import sys
from dataclasses import asdict
from pathlib import Path
from unittest import mock

import verify
from resource_support import ResourceTrace, abort_process_group

ROOT = Path(sys.argv[3]).absolute()


def require_reaped(trace: ResourceTrace) -> int:
    child = trace.child
    if child is None or child.returncode is None:
        raise AssertionError("Native child was not created and reaped")
    try:
        os.killpg(child.pid, 0)
    except ProcessLookupError:
        return child.returncode
    raise AssertionError("An owned process group survived the monitor failure")


def exercise(name: str, expected: int, failure: str) -> None:
    output = ROOT / name
    output.mkdir(parents=True, exist_ok=True)
    verify.OUTPUT = output
    verify.RECEIPTS.clear()
    verify.RESOURCE_REPORTS.clear()
    original = set(os.sched_getaffinity(0))
    real_set = os.sched_setaffinity
    calls = 0
    traces: list[ResourceTrace] = []

    def make_trace(path: Path) -> ResourceTrace:
        trace = ResourceTrace(path)
        traces.append(trace)
        return trace

    def fail_second_set(pid: int, cpus: list[int] | set[int]) -> None:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("frozen post-spawn affinity failure")
        real_set(pid, cpus)

    command = [sys.executable, "-c", "import time; time.sleep(60)"]
    if failure == "finish":
        command = [sys.executable, "-c", f"import sys; sys.exit({expected})"]
    captured = io.StringIO()
    try:
        with contextlib.ExitStack() as stack:
            stack.enter_context(contextlib.redirect_stdout(captured))
            stack.enter_context(mock.patch.object(verify, "ResourceTrace", side_effect=make_trace))
            if failure == "affinity":
                stack.enter_context(mock.patch.object(os, "sched_setaffinity", side_effect=fail_second_set))
            elif failure == "sample":
                stack.enter_context(mock.patch.object(ResourceTrace, "sample",
                                                     side_effect=OSError("frozen sample failure")))
            elif failure == "finish":
                stack.enter_context(mock.patch.object(ResourceTrace, "finish",
                                                     side_effect=OSError("frozen finish failure")))
            else:
                raise ValueError("Unknown frozen failure")
            try:
                verify.run(name, command, timeout=10, measure_resources=True)
            except RuntimeError:
                pass
            else:
                raise AssertionError("Monitor failure was accepted")
        if len(traces) != 1 or len(verify.RECEIPTS) != 1:
            raise AssertionError("Missing unique native trace/command receipt")
        receipt = verify.RECEIPTS[0]
        if receipt.raw_exit != expected or receipt.timed_out or receipt.accepted:
            raise AssertionError(f"Actual child outcome was lost: {receipt}")
        if not receipt.monitor_errors or not any("frozen" in value for value in receipt.monitor_errors):
            raise AssertionError("The monitor error was erased")
        if require_reaped(traces[0]) != expected:
            raise AssertionError("Receipt differs from reaped native child")
        if failure == "affinity" and calls != 2:
            raise AssertionError("The post-spawn restoration fault was not reached")
        (output / "fault.log").write_text(captured.getvalue(), encoding="utf-8")
        print("RESOURCE_SELFTEST_RESULT " + json.dumps({
            "name": name, "receipt": asdict(receipt),
            "native_child_reaped": True, "process_group_absent": True,
            "fault": failure,
        }), flush=True)
    finally:
        real_set(0, original)
        for trace in traces:
            if trace.child is not None and trace.child.returncode is None:
                abort_process_group(trace.child)
        if set(os.sched_getaffinity(0)) != original:
            raise AssertionError("Selftest supervisor affinity did not restore")


def main() -> None:
    exercise("post-spawn-affinity-error", -signal.SIGKILL, "affinity")
    exercise("sampling-error", -signal.SIGKILL, "sample")
    exercise("finish-after-success", 0, "finish")
    exercise("finish-after-exit137", 137, "finish")
    print("RESOURCE_SELFTEST_PASS cases=4", flush=True)


if __name__ == "__main__":
    main()
