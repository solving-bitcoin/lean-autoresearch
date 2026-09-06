#!/usr/bin/env python3
"""Layer-specific regressions for the challenge verifier boundaries."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from unittest import mock

import run_with_rss
from dependency_builds import verify_snapshot, write_snapshot
from verify_submission import artifact_within_bound, audit_submission_symbols, run_limited


ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / "scripts" / "run_with_rss.py"
PYTHON = shutil.which("python3") or sys.executable


def run_helper(command: list[str], cwd: Path, *, timeout: int = 5,
               memory: int = 256 * 1024 * 1024, output: int = 64 * 1024,
               file_size: int = 8 * 1024 * 1024, processes: int = 8,
               disk: int = 16 * 1024 * 1024) -> dict[str, object]:
    pid_file = cwd / "child.pid"
    result = subprocess.run(
        [PYTHON, str(HELPER),
         "--timeout", str(timeout),
         "--memory-limit-bytes", str(memory),
         "--output-limit-bytes", str(output),
         "--file-size-limit-bytes", str(file_size),
         "--process-limit", str(processes),
         "--working-directory-limit-bytes", str(disk),
         "--pid-file", str(pid_file),
         "--", *command],
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
        timeout=timeout + 10,
    )
    return json.loads(result.stdout)


def assert_process_gone(pid: int) -> None:
    deadline = time.monotonic() + 3
    while time.monotonic() < deadline:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.05)
    raise SystemExit(f"REGRESSION_FAILED: descendant {pid} survived group cleanup")


def check_resource_wrapper() -> None:
    assert run_with_rss.aggregate_cpu_limit(5) >= 10

    with tempfile.TemporaryDirectory(prefix="g1-resource-positive-") as temporary:
        result = run_helper([PYTHON, "-c", "print('ok')"], Path(temporary))
        assert result["returnCode"] == 0
        assert result["stdout"].strip() == "ok"
        assert result["resourceMeasurementUnavailable"] is False

    with tempfile.TemporaryDirectory(prefix="g1-resource-output-") as temporary:
        result = run_helper(
            [PYTHON, "-c", "print('x' * 65536)"],
            Path(temporary),
            output=1024,
        )
        assert result["outputLimitExceeded"] is True

    with tempfile.TemporaryDirectory(prefix="g1-resource-memory-") as temporary:
        result = run_helper(
            [PYTHON, "-c", "bytearray(96 * 1024 * 1024)"],
            Path(temporary),
            memory=48 * 1024 * 1024,
        )
        # Fast successful spikes exercise the final ru_maxrss check; slower
        # allocations are stopped by the live aggregate RSS monitor.
        assert result["memoryLimitExceeded"] is True or result["returnCode"] != 0

    with tempfile.TemporaryDirectory(prefix="g1-resource-virtual-memory-") as temporary:
        code = (
            "import mmap,threading; "
            "reservation=mmap.mmap(-1,512*1024*1024); "
            "worker=threading.Thread(target=lambda:None); "
            "worker.start(); worker.join()"
        )
        result = run_helper(
            [PYTHON, "-c", code],
            Path(temporary),
            memory=64 * 1024 * 1024,
        )
        assert result["returnCode"] == 0
        assert result["memoryLimitExceeded"] is False

    with tempfile.TemporaryDirectory(prefix="g1-resource-process-") as temporary:
        code = (
            "import subprocess,sys,time; "
            "children=[subprocess.Popen([sys.executable,'-c',"
            "'import time; time.sleep(30)']) for _ in range(4)]; time.sleep(30)"
        )
        result = run_helper([PYTHON, "-c", code], Path(temporary), processes=2)
        assert result["processLimitExceeded"] is True

    with tempfile.TemporaryDirectory(prefix="g1-resource-disk-") as temporary:
        code = "open('payload.bin','wb').write(bytes(4 * 1024 * 1024))"
        result = run_helper(
            [PYTHON, "-c", code],
            Path(temporary),
            disk=1024 * 1024,
        )
        assert result["diskLimitExceeded"] is True

    with tempfile.TemporaryDirectory(prefix="g1-resource-timeout-") as temporary:
        code = (
            "import subprocess,sys,time; "
            "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
            "print(p.pid,flush=True); time.sleep(30)"
        )
        result = run_helper([PYTHON, "-c", code], Path(temporary), timeout=1)
        assert result["timedOut"] is True
        assert_process_gone(int(str(result["stdout"]).strip()))

    with tempfile.TemporaryDirectory(prefix="g1-resource-orphan-") as temporary:
        code = (
            "import subprocess,sys; "
            "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
            "print(p.pid,flush=True)"
        )
        result = run_helper([PYTHON, "-c", code], Path(temporary))
        assert result["returnCode"] == 0
        assert result["processGroupCleanupFailed"] is False
        assert_process_gone(int(str(result["stdout"]).strip()))

    with mock.patch.object(run_with_rss.sys, "platform", "unsupported-test"):
        assert run_with_rss.process_group_metrics(os.getpgrp()) is None

    # Even a zero exit status must be rejected when the monitor found a memory
    # overrun. Retain the recent compiler context without flooding the log.
    measurement = {"returnCode": 0, "memoryLimitExceeded": True,
                   "peakMemoryBytes": 65, "memoryLimitBytes": 64,
                   "stdout": "old-prefix" + "x" * 8192 + "last-module",
                   "stderr": "compiler context"}
    helper = subprocess.CompletedProcess([], 0, json.dumps(measurement), "")
    with mock.patch("verify_submission.subprocess.run", return_value=helper):
        try:
            run_limited([PYTHON], ROOT, 5, 64, 65536, 65536, 8, 65536,
                        HELPER, "diagnostic regression")
        except SystemExit as error:
            message = str(error)
            assert "exceeded its memory limit (peak 65, limit 64)" in message
            assert "last-module" in message and "compiler context" in message
            assert "old-prefix" not in message and len(message) < 17000
        else:
            raise AssertionError("memory overrun was accepted")

    print("ok — fail-closed resource wrapper regressions")


def check_artifact_bound_property() -> None:
    for score in range(64):
        for artifact in range(96):
            assert artifact_within_bound(artifact, score) is (artifact <= score)
    assert not artifact_within_bound(-1, 0)
    assert not artifact_within_bound(True, 1)
    assert not artifact_within_bound("0", 1)
    print("ok — inclusive variable-artifact bound property")


def check_symbol_audit_layer() -> None:
    compiler = shutil.which("cc")
    if compiler is None:
        raise SystemExit("REGRESSION_FAILED: cc is required for symbol-audit fixture")
    with tempfile.TemporaryDirectory(prefix="g1-symbol-safe-") as temporary:
        project = Path(temporary)
        object_root = (
            project / ".lake" / "build" / "ir" / "GarblingPrize" / "Submission"
        )
        object_root.mkdir(parents=True)
        source = project / "safe.c"
        source.write_text("void ordinary_submission_symbol(void) {}\n", encoding="utf-8")
        subprocess.run(
            [compiler, "-c", str(source), "-o", str(object_root / "Safe.c.o")],
            check=True,
        )
        reference = project / "reference.c"
        reference.write_text(
            "extern void lean_g1_nat_le_32(void);\n"
            "void ordinary_submission_reference(void) { lean_g1_nat_le_32(); }\n",
            encoding="utf-8",
        )
        subprocess.run(
            [compiler, "-c", str(reference),
             "-o", str(object_root / "Reference.c.o")],
            check=True,
        )
        audit_submission_symbols(project)

    for symbol in (
        "lean_g1_sha256", "lean_g1_hmac_sha256", "lean_g1_uniform_below",
        "lean_g1_uniform_below_nat", "lean_g1_nat_le_32",
        "lean_g1_pack_four_254"
    ):
        with tempfile.TemporaryDirectory(prefix="g1-symbol-hostile-") as temporary:
            project = Path(temporary)
            object_root = (
                project / ".lake" / "build" / "ir" / "GarblingPrize" / "Submission"
            )
            object_root.mkdir(parents=True)
            source = project / "hostile.c"
            source.write_text(f"void {symbol}(void) {{}}\n", encoding="utf-8")
            subprocess.run(
                [compiler, "-c", str(source), "-o", str(object_root / "Hostile.c.o")],
                check=True,
            )
            try:
                audit_submission_symbols(project)
            except SystemExit:
                pass
            else:
                raise SystemExit(
                    f"REGRESSION_FAILED: compiled protected symbol {symbol} was accepted"
                )
    print("ok — compiled native-symbol audit fixture")


def check_dependency_snapshot_layer() -> None:
    with tempfile.TemporaryDirectory(prefix="g1-build-snapshot-") as temporary:
        root = Path(temporary)
        packages = root / "packages"
        artifact = packages / "fixture" / ".lake" / "build" / "Fixture.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"trusted olean")
        entries = [{"name": "fixture", "rev": "a" * 40}]
        snapshot = root / "snapshot.json"
        write_snapshot(snapshot, packages, entries, "lean-test")
        verify_snapshot(snapshot, packages, entries, "lean-test")
        artifact.write_bytes(b"replaced olean")
        try:
            verify_snapshot(snapshot, packages, entries, "lean-test")
        except SystemExit:
            pass
        else:
            raise SystemExit("REGRESSION_FAILED: changed dependency build was accepted")
    print("ok — dependency build snapshot tamper fixture")


def main() -> None:
    check_resource_wrapper()
    check_artifact_bound_property()
    check_symbol_audit_layer()
    check_dependency_snapshot_layer()
    print("ok — verifier regression suite")


if __name__ == "__main__":
    main()
