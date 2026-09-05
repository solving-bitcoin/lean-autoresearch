#!/usr/bin/env python3
"""Run one command and report its output plus child peak resident memory."""

from __future__ import annotations

import argparse
import ctypes
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time


def install_limits(file_size_limit: int, cpu_limit: int) -> None:
    """Install inherited hard limits in the child immediately before exec."""
    limits = [(resource.RLIMIT_FSIZE, file_size_limit),
              (resource.RLIMIT_CPU, cpu_limit)]
    # Do not set RLIMIT_AS: it counts harmless virtual reservations, including
    # Lean worker-thread stacks. The parent monitor below enforces the promised
    # aggregate resident-memory bound for the entire process group.
    for kind, requested in limits:
        _soft, hard = resource.getrlimit(kind)
        effective = requested if hard == resource.RLIM_INFINITY else min(requested, hard)
        resource.setrlimit(kind, (effective, effective))


def aggregate_cpu_limit(wall_timeout: int) -> int:
    """Allow a process to use every logical CPU for the full wall interval."""
    return (wall_timeout + 5) * max(1, os.cpu_count() or 1)


def read_output(stream, limit: int) -> tuple[str, bool]:
    size = os.fstat(stream.fileno()).st_size
    stream.seek(0)
    contents = stream.read(min(size, limit)).decode("utf-8", errors="replace")
    return contents, size > limit


def stream_size(stream) -> int:
    return os.fstat(stream.fileno()).st_size


def directory_size(root: Path) -> int:
    """Measure regular files without following dependency or attacker symlinks."""
    total = 0
    for directory, subdirectories, files in os.walk(root, followlinks=False):
        subdirectories[:] = [
            name for name in subdirectories
            if not (Path(directory) / name).is_symlink()
        ]
        for name in files:
            path = Path(directory) / name
            try:
                stat = path.stat(follow_symlinks=False)
            except OSError:
                continue
            if not path.is_symlink():
                total += stat.st_size
    return total


class DarwinTaskInfo(ctypes.Structure):
    _fields_ = [
        ("virtual_size", ctypes.c_uint64),
        ("resident_size", ctypes.c_uint64),
        ("total_user", ctypes.c_uint64),
        ("total_system", ctypes.c_uint64),
        ("threads_user", ctypes.c_uint64),
        ("threads_system", ctypes.c_uint64),
        *[(f"counter_{index}", ctypes.c_int32) for index in range(12)],
    ]


def darwin_group_metrics(pgid: int) -> tuple[int, int] | None:
    """Read aggregate process-group RSS and count through macOS libproc."""
    try:
        libproc = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
        list_pids = libproc.proc_listpgrppids
        list_pids.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_int]
        list_pids.restype = ctypes.c_int
        pid_info = libproc.proc_pidinfo
        pid_info.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_uint64,
                             ctypes.c_void_p, ctypes.c_int]
        pid_info.restype = ctypes.c_int

        capacity = max(list_pids(pgid, None, 0), 1) + 64
        pids = (ctypes.c_int * capacity)()
        count = list_pids(pgid, pids, ctypes.sizeof(pids))
        if count < 0:
            return None
        total = 0
        found = False
        for pid in pids[:count]:
            info = DarwinTaskInfo()
            returned = pid_info(pid, 4, 0, ctypes.byref(info), ctypes.sizeof(info))
            if returned == ctypes.sizeof(info):
                total += info.resident_size
                found = True
        return (total, count) if found else None
    except (AttributeError, OSError, ValueError):
        return None


def linux_group_metrics(pgid: int) -> tuple[int, int] | None:
    """Read aggregate process-group RSS and count from procfs."""
    total = 0
    count = 0
    page_size = os.sysconf("SC_PAGE_SIZE")
    for stat_path in Path("/proc").glob("[0-9]*/stat"):
        try:
            stat = stat_path.read_text(encoding="ascii")
            after_name = stat[stat.rfind(")") + 2:].split()
            if int(after_name[2]) != pgid:
                continue
            statm = (stat_path.parent / "statm").read_text(encoding="ascii").split()
            total += int(statm[1]) * page_size
            count += 1
        except (IndexError, OSError, ValueError):
            continue
    return (total, count) if count else None


def process_group_metrics(pgid: int) -> tuple[int, int] | None:
    """Return aggregate RSS and process count for an isolated process group."""
    if sys.platform == "darwin":
        return darwin_group_metrics(pgid)
    if sys.platform.startswith("linux"):
        return linux_group_metrics(pgid)
    return None


def kill_group(pid: int) -> bool:
    try:
        os.killpg(pid, signal.SIGKILL)
        return True
    except ProcessLookupError:
        return True
    except PermissionError:
        return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, required=True)
    parser.add_argument("--memory-limit-bytes", type=int, required=True)
    parser.add_argument("--output-limit-bytes", type=int, required=True)
    parser.add_argument("--file-size-limit-bytes", type=int, required=True)
    parser.add_argument("--process-limit", type=int, required=True)
    parser.add_argument("--working-directory-limit-bytes", type=int, required=True)
    parser.add_argument("--pid-file", type=Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        raise SystemExit("missing command")
    limits = (
        args.timeout,
        args.memory_limit_bytes,
        args.output_limit_bytes,
        args.file_size_limit_bytes,
        args.process_limit,
        args.working_directory_limit_bytes,
    )
    if any(limit <= 0 for limit in limits):
        raise SystemExit("timeout and resource limits must be positive")

    # Prove that this host has the aggregate monitor promised by policy before
    # starting untrusted work. Fast children may exit before the first poll, so
    # capability is tested against the helper's own live process group.
    monitor_available = process_group_metrics(os.getpgrp()) is not None
    if not monitor_available:
        print(json.dumps({
            "timedOut": False,
            "returnCode": None,
            "stdout": "",
            "stderr": "aggregate process-group metrics are unavailable",
            "outputLimitExceeded": False,
            "memoryLimitExceeded": False,
            "processLimitExceeded": False,
            "diskLimitExceeded": False,
            "resourceMeasurementUnavailable": True,
            "peakMemoryBytes": 0,
        }))
        return

    with tempfile.TemporaryFile() as stdout_file, tempfile.TemporaryFile() as stderr_file:
        process = subprocess.Popen(
            command,
            stdout=stdout_file,
            stderr=stderr_file,
            start_new_session=True,
            preexec_fn=lambda: install_limits(
                args.file_size_limit_bytes,
                aggregate_cpu_limit(args.timeout),
            ),
        )
        try:
            args.pid_file.write_text(str(process.pid), encoding="ascii")
        except OSError:
            kill_group(process.pid)
            process.wait()
            raise
        deadline = time.monotonic() + args.timeout
        timed_out = False
        memory_limited = False
        process_limited = False
        output_limited = False
        disk_limited = False
        measurement_unavailable = False
        cleanup_failed = False
        observed_peak = 0
        next_disk_check = 0.0
        missing_metric_polls = 0
        while process.poll() is None:
            now = time.monotonic()
            if now >= deadline:
                timed_out = True
                cleanup_failed = not kill_group(process.pid)
                break
            metrics = process_group_metrics(process.pid)
            if metrics is None:
                # libproc/procfs may briefly race process creation or exit.
                # A sustained half-second loss fails closed.
                if process.poll() is not None:
                    break
                missing_metric_polls += 1
                if missing_metric_polls >= 10:
                    measurement_unavailable = True
                    cleanup_failed = not kill_group(process.pid)
                    break
                time.sleep(0.05)
                continue
            missing_metric_polls = 0
            resident, process_count = metrics
            observed_peak = max(observed_peak, resident)
            if resident > args.memory_limit_bytes:
                memory_limited = True
                cleanup_failed = not kill_group(process.pid)
                break
            if process_count > args.process_limit:
                process_limited = True
                cleanup_failed = not kill_group(process.pid)
                break
            if (stream_size(stdout_file) > args.output_limit_bytes or
                    stream_size(stderr_file) > args.output_limit_bytes):
                output_limited = True
                cleanup_failed = not kill_group(process.pid)
                break
            if now >= next_disk_check:
                next_disk_check = now + 0.5
                if directory_size(Path.cwd()) > args.working_directory_limit_bytes:
                    disk_limited = True
                    cleanup_failed = not kill_group(process.pid)
                    break
            time.sleep(0.05)
        return_code = process.wait()
        # Do not let background children survive a successful parent process.
        # Avoid signaling a now-empty group after its leader has been reaped.
        if process_group_metrics(process.pid) is not None:
            cleanup_failed = not kill_group(process.pid) or cleanup_failed

        stdout, stdout_limited = read_output(stdout_file, args.output_limit_bytes)
        stderr, stderr_limited = read_output(stderr_file, args.output_limit_bytes)

    peak = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if sys.platform != "darwin":
        peak *= 1024
    peak = max(peak, observed_peak)
    memory_limited = memory_limited or peak > args.memory_limit_bytes
    disk_limited = (
        disk_limited or
        directory_size(Path.cwd()) > args.working_directory_limit_bytes
    )
    print(json.dumps({
        "timedOut": timed_out,
        "returnCode": return_code,
        "stdout": stdout,
        "stderr": stderr,
        "outputLimitExceeded": output_limited or stdout_limited or stderr_limited,
        "memoryLimitExceeded": memory_limited,
        "processLimitExceeded": process_limited,
        "diskLimitExceeded": disk_limited,
        "resourceMeasurementUnavailable": measurement_unavailable,
        "processGroupCleanupFailed": cleanup_failed,
        "peakMemoryBytes": peak,
        "memoryLimitBytes": args.memory_limit_bytes,
        "outputLimitBytes": args.output_limit_bytes,
        "fileSizeLimitBytes": args.file_size_limit_bytes,
        "processLimit": args.process_limit,
        "workingDirectoryLimitBytes": args.working_directory_limit_bytes,
    }))


if __name__ == "__main__":
    main()
