"""Shared dependency provenance, resource guards, and canonical score parsing."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import tempfile


def git_output(arguments: list[str], cwd: Path, purpose: str) -> str:
    try:
        result = subprocess.run(
            ["git", *arguments],
            cwd=cwd,
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f"VERIFY_REJECTED: cannot {purpose} for {cwd}: {error}") from error
    return result.stdout.strip()


def verify_dependency_sources(packages: Path,
                              package_entries: list[dict[str, object]]) -> dict[str, str]:
    """Require every cached Lake dependency to match its resolved Git source."""
    if not packages.is_dir() or packages.is_symlink():
        raise SystemExit(
            "VERIFY_REJECTED: run the challenge's setup.sh to install a regular pinned package tree"
        )

    revisions: dict[str, str] = {}
    for entry in package_entries:
        name = entry.get("name")
        expected = entry.get("rev")
        kind = entry.get("type")
        if not isinstance(name, str) or not isinstance(expected, str) or kind != "git":
            raise SystemExit("VERIFY_REJECTED: every manifest dependency must be pinned by Git commit")

        checkout = packages / name
        if not checkout.is_dir() or checkout.is_symlink():
            raise SystemExit(
                f"VERIFY_REJECTED: run the challenge's setup.sh to install regular pinned checkout {name}"
            )
        actual = git_output(["rev-parse", "HEAD"], checkout,
                            f"read dependency revision {name}")
        if actual != expected:
            raise SystemExit(
                f"VERIFY_REJECTED: dependency {name} is at {actual}, expected {expected}"
            )
        dirty = git_output(
            ["status", "--porcelain=v1", "--untracked-files=all"],
            checkout,
            f"inspect dependency worktree {name}",
        )
        if dirty:
            raise SystemExit(f"VERIFY_REJECTED: dependency {name} worktree is not clean")
        revisions[name] = actual
    return revisions


def kill_recorded_group(pid_file: Path) -> None:
    """Best-effort outer cleanup if the resource helper itself fails."""
    try:
        pid = int(pid_file.read_text(encoding="ascii"))
        if pid <= 0:
            return
        os.killpg(pid, signal.SIGKILL)
    except (FileNotFoundError, PermissionError, ProcessLookupError, ValueError):
        pass


def run_limited(command: list[str], cwd: Path, timeout_seconds: int,
                memory_limit_bytes: int, output_limit_bytes: int,
                file_size_limit_bytes: int, process_limit: int,
                working_directory_limit_bytes: int, rss_helper: Path,
                purpose: str) -> dict[str, object]:
    environment = os.environ.copy()
    for variable in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_HOME"):
        environment.pop(variable, None)
    with tempfile.TemporaryDirectory(prefix="challenge-resource-guard-") as temporary:
        pid_file = Path(temporary) / "child.pid"
        try:
            helper_result = subprocess.run(
                [shutil.which("python3") or "python3", str(rss_helper),
                 "--timeout", str(timeout_seconds),
                 "--memory-limit-bytes", str(memory_limit_bytes),
                 "--output-limit-bytes", str(output_limit_bytes),
                 "--file-size-limit-bytes", str(file_size_limit_bytes),
                 "--process-limit", str(process_limit),
                 "--working-directory-limit-bytes", str(working_directory_limit_bytes),
                 "--pid-file", str(pid_file),
                 "--", *command],
                cwd=cwd,
                env=environment,
                check=True,
                capture_output=True,
                text=True,
                timeout=timeout_seconds + 30,
            )
        except subprocess.TimeoutExpired as error:
            kill_recorded_group(pid_file)
            raise SystemExit(
                f"VERIFY_REJECTED: {purpose} exceeded {timeout_seconds} seconds"
            ) from error
        except subprocess.CalledProcessError as error:
            kill_recorded_group(pid_file)
            raise SystemExit(
                f"VERIFY_REJECTED: resource helper failed during {purpose}:\n" +
                error.stderr
            ) from error

    try:
        measurement = json.loads(helper_result.stdout)
    except json.JSONDecodeError as error:
        raise SystemExit("VERIFY_REJECTED: RSS helper emitted invalid JSON") from error
    if measurement.get("resourceMeasurementUnavailable") is True:
        raise SystemExit(
            f"VERIFY_REJECTED: aggregate resource measurement unavailable for {purpose}"
        )
    if measurement.get("processGroupCleanupFailed") is True:
        raise SystemExit(f"VERIFY_REJECTED: could not clean up {purpose} process group")
    if measurement.get("outputLimitExceeded") is True:
        raise SystemExit(f"VERIFY_REJECTED: {purpose} exceeded its output limit")
    if measurement.get("memoryLimitExceeded") is True:
        # Preserve bounded diagnostics from the killed compiler. Its exit
        # status cannot turn a resource rejection into acceptance.
        output = "\n".join(
            f"{stream} (last 8192 characters):\n{str(measurement[stream])[-8192:]}"
            for stream in ("stdout", "stderr") if measurement.get(stream)
        )
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} exceeded its memory limit "
            f"(peak {measurement.get('peakMemoryBytes')}, "
            f"limit {measurement.get('memoryLimitBytes')})" +
            ("\n" + output if output else "")
        )
    if measurement.get("processLimitExceeded") is True:
        raise SystemExit(f"VERIFY_REJECTED: {purpose} exceeded its process limit")
    if measurement.get("diskLimitExceeded") is True:
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} exceeded its working-directory limit"
        )
    if measurement.get("timedOut") is True:
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} exceeded {timeout_seconds} seconds"
        )
    if measurement.get("returnCode") != 0:
        stdout = str(measurement.get("stdout", ""))
        stderr = str(measurement.get("stderr", ""))
        output = ""
        if stdout:
            output += "stdout:\n" + stdout
        if stderr:
            if output and not output.endswith("\n"):
                output += "\n"
            output += "stderr:\n" + stderr
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} failed:\n" + output
        )
    return measurement


def parse_score(path: Path) -> int:
    raw = path.read_bytes()
    if not re.fullmatch(rb"(?:0|[1-9][0-9]*)(?:\n)?", raw):
        raise SystemExit("SCORE_REJECTED: score.txt must be one canonical ASCII Nat")
    if len(raw.rstrip(b"\n")) > 512:
        raise SystemExit("SCORE_REJECTED: score.txt exceeds 512 decimal digits")
    value = int(raw.strip())
    return value
