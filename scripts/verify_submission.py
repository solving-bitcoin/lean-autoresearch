#!/usr/bin/env python3
"""Build and kernel-audit one submission in a fresh local Lake project."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
from pathlib import Path
import re
import secrets
import signal
import shutil
import subprocess
import sys
import tempfile

from check_submission import check_submission
from dependency_builds import verify_snapshot as verify_dependency_build_snapshot
from protected_tree import assert_protected_tree
from render_benchmark_challenge import parse_score


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "scripts" / "challenge-policy.json"
BASE_FIELD_MODULUS = (
    21888242871839275222246405745257275088696311157297823662689037894645226208583
)
SCALAR_FIELD_MODULUS = (
    21888242871839275222246405745257275088548364400416034343698204186575808495617
)
GENERATOR = (1, 2)
INTERNAL_DOMAIN = b"g1-q-plus-rA/internal-uniform/v1"
LABEL_DOMAIN = b"g1-q-plus-rA/test-label-pad/v1"
MAX_SAMPLING_MODULUS = 1 << 3072


def tree_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.iterdir() if item.is_file()):
        digest.update(path.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def repository_commit(path: Path) -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=path,
            check=True,
            capture_output=True,
            text=True,
            timeout=10,
        )
        return result.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return "unavailable"


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
            "VERIFY_REJECTED: run ./setup.sh to install a regular pinned package tree"
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
                f"VERIFY_REJECTED: run ./setup.sh to install regular pinned checkout {name}"
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


def run_checked(command: list[str], cwd: Path, policy: dict[str, object],
                rss_helper: Path, purpose: str) -> None:
    """Run untrusted elaboration under the same fail-closed group monitor."""
    measurement = run_limited(
        command,
        cwd,
        int(policy["compilerRuntimeTimeoutSeconds"]),
        int(policy["compilerMemoryLimitBytes"]),
        int(policy["compilerOutputLimitBytes"]),
        int(policy["compilerFileSizeLimitBytes"]),
        int(policy["compilerProcessLimit"]),
        int(policy["compilerWorkingDirectoryLimitBytes"]),
        rss_helper,
        purpose,
    )
    stdout = str(measurement.get("stdout", ""))
    stderr = str(measurement.get("stderr", ""))
    if stdout:
        print(stdout, end="" if stdout.endswith("\n") else "\n")
    if stderr:
        print(stderr, end="" if stderr.endswith("\n") else "\n", file=sys.stderr)


def point_add(left: tuple[int, int] | None,
              right: tuple[int, int] | None) -> tuple[int, int] | None:
    """Independent affine BN254 G1 addition used only to generate test inputs."""
    if left is None:
        return right
    if right is None:
        return left
    x1, y1 = left
    x2, y2 = right
    if x1 == x2 and (y1 + y2) % BASE_FIELD_MODULUS == 0:
        return None
    if left == right:
        slope = (3 * x1 * x1) * pow(2 * y1, -1, BASE_FIELD_MODULUS)
    else:
        slope = (y2 - y1) * pow(x2 - x1, -1, BASE_FIELD_MODULUS)
    slope %= BASE_FIELD_MODULUS
    x3 = (slope * slope - x1 - x2) % BASE_FIELD_MODULUS
    y3 = (slope * (x1 - x3) - y1) % BASE_FIELD_MODULUS
    return x3, y3


def point_mul(scalar: int, point: tuple[int, int]) -> tuple[int, int] | None:
    result = None
    addend: tuple[int, int] | None = point
    while scalar:
        if scalar & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        scalar >>= 1
    return result


def random_nonzero_point() -> tuple[int, int]:
    while True:
        scalar = secrets.randbelow(SCALAR_FIELD_MODULUS - 1) + 1
        point = point_mul(scalar, GENERATOR)
        if point is not None:
            return point


def random_full_width_scalar() -> int:
    """Choose a canonical scalar whose top (254th) bit is set."""
    return secrets.randbelow(SCALAR_FIELD_MODULUS - 2**253) + 2**253


def encode_nat(value: int) -> bytes:
    digits = bytearray()
    while value:
        digits.extend((1, value % 256))
        value //= 256
    digits.append(0)
    return bytes(digits)


def reference_sample(modulus: int, purpose: int) -> tuple[int, int, int]:
    width = (modulus - 1).bit_length()
    blocks = max(1, (width + 255) // 256)
    sample_range = 1 << (256 * blocks)
    limit = (sample_range // modulus) * modulus
    attempt = 0
    while True:
        candidate = int.from_bytes(b"".join(
            hmac.new(
                bytes(32),
                INTERNAL_DOMAIN + encode_nat(modulus) + encode_nat(purpose)
                + encode_nat(attempt) + encode_nat(block),
                hashlib.sha256,
            ).digest()
            for block in range(blocks)
        ), "big")
        if candidate < limit:
            return candidate % modulus, attempt, blocks
        attempt += 1


def artifact_within_bound(artifact_bytes: object, score: int) -> bool:
    """The proved score is an inclusive universal upper bound, not an equality."""
    return (
        isinstance(artifact_bytes, int)
        and not isinstance(artifact_bytes, bool)
        and 0 <= artifact_bytes <= score
    )


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
    with tempfile.TemporaryDirectory(prefix="g1-resource-guard-") as temporary:
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
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} exceeded its memory limit "
            f"(peak {measurement.get('peakMemoryBytes')}, "
            f"limit {measurement.get('memoryLimitBytes')})"
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
        raise SystemExit(
            f"VERIFY_REJECTED: {purpose} failed:\n" +
            str(measurement.get("stderr", ""))
        )
    return measurement


def run_native_selftests(binary: Path, cwd: Path, memory_limit_bytes: int,
                         output_limit_bytes: int, file_size_limit_bytes: int,
                         process_limit: int, working_directory_limit_bytes: int,
                         rss_helper: Path) -> None:
    """Check SHA, HMAC, label addressing, and exact rejection sampling."""
    zero_seed = "00" * 32
    huge_purpose = 2**512 + 12345
    cases = [
        ([str(binary), "selftest"], "SELFTEST PASS"),
        ([str(binary), "pad", zero_seed, "label", "0", "0", "0"],
         hmac.new(bytes(32), LABEL_DOMAIN + encode_nat(0) + b"\x00"
                  + encode_nat(0), hashlib.sha256).hexdigest()),
    ]
    for blocks in range(1, 13):
        modulus = 1 if blocks == 1 else (1 << (256 * (blocks - 1))) + 1
        expected, _attempt, actual_blocks = reference_sample(modulus, blocks)
        if actual_blocks != blocks:
            raise SystemExit("VERIFY_REJECTED: invalid block-transition fixture")
        cases.append(([str(binary), "sample", zero_seed, str(modulus), str(blocks)],
                      str(expected)))
    for purpose, modulus in enumerate((
        BASE_FIELD_MODULUS,
        BASE_FIELD_MODULUS - 1,
        SCALAR_FIELD_MODULUS,
        (1 << 248) + 1,
    ), start=100):
        expected, _attempt, _blocks = reference_sample(modulus, purpose)
        cases.append(([str(binary), "sample", zero_seed, str(modulus), str(purpose)],
                      str(expected)))
    rejection_purposes = [2, 0, 1, 0, 5, 0, 0, 0, 0, 2, 1, 1]
    for blocks, purpose in enumerate(rejection_purposes, start=1):
        modulus = (1 << (256 * blocks - 1)) + 1
        expected, attempt, actual_blocks = reference_sample(modulus, purpose)
        if attempt == 0 or actual_blocks != blocks:
            raise SystemExit("VERIFY_REJECTED: invalid rejection fixture")
        cases.append(([str(binary), "sample", zero_seed, str(modulus), str(purpose)],
                      str(expected)))
    maximum, _attempt, blocks = reference_sample(MAX_SAMPLING_MODULUS, 0)
    if blocks != 12:
        raise SystemExit("VERIFY_REJECTED: invalid maximum-modulus fixture")
    cases.append(([str(binary), "sample", zero_seed,
                  str(MAX_SAMPLING_MODULUS), "0"], str(maximum)))
    huge, _attempt, _blocks = reference_sample(17, huge_purpose)
    cases.append(([str(binary), "sample", zero_seed, "17", str(huge_purpose)],
                  str(huge)))
    for command, expected in cases:
        result = run_limited(
            command, cwd, 30, memory_limit_bytes, output_limit_bytes,
            file_size_limit_bytes, process_limit, working_directory_limit_bytes,
            rss_helper, "native SHA/HMAC/rejection self-test",
        )
        if str(result.get("stdout", "")).strip() != expected:
            raise SystemExit(
                "VERIFY_REJECTED: isolated native SHA/HMAC/rejection self-test failed"
            )


def audit_submission_symbols(project: Path) -> None:
    """Reject a submission object that defines the protected native SHA symbol."""
    nm = shutil.which("nm")
    if nm is None:
        raise SystemExit("VERIFY_REJECTED: nm is required for native symbol audit")
    object_root = project / ".lake" / "build" / "ir" / "GarblingPrize" / "Submission"
    object_files = set(object_root.glob("*.c.o")) | set(object_root.glob("*.c.o.export"))
    for object_file in sorted(object_files):
        result = subprocess.run(
            [nm, "-g", str(object_file)],
            check=True,
            capture_output=True,
            text=True,
            timeout=30,
        )
        symbols: set[str] = set()
        for line in result.stdout.splitlines():
            fields = line.split()
            if len(fields) < 2:
                continue
            symbol_type = fields[-2]
            # An undefined reference is resolved by the verifier-owned native
            # library; it is not a candidate definition or override. Lowercase
            # weak/indirect undefined entries likewise have no object address.
            if symbol_type.upper() == "U" or (
                len(fields) == 2 and symbol_type in {"w", "v"}
            ):
                continue
            symbols.add(fields[-1])
        protected_symbols = {
            "lean_g1_sha256", "_lean_g1_sha256",
            "lean_g1_hmac_sha256", "_lean_g1_hmac_sha256",
            "lean_g1_uniform_below", "_lean_g1_uniform_below",
            "lean_g1_uniform_below_nat", "_lean_g1_uniform_below_nat",
            "lean_g1_nat_le_32", "_lean_g1_nat_le_32",
            "lean_g1_pack_four_254", "_lean_g1_pack_four_254",
        }
        collision = symbols & protected_symbols
        if collision:
            raise SystemExit(
                "VERIFY_REJECTED: submission object overrides protected native "
                f"symbol {sorted(collision)[0]}: {object_file.name}"
            )


def run_native_case(binary: Path, cwd: Path, score: int,
                    timeout_seconds: int, memory_limit_bytes: int,
                    output_limit_bytes: int, file_size_limit_bytes: int,
                    process_limit: int, working_directory_limit_bytes: int,
                    rss_helper: Path, q_is_infinity: bool, *,
                    randomness_seed: str | None = None,
                    label_seed: str | None = None,
                    fixed_case: tuple[str, int, tuple[int, int]] | None = None,
                    ) -> dict[str, object]:
    """Run one real garble/evaluate case and measure the child process RSS."""
    if fixed_case is None:
        q = None if q_is_infinity else random_nonzero_point()
        q_text = "infinity" if q is None else f"{q[0]},{q[1]}"
        a = random_nonzero_point()
        r = random_full_width_scalar()
    else:
        q_text, r, a = fixed_case
        if (q_text == "infinity") is not q_is_infinity:
            raise SystemExit("VERIFY_REJECTED: inconsistent fixed native case")
    command = [
        str(binary),
        "run-case",
        "--randomness-seed",
        randomness_seed or secrets.token_hex(32),
        "--label-seed",
        label_seed or secrets.token_hex(32),
        "--q",
        q_text,
        "--r",
        str(r),
        "--a",
        f"{a[0]},{a[1]}",
    ]
    process_measurement = run_limited(
        command, cwd, timeout_seconds, memory_limit_bytes,
        output_limit_bytes, file_size_limit_bytes, process_limit,
        working_directory_limit_bytes, rss_helper, "native garbling case",
    )

    output_lines = [
        line for line in str(process_measurement.get("stdout", "")).splitlines()
        if line.strip()
    ]
    if not output_lines:
        raise SystemExit("VERIFY_REJECTED: native runner emitted no JSON result")
    try:
        measurement = json.loads(output_lines[-1])
    except json.JSONDecodeError as error:
        raise SystemExit("VERIFY_REJECTED: native runner emitted invalid JSON") from error

    if measurement.get("correct") is not True:
        raise SystemExit("VERIFY_REJECTED: native runner produced an incorrect output")
    artifact_bytes = measurement.get("artifactBytes")
    if not artifact_within_bound(artifact_bytes, score):
        raise SystemExit(
            "VERIFY_REJECTED: runtime artifact size exceeds the proved bound"
        )

    artifact_digests = [
        line.split(":", 2)[2]
        for line in str(process_measurement.get("stderr", "")).splitlines()
        if line.startswith("garble-ready:")
    ]
    if len(artifact_digests) != 1 or not re.fullmatch(
        r"[0-9a-f]{64}", artifact_digests[0]
    ):
        raise SystemExit("VERIFY_REJECTED: missing native artifact digest checkpoint")

    peak_memory = process_measurement.get("peakMemoryBytes")
    if not isinstance(peak_memory, int) or peak_memory <= 0:
        raise SystemExit("VERIFY_REJECTED: invalid native peak RSS")
    measurement["peakMemoryBytes"] = peak_memory
    measurement["peakMemoryMeasurement"] = "external-verifier"
    measurement["caseDigest"] = hashlib.sha256(
        f"{q_text}|{r}|{a[0]},{a[1]}".encode("ascii")
    ).hexdigest()
    measurement["artifactDigest"] = artifact_digests[0]
    measurement["qIsInfinity"] = q_is_infinity
    return measurement


def write_challenge(path: Path, score: int) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "import GarblingPrize.Protected.Executable\n"
        "import GarblingPrize.Submission.Solution\n\n"
        "namespace GarblingPrize.Benchmark\n\n"
        "example : GarblingPrize.Protected.RankedClaim\n"
        f"    GarblingPrize.Submission.scheme {score} :=\n"
        "  GarblingPrize.Benchmark.candidate\n\n"
        "end GarblingPrize.Benchmark\n",
        encoding="utf-8",
    )


def verify(submission: Path, result_path: Path | None) -> dict[str, object]:
    submission = submission.resolve()
    protected = assert_protected_tree(ROOT)
    check_submission(submission)
    score = parse_score(submission / "score.txt")
    policy = json.loads(POLICY_PATH.read_text(encoding="utf-8"))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest_packages = manifest["packages"]
    package_entries = {package["name"]: package for package in manifest_packages}
    mathlib_entry = package_entries["mathlib"]
    comp_poly_entry = package_entries["CompPoly"]

    packages = ROOT / ".lake" / "packages"
    dependency_revisions = verify_dependency_sources(packages, manifest_packages)
    packages = packages.resolve()
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    dependency_build_snapshot = ROOT / ".lake" / "dependency-builds.json"
    dependency_build_digest = verify_dependency_build_snapshot(
        dependency_build_snapshot,
        packages,
        manifest_packages,
        toolchain,
    )
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("VERIFY_REJECTED: lake is not available")

    with tempfile.TemporaryDirectory(prefix="g1-garbling-verifier-") as temporary:
        project = Path(temporary)
        shutil.copytree(ROOT / "GarblingPrize" / "Protected",
                        project / "GarblingPrize" / "Protected")
        shutil.copytree(submission, project / "GarblingPrize" / "Submission")
        shutil.copytree(ROOT / "GarblingPrize" / "Executable",
                        project / "GarblingPrize" / "Executable")
        shutil.copytree(ROOT / "native", project / "native")
        (project / "scripts").mkdir(parents=True)
        shutil.copy2(ROOT / "scripts" / "check-axioms.lean",
                     project / "scripts" / "check-axioms.lean")
        shutil.copy2(ROOT / "scripts" / "build_submission_targets.py",
                     project / "scripts" / "build_submission_targets.py")
        shutil.copy2(ROOT / "scripts" / "run_with_rss.py",
                     project / "scripts" / "run_with_rss.py")
        shutil.copy2(ROOT / "lean-toolchain", project / "lean-toolchain")
        shutil.copy2(ROOT / "lakefile.lean", project / "lakefile.lean")
        shutil.copy2(ROOT / "lake-manifest.json", project / "lake-manifest.json")
        (project / ".lake").mkdir()
        os.symlink(packages, project / ".lake" / "packages", target_is_directory=True)
        write_challenge(project / "GarblingPrize" / "Benchmark" / "Challenge.lean", score)

        # Compile the accepted root and its transitive imports. Every extra
        # source file was already scanned above, but an unimported experiment
        # is not part of the candidate proof or executable.
        rss_helper = project / "scripts" / "run_with_rss.py"
        build_helper = project / "scripts" / "build_submission_targets.py"
        run_checked(
            [shutil.which("python3") or "python3", str(build_helper), lake,
             "GarblingPrize.Submission.Solution",
             "GarblingPrize.Benchmark.Challenge", "g1-challenge"],
            project,
            policy,
            rss_helper,
            "submission build",
        )
        audit_submission_symbols(project)
        run_checked(
            [lake, "env", "lean", "scripts/check-axioms.lean"],
            project,
            policy,
            rss_helper,
            "axiom audit",
        )
        run_native_selftests(
            project / ".lake" / "build" / "bin" / "g1-challenge",
            project,
            policy["nativeMemoryLimitBytes"],
            policy["nativeOutputLimitBytes"],
            policy["nativeFileSizeLimitBytes"],
            policy["nativeProcessLimit"],
            policy["nativeWorkingDirectoryLimitBytes"],
            rss_helper,
        )
        binary = project / ".lake" / "build" / "bin" / "g1-challenge"
        native_measurements = [
            run_native_case(
                binary, project, score, policy["nativeRuntimeTimeoutSeconds"],
                policy["nativeMemoryLimitBytes"], policy["nativeOutputLimitBytes"],
                policy["nativeFileSizeLimitBytes"], policy["nativeProcessLimit"],
                policy["nativeWorkingDirectoryLimitBytes"], rss_helper, False,
            ),
            run_native_case(
                binary, project, score, policy["nativeRuntimeTimeoutSeconds"],
                policy["nativeMemoryLimitBytes"], policy["nativeOutputLimitBytes"],
                policy["nativeFileSizeLimitBytes"], policy["nativeProcessLimit"],
                policy["nativeWorkingDirectoryLimitBytes"], rss_helper, True,
            ),
        ]

        # Lake package directories are shared read-only inputs to the isolated
        # project. Detect compilation-time additions or replacements before
        # accepting a result.
        after_build_digest = verify_dependency_build_snapshot(
            dependency_build_snapshot,
            packages,
            manifest_packages,
            toolchain,
        )
        if after_build_digest != dependency_build_digest:
            raise SystemExit("VERIFY_REJECTED: dependency builds changed during verification")

    payload: dict[str, object] = {
        "schemaVersion": policy["schemaVersion"],
        "score": score,
        "challengeVersion": policy["challengeVersion"],
        "profile": policy["profile"],
        "claim": policy["claim"],
        "metric": policy["metric"],
        "unit": policy["unit"],
        "direction": policy["direction"],
        "submissionDigest": tree_digest(submission),
        "protectedDigest": protected,
        "submissionCommit": repository_commit(submission),
        "challengeCommit": repository_commit(ROOT),
        "toolchain": toolchain,
        "mathlibInputRevision": mathlib_entry["inputRev"],
        "mathlibRevision": mathlib_entry["rev"],
        "compPolyInputRevision": comp_poly_entry["inputRev"],
        "compPolyRevision": comp_poly_entry["rev"],
        "internalSeedBytes": policy["internalSeedBytes"],
        "testLabelSeedBytes": policy["testLabelSeedBytes"],
        "internalOracleMaxBits": policy["internalOracleMaxBits"],
        "executableInternalOracle": policy["executableInternalOracle"],
        "externalLabelProvider": policy["externalLabelProvider"],
        "unboundedPurposes": policy["unboundedPurposes"],
        "compilerRuntimeTimeoutSeconds": policy["compilerRuntimeTimeoutSeconds"],
        "compilerMemoryLimitBytes": policy["compilerMemoryLimitBytes"],
        "compilerOutputLimitBytes": policy["compilerOutputLimitBytes"],
        "compilerFileSizeLimitBytes": policy["compilerFileSizeLimitBytes"],
        "compilerProcessLimit": policy["compilerProcessLimit"],
        "compilerWorkingDirectoryLimitBytes":
            policy["compilerWorkingDirectoryLimitBytes"],
        "nativeRuntimeTimeoutSeconds": policy["nativeRuntimeTimeoutSeconds"],
        "nativeMemoryLimitBytes": policy["nativeMemoryLimitBytes"],
        "nativeOutputLimitBytes": policy["nativeOutputLimitBytes"],
        "nativeFileSizeLimitBytes": policy["nativeFileSizeLimitBytes"],
        "nativeProcessLimit": policy["nativeProcessLimit"],
        "nativeWorkingDirectoryLimitBytes":
            policy["nativeWorkingDirectoryLimitBytes"],
        "nativeInputSelection": policy["nativeInputSelection"],
        "nativeHashSelfTested": True,
        "nativeSymbolsAudited": True,
        "protectedSeededOracleContractChecked": True,
        "nativeArtifactDigestsRecorded": True,
        "nativeGarblingBenchmarked": True,
        "nativeMeasurements": native_measurements,
        "proofAndSizeAccepted": True,
        "releaseReady": True,
        "dependencySourceRevisions": dependency_revisions,
        "dependencyBuildTrust": policy["dependencyBuildTrust"],
        "dependencyBuildDigest": dependency_build_digest,
        "locallyKernelChecked": True,
        "independentVerified": False,
        "verificationAuthority": "isolated-local-verifier",
    }
    if result_path is not None:
        result_path.parent.mkdir(parents=True, exist_ok=True)
        result_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("submission", type=Path)
    parser.add_argument("--result", type=Path)
    args = parser.parse_args()
    payload = verify(args.submission, args.result)
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
