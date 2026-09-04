#!/usr/bin/env python3
"""Prove that the release verifier rejects representative hostile submissions."""

from __future__ import annotations

from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from check_submission import check_submission
from render_benchmark_challenge import parse_score
from verify_submission import verify, verify_dependency_sources


ROOT = Path(__file__).resolve().parents[1]
HONEST = ROOT / "GarblingPrize" / "Submission"


def fixture(mutator) -> tempfile.TemporaryDirectory[str]:
    temporary = tempfile.TemporaryDirectory(prefix="g1-garbling-fixture-")
    destination = Path(temporary.name) / "Submission"
    shutil.copytree(HONEST, destination)
    mutator(destination)
    return temporary


def expect_policy_rejection(name: str, mutator) -> None:
    temporary = fixture(mutator)
    submission = Path(temporary.name) / "Submission"
    try:
        check_submission(submission)
        parse_score(submission / "score.txt")
    except SystemExit:
        print(f"ok — rejected hostile fixture: {name}")
    else:
        raise SystemExit(f"FIXTURE_FAILED: verifier accepted {name}")
    finally:
        temporary.cleanup()


def expect_kernel_rejection(name: str, mutator) -> None:
    temporary = fixture(mutator)
    submission = Path(temporary.name) / "Submission"
    try:
        verify(submission, None)
    except (SystemExit, subprocess.CalledProcessError, subprocess.TimeoutExpired):
        print(f"ok — rejected hostile fixture: {name}")
    else:
        raise SystemExit(f"FIXTURE_FAILED: verifier accepted {name}")
    finally:
        temporary.cleanup()


def write(path: Path, value: str) -> None:
    path.write_text(value, encoding="utf-8")


def rename_identifier(submission: Path, old: str, new: str) -> None:
    """Rename an exported identifier without assuming baseline file names."""
    pattern = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(old)}(?![A-Za-z0-9_'])")
    replacements = 0
    for path in sorted(submission.glob("*.lean")):
        source = path.read_text(encoding="utf-8")
        changed, count = pattern.subn(new, source)
        if count:
            write(path, changed)
            replacements += count
    if replacements == 0:
        raise SystemExit(f"FIXTURE_SETUP_FAILED: exported identifier {old} not found")


def main() -> None:
    # Positive lexer fixture: policy words in documentation and ordinary
    # strings are inert, while the real code still has to follow import rules.
    temporary = fixture(lambda submission: write(
        submission / "CommentFixture.lean",
        "import GarblingPrize.Submission.Solution\n"
        "import Mathlib.Data.Nat.Basic\n"
        "import CompPoly.Fields.PrattCertificate\n"
        "/- nested /- sorry axiom unsafe -/ documentation -/\n"
        "def harmlessPolicyText : String := \"sorry admit axiom unsafe\"\n",
    ))
    check_submission(Path(temporary.name) / "Submission")
    temporary.cleanup()
    print("ok — comment/string-aware lexer fixture")

    dependency_temporary = tempfile.TemporaryDirectory(
        prefix="g1-garbling-dependency-fixture-"
    )
    dependency_packages = Path(dependency_temporary.name) / "packages"
    dependency_checkout = dependency_packages / "fixture"
    dependency_checkout.mkdir(parents=True)
    subprocess.run(["git", "init", "--quiet"], cwd=dependency_checkout, check=True)
    subprocess.run(
        ["git", "config", "user.email", "fixture@example.invalid"],
        cwd=dependency_checkout,
        check=True,
    )
    subprocess.run(
        ["git", "config", "user.name", "Verifier Fixture"],
        cwd=dependency_checkout,
        check=True,
    )
    dependency_source = dependency_checkout / "Fixture.lean"
    write(dependency_source, "def fixture : Nat := 1\n")
    subprocess.run(["git", "add", "Fixture.lean"], cwd=dependency_checkout, check=True)
    subprocess.run(
        ["git", "-c", "commit.gpgsign=false", "commit", "--quiet", "-m", "fixture"],
        cwd=dependency_checkout,
        check=True,
    )
    dependency_revision = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=dependency_checkout,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    dependency_entry = {
        "name": "fixture",
        "type": "git",
        "rev": dependency_revision,
    }
    verified = verify_dependency_sources(dependency_packages, [dependency_entry])
    if verified != {"fixture": dependency_revision}:
        raise SystemExit("FIXTURE_FAILED: clean dependency revision was not recorded")
    try:
        verify_dependency_sources(
            dependency_packages,
            [{**dependency_entry, "rev": "0" * 40}],
        )
    except SystemExit:
        print("ok — rejected hostile fixture: dependency revision mismatch")
    else:
        raise SystemExit("FIXTURE_FAILED: verifier accepted wrong dependency revision")
    write(dependency_source, "def fixture : Nat := 2\n")
    try:
        verify_dependency_sources(dependency_packages, [dependency_entry])
    except SystemExit:
        print("ok — rejected hostile fixture: dirty dependency source")
    else:
        raise SystemExit("FIXTURE_FAILED: verifier accepted dirty dependency source")
    dependency_temporary.cleanup()

    expect_policy_rejection(
        "noncanonical score",
        lambda submission: write(submission / "score.txt", "01\n"),
    )
    expect_policy_rejection(
        "forbidden import",
        lambda submission: write(
            submission / "Forbidden.lean",
            "import Lean\n",
        ),
    )
    expect_policy_rejection(
        "extra artifact channel",
        lambda submission: (submission / "advice.bin").write_bytes(b"hidden advice"),
    )
    expect_policy_rejection(
        "kernel bypass",
        lambda submission: write(
            submission / "Bypass.lean",
            "import GarblingPrize.Protected.Target\n"
            "set_option debug.skipKernelTC true\n",
        ),
    )
    expect_policy_rejection(
        "native symbol export",
        lambda submission: write(
            submission / "ExportHijack.lean",
            "import GarblingPrize.Protected.Target\n"
            "@[export lean_g1_sha256]\n"
            "def replaceProtectedHash (_ : ByteArray) : ByteArray := ByteArray.empty\n",
        ),
    )
    expect_policy_rejection(
        "partial executable definition",
        lambda submission: write(
            submission / "Partial.lean",
            "import GarblingPrize.Protected.Target\n"
            "partial def loop (value : Nat) : Nat := loop value\n",
        ),
    )
    expect_policy_rejection(
        "executable namespace shadow",
        lambda submission: write(
            submission / "RunnerShadow.lean",
            "import GarblingPrize.Protected.Target\n"
            "namespace GarblingPrize.Executable\n"
            "def reference : Nat := 0\n"
            "namespace Submission\n"
            "def claimedBytes : Nat := 0\n"
            "end Submission\n"
            "end GarblingPrize.Executable\n",
        ),
    )
    expect_policy_rejection(
        "nested executable namespace shadow",
        lambda submission: write(
            submission / "NestedRunnerShadow.lean",
            "import GarblingPrize.Protected.Target\n"
            "namespace GarblingPrize\n"
            "namespace Executable\n"
            "def reference : Nat := 0\n"
            "end Executable\n"
            "end GarblingPrize\n",
        ),
    )

    expect_kernel_rejection(
        "fake score",
        lambda submission: write(submission / "score.txt", "0\n"),
    )

    expect_kernel_rejection(
        "missing ranked theorem export",
        lambda submission: rename_identifier(
            submission, "candidate", "missingRankedCandidate"
        ),
    )
    print("ok — all hostile verifier fixtures rejected")


if __name__ == "__main__":
    main()
