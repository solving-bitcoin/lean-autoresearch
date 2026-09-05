#!/usr/bin/env python3
"""Digest and validate the protected challenge and verifier inputs."""

from __future__ import annotations

import hashlib
from pathlib import Path


EXPLICIT_PATHS = (
    ".github/workflows/challenge.yml",
    "GarblingPrize/AGENTS.md",
    "GarblingPrize/Executable/Main.lean",
    "GarblingPrize.lean",
    "README.md",
    "benchmark.sh",
    "benchmark.json",
    "challenges.json",
    "lake-manifest.json",
    "lakefile.lean",
    "lean-toolchain",
    "native/sha256.c",
    "scripts/challenge-policy.json",
    "scripts/build_submission_targets.py",
    "scripts/check-axioms.lean",
    "scripts/check-no-gaps.py",
    "scripts/check-submission-imports.sh",
    "scripts/check.sh",
    "scripts/check_protected_tree.py",
    "scripts/check_submission.py",
    "scripts/check_seeded_oracle.py",
    "scripts/check_verifier_regressions.py",
    "scripts/dependency_builds.py",
    "scripts/lean_source_policy.py",
    "scripts/protected_tree.py",
    "scripts/render_benchmark_challenge.py",
    "scripts/render_ci_summary.py",
    "scripts/run_with_rss.py",
    "scripts/run_hostile_fixtures.py",
    "scripts/verify_submission.py",
    "setup.sh",
)


def protected_paths(root: Path) -> list[Path]:
    paths = [root / relative for relative in EXPLICIT_PATHS]
    paths.extend(sorted((root / "GarblingPrize" / "Protected").rglob("*.lean")))
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix())


def protected_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in protected_paths(root):
        if not path.is_file() or path.is_symlink():
            raise SystemExit(f"PROTECTED_TREE_REJECTED: missing regular file {path}")
        relative = path.relative_to(root).as_posix()
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def assert_protected_tree(root: Path) -> str:
    expected_path = root / "scripts" / "protected-tree.sha256"
    expected = expected_path.read_text(encoding="ascii").strip()
    actual = protected_digest(root)
    if actual != expected:
        raise SystemExit(
            "PROTECTED_TREE_REJECTED: protected digest mismatch "
            f"(expected {expected}, got {actual})"
        )
    return actual
