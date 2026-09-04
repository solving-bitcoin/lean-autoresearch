#!/usr/bin/env python3
"""Snapshot and authenticate the trusted compiled Lake dependency cache."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
import platform
import sys


SCHEMA_VERSION = 1
CHUNK_BYTES = 1024 * 1024


def reject(message: str) -> None:
    raise SystemExit(f"DEPENDENCY_BUILD_REJECTED: {message}")


def hash_field(digest, value: bytes) -> None:
    """Hash one unambiguous length-delimited manifest field."""
    digest.update(len(value).to_bytes(16, "big"))
    digest.update(value)


def package_revisions(package_entries: list[dict[str, object]]) -> dict[str, str]:
    revisions: dict[str, str] = {}
    for entry in package_entries:
        name = entry.get("name")
        revision = entry.get("rev")
        if not isinstance(name, str) or not isinstance(revision, str):
            reject("manifest package is missing a name or resolved revision")
        revisions[name] = revision
    return dict(sorted(revisions.items()))


def dependency_build_digest(packages: Path,
                            package_entries: list[dict[str, object]]) -> str:
    """Hash every compiled dependency byte, its path, and its source revision."""
    digest = hashlib.sha256()
    for name, revision in package_revisions(package_entries).items():
        hash_field(digest, b"package")
        hash_field(digest, name.encode("utf-8"))
        hash_field(digest, revision.encode("ascii"))
        build = packages / name / ".lake" / "build"
        if not build.exists():
            hash_field(digest, b"missing-build")
            continue
        if not build.is_dir() or build.is_symlink():
            reject(f"{name} has a non-regular build directory")
        for path in sorted(build.rglob("*")):
            if path.is_symlink():
                reject(f"compiled dependency contains a symlink: {path}")
            if not path.is_file():
                continue
            relative = path.relative_to(build).as_posix()
            hash_field(digest, b"file")
            hash_field(digest, relative.encode("utf-8"))
            try:
                expected_size = path.stat().st_size
                digest.update(expected_size.to_bytes(16, "big"))
                actual_size = 0
                with path.open("rb") as stream:
                    while chunk := stream.read(CHUNK_BYTES):
                        actual_size += len(chunk)
                        digest.update(chunk)
            except OSError as error:
                reject(f"cannot hash {path}: {error}")
            if actual_size != expected_size:
                reject(f"compiled dependency changed while hashing: {path}")
    return digest.hexdigest()


def snapshot_payload(packages: Path, package_entries: list[dict[str, object]],
                     toolchain: str) -> dict[str, object]:
    return {
        "schemaVersion": SCHEMA_VERSION,
        "platform": sys.platform,
        "machine": platform.machine(),
        "toolchain": toolchain,
        "packageRevisions": package_revisions(package_entries),
        "buildDigest": dependency_build_digest(packages, package_entries),
    }


def write_snapshot(path: Path, packages: Path,
                   package_entries: list[dict[str, object]], toolchain: str) -> None:
    payload = snapshot_payload(packages, package_entries, toolchain)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def verify_snapshot(path: Path, packages: Path,
                    package_entries: list[dict[str, object]],
                    toolchain: str) -> str:
    if not path.is_file() or path.is_symlink():
        reject("run ./setup.sh to create a trusted dependency build snapshot")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as error:
        reject(f"invalid trusted snapshot: {error}")
    expected_metadata = {
        "schemaVersion": SCHEMA_VERSION,
        "platform": sys.platform,
        "machine": platform.machine(),
        "toolchain": toolchain,
        "packageRevisions": package_revisions(package_entries),
    }
    for key, expected in expected_metadata.items():
        if payload.get(key) != expected:
            reject(f"trusted snapshot {key} does not match this verifier")
    expected_digest = payload.get("buildDigest")
    if not isinstance(expected_digest, str) or not len(expected_digest) == 64:
        reject("trusted snapshot has no canonical SHA-256 build digest")
    actual_digest = dependency_build_digest(packages, package_entries)
    if not hmac.compare_digest(expected_digest, actual_digest):
        reject(
            "compiled dependency cache changed after trusted setup "
            f"(expected {expected_digest}, got {actual_digest})"
        )
    return actual_digest


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packages", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("toolchain", type=Path)
    parser.add_argument("snapshot", type=Path)
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    toolchain = args.toolchain.read_text(encoding="utf-8").strip()
    write_snapshot(
        args.snapshot,
        args.packages.resolve(),
        manifest["packages"],
        toolchain,
    )
    print(f"ok — trusted dependency builds {args.snapshot}")


if __name__ == "__main__":
    main()
