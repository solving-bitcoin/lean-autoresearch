#!/usr/bin/env python3
"""Cross-check the protected HMAC/rejection oracle against Python."""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake" / "build" / "bin" / "g1-challenge"
ZERO_SEED = "00" * 32
ZERO_KEY = bytes(32)
INTERNAL_DOMAIN = b"g1-q-plus-rA/internal-uniform/v1"
LABEL_DOMAIN = b"g1-q-plus-rA/test-label-pad/v1"
MAX_MODULUS = 1 << 3072
BASE_FIELD_MODULUS = (
    21888242871839275222246405745257275088696311157297823662689037894645226208583
)
SCALAR_FIELD_MODULUS = (
    21888242871839275222246405745257275088548364400416034343698204186575808495617
)


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
        candidate_bytes = b"".join(
            hmac.new(
                ZERO_KEY,
                INTERNAL_DOMAIN
                + encode_nat(modulus)
                + encode_nat(purpose)
                + encode_nat(attempt)
                + encode_nat(block),
                hashlib.sha256,
            ).digest()
            for block in range(blocks)
        )
        candidate = int.from_bytes(candidate_bytes, "big")
        if candidate < limit:
            return candidate % modulus, attempt, blocks
        attempt += 1


def output(*arguments: str, check: bool = True,
           timeout: int = 30) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [BINARY, *arguments],
        cwd=ROOT,
        check=check,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def sample(modulus: int, purpose: int) -> int:
    result = output("sample", ZERO_SEED, str(modulus), str(purpose))
    return int(result.stdout.strip())


def artifact_digest(randomness_seed: str) -> str:
    result = output(
        "run-case",
        "--randomness-seed", randomness_seed,
        "--label-seed", "11" * 32,
        "--q", "infinity", "--r", "3", "--a", "1,2",
        timeout=120,
    )
    measurement = json.loads(result.stdout.strip().splitlines()[-1])
    if measurement.get("correct") is not True:
        raise SystemExit("EXECUTABLE_REJECTED: official artifact regression failed")
    digests = [
        line.split(":", 2)[2]
        for line in result.stderr.splitlines()
        if line.startswith("garble-ready:")
    ]
    if len(digests) != 1 or not re.fullmatch(r"[0-9a-f]{64}", digests[0]):
        raise SystemExit("EXECUTABLE_REJECTED: missing official artifact digest")
    return digests[0]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--artifact-regression",
        action="store_true",
        help="also run two full official artifacts with fixed labels and hidden input",
    )
    args = parser.parse_args()

    if output("selftest").stdout.strip() != "SELFTEST PASS":
        raise SystemExit("EXECUTABLE_REJECTED: SHA/HMAC self-test failed")

    label = output("pad", ZERO_SEED, "label", "0", "0", "0").stdout.strip()
    expected_label = hmac.new(
        ZERO_KEY,
        LABEL_DOMAIN + encode_nat(0) + b"\x00" + encode_nat(0),
        hashlib.sha256,
    ).hexdigest()
    if label != expected_label:
        raise SystemExit("EXECUTABLE_REJECTED: test-label HMAC vector mismatch")

    # Check the first modulus at every 256-bit block-count transition.
    for blocks in range(1, 13):
        modulus = 1 if blocks == 1 else (1 << (256 * (blocks - 1))) + 1
        expected, _attempt, actual_blocks = reference_sample(modulus, blocks)
        if actual_blocks != blocks or sample(modulus, blocks) != expected:
            raise SystemExit(
                f"EXECUTABLE_REJECTED: {blocks}-block transition mismatch"
            )

    # Exercise the same-byte-width reduction fast path used by the official
    # construction, including its worst possible (sub-256) quotient shape.
    for purpose, modulus in enumerate((
        BASE_FIELD_MODULUS,
        BASE_FIELD_MODULUS - 1,
        SCALAR_FIELD_MODULUS,
        (1 << 248) + 1,
    ), start=100):
        expected, _attempt, _blocks = reference_sample(modulus, purpose)
        if sample(modulus, purpose) != expected:
            raise SystemExit(
                "EXECUTABLE_REJECTED: full-width exact reduction mismatch"
            )

    # These fixed purposes force at least one rejected candidate for each
    # block count, and then check the eventually accepted residue.
    rejection_purposes = [2, 0, 1, 0, 5, 0, 0, 0, 0, 2, 1, 1]
    for blocks, purpose in enumerate(rejection_purposes, start=1):
        modulus = (1 << (256 * blocks - 1)) + 1
        expected, attempt, actual_blocks = reference_sample(modulus, purpose)
        if actual_blocks != blocks or attempt == 0:
            raise SystemExit(
                f"EXECUTABLE_REJECTED: invalid rejection fixture for {blocks} blocks"
            )
        if sample(modulus, purpose) != expected:
            raise SystemExit(
                f"EXECUTABLE_REJECTED: rejected-candidate vector mismatch at {blocks} blocks"
            )

    maximum_expected, maximum_attempt, maximum_blocks = reference_sample(
        MAX_MODULUS, 0
    )
    if maximum_blocks != 12 or maximum_attempt != 0:
        raise SystemExit("EXECUTABLE_REJECTED: invalid 3072-bit maximum fixture")
    if sample(MAX_MODULUS, 0) != maximum_expected:
        raise SystemExit("EXECUTABLE_REJECTED: 3072-bit maximum mismatch")

    huge_purpose = (1 << 512) + 12345
    expected, _attempt, _blocks = reference_sample(17, huge_purpose)
    if sample(17, huge_purpose) != expected:
        raise SystemExit("EXECUTABLE_REJECTED: unbounded-purpose mismatch")

    if output("sample", ZERO_SEED, "0", "0", check=False).returncode == 0:
        raise SystemExit("EXECUTABLE_REJECTED: zero modulus was accepted")
    if output("sample", ZERO_SEED, "017", "0", check=False).returncode == 0:
        raise SystemExit("EXECUTABLE_REJECTED: non-canonical modulus was accepted")
    if output("sample", ZERO_SEED, "17", "00", check=False).returncode == 0:
        raise SystemExit("EXECUTABLE_REJECTED: non-canonical purpose was accepted")
    if output(
        "sample", ZERO_SEED, str(MAX_MODULUS + 1), "0", check=False
    ).returncode == 0:
        raise SystemExit("EXECUTABLE_REJECTED: oversized modulus was accepted")

    print("ok — protected HMAC/rejection oracle (1..12 blocks)")

    if args.artifact_regression:
        first = artifact_digest("00" * 32)
        second = artifact_digest("22" * 32)
        if first == second:
            raise SystemExit(
                "EXECUTABLE_REJECTED: distinct internal seeds produced identical "
                "official artifacts"
            )
        print("ok — distinct internal seeds change the official artifact digest")


if __name__ == "__main__":
    main()
