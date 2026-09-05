#!/usr/bin/env python3
"""Render the isolated verifier result as a GitHub Actions job summary."""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path


def text(value: object, field: str) -> str:
    if not isinstance(value, str) or not value:
        raise SystemExit(f"CI_SUMMARY_REJECTED: {field} must be a nonempty string")
    return value


def integer(value: object, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise SystemExit(f"CI_SUMMARY_REJECTED: {field} must be a nonnegative integer")
    return value


def boolean(value: object, field: str) -> bool:
    if not isinstance(value, bool):
        raise SystemExit(f"CI_SUMMARY_REJECTED: {field} must be a boolean")
    return value


def cell(value: object) -> str:
    return html.escape(str(value), quote=True).replace("|", "&#124;").replace("\n", " ")


def code(value: object) -> str:
    return f"<code>{cell(value)}</code>"


def yes_no(value: bool) -> str:
    return "✅ Yes" if value else "❌ No"


def mib(value: int) -> str:
    return f"{value / (1024 * 1024):,.1f} MiB"


def load_result(path: Path) -> dict[str, object]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise SystemExit(f"CI_SUMMARY_REJECTED: cannot read verifier result: {error}") from error
    if not isinstance(payload, dict):
        raise SystemExit("CI_SUMMARY_REJECTED: verifier result must be a JSON object")
    return payload


def render(payload: dict[str, object]) -> str:
    score = integer(payload.get("score"), "score")
    unit = text(payload.get("unit"), "unit")
    metric = text(payload.get("metric"), "metric")
    direction = text(payload.get("direction"), "direction")
    proof_accepted = boolean(payload.get("proofAndSizeAccepted"), "proofAndSizeAccepted")
    release_ready = boolean(payload.get("releaseReady"), "releaseReady")
    measurements = payload.get("nativeMeasurements")
    if not isinstance(measurements, list) or not measurements:
        raise SystemExit("CI_SUMMARY_REJECTED: nativeMeasurements must be a nonempty array")

    lines = [
        "# Submission result",
        "",
        f"> **Score: {score:,} {cell(unit)}** ({cell(direction)} `{cell(metric)}`)",
        "",
        "| Verification | Result |",
        "| --- | --- |",
        f"| Proof and size accepted | {yes_no(proof_accepted)} |",
        f"| Release ready | {yes_no(release_ready)} |",
        f"| Challenge | {code(text(payload.get('challengeVersion'), 'challengeVersion'))} |",
        f"| Profile | {code(text(payload.get('profile'), 'profile'))} |",
        f"| Toolchain | {code(text(payload.get('toolchain'), 'toolchain'))} |",
        f"| Verification authority | {code(text(payload.get('verificationAuthority'), 'verificationAuthority'))} |",
        "",
        "## Native verification cases",
        "",
        "| Hidden Q | Correct | Artifact | Garble | Evaluate | Peak RSS | Artifact digest |",
        "| --- | --- | ---: | ---: | ---: | ---: | --- |",
    ]

    for index, raw_measurement in enumerate(measurements):
        if not isinstance(raw_measurement, dict):
            raise SystemExit(
                f"CI_SUMMARY_REJECTED: nativeMeasurements[{index}] must be an object"
            )
        q_is_infinity = boolean(
            raw_measurement.get("qIsInfinity"), f"nativeMeasurements[{index}].qIsInfinity"
        )
        correct = boolean(
            raw_measurement.get("correct"), f"nativeMeasurements[{index}].correct"
        )
        artifact_bytes = integer(
            raw_measurement.get("artifactBytes"),
            f"nativeMeasurements[{index}].artifactBytes",
        )
        garble_ms = integer(
            raw_measurement.get("garbleMilliseconds"),
            f"nativeMeasurements[{index}].garbleMilliseconds",
        )
        evaluate_ms = integer(
            raw_measurement.get("evaluateMilliseconds"),
            f"nativeMeasurements[{index}].evaluateMilliseconds",
        )
        peak_memory = integer(
            raw_measurement.get("peakMemoryBytes"),
            f"nativeMeasurements[{index}].peakMemoryBytes",
        )
        artifact_digest = text(
            raw_measurement.get("artifactDigest"),
            f"nativeMeasurements[{index}].artifactDigest",
        )
        lines.append(
            f"| {'Infinity' if q_is_infinity else 'Finite'} | {yes_no(correct)} | "
            f"{artifact_bytes:,} bytes | {garble_ms:,} ms | {evaluate_ms:,} ms | "
            f"{mib(peak_memory)} | {code(artifact_digest)} |"
        )

    details = (
        ("Claim", "claim"),
        ("Submission commit", "submissionCommit"),
        ("Submission digest", "submissionDigest"),
        ("Protected digest", "protectedDigest"),
        ("Dependency build digest", "dependencyBuildDigest"),
        ("Mathlib revision", "mathlibRevision"),
        ("CompPoly revision", "compPolyRevision"),
    )
    lines.extend([
        "",
        "<details>",
        "<summary>Verifier details</summary>",
        "",
        "| Field | Value |",
        "| --- | --- |",
    ])
    for label, field in details:
        lines.append(f"| {label} | {code(text(payload.get(field), field))} |")
    lines.extend(["", "</details>", ""])
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("result", type=Path)
    parser.add_argument("summary", type=Path)
    args = parser.parse_args()

    payload = load_result(args.result)
    summary = render(payload)
    try:
        with args.summary.open("a", encoding="utf-8") as output:
            output.write(summary)
    except OSError as error:
        raise SystemExit(f"CI_SUMMARY_REJECTED: cannot write job summary: {error}") from error

    score = integer(payload.get("score"), "score")
    unit = text(payload.get("unit"), "unit").replace("\r", " ").replace("\n", " ")
    print(f"::notice title=Submission score::{score} {unit}")


if __name__ == "__main__":
    main()
