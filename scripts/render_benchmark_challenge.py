#!/usr/bin/env python3
"""Bind the canonical score file to the exact protected Lean target."""

from pathlib import Path
import re
import sys


def parse_score(path: Path) -> int:
    raw = path.read_bytes()
    if not re.fullmatch(rb"(?:0|[1-9][0-9]*)(?:\n)?", raw):
        raise SystemExit("SCORE_REJECTED: score.txt must be one canonical ASCII Nat")
    if len(raw.rstrip(b"\n")) > 512:
        raise SystemExit("SCORE_REJECTED: score.txt exceeds 512 decimal digits")
    value = int(raw.strip())
    return value


def main() -> None:
    if len(sys.argv) != 3:
        raise SystemExit("usage: render_benchmark_challenge.py SCORE OUTPUT")
    score = parse_score(Path(sys.argv[1]))
    output = Path(sys.argv[2])
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        "import GarblingPrize.Protected.Executable\n"
        "import GarblingPrize.Submission.Solution\n\n"
        "namespace GarblingPrize.Benchmark\n\n"
        "example : GarblingPrize.Protected.RankedClaim\n"
        f"    GarblingPrize.Submission.scheme {score} :=\n"
        "  GarblingPrize.Benchmark.candidate\n\n"
        "end GarblingPrize.Benchmark\n",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
