#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT_DIR"

./scripts/check-submission-imports.sh
python3 scripts/check_protected_tree.py
python3 scripts/check-no-gaps.py
python3 scripts/render_benchmark_challenge.py \
  GarblingPrize/Submission/score.txt \
  GarblingPrize/Benchmark/Challenge.lean

python3 scripts/verify_submission.py GarblingPrize/Submission \
  --result .yukon/bn254-g1-hidden-affine-map-score.json

score="$(tr -d '\n' < GarblingPrize/Submission/score.txt)"
echo "RELEASE CHECK ACCEPTED BY ISOLATED LOCAL VERIFIER (non-authoritative): universal artifact bound = ${score} bytes"
echo "The result JSON includes native garbling/evaluation time and externally measured peak RSS."
