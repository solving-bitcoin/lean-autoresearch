#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

./scripts/check-submission-imports.sh
python3 scripts/check_protected_tree.py
python3 scripts/check-no-gaps.py

# `Solution` is the accepted root; Lake compiles every transitive helper it
# imports. Unused experiments remain source-policy scanned but are not part of
# the accepted executable or proof graph.
lake build GarblingPrize g1-challenge GarblingPrize.Submission.Solution

while IFS= read -r source; do
  lake env lean "$source"
done < <(rg --files GarblingPrize/Protected \
  -g '*.lean' | sort)

lake exe g1-challenge selftest
python3 scripts/check_seeded_oracle.py
python3 scripts/check_verifier_regressions.py
git diff --check
