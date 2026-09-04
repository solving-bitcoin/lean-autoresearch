#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT_DIR"

lake build GarblingPrize.Protected.Target GarblingPrize.Protected.Runner g1-challenge
python3 scripts/dependency_builds.py \
  .lake/packages lake-manifest.json lean-toolchain .lake/dependency-builds.json
