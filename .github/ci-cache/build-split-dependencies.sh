#!/usr/bin/env bash
set -euo pipefail

directory=$1
lake exe cache get
python3 .github/ci-cache/dependency-targets.py --snapshot-mathlib > "$RUNNER_TEMP/mathlib-before.json"
python3 .github/ci-cache/dependency-targets.py Colib ColibTest > "$directory/split-targets"
mapfile -t dependencies < "$directory/split-targets"
lake --log-level=error build "${dependencies[@]}" batteries/runLinter mathlib/lint-style mathlib/mk_all
bash scripts/lean_tools/_lint/run.sh --prepare-only
bash .github/ci-cache/prepare-axiom-audit.sh
