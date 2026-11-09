#!/usr/bin/env bash
set -euo pipefail

directory=$1
cmp <(head -n 4 "$directory/split-identity") <(
  printf '%s\n' "$GITHUB_REPOSITORY" "$GITHUB_SHA" "$GITHUB_RUN_ID" "$GITHUB_RUN_ATTEMPT"
)
read -r producer < <(tail -n 1 "$directory/split-identity")
test -n "$producer" && test "$producer" != "$RUNNER_NAME"
(cd "$directory" && sha256sum --check --strict split-sha256)
for layer in dependencies stacks tools; do
  python3 .github/ci-cache/checkpoint.py restore --root . --layer "$layer" --input "$directory/$layer.tar.zst"
done

lake --no-build --rehash exe cache get
tar --zstd --unlink-first -xf "$directory/mathlib-delta.tar.zst"
mapfile -t dependencies < "$directory/split-targets"
lake --no-build build --rehash "${dependencies[@]}" batteries/runLinter mathlib/lint-style mathlib/mk_all
CI_LINT_NO_BUILD=true bash scripts/lean_tools/_lint/run.sh --prepare-only
bash .github/ci-cache/prepare-axiom-audit.sh --no-build --rehash
