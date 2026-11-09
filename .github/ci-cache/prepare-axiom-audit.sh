#!/usr/bin/env bash
set -euo pipefail

tool="$LAKE_CACHE_DIR/axiom-audit"
if ! test -d "$tool/.git"; then
  source=$(mktemp -d "$RUNNER_TEMP/axiom-audit-source.XXXXXX")
  trap 'rm -rf -- "$source"' EXIT
  git clone --depth 1 --branch v0.1.2 https://github.com/leanprover-community/axiom-audit.git "$source/checkout"
  test "$(git -C "$source/checkout" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3
  mkdir -p "$tool"
  cp -a "$source/checkout/." "$tool/"
fi
test "$(git -C "$tool" rev-parse HEAD)" = 46024e005996495c65ef609368e11ab39c4222e3
cp lean-toolchain "$tool/lean-toolchain"
(cd "$tool" && lake "$@" build)
test -x "$tool/.lake/build/bin/axiom-audit"
