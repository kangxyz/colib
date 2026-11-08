#!/usr/bin/env bash
set -euo pipefail

setup_with_elan() (
  # Keep the API token out of the downloaded installer's environment.
  unset GH_TOKEN
  installer="$RUNNER_TEMP/elan-init.sh"
  curl --fail --silent --show-error --location --retry 2 --retry-all-errors \
    --connect-timeout 20 --max-time 120 \
    https://elan.lean-lang.org/elan-init.sh --output "$installer" || return
  chmod +x "$installer" || return
  "$installer" -y --default-toolchain none || return
  elan_bin="${ELAN_HOME:-$HOME/.elan}/bin"
  export PATH="$elan_bin:$PATH"
  for attempt in 1 2 3; do
    if lake_path=$(elan which lake) && lean --version && "$lake_path" --version; then
      printf '%s\n' "$elan_bin" >> "$GITHUB_PATH"
      return
    fi
    if test "$attempt" -lt 3; then
      echo "::warning::Lean toolchain acquisition failed (attempt $attempt/3); retrying."
      sleep "$((attempt * 5))"
    fi
  done
  return 1
)

download_api() {
  local destination=$1
  shift
  local attempt
  for attempt in 1 2 3; do
    if timeout --kill-after=10s 5m gh api "$@" > "$destination"; then
      return 0
    fi
    if test "$attempt" -lt 3; then
      sleep "$((attempt * 5))"
    fi
  done
  return 1
}

setup_from_release_api() (
  tag=$1
  asset="lean-${tag#v}-linux.tar.zst"
  temporary=$(mktemp -d "$RUNNER_TEMP/lean-release.XXXXXX")
  trap 'rm -rf -- "$temporary"' EXIT

  download_api "$temporary/release.json" "repos/leanprover/lean4/releases/tags/$tag"
  metadata=$(jq -er --arg tag "$tag" --arg asset "$asset" '
    select(.tag_name == $tag and .draft == false)
    | [.assets[] | select(.name == $asset and .state == "uploaded")]
    | select(length == 1) | .[0] | [.id, .size, .digest] | @tsv
  ' "$temporary/release.json")
  IFS=$'\t' read -r asset_id asset_size digest <<< "$metadata"
  [[ "$asset_id" =~ ^[1-9][0-9]*$ && "$asset_size" =~ ^[1-9][0-9]*$ && "$digest" =~ ^sha256:[0-9a-f]{64}$ ]]

  archive="$temporary/$asset"
  download_api "$archive" "repos/leanprover/lean4/releases/assets/$asset_id" \
    -H 'Accept: application/octet-stream'
  test "$(stat -c %s "$archive")" = "$asset_size"
  printf '%s  %s\n' "${digest#sha256:}" "$archive" | sha256sum --check --status

  distribution="$temporary/toolchain"
  mkdir "$distribution"
  tar --zstd -xf "$archive" -C "$distribution" --strip-components=1
  version=$("$distribution/bin/lean" --version)
  [[ "$version" == "Lean (version ${tag#v},"* ]]
  printf '%s\n' "$version"
  "$distribution/bin/lake" --version
  rm -- "$archive" "$temporary/release.json"
  printf '%s\n' "$distribution/bin" >> "$GITHUB_PATH"
  trap - EXIT
)

if setup_with_elan; then
  exit 0
fi

if [[ "${RUNNER_ENVIRONMENT:-}" == github-hosted && "${RUNNER_OS:-}" == Linux &&
      "${RUNNER_ARCH:-}" == X64 ]]; then
  toolchain=$(< lean-toolchain)
  if [[ "$toolchain" =~ ^leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9._-]+)?$ ]]; then
    echo '::warning::Elan setup failed. Trying the pinned Lean release via the GitHub Asset API.'
    setup_from_release_api "${toolchain#leanprover/lean4:}"
    exit 0
  fi
fi

echo '::error::Lean toolchain acquisition failed.'
exit 1
