#!/usr/bin/env bash
set -euo pipefail

# The runner supplies these values before any workflow step executes.
if [[ "${GITHUB_REPOSITORY:-}" == kangxyz/colib &&
      "${GITHUB_REF_TYPE:-}" == branch &&
      "${GITHUB_REF:-}" == refs/heads/* &&
      "${GITHUB_ACTOR:-}" == kangxyz &&
      "${GITHUB_TRIGGERING_ACTOR:-}" == kangxyz ]]; then
  ref="${GITHUB_REF}"
  case "${GITHUB_EVENT_NAME:-}:${GITHUB_WORKFLOW_REF:-}:${GITHUB_JOB:-}" in
    "push:kangxyz/colib/.github/workflows/ci.yml@$ref:build" | \
    "push:kangxyz/colib/.github/workflows/ci.yml@$ref:test_lint" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ci.yml@$ref:build" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ci.yml@$ref:test_lint" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ci-split.yml@$ref:dependencies" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ci-split.yml@$ref:build" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ci-split.yml@$ref:test_lint" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/dependency-warmup.yml@$ref:compile" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ec2-pilot.yml@refs/heads/main:probe" | \
    "workflow_dispatch:kangxyz/colib/.github/workflows/ec2-pilot.yml@refs/heads/main:handoff")
      exit 0
      ;;
  esac
fi

echo '::error::This runner only accepts authorized Colib branch CI and warmup jobs.'
exit 1
