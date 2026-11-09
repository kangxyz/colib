#!/usr/bin/env bash
set -euo pipefail

if [[ "${RUNNER_NAME:-}" == "colib-ci-run-${GITHUB_RUN_ID:-}-${GITHUB_RUN_ATTEMPT:-}-i-"* &&
      "${GITHUB_REPOSITORY:-}" == kangxyz/colib &&
      "${GITHUB_REF_TYPE:-}" == branch &&
      "${GITHUB_REF:-}" == refs/heads/* &&
      "${GITHUB_ACTOR:-}" == kangxyz &&
      "${GITHUB_TRIGGERING_ACTOR:-}" == kangxyz &&
      "${GITHUB_WORKFLOW_REF:-}" == "kangxyz/colib/.github/workflows/ci.yml@${GITHUB_REF}" &&
      ( "${GITHUB_EVENT_NAME:-}" == push || "${GITHUB_EVENT_NAME:-}" == workflow_dispatch ) &&
      ( "${GITHUB_JOB:-}" == build || "${GITHUB_JOB:-}" == test_lint ) ]]; then
  exit 0
fi

echo '::error::This job does not belong to the Colib CI attempt that owns this runner.'
exit 1
