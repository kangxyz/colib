#!/usr/bin/env bash
set -euo pipefail

# These values come from the runner's GitHub context before workflow steps run.
if [[ "${GITHUB_REPOSITORY:-}" != kangxyz/colib ||
      "${GITHUB_EVENT_NAME:-}" != workflow_dispatch ||
      "${GITHUB_REF:-}" != refs/heads/main ||
      "${GITHUB_WORKFLOW_REF:-}" != kangxyz/colib/.github/workflows/dependency-warmup.yml@refs/heads/main ||
      "${GITHUB_ACTOR:-}" != kangxyz ||
      "${GITHUB_TRIGGERING_ACTOR:-}" != kangxyz ||
      "${GITHUB_JOB:-}" != compile ]]; then
  echo '::error::This runner only accepts the owner-dispatched Colib dependency warmup job.'
  exit 1
fi
