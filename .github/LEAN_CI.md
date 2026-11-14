# Lean CI

Colib adapts the complete current main CI from
[kangxyz/aglib at 1943d6eee4976a2d3a01b55e76d6d5890130ee63](https://github.com/kangxyz/aglib/tree/1943d6eee4976a2d3a01b55e76d6d5890130ee63/.github),
including the resource scopes, layered checkpoints, native staging validation,
parallel declaration linter, and runner-local Build-to-Test handoff. This replaces
Colib's original portable workflow. The code and operating limits are shared by
both runner profiles; the mathematical dependency pins are unchanged.

## Profiles and routing

| Setting | GitHub-hosted | EC2 |
|---|---|---|
| Labels | `ubuntu-24.04` | `colib-ci-run-<run>-<attempt>` |
| Native scope memory request | 13,824 MiB | 57,344 MiB |
| Lake threads / declaration lint workers | 4 / 4 | 8 / 8 |
| Build job / compiler cap | 360 minutes / remaining safe window | 240 / 180 minutes |
| Test job limit | 360 minutes | 90 minutes |
| Build-to-Test transfer | Same-run dependency and root archives | Same checkout and native store |

The native scope clamps its request to physical RAM minus a 2,048 MiB runner
reserve and disables swap. Compiler and staging scopes stop before checkpoints
are read. A job deadline reserves time for staging and saving completed work after
compiler failure. Resource samples are retained as workflow artifacts.

With `COLIB_SELF_HOSTED_ENABLED=true` and `COLIB_PARALLEL_RUNNER_ENABLED=true`,
owner pushes and manual runs on Colib branches default to EC2. Pull requests and
the explicit `hosted` profile use GitHub-hosted runners. Setting either variable
to `false` routes new runs to GitHub-hosted runners with their usual resource limits.

CI queues separately for each ref. The EC2 controller admits up to three attempts
across branches. Build and Test use the same per-attempt runner label and share the
checkout and native store. The controller releases the instance when the attempt ends.

The [EC2 operating guide](../infra/ci/ec2/README.md) documents the controller and
deployment. The root-owned marker is `colib-ci-runner-v1` in
`/etc/colib-ci-runner-mode`. Build and Test restart `colib-ci-expiry.timer`.

## Checkpoints and transport

The workflow retains independent compilation, staging, verification, Test, text-style,
declaration-lint, axiom-audit and Library steps. Build uses normal Lake progress and
completion logs. The performance repair changes cache scope, not check boundaries.

The adapted schema has four independently stored generated-output layers:

| Layer | Contents |
|---|---|
| Root | Colib build/configuration outputs, including in-package tests |
| Dependencies | Generated outputs for resolved dependencies other than Stacks and official Mathlib |
| Stacks | Only `.lake/packages/Stacks/.lake/build` and `.lake/config` |
| Tools | Private lint/auditor builds, non-Stacks dependency changes and small Mathlib checker-tool outputs |

The context binds compiler, platform, resolved pins and package configuration.
Tools also bind the lint adapter and auditor pin. Archives carry file integrity
and coverage manifests; immutable cache generations are derived from content.
Source checkouts, Git data and the mixed native artifact store are not checkpointed.
The packer reuses a validated compressed archive when content has not changed.
An earlier compatible `colib-v2` cache and the earlier separate Stacks cache can
seed the first run of this schema. They are not the normal save path.

Build and cross-runner Test acquire the pinned official Mathlib cache directly.
Mathlib production outputs are excluded from dependency packing and tools-layer
scanning. The dependency/tools context binds this scope policy. The performance
case in `docs/performance/ci-mathlib-checkpoint.md` records the measured regression.

Build overlays optional checkpoints and uses native `lake build --rehash` for
production roots. Available completed work is checkpointed after a compiler
failure. On GitHub-hosted runners, Test must overlay this Build's complete non-Mathlib
`build-dependencies`, separate `build-stacks`, and native `cache-staging`, even
when optional caches hit. Native `--no-build --rehash` verifies the current inputs
before checks. Stacks is excluded from the dependency and tools layers, including
test-only dependency compilation.

On EC2, Build seals runner, repository, revision, run and attempt identity in the
preserved checkout. Test checks that identity, `HEAD` and archive digest. It uses
the same native store and dependency trees. The upstream `verify-root.sh` native
archive check remains in place. The compressed Stacks checkpoint also survives
per-job temporary-directory cleanup. Restore and Build record the file hashes
of Colib and Stacks outputs in the same checkout. Build and Test reuse those
hashes while the file identity still matches. New and modified files are hashed
and a changed generation is packed and saved.

Successful main pushes publish Colib's native archive and the independently named
`stacks-checkpoint-<Stacks revision>-<context>` release. When configured, Publish
cache also backs up the verified Colib native archive and Stacks checkpoint to
R2. CI checks the R2 pointer and GitHub Release metadata before transferring the
Stacks archive and only stages it when a destination needs publication. R2 keeps
up to two distinct Colib archives and up to two Stacks generations
per dependency context. Build can restore either baseline from R2 with GitHub
Release fallback.
See [R2 setup and cache operations](../docs/CACHING.md#cloudflare-r2-for-stacks-and-colib).

## Native checks and Library

Test prepares the native Mathlib/Batteries tools and runs generated-entry checks,
all Colib/ColibTest text-style inputs, in-package tests, full declaration lint,
and the pinned production axiom auditor. The declaration adapter batches the same
selected upstream checks over declarations defined in Colib modules. It retains
native fallback for unknown linter implementations; successful lint results are
never cached. Local `scripts/check.sh` uses the same adapter.

Both builtin lint replay and the declaration driver select by defining module,
not declaration namespace. Stacks is outside the report scope. Lake's cached
build warning logs are suppressed with `--log-level=error`; native lint reports
remain visible and Colib retains `warningAsError=true`.

The structured Library export and website are additional Colib checks. The final
Verification table requires every outcome, including that export, to succeed.
Pages consumes the resulting `colib-site` artifact from a trusted main push.

## Pin-specific adaptations

Linux x64 jobs try the standard Elan setup first. If it fails,
they obtain the official Lean distribution named in `lean-toolchain` through
the Release Asset API. The fallback checks the asset size, SHA-256 digest and
Lean version before putting the distribution on PATH.

The checkpoint and staging helpers admit the pinned Lean 4.35.0 toolchain and
verify the exact Mathlib and ProofWidgets configuration bytes. The lint adapter
binds Batteries `66e4691` and the known Mathlib linter implementations for that
compiler. It runs the full set of Colib declarations.
Unknown layouts fail before compilation instead of silently choosing the old
combined-cache path. Aglib's historical, repository-specific `first-ci-cache`
promotion seed is rejected; its recorded producer and cache do not belong to Colib.

Cache integrity tests live in `ci-cache/test_*.py`. Actionlint 1.7.12 needs a
narrow ignore because it does not recognize GitHub's `concurrency.queue` field.

```bash
actionlint -shellcheck= -ignore 'unexpected key "queue" for "concurrency" section'
python3 -m unittest discover -s .github/ci-cache -p 'test_*.py'
```

Publication checks the live default-branch revision before creating a release.
If the branch advanced, the optional release is reported as skipped while the
exact producer artifacts and native check results remain available. Artifacts
are never retargeted to a newer commit. A 403 race is classified as stale only
after rechecking the branch; unrelated publication failures remain failures.
