# Compilation caches

The [current Lean CI](../.github/LEAN_CI.md) uses Aglib's optimized checkpoint and
native staging flow, adapted to Colib's fixed compiler/dependencies and an
independent Stacks layer.

## Storage boundaries

| Object | Stored content |
|---|---|
| Root checkpoint | `.lake/build` and `.lake/config` for Colib |
| Dependency checkpoint | Working build/configuration outputs of resolved dependencies except Stacks and official Mathlib |
| Stacks checkpoint | Working build/configuration outputs of the pinned Stacks package only |
| Tools checkpoint | Lint/auditor builds, non-Stacks dependency changes and small Mathlib checker-tool outputs |
| Native publication archive | The verified production stage, with producer repository/revision identity |

Mathlib production artifacts come directly from its existing official cache in
both hosted jobs. They are not repacked or scanned for the dependency/tools
checkpoints. Native verification still checks Colib against the actual acquired
inputs. Each build/check/audit remains a separate workflow step.

Each layer has its own immutable Actions cache key and content generation. Keys
bind toolchain, platform, resolved manifest and configuration; tool keys also bind
tool source/pins. Checkpoint archives do not contain dependency sources or Git
metadata. A mixed `LAKE_CACHE_DIR` content store is never saved as a working
checkpoint. Native archive validity is checked by Lake against the actual inputs.

The Stacks checkpoint is excluded from both dependencies and tools. Build saves
it separately, including useful partial compilation. Cross-runner Test receives
this run's `build-stacks` independently of `build-dependencies`, then saves any
additional Stacks outputs in the same independent layer. The Stacks
acquisition boundary can later fetch an upstream Stacks cache before native
compilation without changing Colib's root/tool/dependency caches.

## Reuse and transfer

Build compares the warm Stacks manifest with the published baseline's generation
or a bounded preview of its manifest. A warm checkpoint that covers the baseline
is restored once. For a partial checkpoint, Build restores the baseline and then
overlays the warm archive to keep newer completed outputs. The restore helper
tries R2 when configured and uses the GitHub Release if R2 is unavailable or
invalid. Both sources bind the Stacks revision and checkpoint context.

The standard Actions cache directory is `.lake/ci-checkpoints/`, relative to
the repository checkout. Its four archives are `root.tar.zst`,
`dependencies.tar.zst`, `stacks.tar.zst` and `tools.tar.zst`. The workflow
passes these same relative paths to `actions/cache` on GitHub-hosted and
self-hosted Linux runners so their path-based cache versions agree.

On a portable cache miss, the restore action can read the earlier
`runner.temp/layered-cache` versions. Both supported layouts stored the old
files under `../../_temp/layered-cache` relative to the checkout. The action
checks this layout before looking up either old version, then moves a restored
archive into the standard directory. Native checkpoint validation still runs
before application, and the normal save steps publish the portable version.

Production sources do not invalidate compatible checkpoint prefixes. Lake's
native `--rehash` decides applicability. Root and tools restores prefer a
compatible ref. Dependency and Stacks generations use their content identity.
The packer checks integrity and coverage, preserves regular generated files,
and reuses an already validated compressed archive when its content is unchanged.

GitHub-hosted Test must consume the current Build's complete dependency, Stacks
and root archive overlays, even if optional checkpoint caches hit. EC2 handoff
retains the working trees/native store and verifies its runner/repository/run
identity. Both paths verify production outputs before preparing checker tools.
Checkpoint integrity is a transport check, not a new mathematical proof audit.

The earlier `colib-v2` environment cache contains explicitly selected root and
non-Stacks package paths. The earlier `stacks-<context>` cache contains only the
Stacks package. These independent caches can seed the first layered run; the
optimized workflow does not normally save those source-tree caches.

### Reuse after merging a branch

A default-branch push can warm Build from a successful earlier push run of the
same repository's Colib CI. A fast-forward can use a run at the same commit.
A two-parent merge can use a run at its second parent even when the target
branch contributes other changes. When GitHub pull request metadata supplies
a different source revision, its Git tree must match the target checkout.
The workflow verifies the run, immutable artifact digests and native producer
metadata before importing the branch stage. The dependency and Stacks
checkpoints are optional overlays.

On EC2, a successful branch push uploads the verified native stage after Test
from the preserved workspace. It also uploads the existing dependency or Stacks
archive if the latest matching default-branch cache has a different generation
or cannot be checked. These artifacts supply later merge builds. The same-run
handoff continues to use the local workspace.

Build keeps the regular target-branch checkpoints and uses Lake's artifact
store for the imported native outputs. A successful native import adds
`--rehash` to that Build invocation. If a matching branch run or usable artifact
is unavailable, the usual incremental build can proceed.

When the root checkpoint and a checked branch seed are absent, Build can
reuse a published Colib stage from a successful default-branch push.
The archive must match the runner's toolchain domain, the published digest,
and the producer repository, revision and compiler. The native stage
validator checks the module archives before import. Lake then rehashes
the current inputs and restores only matching outputs.

## Publication and manual exports

After all checks pass, main pushes publish the normal `lean-native-<Colib revision>`
production archive and a separate `stacks-checkpoint-<Stacks revision>-<context>`
release. Checkpoints under GitHub's 2 GiB per-asset limit use one `.tar.zst`
asset. Larger checkpoints use numbered volumes and a `.parts.json` index.
The publisher verifies each uploaded volume before exposing the index.
The CI reader checks the size and SHA-256 of every volume and the reassembled
archive. To restore a local single or reassembled `.tar.zst` archive, run:

```bash
python3 .github/ci-cache/checkpoint.py restore --root . --layer stacks \
  --input /path/to/stacks-checkpoint.tar.zst
```

Materialize the pinned dependency sources first. A later native build/verification
checks applicability; a matching archive alone is not a successful compilation.

### Cloudflare R2 for Stacks and Colib

Create a private Standard bucket named `colib-stacks-cache` and two S3 credentials
scoped to it, one with **Object Read only** and one with **Object Read & Write**.
Use the S3 API's Access Key ID and Secret Access Key. [Cloudflare R2 authentication](https://developers.cloudflare.com/r2/api/tokens/)

| GitHub Actions setting | Value |
|---|---|
| Repository variable `STACKS_R2_BUCKET` | `colib-stacks-cache` |
| Repository variable `STACKS_R2_ENDPOINT` | The bucket's S3 API endpoint, such as `https://<account-id>.r2.cloudflarestorage.com` |
| Repository secrets `STACKS_R2_READ_ACCESS_KEY_ID`, `STACKS_R2_READ_SECRET_ACCESS_KEY` | The read-only credential pair |
| Environment secrets `STACKS_R2_WRITE_ACCESS_KEY_ID`, `STACKS_R2_WRITE_SECRET_ACCESS_KEY` | The read/write credential pair in `stacks-cache-publish` |

In the `stacks-cache-publish` environment, set **Deployment branches and tags** to
**Selected branches and tags** and add a branch rule for `main`. Add the repository
variables after setting up the secrets to enable R2.

The next successful main push can populate the bucket from its staged Stacks
checkpoint. To seed it beforehand, use a Linux x64 checkout with the archive's
matching pins, download the desired GitHub Release asset, and load the write
credentials into `STACKS_R2_ACCESS_KEY_ID` and `STACKS_R2_SECRET_ACCESS_KEY`.
Set the same endpoint and bucket variables and run:

```bash
python3 -u .github/ci-cache/restore_stacks.py --publish-r2 /path/to/stacks-checkpoint.tar.zst
```

Colib's verified native Release archives also have a private R2 backup under
`colib/v1/`. The index keeps the two most recently published distinct sets of
native outputs from default-branch CI. A repeated output set reuses its backup
even if the CI revision and tar metadata have changed. Publication uploads the
archive, advances the index, then removes the evicted archive. A later
publication also cleans up unindexed archives left by an interrupted upload.

When a verified working checkpoint or merge seed is unavailable, Build tries the
compatible Colib R2 archives in order, followed by the GitHub Release baseline.
The restore checks the producer run and archive digest before the existing
native-stage validation and Lake input rehash.

A repository maintainer can preseed a verified external build by uploading its
native archive to `colib/v1/objects/<domain>/<sha256>.tar` and setting the
`COLIB_R2_PRESEED` repository variable. The JSON value records the archive
`domain`, `sha256`, and `size` in bytes, the producer `revision`, and the
exact `consumer` commit on the default branch. Build uses it on that commit's
push after the usual archive and Lake checks. Remove the variable after that
run. The verified CI archive enters the normal two-generation index.

Failed and timed-out builds save the completed Colib outputs to the branch's
Actions checkpoint after the compiler stops. The next run can resume with those
outputs when Lake's input hashes match. A job cancelled before its checkpoint
save finishes resumes from the last saved checkpoint. R2 retains verified
default-branch archives from builds that passed Test, lint, and the axiom audit.

Each `stacks/v2/<Stacks revision>/<context>/current.json` points to an immutable
archive named by its checkpoint generation and records its SHA-256. Publication
verifies the archive and advances the pointer when the new checkpoint covers
the previous baseline. Conditional writes let concurrent publishers share one
object per generation. After both publication steps succeed, CI prunes older
R2 checkpoints for the active dependency context. It retains the current archive
and the previous generation recorded in the pointer.

GitHub Release checkpoints use the generation to identify the single asset or
the volume index. CI keeps the latest two complete generations per release
after publication. Both formats remain readable. A retry can reuse the volume
bytes that are already present, or match a legacy checkpoint by its manifest.

`scripts/stacks_cache.py pack/restore` retains the initial standalone `.tar.gz`
format for existing consumers and earlier `stacks-native` releases. It verifies
exact Stacks source revision, dependency/compiler context and artifact digests.
Those archives are separate from the new checkpoint format. The script's `layout`
command also owns the independent migration-seed paths and identity.
