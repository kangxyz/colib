# Milnor K-theory handoff, 2026-11-10

The [Milnor handoff completion](MILNOR_MOTIVIC_MIGRATION.md#milnor-handoff-completion)
records the subsequent migrations and their mathematical scope.

## Delivery boundary

This is a handoff checkpoint, not a merge-ready or fully verified release. Further Milnor development stops at this handoff. The next maintainer should finish integration before extending the mathematics.

- Repository: `kangxyz/colib`.
- Base main: `d0125e3b4b8c605d08f3262fb6e11960e7341424`.
- Original frozen 266-source checkpoint: `6464e150ed48d43f6efe4d0d1d9bca2a71dbb66b`, branch `checkpoint/milnor-norm-finite-separable-266-20261110`.
- Handoff branch: `checkpoint/milnor-handoff-compiled-20261110`.
- Source scope: 135 production modules and 131 consumer modules. The handoff applies 31 later source changes with exact matching successful native build receipts, plus the associated COL-0396 documentation and this handoff. The 235 other source files retain the frozen checkpoint bytes.
- One current consumer draft is deliberately excluded from the code overlay: `ColibTest/MilnorNestedScalarBranchSquare.lean`. Its older frozen version stays in the branch. That older consumer is **not** claimed to pass against the revised producer.
- The local integration candidate, including that unresolved consumer, reached **110 of 111** required rebuild targets with source-matching exit-zero receipts. This is a build-target count, not a percentage of the complete mathematical project.
- No Lean or Lake process was started for this handoff. No CI was manually launched. Publication uses `[skip ci]`; a skipped or absent CI run is not a pass.

`MILNOR_HANDOFF_STATUS_20261110.json` lists the 31 source hashes, every current accepted integration target, and the remaining gates. The separate handoff bundle preserves the unvalidated source drafts outside the compiled source tree.

## Mathematical goal and implementation contract

Retain the pinned Stacks Milnor groups/ring, original tame symbols, field maps, quotient fields and recursive `milnorKNormAux` / `milnorKNormRing` / homogeneous `milnorKNorm`. Prove actual comparison, residue, base-change and tower identities for those objects. Do not substitute another norm model or assume the desired compatibility.

The broader route is:

1. Native symbols, Steinberg relations, generation and functorial field transport.
2. Restriction detection, rational-function residues and actual polynomial/tensor branches.
3. Simple-norm presentation independence, prime diamonds, towers and comparison with the original recursive chosen norm.
4. General DVR norm-residue compatibility, all branches, finite-support Dedekind pushforward and curve reciprocity.
5. Affine unramified norm and equality of the actual weighted endpoint sums in all degrees.
6. A separate later comparison with motivic cohomology, including the diagonal `K_n^M(F) ≃ H^{n,n}(F)`. This final comparison is **not proved by this checkpoint**. It needs the actual motivic cycle/transfer constructions and compatibility with these norms and residues.

Keep mathematical scopes separate: the finite-separable chosen-tower result below does not require characteristic zero; the prepared general DVR/curve endpoints retain their original characteristic-zero assumptions. General inseparable chosen-norm towers and independent-universe general towers remain open.

Pinned validation toolchain: Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; Stacks `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.

## Completed scoped results

### Native lower infrastructure

The checkpoint contains actual restriction-kernel and Sylow joint-detection arguments, mixed-symbol generation, rational coefficient transport, native factor-index equivalences, quotient/root/coefficient formulas, actual tensor-swap branches, and degree bounds. Relevant owners include `RestrictionKernel`, `RestrictionSylow`, `FiniteMixedGenerationArbitrary`, the `AdjoinRoot` factor modules, and `Residue/TensorBranchLinear`.

### Rational residues and prime norm geometry

The original and separable rational chart, completion, constant, origin, infinity/linear and finite-place norm-residue arguments are present. Full finite-place sums retain their actual branch indexing and multiplicities; separability supplies multiplicity one where needed. The prime diamond is derived from a genuine single-place rational lift and the actual infinity square, rather than postulated norm compatibility.

Key module families under `Colib/RingTheory/KTheory/MilnorK/Norm/`:

- `Rational*`, `Laurent*`, `DVR*Separable` and `SeparableScalarFactors`.
- `PrimeDiamond*`, `PrimeTower*`, `PGroupTower*`.
- `BranchFactor*`, `NestedScalarBranch*`, `NestedScalarTower*`.

### Chosen norms and finite-separable towers

`TowerSeparable`, `TowerPresentationSeparable`, `ChosenComparisonSeparable` and `ChosenTowerSeparable` give the culminating finite-separable route. For the original fields and compatible scalar actions in the same `Type u`, it proves comparison with actual simple presentations, algebra-equivalence naturality and the original chosen-norm tower identity, as additive maps and in every homogeneous degree, including degree zero.

Canonical endpoint: `Stacks.Chow.milnorKNorm_comp_milnorKNorm_of_isSeparable` in `ChosenTowerSeparable.lean`, documented by COL-0396. Separability of the total extension supplies the lower/relative hypotheses. There is no characteristic-zero, normality, prime-degree or assumed norm-square premise in this endpoint.

The frozen 266 packet was validated incrementally with original producers, actual consumers, focused checks and native source textstyle. The final eight-source stage added 16 focused public endpoints and 21 actual consumer examples. These scoped results do not establish full aggregate, full 15-linter or latest-main acceptance.

## Later integration repairs and actual validation

The later 31 published source updates have exact matching successful native build receipts. They cover:

- Explicit names for 24 local instances in five owners, eliminating the identified generated-name collisions. Old/new joint import probes passed.
- Precise lower import boundaries, four genuine non-Prop definition renames, their references and documentation.
- Explicit original quotient indices, carriers and field dictionaries at real default `checkType` failures. The maps, full sums and hypotheses were not weakened.
- The legacy characteristic-zero `NestedScalarBranchSquare` producer uses a shared-let statement and the original characteristic-zero atomic argument. Its characteristic-zero premise is genuinely used.

The unchanged full set of 15 native linters and ordinary-axiom checks passed in explicitly scoped runs for six owners/191 declarations, five further owners/82 declarations, and the complete branch-square owner/one declaration. This is **12 owners, not all 135**. Earlier failed diagnostics are not counted as passes. Full current-environment acceptance remains open.

The latest main rebase was checked to be disjoint from the audited native source closure. That source correspondence preserves scoped evidence; it is not a fresh full latest-main build.

## Immediate blocker: full expanded legacy consumer

Target: `ColibTest.MilnorNestedScalarBranchSquare`.

The production theorem `Stacks.Chow.simpleMilnorNorm_nestedScalarFactor_pGroup_square` and its full native-lint/ordinary checks passed. The complete expanded consumer repeatedly exceeded the original 85-second inner limit. Earlier measured runs spent about 42.6 seconds elaborating the expanded statement; independent inference and local simplification were fast, while the final match remained expensive. This is an unresolved validation/performance issue, not a proved mathematical contradiction.

A bounded structural diagnostic found that the goal used the `AdjoinRoot` carrier constructor while the inferred theorem used the explicit quotient carrier. Both equations had no metavariables and matching result types. The diagnostic stopped after bounded differences and did not establish complete definitional equality.

The preserved current draft adds explicit original quotient carriers/field dictionaries to three map applications and fixes parentheses around singleton ideals. Current draft SHA-256: `15bf4fb074bee8970b533459e2027634f4ee7bda013db1d5a2aa0ab4dd88587e`. A separate untested patch removes `dsimp only [AdjoinRoot] at hbranch ⊢`, producing candidate hash `57c269800d395b62e904de61f572fd6eed7a22b85b7a02abe68b80cd846c6b18`. Neither is accepted. Preserve the complete expanded formula and all hypotheses; do not replace the consumer with a weaker alias test.

Recommended integration order:

1. Resolve and actually compile this complete consumer without changing the theorem's scope.
2. Rebind exact source/dependency/artifact hashes and invalidate any changed reverse dependencies.
3. Run all original 15 native linters plus ordinary-axiom closure on all 135 production owners, including generated declarations. The prepared grouping has 14 complete-owner groups; no checks may be suppressed.
4. Run exact 266-source native textstyle, official generated-root generation/check, all relevant original consumers and complete aggregate checks.
5. Validate COL-0396's real compiled tag/reference export and catalog. Prepared metadata is not export acceptance. The export should verify eleven bindings, fifteen citations and the canonical primary theorem.
6. Review and run the required repository CI before merging. Do not infer a pass from this checkpoint's skipped CI.

Use `AGENTS.md`, `CONTRIBUTING.md`, `docs/LIBRARY.md` and applicable stages of `scripts/check.sh`. Respect the existing resource limits and shared compilation ownership. Do not increase limits, change dependency pins, rerun old checkpoints unnecessarily, weaken tests or add kernel replay as a substitute for the required checks.

## Remaining mathematical work and preserved drafts

### General DVR, Dedekind and curve endpoints: 76 source-only files

The preserved packet contains 51 production and 25 consumer files. It has source/dependency ordering, not native validation. These are cumulative files; the intermediate packets of 26, 39, 51 and 65 files must not be added together or counted as independent accomplishments.

Validate in dependency order:

1. Completion and ramified-branch residue/norm machinery.
2. General complete-DVR endpoint `Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_complete`, with complete DVR, residue characteristic zero, finite fraction extension and actual integral closure.
3. Original-branch DVR sum `Stacks.Chow.dvrMilnorTameSymbol'_milnorKNorm_eq_sum_originalBranches`, for the actual finite torsion-free Dedekind model and **all** branches.
4. Dedekind finite-support direct-sum square `Stacks.Chow.DedekindResidue.totalResidue_milnorKNorm`.
5. `Stacks.Chow.DedekindResidue.normalized_curve_reciprocity`, including actual finite and infinity branches.
6. `Stacks.Chow.DedekindResidue.norm_mem_constant_range_of_totalResidue_zero`.
7. `Stacks.Chow.DedekindResidue.endpointWeightedResidueSum_eq_all`, for the original weighted endpoint sums in every degree, including zero.

Reference source: Aglib commit `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, especially `Norm/FiniteExtension/{Complete,DVR}.lean` and `Dedekind/{ResidueDirectSum,NormalizedCurveReciprocity,AffineUnramifiedNorm,AffineEndpointNormAllDegrees}.lean`. Adapt statements to the native Stacks objects; do not import Aglib's alternate norm model.

A localization at a single upper prime of a semilocal normalization is not automatically finite over the original DVR. Do not replace the complete branch sum with that invalid shortcut.

### Purely inseparable work: eight source-only files

Four producer/consumer pairs are preserved: `SimpleInseparableTrace`, `ChosenInseparableTrace`, `PrimeInseparablePresentation`, and `PrimeInseparableChosenComparison`. They have no native acceptance. Native prime trace already exists in main; reuse it rather than introduce another trace model.

Even after these pairs compile, arbitrary purely inseparable/composite towers still need an actual proof relating simple presentations to the chosen recursive norm, mixed separable/inseparable decompositions, scalar transport, and transitivity. `IsMilnorNorm.comp` expresses listed properties, not uniqueness. Polynomial presentation independence alone does not identify arbitrary chosen recursive towers.

### Motivic interface

Do not count this checkpoint as constructing the full motivic comparison, proving `K_n^M ≃ H^{n,n}`, or finishing norm-residue compatibility for a motivic realization. The next Milnor maintainer should expose stable native APIs and communicate their exact hypotheses to the motivic work. The unresolved endpoint and inseparable work remain explicit dependencies rather than implicit assumptions.
