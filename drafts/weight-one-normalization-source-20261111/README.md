# Weight-one normalization source checkpoint

**WIP: NOT COMPILED / NOT NATIVE ACCEPTED.** This is a source-only backup and
review snapshot, not a merge-ready mathematical contribution. No successful
Lean compilation, kernel validation, independent mathematical review, or
completion of the weight-one topic is asserted for these bytes.

Snapshot: `2026-11-11T05:09:25Z`. Base: [`db74eb2403109105cc51ceba1a4e8a8391a4543c`](https://github.com/kangxyz/colib/commit/db74eb2403109105cc51ceba1a4e8a8391a4543c).
The exact base Git tree is `2e00fa5867f447a2399e913f0e68e5f21c5f6674`.

## Contents and mathematical scope

`sources/` preserves exactly 10 proposed production modules and 6 consumer
modules, with their repository-relative paths. It contains the reconstructed
spectrum norm coordinates and units contraction normalization; occupied
single-complex, chain, target, field, and point component calculations; the
integral weight-one norm equivalence and rational graph inverse; and the
finite-coefficient weight-one equivalence with units modulo powers.

The intended field statements retain the original signed determinant norm,
positive coefficient insertion, actual derived comparison, and literal graph
representatives. The finite-coefficient candidate includes all natural levels,
including zero, one, composite levels, and levels divisible by the
characteristic. These are the intended statements of unvalidated source.
They do not assert strict A1 invariance, arbitrary-field naturality, a
roots-of-unity computation in degree zero, or a higher-weight computation.

`metadata-drafts/` preserves the proposed COL-1008 integral and COL-1007 finite
Library entries and two section-transition fragments. These are isolated
unregistered drafts. Their `author_checked` metadata concerns the author's
source comparison only; it is not native acceptance or independent review.
The section fragments are insertions, not full chapter replacements.

The active root imports, maintained Library catalog, existing main source
files, dependency locks, and workflows are unchanged. This directory is not
wired into the active Lean libraries. The sources depend on the base project;
this is not a standalone package. To validate, stage the preserved sources at
their proposed destinations in a separate checkout and retain these originals.

## Pinned sources

- Lean: `4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Stacks: `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`.
- Original Motivic implementation: `a6805c4a87cdfd7717dd7a94039246a167f15380`.

Original source attribution and license headers are retained without changes.
The exact selected `IntegralEquivalence.lean` is the corrected tagged successor
with SHA-256 `395a12db9b1548e00100a8fc416a28f77d11a33bd93faf83faee6e7c295d72c8`.
The finite endpoint has SHA-256
`170b6ce7a681af5194d8a0c31845f52e4092fe883b22e66364d7bfb8b2072a5b`.

## What remains to validate

1. Compile these exact source bytes and their actual prerequisites with the
   pinned toolchain, then repair any elaboration or proof failures.
2. Run the applicable repository checks, consumer tests, linters, native
   export, production axiom audit, and Library validation on the resulting
   contribution. No compiled products or proof-test results are included here.
3. Reconcile current main, permanent IDs COL-1007 and COL-1008, Library reading
   order and root imports before a later integration. This checkpoint itself
   must not be mistaken for that integration.
4. Review the actual maps, signs, hypotheses, universes, and literature
   correspondence independently before making any independent-review claim.

`manifest.json` records relative source paths, proposed destinations, byte
counts, Git blob identities, and SHA-256 hashes. Hash checks establish byte
identity only, not mathematical correctness. Earlier compilation results for
other source revisions do not certify this candidate.

## Exact source SHA-256 hashes

```text
9143f34b86ba7837db83583f953e7f3cffb273c9d52eca2ee798fc55295da181  sources/Colib/Algebra/Homology/Embedding/SingleComponent.lean
7807b1e86cd09ecac3ce44c0257167c5c75eb2424c676e662232c349eb454523  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/ChainNormalization.lean
75c5443e194de424c21719f4c7cb6d1cfcd6797dd28a7b4b254b1167af692e5b  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/FieldComponent.lean
872edd0351fc59563325492f20c1bd64338c78f58e04d48dd36d413cbdf69c2a  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/FieldEquivalence.lean
395a12db9b1548e00100a8fc416a28f77d11a33bd93faf83faee6e7c295d72c8  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/IntegralEquivalence.lean
b2c5b15bd1b99ad3c6553a6a6533ad02646b69584b729392793c78aff8620339  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/PointNormalization.lean
fa34751ed6fdd77f18e6489ab94922e1c75e2ee9c839806ac3c4af2085dc2c70  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/TargetNormalization.lean
33cf43114894f195c0c413100745c6d0236e2cce65a88c5306d097caf82d7de3  sources/ColibTest/WeightOneRecoveredComponents.lean
d85a5f6a41a5b24e37f51c19d21167ac9f911c18731fdcc5c7084879e9fb28d5  sources/ColibTest/WeightOneRecoveredFieldNormalization.lean
ef58b17def659b0aedc180a892c8cc6b191d824bc43f77d1139a70a5070aef51  sources/ColibTest/WeightOneRecoveredIntegralNormalization.lean
a3fa3919c306ef91ed29a7b60047420134639d3411b142c55b0696a70ad65d87  sources/Colib/AlgebraicGeometry/MotivicCohomology/WeightOne/NormCoordinates.lean
886ecfbdafce16fac802f905dcb287402a440db28a58afeaf04cdc5978b3b8d0  sources/ColibTest/ActualWeightOneNormCoordinates.lean
8122076a0f7cee82c219a867ab607e4fc4119bce8c6f328969babf586bab2b91  sources/Colib/AlgebraicGeometry/Sites/Smooth/Units/UnitNormalization.lean
8c760469fcdaa23df8333e6a109d50a78c5bdb17a09e6699b16522e60894ce9f  sources/ColibTest/ActualUnitNormalization.lean
170b6ce7a681af5194d8a0c31845f52e4092fe883b22e66364d7bfb8b2072a5b  sources/Colib/AlgebraicGeometry/MotivicCohomology/Finite/WeightOne.lean
d5fecbc680987659deb832fc9bbc87a0319a6f22108c392c71546d5f970e4a00  sources/ColibTest/WeightOneRecoveredFiniteNormalization.lean
8d44485e07ce85195282fd6467f0afbe8e397bebc1292e1b3aea576103c83900  metadata-drafts/entries/COL-1008.toml
6ded5d3189e22f25118b7e86a4d65144f0f93193cd29a1861faca90b688d49e8  metadata-drafts/entries/COL-1007.toml
4ce45d4c051c8fa6f5de5273b7d24d91fc8d55f0611c7b61bd048fea45af4e8c  metadata-drafts/section-fragments/COL-1008.toml.in
101551765a34dfb6d8537f255791762b6e468af258629f0bf37cc8eb1889513f  metadata-drafts/section-fragments/COL-1007.toml.in
```
