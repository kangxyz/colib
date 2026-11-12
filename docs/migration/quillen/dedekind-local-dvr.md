# Native local-DVR coordinates

## Checked endpoint

The implementation follows `Quillen/GTheory/Dedekind/LocalDvrSupport.lean`,
`LocalDvrComparison.lean`, and `LocalDvrBoundaryNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Its mathematical endpoints are
COL-0609 and COL-0610 in the ring K-theory chapter.

The actual finite-module localization square preserves torsion support. The
canonical fraction-ring scalar restriction is naturally isomorphic to the
original tensor extension. Naturality of the original Serre connecting map,
including its canonical small-model comparisons, then identifies the actual
local-DVR boundary with the residue-coordinate boundary in positive supported
degrees. These are equalities of the original maps, not selected abstract group
isomorphisms.

The generic image is consequently the intersection of the local-DVR coordinate
kernels in degree at least two. The finite-family G1 lifting theorem explicitly
assumes injectivity of the generic G1 map and records both the raw supported
boundary and every local-DVR coordinate. That hypothesis is not discharged here.

## Native dependencies

The proof uses the existing `FGModuleCat` localization and finite scalar
restriction functors, the abelian exact structure, the canonical `SmallModel`
comparison, and the actual Serre fiber. No replacement module category,
compatibility model, or newly assumed boundary naturality is introduced.
The homotopy-fiber and Serre naturality arguments are migrated with their full
proofs into their mathematical source owners.

## Validation and limits

The six-module proof closure compiled locally (3971 jobs). The public consumer
`ColibTest.DedekindLocalDvr` compiles (3972 jobs), retaining the original tensor
map in the finite-family theorem and the actual generic G2 image. The Python
catalog/metadata suite passed 133 tests. Full integrated declaration lint and
axiom audit remain remote release checks, not conclusions of leaf compilation.

The geometric principal-closed scheme boundary is not compared in this topic.
`PrincipalDvrBoundaryComparison.lean` also needs the original affine coherent
G-comparison, ring-isomorphism naturality, and principal-boundary comparison.
Those dependencies must be developed on the existing native coherent category;
their absence is not replaced by an adapter or an unspecified equivalence.
