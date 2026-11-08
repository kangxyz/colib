# Supported relative-open coarse fibration (COL-0331)

For any scheme X, open immersion j : U → X, and arbitrary auxiliary open T,
COL-0331 constructs the native stalk/homology support restriction, Mono/QuasiIso
joint structure and coarse Waldhausen fibration. The fiber has literal support
X minus the union of T and j.opensRange. Its canonical inclusion, fiber map,
boundary and projection form the exact sequence in every natural degree,
including the coarse relative K0 tail. No qcqs or CompactSpace T assumption
is imposed. The target is PerfectSupportedOpenCoarseK, not fine K(U).

## Source correspondence

Original Quillen revision: `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The following precise spans
record the source comparison; they do not replace independent mathematical review.

- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Restriction.lean`, lines 53–65:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportedRestriction.lean`. Actual restriction, native Mono exactness; opposite exactness is not an endpoint of this topic.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Fibration.lean`, lines 31–103:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedOpenFibration.lean`. Genuine inverse-image weak class, native cone cylinder, extension and canonical weak equivalence.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean`, lines 36–182:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedOpenSupport.lean`. Literal two-wrapper flattening and exact inverse; Mono replaces redundant quotient argument.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Support.lean`, lines 184–218:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedOpenMaps.lean`. Actual support-union inclusion and forward exact-equivalence K-map.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/LongExactSequence.lean`, lines 34–163:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedOpenLongExactSequence.lean`. Original canonical fiber map, boundary orientation, projection and all n including zero exactness.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/Restriction.lean`, lines 53–79:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportedRestriction.lean`. Native perfectness and stalk-based inverse-image support.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/RestrictionVanishing.lean`, lines 186–197:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportRestrictionVanishing.lean`. Direct native homology and sheaf stalk proof, no derived-zero adapter.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/Union.lean`, lines 30–85:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportUnion.lean`. Direct stalkwise union iff and opensRange iff.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/Cone.lean`, lines 29–43:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportedJoint.lean`. Native perfect cone and actual acyclic restriction; no shift assumption needed by native Mono cylinder.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Restriction.lean`, lines 80–90:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedOpenMaps.lean`. Original exact supported restriction K-map and its support-forgetting square.

## Boundaries and validation

This forward/coarse topic does not claim opposite-exact auxiliary statements,
prespectrum or stable/chosen-zero transport, fine supported-open TT 5.1.2,
or Bass nonconnective localization. Those Library exclusions remain in force.
The construction uses native Mathlib/Stacks objects and no Aglib adapter.
Local affected-closure compilation, source comparison, independent review,
and exact-revision remote Library/axiom/lint checks are separate gates.
