# Supported-Cover Excision (COL-0332)

For an open immersion j : U → X and an auxiliary open T with image(j) ∪ T = X,
COL-0332 constructs genuine scheme module-sheaf extension by zero left adjoint
to literal restriction, its actual unit and counit and both triangle identities.
Off-image stalks vanish. Stalkwise arguments establish preservation of Mono,
homology and QuasiIso. Two-open descent proves supported perfectness.
The resulting literal restriction admits an actual S-realization homotopy inverse
and is a K-equivalence in every natural degree, including K0. Its normalized
connective prespectrum map is stable in every integer degree.
There is no qcqs, compactness, separation or supplied-equivalence premise.
Negative stable degrees are connective vanishing, not Bass nonconnective K-theory.

## Exact Original Source Crosswalk

Original Quillen revision: `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Source comparison and independent review are separate evidence.

- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/Excision.lean`, lines 1–151 (complete original module), SHA256 `79e2f6361498b7b2475a7a5cb01abe557557cf0298d3b8861d28eb018ea549d2`:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedExcision.lean`. Actual restriction to inverse-image support; extension inverse; weak genuine unit/counit; actual S-realization homotopy inverse and all natural K degrees including zero. Native inherited Waldhausen Mono replaces Aglib exact-category inflation.
- `Quillen/AlgebraicGeometry/PerfectComplexes/SupportedOpen/ExcisionSpectrum.lean`, lines 1–60 (complete original module), SHA256 `a3bd44709449fb2add3d80ebc3fcc089a6ddba951cf24ef33f348796c533e39b`:
  `Colib/AlgebraicGeometry/KTheory/PerfectSupportedExcisionSpectrum.lean`. Normalized exactOriginalPrespectrumMap; stable in every integer degree; unchanged originalKStableEquiv comparison in all natural degrees. 
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/ExtensionByZero.lean`, lines 1–124 (complete original module), SHA256 `65fc91dd171e816ea71e988d83f268b1e2f9ad905d859bf8daff3e8554aa97fc`:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportedExtensionByZero.lean`. Auxiliary-open support preservation, perfectness under the original two-open cover and actual counit quasi-isomorphism. Native stalk/homology proof replaces base-change detour, without extra hypotheses or chosen equivalences.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/ExcisionAdjunction.lean`, lines 1–98 (complete original module), SHA256 `33daedfa7e21ad2ce4b8ad6ca00019f7b209d0052c09e84f8c198c240a80d5dd`:
  `Colib/AlgebraicGeometry/Modules/PerfectSupportedExcisionAdjunction.lean`. Underlying functors, degreewise unit/counit and both triangle identities. Native Mono/QuasiIso exactness instead of Aglib ExactFunctor.
- `Quillen/Aglib/AlgebraicGeometry/Modules/Complex/ExtensionByZero.lean`, lines 1–139 (complete original module), SHA256 `baee10d1ba29a06aff517b761345cdd78847f1a4dcbb55255f77c51f18875c49`:
  `Colib/AlgebraicGeometry/Modules/ExtensionByZeroComplex.lean`. Actual chain-level adjunction with module unit/counit, exactness, QuasiIso preservation and restricted counit iso. Genuine native module-sheaf extension constructed directly from Mathlib pullback along image-open functor, not an Aglib object.

## Scope and Validation

This cover excision topic does not enlarge COL-0331's forward/coarse fibration
into fine TT localization. COL-0331 retains its coarse target and exclusions.
Opposite exactness, full fine TT localization, Bass/nonconnective comparison and
a general open-square extension base-change API remain unclaimed.
Native Mathlib and Stacks objects are used directly, without an Aglib or Quillen
adapter. Stacks Tags 00AB and 08CM supply extension-by-zero background and local
perfectness respectively. Exact compiled references remain in the native metadata.
Local changed-closure compilation, independent source/proof review and later
exact-revision full private Library, axiom and style gates are distinct checks.
