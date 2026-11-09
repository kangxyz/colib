# Bounded-above flat perfect prespectrum comparison (COL-0351)

This comparison is a prerequisite for coefficient section models, not a supplied
spectrum equivalence and not the coefficient row itself.

## Native construction

`BoundedFlatPerfectPrespectrumComparison` realizes the actual exact inclusion
using `exactOriginalPrespectrumMap`. Its existing canonical zero rebase is
retained. `boundedAboveFlatPerfectToPerfectKMap_bijective` and
`exactOriginalPrespectrumMap_isStableEquivalence_iff` prove stability in all
integer degrees on compact ringed spaces. The forward stable map and the
zero-space map retain the original inclusion K-map for every natural degree,
including zero. The same map specializes to Spec of every commutative ring.
Compactness is not assumed for the maps or their forward-map equations.

`BoundedFlatPerfectPrespectrumPullback` uses actual termwise scheme pullback.
The flat-model map is exact for arbitrary scheme morphisms. The comparison with
perfect pullback requires a flat morphism. The existing native `boundedAboveFlatPerfectInclusionFlatPullbackIso` is
identity on the underlying pulled-back complex. The whole spectrum square is
the reverse canonical composition track, followed by the normalized isomorphism
track, followed by the other canonical composition track. It fixes the chosen
zero throughout. Level n, homotopy time s and structure time t are independent,
including n = 0. No compactness is required for this square.

## Source correspondence

Original source: Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean`:
  actual inclusion K-comparison, already native as COL-0325.
- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean`:
  literal forward map, already native as COL-0323.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Pullback.lean`
  and `PullbackIsomorphisms.lean`: actual bounded-above flat geometric pullback,
  already native as COL-0326. No legacy category or adapter is imported.
- `Quillen/Waldhausen/SConstruction/Iterated/ExactMaps.lean`, `ExactCoherence.lean`,
  `PrespectrumHomotopy.lean` and `StableFunctoriality.lean`: existing native
  canonical normalization, complete tracks and actual-map stability criterion.

The comparison uses native Mathlib/Stacks ringed-space complexes and perfectness,
not an identification of legacy predicates. The existing COL-0328 flat K-map square is also reused directly. The full public consumer checks the
actual normalized map, forward equivalence and induced maps in every degree and
separately at K0, the affine instance, actual isomorphism components, both whole
square endpoints, chosen zero and independent structure parameters.

## Boundaries

Stable equivalence alone is not levelwise homotopy equivalence. The negative
connectivity of these original connective models proves no Bass localization.
This item does not construct strict coefficient sections, a coefficient row,
arbitrary perfect derived-pullback prespectrum functor laws, a Bass seed,
nonconnective identification, or Thomason–Trobaugh 7.4. Independent mathematical
review and exact local compilation remain distinct evidence.
