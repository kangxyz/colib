# Arbitrary native pullback of bounded vector-bundle complexes

## Mathematical boundary

COL-0322 is a complete arbitrary-morphism pullback prerequisite for the later perfect
localization naturality topic. It does not complete `GlobalLocalizationNaturality`.
The actual source property is
`Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex`:
global upper and lower bounds on terms and finite local freeness in every degree.
It is not `StrictlyPerfect.IsStrictlyPerfect`, whose global finite-free-retract terms
are narrower on a general scheme.

Every scheme morphism is allowed. No flatness, affineness, cartesianness,
Noetherianity, regularity, quasi-compactness or resolution-property assumption is added.
The cofibrations are still the inherited admissible monomorphisms whose quotients
remain bounded finite locally free. They are not all ambient monomorphisms.
Weak equivalences are the actual quasi-isomorphisms of the original chain maps.

## Actual maps and proofs

1. Native `Scheme.Modules.pullback` lifts to `Scheme.Vect`. Local splitting of a
   short exact sequence with finite locally free quotient proves exactness under
   arbitrary pullback, without asserting exactness of the ambient module functor.
2. Termwise native pullback retains global term bounds and finite local freeness.
   The cycles of an acyclic bounded vector-bundle complex are finite locally free.
   Pullback keeps each actual cycle sequence short exact. This proves acyclicity,
   then the actual signed mapping-cone criterion proves preservation of quasi-isomorphisms.
3. The inherited exact and Waldhausen structures give the actual canonical,
   chosen-zero-normalized K-map. Native identity and composition isomorphisms prove
   its strict contravariant functoriality in every nonnegative degree.
4. Open restriction remains native `restrictFunctor` degree by degree. A constructed
   natural isomorphism compares it to pullback. Their canonical K-maps agree.
   Any commutative open-pair square therefore commutes on those actual K-maps;
   no cartesian square or pre-existing naturality equation is an input.
5. The original degree-zero vector-bundle inclusion commutes by the actual native
   single-complex/pullback isomorphism. Its canonical Waldhausen KMap square is proved.
   This does not assume or prove a Q/S or Gillet--Waldhausen comparison.
6. The separate existing scheme vector-bundle Quillen K-groups acquire the actual
   small-model pullback, identity/composition laws, the original restriction comparison,
   a contravariant functor and the inverse maps of a scheme isomorphism.

## Original-to-native source crosswalk

The original source pin is Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Implementation provenance is retained
independently of literature correspondence. Native modules keep their own object models.

- `Quillen.PerfectComplexes.strictPerfect_pullback` becomes
  `Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex_pullback`.
- `acyclic_pullback_of_strictPerfect` and `quasiIso_pullback_of_strictPerfect` become
  `acyclic_pullback_of_boundedFiniteLocallyFree` and
  `quasiIso_pullback_of_boundedFiniteLocallyFree` in that same native namespace.
- `strictPullback`, `strictExactPullback` and `strictPullback_waldhausenExact` become
  `boundedFiniteLocallyFreePullback`, `boundedFiniteLocallyFreeExactPullback` and
  `boundedFiniteLocallyFreePullback_isExact`.
- `strictPullbackIdIso`, `strictPullbackCompIso` and `strictRestrictIsoPullback` become
  the corresponding `boundedFiniteLocallyFree` comparisons. The restriction functor
  is the actual termwise native restriction, not a synonym for pullback.
- `Quillen.PerfectComplexes.vectorBundleInclusionPullbackIso` becomes
  `Stacks.Perfect.BoundedLocallyFreeComplexes.vectorBundleComplexInclusionPullbackIso`.
- `Quillen.PerfectComplexes.strictKPullback` becomes
  `AlgebraicGeometry.Scheme.boundedFiniteLocallyFreeKPullback`; its identity,
  composition and restriction equations retain the same actual geometric maps.
  `boundedFiniteLocallyFreeKRestrict_pullback` allows every commutative open-pair
  square, extending the original inverse-image-open specialization.
- The canonical degree-zero inclusion square is
  `AlgebraicGeometry.Scheme.vectorBundleToBoundedFiniteLocallyFreeKMap_pullback`.
- Original `AlgebraicGeometry.Scheme.pullbackK`, `KFunctor` and their laws keep
  these native namespace names, with the existing native `Scheme.K` and
  `Scheme.Modules.vectorBundleExactStructure` as their source model.

## Why the final localization naturality remains separate

The original `GlobalLocalizationNaturality.lean` imports the actual relative
boundary square from `ConnectingNaturality`, the actual endpoint square from
`PairRestriction`, and the support/change-weak squares from `PairPullback`.
Those maps are not arbitrary parameters: they are transported from geometric
bounded-flat pullback through the proved literal inclusion K-equivalences.
`DerivedPullbackFunctor` and `DerivedPullback` depend on `BoundedFlat.KComparison`.
The bounded-flat model, its exact pullback, its comparison with all perfect
complexes and its supported/relative comparisons have not yet been migrated.

Pinned Stacks already has genuine K-flat derived pullback and preservation of
perfectness. That fact alone does not construct these exact-chain/Waldhausen
KMaps or their literal inclusion comparisons. Underived pullback on all locally
perfect complexes would be invalid. COL-0322 therefore proves the actual
arbitrary-morphism bounded-vector-bundle prerequisite rather than inserting the
three required naturality squares as assumptions or reducing to open immersions.

The positive fine endpoint and supported degree-zero boundary naturality remain
pending with those genuine derived-model comparisons. The precise geometric
`HasDerivedRoofs` and `HasPerfectComplements` hypotheses in COL-0318 are distinct
from this missing pullback layer. No qcqs geometric discharge, prescribed
image-cover spectrum identification or Bass nonconnective localization is claimed.

## Validation and integration ownership

The local component records actual native Lean header parses, source snapshots,
all direct import five-family fingerprints, exact compiler commands and outputs,
and full-signature in-package consumers. Compilation, source correspondence,
independent mathematical review and remote lint/axiom/Library checks are separate facts.
This component owns only its new sources, COL-0322 entry and this reader crosswalk.
Shared root, chapter and migration edits are proposals for parent integration.
