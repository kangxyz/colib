# Native Bounded Above Flat Perfect Complexes

## Mathematical Boundary

COL-0323 constructs the genuine bounded-flat model needed before the original
`BoundedFlat.KComparison`. Its objects are actual native sheaf complexes satisfying
`RingedSpace.IsPerfectComplex`, with some integer `b` such that `IsStrictlyLE b`,
and flat sheaves in every degree. Native Stacks Tag 05NE identifies this last
condition with flatness of every stalk. No lower term bound is imposed.

This is not the bounded finite locally free subcategory from COL-0313 and COL-0322.
It is not the narrower global finite-free-retract strictly perfect model. The terms
need not be finite, locally free or quasicoherent. The proofs work on arbitrary
ringed spaces with the native synchronized sheaf universes and hence on every scheme.
No affine, flat, regular, Noetherian, quasi-separated or resolution-property hypothesis
is inserted.

## Actual Structures and Maps

1. Native perfectness, explicit upper term bounds and native flat-extension closure
   prove closure under zero, chain isomorphisms and all short exact extensions.
2. The inherited exact structure consists of ambient short exact sequences. A
   cofibration is an actual inclusion whose quotient belongs to the same bounded-above
   flat perfect class. It is not an arbitrary ambient monomorphism. Weak equivalences
   are the unchanged homology-based quasi-isomorphisms.
3. The original signed shifts and mapping cones stay in the class. The actual
   identity-cone joint cylinder is consequently constructed, with the unchanged
   second endpoint retracting its projection. No joint-cylinder premise is added.
4. The literal full-chain inclusion into all native perfect complexes is Waldhausen
   exact, with the target's existing ambient-monomorphism structure. It reflects
   weak equivalences literally. Its connective K-map retains the canonical
   chosen-zero normalization, in all nonnegative degrees including zero.
5. The actual bounded finite locally free complex is flat by native Stacks flatness
   of locally free sheaves. Its literal inclusion is exact. Composing the strict-to-flat
   and flat-to-perfect K-maps gives the already existing strict-to-perfect K-map.
6. Native flat covers (Tag 03EW) and the bounded-above resolution theorem (Tag 05T7)
   give an actual augmentation `P → K` from flat perfect `P`, with `P.IsStrictlyLE b`
   whenever `K.IsLE b`. If `K` is termwise upper-bounded, the augmentation can also
   be degreewise epimorphic. The source remains a real sheaf complex and the map a
   real chain map, rather than an isomorphism only in a derived category.
7. Quasi-compactness alone supplies an actual cohomology upper bound for every
   native perfect complex. The resulting actual flat augmentation needs neither
   quasi-separatedness nor a resolution property.
8. Every map from a termwise upper-bounded source factors exactly through the target's
   good truncation. The displayed composite equals the original chain map.

## Original-to-Native Crosswalk

The Quillen source pin is `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Original implementation provenance and mathematical references are recorded separately.

- Original `boundedFlatPerfect` becomes
  `AlgebraicGeometry.RingedSpace.boundedAboveFlatPerfectComplex`.
  It uses native `IsPerfectComplex` and native sheaf `IsFlat`, whose stalk criterion
  is explicitly exercised by the in-package scheme consumer.
- Original `boundedFlatPerfectInclusion` becomes
  `boundedAboveFlatPerfectInclusion`, with literal original objects and chain maps.
- Original `boundedFlatPerfectWaldhausen` becomes
  `boundedAboveFlatPerfectWaldhausen`, with the actual quotient condition exposed
  by `boundedAboveFlatPerfectWaldhausen_cof_iff`.
- Original `boundedFlatPerfect_shift` and `boundedFlatPerfect_mappingCone` become
  `boundedAboveFlatPerfectComplex_shift` and
  `boundedAboveFlatPerfectComplex_mappingCone`.
- Original `boundedFlatPerfectJointData` becomes
  `boundedAboveFlatPerfectJointData`. The native construction works for every
  nested weak class containing quasi-isomorphisms, including the reflexive class
  required by approximation.
- Original `BoundedFlatPerfectK` and `boundedFlatPerfectToPerfectKMap` become
  `boundedAboveFlatPerfectK` and `boundedAboveFlatPerfectToPerfectKMap`.
- Original `strictToBoundedFlatPerfectKMap` becomes
  `Scheme.boundedFiniteLocallyFreeToFlatKMap`. The original composite identity is
  `Scheme.boundedAboveFlatPerfectToPerfectKMap_comp`.
- Original `exists_flat_perfect_replacement_of_homology_bound` becomes
  `exists_boundedAboveFlatPerfectComplex_of_isLE`, using Mathlib's equivalent
  cohomological-bound class and preserving the sharp original term bound.
- Original `exists_flat_perfect_replacement_of_quasiCompact` becomes
  `exists_boundedAboveFlatPerfectComplex_of_quasiCompact`, retaining exactly
  `CompactSpace` and the original augmentation direction.
- Original `mapToGoodTruncation` and its exact factorization become
  `boundedAboveMapToTruncLE` and `boundedAboveMapToTruncLE_comp`.

## Remaining Comparison Obligation

The original K-comparison assumes only `CompactSpace X`, meaning quasi-compactness,
and states bijectivity of the literal inclusion K-map for every `n : ℕ`, including
zero. Its forward equivalence map is that same map. No quasi-separatedness,
regularity or resolution property belongs to that original theorem.

The missing relative statement is stronger than object replacement. Given an actual
map from bounded-above flat perfect `K` to perfect `L`, it constructs a factorization
`K → M → L` whose composite is the original map, whose first arrow is an admissible
cofibration with flat perfect quotient, and whose second arrow is an actual
quasi-isomorphism. The original proof uses a common upper bound after good truncation,
relative projective factorization of the underlying presheaf map, exact sheafification,
and flatness of sheafified projective presheaves. The forgetful functor from sheaves
to presheaves is not asserted exact.

A non-relative augmentation does not supply this commuting triangle or lift the map
from `K`. No `HasApproximationProperty`, relative-replacement, App2 or desired
K-equivalence hypothesis is introduced to hide that gap. The constructed exact model,
App1 and cylinders are prerequisites; the relative factorization and resulting App2
remain to migrate before asserting `BoundedFlat.KComparison`.

The original dependency route to full localization naturality remains
`GlobalLocalizationNaturality` → `PairPullback` → `DerivedPullbackFunctor` /
`DerivedPullback` → `BoundedFlat.KComparison`. Arbitrary underived pullback on all
perfect chain complexes is not substituted. Supported/relative comparison maps,
full open-pair localization naturality, geometric roofs/complements, the prescribed
TT 5.1 image-cover comparison and Bass TT 7.4 are separate obligations.

## Validation and Integration

Owned sources and their full-signature in-package consumer are compiled locally
against immutable native providers. Evidence records the actual commands, source
snapshots, direct import five-family fingerprints, output hashes and native Lean
header graphs. Compilation and author-checked source correspondence are separate
from independent review and remote lint, axiom and Library checks.

The component does not edit shared roots, chapter files or migration summaries.
Parent integration retains newer main documentation and adds the recorded shared
proposals. Publication consists only of the owned source, test and documentation files.
