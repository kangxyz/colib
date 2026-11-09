# Fixed-pair qcqs connective image-cover localization

COL-0330 specializes the native conditional comparison using actual qcqs geometry from
COL-0307. It retains the existing coarse model as the actual image-cover target of
Thomason–Trobaugh Theorem 5.1.1. The chosen derived category on the open is arbitrary.
The only geometric hypotheses are compact ambient and open spaces, quasi-separated ambient
space, and an open immersion. No resolution, regularity, Noetherian or separated assumption
is added; roofs and complements are conclusions of native geometry, not input predicates.

## Actual objects and maps

Write E for `perfectOpenPrespectrum j`, the existing original coarse S-prespectrum.
`perfectOpenPrespectrum_isOmega` proves the all-level Omega property, including components;
`perfectOpenPrespectrum_neg_subsingleton` gives negative stable vanishing.
The actual map K(X) to E is `Fibration.changeWeakPrespectrumMap (perfectOpenNested j)`.
The actual map E to K(U) is `perfectOpenRestrictPrespectrumMap j`.
`perfectOpenOriginalRestrictionFlatHomotopy` is the entire coherent homotopy from this
composite to `perfectFlatPrespectrumMap j`. It has no scalar hypothesis despite its original
implementation owner. `perfectOpenRestrictPrespectrumMap_comp_stable` records the resulting
equality of actual stable maps in every integer degree.

`perfectSupportedFiberPrespectrumMap j` is the original supported path-space lift into the
homotopy fiber of that actual changeWeak map. Its projection is the unchanged supported
inclusion, and `perfectSupportedPrespectrumNullhomotopy` is its whole path coordinate.
The existing `eq_lift`, `path` and `structure` theorems retain the actual lift and independent
homotopy/loop parameters. Both this map and its canonical rebase are stable equivalences
in all integer degrees. These are reused COL-0319 constructions, not new assumed fields.
The support denotes perfect complexes on X acyclic on U, not K-theory of the closed subscheme.

## Geometric discharge and the exact zero endpoint

`perfectOpenRestrictPrespectrumMap_succ_bijective_of_qcqs` proves the actual stable map
bijective in every positive degree. `perfectOpenRestrictPrespectrumMap_zero_injective_of_qcqs`
proves degree-zero injectivity. `perfectOpenStableZeroImageEquivOfQcqs` identifies stable zero
with the actual global restriction image, and its `coe` equation identifies the original map,
not merely an abstract isomorphic group. The existing
`perfectOpenRestrictPrespectrumMap_zero_mem_range_iff` identifies its exact image.
These companion declarations are part of the item alongside the concrete-diagram assembly
`perfectQcqs_connectiveImageCoverLocalization`. Surjectivity onto all K-zero of U is not claimed.

The proofs install the actual `hasDerivedRoofs_of_qcqs` result locally and pass the actual
`hasPerfectComplements_of_qcqs` theorem. Neither geometric predicate appears as an assumed
hypothesis of the public qcqs endpoints. A second prescribed topological cover is unnecessary:
E itself has the proved connective image-cover properties for its actual map to K(U).

## Original-source crosswalk

The implementation source is Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:
[GlobalLocalization, lines 39–153](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean#L39-L153).

- `qcqsPerfectConnectingHom` becomes `perfectQcqsConnectingHom`.
- The original whole relative-boundary equation and uniqueness are
  `perfectQcqsConnectingHom_comp_relative` and `perfectQcqsConnectingHom_unique`.
- The three recurring exact positions are `perfectQcqs_positiveLongExactSequence`.
  Setting n to zero gives K-one of U to supported K-zero to K-zero of X to K-zero of U.
- The honest image-valued terminal arrow remains `perfectKZeroToOpenImage`;
  `perfectQcqs_zeroImageTail` terminates surjectively in that subgroup only.
- COL-0318 retains conditional connective group/stable comparison and the original maps;
  COL-0330 removes its geometric input predicates using COL-0307.
- COL-0319 retains the actual supported fiber transport and canonical rebasing.
  No second proof of those constructions is asserted here.

## Literature and scope

[Thomason–Trobaugh, Theorem 5.1.1 and proof 5.2, printed pp. 337–338](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Thomason-Trobaugh.pdf)
uses the actual coarse-to-fine restriction, positive comparison and degree-zero injectivity.
The exact zero image supplies the connective correction. This follows that proof with the
coarse model itself as the selected image-cover, rather than requiring an independently
prescribed Eilenberg–MacLane construction. The group boundary is transported through the
proved positive comparison and preserves its original relative map and sign conventions.

This is fixed-pair TT 5.1.1, not all of TT 5.1. The auxiliary closed support Z in 5.1.2 needs
its own supported geometric development. Arbitrary open-pair pullback naturality from
Quillen GlobalLocalizationNaturality remains separate. TT 7.4 (printed p. 365) is the
nonconnective Bass localization theorem; integer indexing and negative vanishing of these
connective spectra do not establish it.

## Validation boundaries

Both owned production leaves and both full-signature in-package consumers were actually
compiled locally with recorded production/test options. The qcqs consumer supplies no
roof/complement hypothesis and checks positive degrees, exact K-zero image, actual map
compatibility, boundary uniqueness, all exact positions and the n = 0 image tail. The
independent diagram consumer checks the actual homotopy, lift, path, structure parameters,
all-integer stable equivalences and canonical rebasing. Native declaration metadata is
read separately; final aggregate root and regression compilation belongs to integration.
Full private Library, axiom and lint checks remain the remote gates. Local compilation,
source correspondence, independent review and remote validation are distinct facts.
