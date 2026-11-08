# Actual finite, stable and Waldhausen self-track operations

COL-0321 adapts the complete generic operation chain from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original whole tracks, coordinate
orders, group products, chosen cancellations and stable signs are retained.
The source uses Mathlib's generalized loops, paths, homotopy quotients,
native categorical sequential colimits and the already constructed Colib
Waldhausen S-prespectrum. There is no Aglib import or compatibility namespace.

## Reused foundations

The native generalized-loop normalization, transport, spatial product and
naturality modules already provide actual constructions. Likewise, the native
`Topology.LoopPrespectrum` contains coherent whole based homotopies, the
integer-graded stable systems, loop-shift signs and exact tail reindexing.
The Waldhausen source is the native strict chosen-zero wide subcategory of
`SmallWaldhausenCategory`; arbitrary exact functors use canonical zero rebasing.
No new record containing the desired operation laws replaces these objects.

## Finite operation and successor signs

The `SelfTrackRepresentative` and `SelfTrackHomotopyClass` modules evaluate the
actual whole level homotopy on the original based cube. A path of input cubes
provides its own conjugacy square, so the actual normalized higher track class
descends to the original homotopy quotient. This gives a function from $\pi_{m+1}$
to $\pi_{m+2}$, including the input Pi-one case.

`SelfTrackHomotopyAdditivity` proves the group law for input degree at least two,
using a second spatial coordinate distinct from the normalization coordinate.
`SelfTrackCoordinateChange` and `SelfTrackSuccessorRepresentative` compare the
actual normalized cubes before passing to classes. `SelfTrackSuccessorSign`
then identifies the literal swap of track time and structure time with inversion.
`SelfTrackSuccessorPositive` establishes the sign also for input Pi-one without
assuming additivity in that degree.

The additional generalized-loop evaluation and successor-coordinate lemmas are
owned below prespectra, in `Topology.Homotopy.HomotopyGroup`.

## Stable operation and complete-track laws

`SelfTrackStableOperation` uses the actual finite homomorphisms and their proved
anti-commuting successor squares. Alternating by $(-1)^n$ gives a natural map of
the unchanged sequential systems. Its colimit map and the actual shifted-tail
identification give the integer-graded stable operation. The stage formula
retains the exact integer degree, level, alternating sign and tail offset.
No Omega-spectrum hypothesis is needed for this construction.

Whole relative homotopies and supplied intertwining squares preserve the
finite and stable operations. Reversing track time negates the stable map,
and concatenating tracks adds their actual operations. These statements keep
complete homotopies rather than only equalities of induced ordinary maps.

`SelfTrackInterchange` normalizes two independent tracks in distinct spatial
coordinates and compares their literal cubes by swapping the two track times.
The resulting finite operations anti-commute in degree at least two.
`SelfTrackStableInterchange` gives the corresponding nonnegative stable
anti-commutation theorem, assuming only that the source is an Omega-spectrum.

## Actual Waldhausen K-operation

`KTheory.Waldhausen.Iterated.SelfTrackKOperation` transports the constructed
stable operation through the actual original-K/stable equivalences. It is a
genuine homomorphism in every nonnegative input degree, including K-zero.
The stable comparison uniquely determines it on every original K-class.

`SelfTrackKOperationLevelOne` identifies it with the inverse of the literal
level-one normalized finite track class under the unchanged AsSmall comparison.
Both relevant Omega conditions are already proved for these actual S-prespectra.
`SelfTrackKOperationPath` retains the supplied complete path representative:
the level-one successor inverse and path normalization inverse cancel, yielding
the original forward K-one normalization.

`SelfTrackKOperationIntertwining`, `SelfTrackKOperationLevelExt` and
`SelfTrackKOperationNaturality` retain whole-track transport, endpoint casts
and the canonical source and target KMaps of arbitrary exact functors.
The strict-zero transformation specializations use native wide-subcategory
morphisms; the arbitrary-exact-functor specializations use actual normalized
weak transformations and their proved relative composition triangle.

## Supplied-null factorization and cone transition

The normalized actual finite self-track is compared with its specified
null-conjugated loop map. The stable comparison retains the loop-shift sign,
original stage maps and the complete supplied nullhomotopy. Vanishing of the
one-higher intermediate stable group therefore annihilates that actual map
in every integer degree, without a levelwise vanishing or replacement premise.

`SelfTrackConeTransition` supplies the three previously absent cone-specific
constructions from the final part of original `Prespectrum/HomotopyLoop.lean`.
Its null path is the existing reduced cone's actual canonical nullhomotopy.
The cone-independent source declarations remain unchanged at their prior owners.

## Exact remaining boundary

This generic topic does not construct the scheme scalar-unit tracks or identify
the prescribed scalar return class of COL-0320 with the actual K-operation.
The original `ScalarUnitTrack`, `ScalarUnitTrackTransport`, scalar operation,
whole small-model cube transport and return-class operation comparison remain
separate scheme-owned work. Their later fiber comparison must retain that
identification rather than assume it.

Input descent, subdivision coverage, the global scalar formula and the scheme
restriction corollaries are not consequences claimed here. This is not TT
localization or a Bass nonconnective formula. No Nil vanishing or homotopy
invariance follows. The relative positive signed-cone convention is not changed
into the T-first forward Laurent-unit negative structure-sheaf convention.

## Verification and source correspondence

Each production module cites its original source and preserves its license.
The full-signature regression consumer covers actual finite, signed stable
and original K-group formulas, including Pi-one, K-zero, supplied nulls,
whole relative tracks and independent-track interchange. Local compilation,
author source comparison, independent review and remote native lint/axiom/Library
checks are separate validation facts; a compilation receipt alone is not an
independent mathematical review.
