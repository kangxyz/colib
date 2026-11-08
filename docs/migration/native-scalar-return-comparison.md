# Prescribed scalar return and canonical fiber comparison

COL-0320 continues COL-0316 and COL-0317 using the same native perfect complexes, fine and
coarse Waldhausen realizations, chosen zero objects and original path-space homotopy fiber.
The input is an open immersion `j : U ⟶ X`, a section `r` restricting to a specified unit `q`,
and an original subdivision cube `p` of dimension `n + 1`. There is no assumption about an
unspecified filler, geometric Theta, null comparison or return class.

## The complete mathematical result

The prescribed fine return is the reversed same-rebase projection followed by the scalar
sequence edge. Its whole coarse image is followed by the reversed quotient-first sum edge
and reversed identity additivity track. The actual scalar boundary square constructs an
endpoint-fixed homotopy from this exact signed word to the inverse of the original
inclusion/projection composition. The corresponding actual self-track classes are equal
with exactly that inverse, also when `n = 0`.

The original inverse-prefix normalization retains both cancellation paths. Constructive
path associators identify the resulting normalized self-track with the returned fiber loop,
without changing a path's parametrization by an asserted equality. The geometric endpoint
homotopy from COL-0317, source transport and unpadding then give an explicit whole-boundary
relative homotopy from the loop inclusion of the normalized cube to the original canonical
acyclic-to-fiber map evaluated on the public acyclic cone cube.

The two endpoint faces are exact. At the initial face, coordinate zero is the normalized
track time. At the final face, every stored path time is the once-reversed canonical null.
Every intermediate time fixes the complete original spatial boundary. Applying the actual
coordinate-zero topological connecting homomorphism gives the canonical fiber K-map of the
scalar acyclic-cone K-map on this original input, with positive cone sign.

## Source and native owners

The implementation source is Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Paths below are relative to its `Quillen/` folder.

- `Topology/Path/SquareProjectionReturn.lean:22–60` becomes
  `Colib.Topology.Path.Homotopy.SquareProjectionReturn`: actual square return homotopies,
  including arbitrary independent fine/coarse universes. Historical deprecated aliases
  are not introduced.
- `Topology/HomotopyGroups/GenLoopNormalizedSelfTrackPrefix.lean:22–86` becomes
  `Colib.Topology.Homotopy.HomotopyGroup.GenLoopNormalizedSelfTrackPrefix`: exact original
  inverse-prefix word and coordinate-zero currying, retaining every residual coordinate.
- `Topology/HomotopyFiber/GenLoopNormalizedReturn.lean:24–108` becomes
  `Colib.Topology.HomotopyFiber.GenLoopNormalizedReturn`: whole normalized-return comparison
  over an arbitrary based continuous map with independent source and target universes.
- `AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeReturn.lean:27–86` becomes
  `Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeReturn`: all six original public
  definitions and theorems, retaining the literal return word and both homotopy times.
- `AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean:99–103,
  210–224` supplies only the original composition loop and the inverse-class part of the
  original proof in `PerfectScalarCofiberCubeReturnClass`. The new intermediate theorem
  is named `perfectOpenScalarCubeReturn_inverseCompositionClass`; it does not claim the
  original prespectrum operation equality.
- `AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberFiberComparison.lean:35–159`
  becomes `Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFiberComparison`: every
  declaration through `perfectOpenScalarNormalizedCube_connecting`, with all original
  hypotheses, maps and stored path coordinates. Lines 161–181 are not migrated here.

The generic declarations retain their native Topology or Path owners. Scheme-specific
wrappers belong to `AlgebraicGeometry.Scheme.Modules`. No Quillen or Aglib compatibility
namespace or dependency is introduced. The implementation uses the existing native
`GenLoop.postcomp`, `SSet.diagonalSSet` and perfect-complex object property.

## Exact remaining boundary

The prescribed return class is now compared with the actual canonical fiber and connecting
map. It has not yet been identified with `originalKSelfTrackOperation`. That original
operation uses additional full prespectrum constructions, not a missing premise that may
be assumed. The next independent source chain is:

1. `Topology/Prespectrum/SelfTrackRepresentative`, `SelfTrackHomotopyClass`,
   `SelfTrackHomotopyAdditivity`, coordinate interchange and successor signs, and
   `SelfTrackStableOperation` provide the actual finite and stable operations. Relative
   homotopy, level-one and intertwining comparisons must use those same whole tracks.
2. `Waldhausen/SConstruction/Iterated/SelfTrackKOperation.lean:31–55`,
   `SelfTrackKOperationLevelOne.lean:31–43` and
   `SelfTrackKOperationIntertwining.lean:22–28` define the actual K-operation and identify
   its level-one inverse and normalization transport. Naturality is needed for restriction.
3. `AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarUnitTrack.lean:38–111` and
   `ScalarUnitTrackTransport.lean:34–124` supply the actual scalar, rebase and flat-unit
   tracks. `ScalarCofiberProjectionTrack.lean:95–108,134–180` supplies the original
   prespectrum projection/inclusion, composition triangle and raw normalization prefix.
4. `Spectrum/ScalarCofiberInclusionDiagonal.lean:41–72` and the remaining
   `ScalarCofiberCubeReturnClass.lean:42–98,105–208,225–255` transport whole paths through
   the actual small-model homeomorphism, identify the class with the actual operation,
   retain the raw normalization prefix and prove the restriction corollary.
5. Only then do `Spectrum/ScalarCofiberFiberComparison.lean:161–181` identify that operation
   under the connecting map. `ScalarCofiberInputDescent` and later global consumers require
   actual subdivision coverage and descent to arbitrary inputs; neither is asserted here.

The prespectrum relative/rotated canonical-null pasting in
`ScalarCofiberCanonicalNull.lean:101–161` also remains separate. It is not needed for the
ordinary prescribed-return result proved here, which uses the actual ordinary canonical
null and normalization from COL-0317.

This is not TT localization. Image-corrected connective targets in TT §5.1 and Bass
nonconnective K-theory in §7.4 are different boundaries. No all-integer Bass formula,
Nil vanishing or homotopy invariance follows. The relative positive signed-cone orientation
is not changed into the T-first forward Laurent-unit negative structure-sheaf convention.

## Verification boundary

The independent regression module checks complete statement types, arbitrary coordinates,
both interpolation times and an explicit `n = 0` specialization. Local compilation and
source correspondence are recorded separately from independent mathematical review.
The parent integration owns root generation, the shared reading order and remote native
lint, production axiom checks and Library export. This contribution does not replace main
with an older dependency tree.
