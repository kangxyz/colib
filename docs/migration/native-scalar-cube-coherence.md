# Coherent scalar additivity cubes

COL-0316 constructs the original scalar additivity square on every positive-dimensional
based subdivision cube and compares its whole boundary routes with the actual fine
additivity paths. This is a complete cube-coherence result. It is not yet the scalar
canonical-fiber comparison or an all-degree connecting-boundary formula.

## Objects and hypotheses

Let `j : U ⟶ X` be an open immersion of schemes, `r : Γ(X, ⊤)` a global scalar, and
`q : Γ(U, ⊤)ˣ` a specified unit with `j.appTop r = q`. Let `n : ℕ` and let `p` be a
`GenLoop (Fin (n + 1))` in the actual subdivided realization, based at the chosen zero.
There are no quasi-compactness, quasi-separatedness or scalar-regularity hypotheses.

The perfect objects are the native full subcategory defined by
`RingedSpace.IsPerfectComplex (X := X.toRingedSpace)`. Its fine Waldhausen structure is
`RingedSpace.perfectComplexesWaldhausen X.toRingedSpace`. The coarse structure is
`(perfectOpenNested j).coarse`, with weakness detected by the actual open restriction.
The original scalar cylinder, signed-cone quotient and chosen zero remain unchanged.

## Construction and conclusion

1. `perfectOpenScalarCofiberCubeSquare` evaluates the actual COL-0303 based square on
   `p`, then applies the original diagonal realization map. It is continuous as a map
   from the two-parameter square into the original generalized-loop space. Both times
   and all spatial coordinates are unchanged. Its entire spatial boundary stays at zero.
2. Its four whole faces are the identity additivity track, scalar additivity track,
   normalized inclusion cylinder and quotient-first normalized sum cylinder. The four
   edge paths are literal restrictions of that square, with no replacement paths.
3. The original normalized pushout and every mixed cut commute with fine-to-coarse
   change. This gives the simplicial endpoint and mixed-cylinder equations, their
   whole realization equations, and finally
   `subdividedBasedAdditivityHomotopy_changeWeak` for the prescribed three-stage track.
   The original reversal and concatenation parameters are retained.
4. `perfectOpenScalarIdentityFineCubePath` and `perfectOpenScalarSequenceFineCubePath`
   are constructed independently from the actual fine cofibration sequences. Their
   whole images equal the corresponding coarse edge paths. The four
   `perfectOpenScalarFineCorner00`, `01`, `10` and `11` equations follow by evaluating
   these whole-path equations at the endpoints, rather than assuming corner identifications.
5. `perfectOpenScalarFineCubeBoundaryHomotopy` is the prescribed square interpolation,
   reversed once, with endpoint casts justified by those four equations. Its source is
   the cast inclusion followed by the image of the fine scalar path; its target is the
   image of the fine identity path followed by the cast sum path. The `_apply` theorem
   identifies every interpolation time, path time and spatial coordinate with the
   original interpolation. The `_boundary` theorem fixes the entire spatial boundary.

Thus the supplied data include no `scalarTheta`, unknown cube filler, assumed fine-edge
comparison or unspecified transport. The endpoint homotopy is explicitly constructed.

## Exact source crosswalk

Implementation source is Quillen K-theory commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, recorded as `quillen` in the bibliography.
Authors and Apache 2.0 notices are retained. The following paths are relative to the
respective repository roots. The native namespaces are
`CategoryTheory.Waldhausen.Additivity` and `AlgebraicGeometry.Scheme.Modules`.

- `Quillen/Waldhausen/Additivity/ChangeWeakDeformation.lean:26-87` becomes
  `Colib/CategoryTheory/Waldhausen/Additivity/ChangeWeakDeformation.lean`.
  The four public declarations retain their names: cofibration-change naturality,
  `normalizedPushoutFunctor_changeWeak`, `normalizedMixedGrid_changeWeak` and
  `normalizedMixedMap_changeWeak`. The private normalization lemma uses the already
  selected native `CategoryTheory.rebaseFunctor` of the actual normalized pushout.
- `Quillen/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean:34-46,70-100`
  becomes `Colib/CategoryTheory/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean`.
  It contains `normalizedIdentityEndpointHomotopy_changeWeak`,
  `isCofibrationSequence_changeWeak` and `normalizedSeparatedEndpointHomotopy_changeWeak`.
  The realization declarations at lines 49-68 and 103-118 become
  `Colib/KTheory/Waldhausen/Additivity/ChangeWeakEndpointHomotopies.lean`.
- `Quillen/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean:36-54` becomes
  `Colib/CategoryTheory/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean`.
  Its `normalizedMixedEndpointHomotopy_changeWeak` retains the actual simplicial cylinder.
  `normalizedMixedRealizationHomotopy_changeWeak`, at lines 57-76, becomes
  `Colib/KTheory/Waldhausen/Additivity/ChangeWeakMixedHomotopy.lean`.
- `Quillen/Waldhausen/Additivity/ChangeWeakBasedHomotopy.lean:27-65` becomes
  `Colib/KTheory/Waldhausen/Additivity/ChangeWeakBasedHomotopy.lean`.
  The private concatenation helper and the complete based-track naturality proof are retained.
- `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCubeSquare.lean:40-193`
  becomes `Colib/AlgebraicGeometry/KTheory/PerfectScalarCofiberCubeSquare.lean`.
  All 18 public declarations are retained: the square, evaluation and boundary equations,
  four whole-face equations, four literal paths with their evaluation equations, and the
  explicit boundary homotopy with its defining equality and full spatial-boundary equation.
- `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineCubeEdges.lean:39-292`
  becomes `Colib/AlgebraicGeometry/KTheory/PerfectScalarCofiberFineCubeEdges.lean`.
  All 29 public declarations are retained: the fine source and target maps and cubes,
  the original fine homotopy and its basedness, the change-weak map, both fine paths,
  whole-path image equations, four derived corners, cast edges, and the final explicit
  fine-boundary interpolation. Native `GenLoop.postcomp` and `GenLoop.postcompHomotopy`
  operate on Mathlib's actual generalized loops.

Categorical and simplicial statements are below realization and scheme applications.
There is no replacement compatibility namespace or dependence on Aglib. The regression
module `ColibTest.PerfectScalarCofiberCube` checks all four faces, whole fine-path images,
all four corners, cast-path equations and the actual interpolation in arbitrary dimension.

## Remaining mathematical boundary

The actual projection, canonical null and compact-coproduct normalization are outside
COL-0316 itself. The integrated COL-0317 separately supplies
`ScalarCofiberFineProjectionCubePath`, `ScalarCofiberCanonicalNull`,
`ScalarCofiberCanonicalPairCylinder`, `ScalarCofiberSumNormalizationSquare` and
`ScalarCofiberCanonicalSumCube`, then carries the unchanged subdivision cube through
`ScalarCofiberSumCubeNormalization` and `Spectrum/ScalarCofiberCanonicalFiberCube`.
COL-0320 separately supplies the actual prescribed normalized return and connecting-map
comparison from `Spectrum/ScalarCofiberCubeReturnClass` and
`Spectrum/ScalarCofiberFiberComparison` on these original cubes. Identification with the
prespectrum scalar operation and arbitrary-input descent remain subsequent work.
Only after the actual input-descent and self-track comparisons can one claim the corresponding
all-positive-degree scalar connecting-boundary theorem.

The existing relative degree-one formula remains `+[signedCone(r)]`. It must not be confused
with the T-first Mayer-Vietoris forward Laurent-unit formula, whose first coordinate is
`−[O]`; the inverse-unit class gives the positive splitting. These later comparisons are not
proved here. COL-0316 asserts no Laurent or Bass formula, nonconnective localization, all-integer result,
Nil vanishing or homotopy invariance.
