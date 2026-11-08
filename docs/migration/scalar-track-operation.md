# Scalar tracks and the actual K-operation

COL-0324 closes the comparison left open by COL-0320, using the actual generic self-track
operation of COL-0321. The return class is no longer only an inverse-composition class: the
same full composition loop is carried forward through the native `AsSmall` homeomorphism,
including its actual time-zero endpoint equality, and is identified with the prescribed
prespectrum operation. The two inverses, one from level one and one from the signed return,
produce the original scalar operation. Both the raw and normalized tracks give the positive
cone connecting image, including degree zero.

## Native objects and proof direction

1. Genuine flat scheme morphism pullback preserves the Stacks native perfect-complex predicate
   by transporting the actual local strict model and quasi-isomorphism. The inherited Mono,
   QuasiIso and pushout structure proves Waldhausen exactness. The open-restriction comparison
   uses the actual module pullback isomorphism and original left unitor.
2. The scalar and flat-unit transformations give actual original prespectrum tracks. Binary
   zero-normalization pasting and the categorical scalar square prove whole relative
   intertwining. Raw normalization is constructed with the actual rebase isomorphism.
3. The inclusion/projection triangle uses the same endpoint rebases as the existing fine
   projection. Its diagonal realization agrees with the ordinary cylinder at every time.
4. Forward small-model transport preserves the entire composition loop and both endpoint
   casts. COL-0321's level-one theorem supplies the exact inverse sign in every nonnegative
   K-degree. The prescribed return of COL-0320 therefore represents that operation.
5. COL-0320's already constructed whole canonical-fiber homotopy then proves the connecting
   comparison with positive cone sign. The full prespectrum canonical-null square and rotated
   pasting are also constructed rather than assumed.

## Original source correspondence

At Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, the main sources are
`PerfectComplexes/Spectrum/ScalarUnitTrack`, `ScalarUnitTrackTransport`,
`ScalarUnitTrackOperation`, `ScalarCofiberProjectionTrack`, `ScalarCofiberInclusionDiagonal`,
`ScalarCofiberCubeReturnClass` and `ScalarCofiberFiberComparison`. The generic
`NormalizationNaturality`, `NormalizationPasting`, `NormalizationTrackPasting`,
`ExactPastingHomotopy` and relative prespectrum pasting constructions are below the scheme
application. Native objects replace the old Aglib/Quillen ownership without compatibility
namespaces or new mathematical premises. Exact declarations carry compiled source references.

The old `perfectGlobalScalar_openWeak` proof is supplied directly by the existing native
`quasiIso_restrict_complexGlobalScalar`. Restriction uses
`perfectComplexesRestrictOpenImmersion` and `perfectOpenRestrict_isExact`.
The old `smallModelDeloopingHomeomorph` and `smallModelKEquiv` are the native
`asSmallDeloopingHomeomorph` and `asSmallKEquiv`; all coordinates and endpoint orientations stay.

## Exact boundary

The finite/stable restriction comparison applies to the stated arbitrary finite input and all
integer stable degrees. The return-to-operation and connecting equalities are proved on the
original subdivision cubes. `ScalarCofiberInputDescent`, subdivision coverage and subsequent
global formulas are a separate topic; no arbitrary-input surjectivity is asserted here.
Object-generator and row K-one applications are not prerequisites for this comparison and
are not claimed migrated by it. This is not TT localization or a Bass/nonconnective boundary
formula. The relative positive signed cone does not change the T-first forward Laurent-unit
negative structure-sheaf convention.

The original flat-unit canonical-null transport in `Spectrum/ScalarUnitTrackNull` is a
separate family. It is distinct from the scalar-cone canonical-null square and rotated
prespectrum pasting constructed here, and is not claimed by COL-0324.
