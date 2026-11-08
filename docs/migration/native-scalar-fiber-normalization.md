# Actual scalar sum normalization and canonical fiber cubes

COL-0317 continues the actual coherent scalar cube of COL-0316. It closes the
normalization and canonical-fiber-lift subtopic on each original subdivision cube.
It uses the native Stacks perfect complexes and the existing signed scalar cone,
not a second model or an adapter to the former implementation.

## Mathematical reading route

1. `PerfectScalarCofiberProjectionTrack` proves that the very same coarse-rebased
   identity and cylinder-middle functors are fine exact. The original weak
   projection cylinder changes weak equivalences at every input and time.
   `PerfectScalarCofiberFineProjectionCubePath` identifies both actual endpoints
   through diagonal naturality before casting that entire path.
2. `PerfectScalarCofiberCanonicalNull` constructs the cone normalization using the
   actual inclusion-whiskered rebase isomorphism. The zero-normalization square is
   an equality of the original transformations. Its whole ordinary zero cylinder
   is constant, and the public acyclic null is precisely the whiskered original
   zero-to-inclusion cylinder reversed once.
3. `PerfectScalarCofiberSumNormalization` retains every normalization factor of the
   quotient-first pair. `PerfectScalarCofiberSumNormalizationSquare` constructs
   the actual simplicial square, its four faces, its realized square with two
   independent times, and the fine-to-coarse images of both whole Theta paths.
4. `PerfectScalarCofiberCanonicalPairCylinder` proves that the first projection
   is the original zero-to-cone cylinder and the second is the fixed rebased
   identity. `SeparatedPairMap` preserves the distinct first and right subdivision
   restrictions. The original first restriction supplies the acyclic cone; the
   right restriction supplies the identity summand.
5. `PerfectScalarCofiberCanonicalSumCube` uses actual product-comparison injectivity
   to identify both compact coproduct targets and the entire reversed sum
   cylinder. Every time and spatial coordinate remains unchanged.
6. `PerfectScalarCofiberSumCubeNormalization` constructs the geometric Theta word
   and the normalized endpoint homotopy. Its two inverse-prefix cancellations,
   original identity additivity path, moving null source, exact endpoint casts
   and full spatial boundary are retained. No Theta is supplied as a premise.
7. `PerfectScalarCofiberCanonicalFiberCube` evaluates the actual public cone and
   canonical null in the original path-space homotopy fiber. Its source coordinate
   and every stored path time agree with the canonical acyclic-to-fiber map;
   extensionality proves equality of the whole based cube.

The generic identity and separated-pair simplicial constructions belong to
`CategoryTheory.Waldhausen`; their realization belongs to `KTheory.Waldhausen`.
The generic fiber evaluation and whole-path transport belong to
`Topology.HomotopyFiber`. Scheme specialization stays in `AlgebraicGeometry.KTheory`.
The independent regression module checks full signatures, arbitrary universes,
all spatial coordinates, four square faces, whole paths and both times.

## Precise implementation crosswalk

The implementation source is the Apache-2.0 Quillen development by kangxyz and
its attributed contributors, pinned at
[c561118b7795eb9780be9ed391c3251d6a4d0afd](https://github.com/kangxyz/quillen-k-theory/tree/c561118b7795eb9780be9ed391c3251d6a4d0afd). Each native module retains attribution
and a compiled `quillen` reference. The following paths are relative to `Quillen/`:

| Original source | Migrated span and native owner |
| --- | --- |
| `Waldhausen/SConstruction/IdentityCylinder.lean` | 27–92: categorical identity grids; 93–112: realized identity cylinder |
| `Waldhausen/Additivity/SeparatedPairMap.lean` | 31–103: categorical first/right pair; 105–165: realized product projections |
| `Topology/Path/HomotopyThreeRoutes.lean` | 19–55: actual rotated and three-route path words, attributed to Codex |
| `Topology/HomotopyFiber/GenLoopEvaluation.lean` | 32–154: native fiber evaluation, both coordinates, full boundary and loop currying |
| `Topology/HomotopyFiber/GenLoopPathTransport.lean` | 22–208: native whole-null variation, actual source slide/unpadding and return transport |
| `AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberProjectionTrack.lean` | 37–94, 109–133: same-normalization fine projection and whole realization naturality |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineProjectionCubePath.lean` | 34–152: actual fine projection cube with its proved endpoint identifications |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalNull.lean` | 34–100, 162–219: actual normalization transformations and once-reversed canonical null |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalization.lean` | 34–341: complete categorical quotient-first normalization |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalizationSquare.lean` | 34–557: whole actual square, four faces and fine Theta naturality |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalPairCylinder.lean` | 34–173: whole canonical pair cylinder and projections |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalSumCube.lean` | 34–379: distinct input restrictions, compact targets and whole sum cylinder |
| `AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumCubeNormalization.lean` | 34–609: actual geometric Theta word and complete normalized endpoint |
| `AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCanonicalFiberCube.lean` | 34–76: actual canonical fiber cube and equality with the canonical map |

These are implementation correspondences, not claims that the source's later
prespectrum statements follow from a partially migrated interface. The abstract
compact-coproduct endpoint construction is already native; this contribution
supplies its actual geometric data rather than restating its conditional theorem.
All cubes have `n + 1` spatial coordinates for `n : Nat`, including one-coordinate
inputs relevant to degree zero.

## Exact remaining boundary

The prespectrum-only declarations in `ScalarCofiberProjectionTrack.lean:95–108,
134–180` and `ScalarCofiberCanonicalNull.lean:101–161` are not part of this item.
They need the original levelwise scalar normalization and pasting tracks.
In this integrated topic COL-0320 separately supplies the actual prescribed normalized
scalar return and comparison with the original topological connecting map, from
`ScalarCofiberCubeReturn`, `Spectrum/ScalarCofiberCubeReturnClass` and
`Spectrum/ScalarCofiberFiberComparison`. Identification with the prespectrum scalar operation,
`Spectrum/ScalarCofiberInputDescent`, subdivision coverage and the global scalar boundary
remain subsequent work. No canonical-fiber equivalence or unproved filler is inferred here.

The existing relative K₁-to-K₀ boundary is positive `+[signedCone]`. This does not
change the T-first forward Laurent-unit/Mayer–Vietoris convention `−[O]` or the
all-degree forward-unit inverse convention. Connective constructions do not
establish a nonconnective formula, remove Nil terms or imply homotopy invariance.
