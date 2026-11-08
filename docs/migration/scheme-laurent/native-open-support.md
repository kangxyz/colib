# Native perfect open support and scalar-cone inputs

COL-0298 constructs the actual open-detected weak structure on the existing
native category of perfect chain complexes and compares its acyclic category
with the actual supported category. The scope is every open immersion
`j : Y ⟶ X`, without compactness, separatedness, regularity or Noetherianity.

## Original objects and maps

The perfectness predicate is Stacks `RingedSpace.IsPerfectComplex`. The
Waldhausen cofibrations remain ambient monomorphisms and the fine weak
equivalences remain genuine quasi-isomorphisms. The new coarse weak class is
the inverse image of quasi-isomorphisms under the literal degreewise
`Scheme.Modules.restrictFunctor j`. It changes neither the category nor its
chosen zero or pushouts.

Support means that this actual restricted complex is acyclic. Flattening and
restoring the two full-subcategory witnesses leave the complex and chain map
unchanged. Both functors are exact for their fine weak classes. The induced
K-equivalence preserves the original supported inclusion in every nonnegative
degree, including zero. The public opens-only restriction K-map remains the
same map and factors through this coarse structure.

The scalar action is the existing Stacks `RegularSequence.globalSmulCenter`,
lifted to chain maps. A unit acts by its actual scalar and has inverse the
actual inverse scalar. The signed Mathlib mapping cone is unchanged; restriction
to an invertible scalar proves its acyclicity on the open. The cone functors
preserve actual ambient short exact sequences. The rank-one object is the
structure sheaf in degree zero.

The affine-line and Laurent objects are Stacks' existing
`additiveGroupBaseChange` and `multiplicativeGroupBaseChange`. The map is the
base change of `Spec.map Polynomial.toLaurent`. Their existing first projections
pull back the polynomial coordinate and the forward Laurent unit. Thus the
coordinate equality sends X to T, not its inverse. Original Quillen uses the
opposite ordering of this fiber product and its second projection; no second
model or replacement group scheme is introduced here.

## Source correspondence

The implementation source is Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `Quillen/Waldhausen/Fibration/InverseImageWeak.lean`: the full generic
  construction, with distinct source and target universes.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenSupport.lean`: the actual
  flattening equivalence and canonical K-map comparisons.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenFibration.lean`, relative
  weak structure and K-map definitions only. Its fiber theorem is not imported
  as an assumption or asserted here.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalScalar.lean`,
  `GlobalUnit.lean`, `RankOne.lean`, `ScalarRestrictionPerfect.lean` and
  `ScalarCone.lean`: actual scalar maps, restriction and cone constructions.
- `Quillen/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/NativeCoordinates.lean`:
  the positive open and its forward coordinate, directly on the pinned native
  Stacks schemes.

The original exact-subcategory cofibration proof is not reused as if it were
definitionally the native ambient-monomorphism structure. Exactness here is
proved directly for the existing native cofibrations and displayed pushouts.
The cone criterion is the existing public Stacks
`CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone`.

## Verification and remaining scope

The source and immediate native APIs received independent read-only review.
That review is distinct from compilation. The submitted candidate requires the
unmodified native CI build, tests, declaration/text lint, axiom audit and Library
checks; no local whole-library check is claimed for this slice.

A genuine ambient-monomorphism joint cylinder and the actual relative fiber
theorem remain separate obligations. Fine K-theory of the open is not identified
with the coarse K-group. The independent [T] K-one class, the full cofiber/weak-
composition track, the inverse-loop comparison and the connecting-sign
cancellation are later consumers. No Bass boundary sign, zero-section
devissage, Nil vanishing or nonconnective statement is asserted.
