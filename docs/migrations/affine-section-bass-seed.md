# Ambient affine-section one-step Bass seed

This source migrates the ambient seed of Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd` without importing Aglib. The lower coefficient
square uses the same canonical Mathlib homomorphisms as the original Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`. It does not duplicate coefficient extension
or alter the frozen affine-section Laurent action.

## Source correspondence

- `Colib/RingTheory/Polynomial/LaurentSquare.lean` adapts
  `Aglib/Algebra/Polynomial/Laurent/Square.lean:40-101` and the coefficient, positive-chart,
  inversion and inverse-chart identities in `BaseChange.lean:44-50,183-224`.
  Polynomial pushout and Laurent pushout theory are not claimed or required.
- `Colib/RingTheory/KTheory/Bass/StrictRingDiagram.lean` and `StrictRingSeed.lean` specialize
  the native diagram functor and assemble pointwise natural maps, as in
  `Quillen/KTheory/Bass/StrictRingDiagram.lean:25-50` and `StrictRingSeed.lean:23-40`.
  These generic assemblers alone do not construct the geometric seed.
- `Colib/AlgebraicGeometry/KTheory/BoundedFlatAffineSectionBassSeed.lean` constructs the
  actual model and prespectrum squares and the original seed of
  `Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:33-141`.
  The native exact model is already small and strictly zero-preserving. The extra
  model-square and whole-null-homotopy endpoints expose the same construction before
  realization and after explicit endpoint transport.

## Canonical maps and parameters

The square corners are the coefficient ring, two polynomial rings and the Laurent ring.
The right vertical chart is `Polynomial.toLaurent`; the bottom horizontal chart is
`LaurentPolynomial.invert` after `Polynomial.toLaurent`. Their images of `X` are respectively
`T 1` and `T (-1)`. Inversion of the exponent is not additive negation. Both source composites
are literally the existing Laurent coefficient inclusion. All four coefficient maps are
canonical, and no flatness or nonzero-ring hypothesis is imposed.

The double cylinder, comparison, mapping cone, cone inclusion and cone maps are the existing
native constructions. The null track is the actual cone cylinder on the source leg. The
middle track is the previously constructed forward `T 1` unit, postcomposed with the cone
inclusion. The seed loop is exactly `N.symm.trans (V.trans N)`. Its durations are one half,
one quarter and one quarter, with Mathlib's branch convention at the joins.

At degree zero the input is itself a loop. Its internal coordinate is evaluated before the
cone inclusion. An arbitrary cone point is not a loop. The output seed-loop parameter,
internal degree-zero loop coordinate and prespectrum structure coordinate remain independent.
The consumers test the entire strict maps and tracks, not just homotopy or K-groups.

## Boundary

The construction is the ambient, strict, one-step affine-section Bass seed with full
coefficient naturality. Formal finite iteration is available through the native diagram
functor. No evaluation comparison, supported localization, supported cone/unit comparison,
Bass telescope identification, negative K-localization or Thomason--Trobaugh 7.4 is asserted.
