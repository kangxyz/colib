# Native Relative Flat Perfect Comparison

## Result and original model

COL-0325 completes the relative factorization and connective K-comparison left open by
COL-0323. The source category consists of genuine native locally perfect sheaf complexes with
an upper term bound and flat terms. No lower term bound, finite local freeness or quasicoherence
is imposed on the terms. Morphisms are the original chain maps. The target is the existing
native perfect-complex Waldhausen category.

On a ringed space whose underlying topological space is quasi-compact, every map from the
bounded-above flat perfect model to the perfect model has an actual factorization
`K → M → L`. Its composite is the original chain map, not merely its derived class. The first
arrow belongs to the inherited exact structure: there is an actual short exact sequence
`0 → K → M → Q → 0` with `Q` bounded-above, flat and perfect. The second arrow is a genuine
quasi-isomorphism. The construction requires only `CompactSpace`, and in particular it has the
original quasi-compact-only scheme specialization.

App1 is literal reflection of quasi-isomorphisms. This constructed relative factorization
proves App2. Together with the actual identity-cone cylinders from COL-0323 and the existing
independent-universe approximation theorem, it proves bijectivity of the canonical K-map of
the literal inclusion for every natural degree. Degree zero is explicitly retained. The
forward monoid homomorphism of the resulting group equivalence is definitionally that same
canonical inclusion K-map.

## Construction and native ownership

1. `CochainComplex.exists_boundedAbove_relative_projective_factorization` uses Mathlib's full
   CM5a theorem in the opposite abelian category and the native degree-reversing cochain
   equivalence. The original endpoints and triangle remain unchanged. The new middle complex
   has upper bound `b + 1`, the first map is degreewise split monic with projective cokernel,
   and the second map is an actual quasi-isomorphism. The source need not be projective.
2. Native Stacks presheaves of modules have enough projectives. Native projective sections,
   the objectwise flatness criterion (03ES) and exact sheafification (03ET) show that a
   projective presheaf sheafifies to a flat module sheaf. Sheafification is not asserted to
   preserve projectivity.
3. Apply that actual relative factorization to the underlying presheaf chain map. Exact
   sheafification preserves the short exact sequence and quasi-isomorphism. Its original
   counit isomorphisms identify both endpoints. Naturality proves strict equality of the
   resulting composite with the original sheaf chain map. The forgetful functor is used only
   to preserve zero terms, never assumed exact. Both the middle complex and quotient retain
   upper bound `b + 1`.
4. Good truncation of the target permits a common upper term bound. Quasi-compactness supplies
   the target cohomology bound by native local perfectness. The source already has an upper
   term bound. Perfectness of the actual quotient follows from the existing native
   cone-to-quotient quasi-isomorphism. No desired relative replacement, App2 or K-equivalence
   appears as an additional hypothesis.
5. The K-theoretic comparison consumes these proved inputs and the actual canonical inclusion
   map. It neither changes the model to bounded vector bundles nor drops the degree-zero case.

Generic homological algebra is owned under `Colib.Algebra.Homology.CochainComplex.BoundedAbove`.
Projective-presheaf sheafification is owned under `Colib.Algebra.Category.ModuleCat.Sheaf`.
Ringed-space factorization and approximation are under `Colib.AlgebraicGeometry.Modules`, and
the connective K-comparison is under `Colib.AlgebraicGeometry.KTheory`.

## Source correspondence

Original implementation: kangxyz/Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `Quillen/Aglib/Algebra/Homology/CochainComplex/BoundedAbove/RelativeProjectiveFactorization.lean`:
  dual CM5a, unchanged endpoints, actual quasi-isomorphism, split monomorphism and projective
  quotient terms. Replaced by native Mathlib objects and the existing native opposite
  quasi-isomorphism comparison.
- `Quillen/Aglib/AlgebraicGeometry/Modules/Flat/RelativeFactorization.lean`:
  projective presheaf replacement, exact sheafification, actual counits, flat quotient, explicit
  `b + 1` bound and strict triangle. Generalized from schemes to ringed spaces with the same
  module universe.
- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Approximation.lean`:
  common-bound truncation and the actual relative factorization prove the original App2.
- `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/KComparison.lean`:
  quasi-compact-only bijectivity of the original literal inclusion K-map and equality with the
  forward map of its equivalence, in every nonnegative degree.

Native dependencies are Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679` and Stacks at
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`. No Aglib compatibility namespace, new axiom or
factorization assumption is introduced. The bibliography retains implementation provenance
separately from the Stacks and Waldhausen theorem citations.

## Boundary

This item closes relative bounded-above flat factorization, App2 and the connective
flat-to-perfect inclusion comparison. Arbitrary morphism pullback on bounded-flat objects,
all-perfect transport, supported/relative comparisons and the final open-pair localization
naturality remain separate items. It does not assert Quillen Q/S comparison, a new
Gillet-Waldhausen theorem, Thomason-Trobaugh 5.1 image-cover, or Bass 7.4 conclusions.
