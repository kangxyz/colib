# Native Matsumoto injectivity and the canonical kernel equivalence

## Source and scope

This continuation adapts the full dependency closure of
`Quillen/Algebra/Group/StableSteinberg/Matsumoto/Injectivity.lean` from pinned
Quillen revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`, reusing the native
stable Steinberg presentation and its existing map to the elementary group.
The source closure consists of 38 Quillen modules. Its previously migrated
stable matrix, Steinberg and symbol foundations are not recreated.

Over an infinite field, diagonal covariance with a unit different from one
gives the two commutator relations needed for injectivity. Over finite fields
injectivity follows from the vanishing of native Milnor K₂. Surjectivity comes
from the all-rank kernel-generation proof over arbitrary fields.

## Native objects and complete construction

The coefficient group is Stacks' `MilnorKTheory F 2`, and every ordered pair is
literally `milnorKTupleSymbol ![a, b]`. The coefficient identities are derived
inside the native homogeneous subgroup from Stacks' ring-symbol identities.
There is no secondary Milnor quotient or transport adapter.

The native `Matrix.GeneralLinearGroup`, `Equiv.Perm`, `SemidirectProduct`,
`PresentedGroup` and existing `Matrix.GeneralLinearGroup.elementary` provide
the matrix and group foundations. The construction proceeds through:

1. The explicit type-A cocycle torus and its faithful Milnor coefficient.
2. Actual reflection and ascent/descent Weyl permutations, the generated
   normalizer, its signed matrix section, and its exact coefficient kernel.
3. Native matrix Bruhat coordinates, decomposition, uniqueness, root updates,
   opposite-root transformations and reduction.
4. The actual left and right Bruhat state actions. The torus and Weyl
   transporters prove the nondegenerate crossing and diamond identities.
5. The genuine Bruhat left group, faithful coefficient translations, matrix
   projection, and central kernel. None of these is a supplied detector input.
6. Additive root sections, diagonal covariance, and the original Steinberg
   root relations in matrix dimension at least five. A balanced diagonal
   scales by `q ≠ 1`. For a root parameter `a`, write `qt = a + t` with
   `t = a / (q - 1)`. The lifted commutator and the specified output root
   have the same matrix image, so their difference is fixed by conjugation.
   The comparison at `t` and `qt` gives the original root relation at `a`.
7. The eventual-product representation of the original finite-rank-labelled
   Steinberg presentation. Its original 01/02 commutator has the positive
   native coefficient mark. The fixed eventual cutoff is five; no
   stabilization maps between finite detector state sets are assumed.

The matrix foundations live under `Colib/LinearAlgebra/Matrix/Bruhat`, generic
central-lift calculations under `Colib/GroupTheory/MonoidHom`, and the actual
Matsumoto construction under `Colib/GroupTheory/Steinberg/Matsumoto`.
The construction retains the native objects, exact ranks, ordered coefficients
and signs.

## Canonical endpoint

`StableSteinberg.milnorToKernel_injective` proves injectivity of the canonical
map over every field.
`StableSteinberg.milnorKernelEquiv` combines it with actual surjectivity:

- Its additive homomorphism is definitionally `milnorToKernel F`.
- An ordered symbol maps to `Additive.ofMul (torusDefectKernel a b)`.
- The inverse sends that actual kernel word back to the same ordered symbol.
- The equivalence commutes with the existing field-change maps, including
  independent source and target universes.

These endpoints live in `Colib/RingTheory/KTheory/MilnorK/Steinberg/Equivalence.lean`.

## Relation to the Quillen comparison

This theorem identifies native Milnor K₂ with the actual stable Steinberg
kernel. The separate [stable-fiber proof](field-k2-stable-fiber.md) establishes
perfectness and bijectivity of the original kernel-to-Quillen map, with the
original right-projective and upper finite-module comparisons. The
[final comparison source](field-k2-comparison.md) combines these results using
the same forward composite, proves both field-change directions and retains
the negative of the positive inverse over every field.
Earlier characteristic-zero endpoints passed focused native checks within their recorded
source scope. The separate original whole-library checks passed for published
Lean 4.35 commit `0fd43f0253d6ff441fbc3e82420a0573ad694310` in
[CI run 42373233801](https://github.com/kangxyz/colib/actions/runs/42373233801).
That exact-commit pass does not certify later descendants.
