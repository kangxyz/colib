# Native scalar cofiber and based-additivity square

## Mathematical target

COL-0303 specializes the full two-parameter based-additivity square to the
literal identity-to-scalar map of cofibration sequences. The source is the
identity-to-identity-to-chosen-zero sequence. The target is the original scalar
cylinder, followed by its literal signed scalar cone. The vertical components
are identity, the actual first factor, and zero-to-acyclic-inclusion whiskered
by the actual scalar-cone functor.

The hypotheses are an arbitrary open immersion `j : U ⟶ X`, a section
`r : Γ(X, top)`, a unit `q : Γ(U, top)ˣ`, and the equality `j.appTop r = q`.
The section need not be regular or invertible on X.

## Native objects and proof obligations

The objects are the existing full subcategory cut out by
`RingedSpace.IsPerfectComplex`; no alternate perfectness predicate is defined.
The fine Waldhausen structure is `RingedSpace.perfectComplexesWaldhausen`:
ambient monomorphisms and genuine quasi-isomorphisms. The coarse structure is
`perfectOpenWeakWaldhausen`, using actual degreewise restriction.

An ambient monomorphism between perfect complexes has perfect cokernel by the
native short-exact third-vertex result. This proves that inherited admissible
monomorphisms are precisely the existing ambient monomorphisms, without
replacing the Waldhausen structure. Exactness of the original middle and cone
functors follows from their actual ambient short exact sequences. The quotient
functor's exactness proves the relative cofibration condition.

The scalar middle object is `Cone(id) ⊞ K`. The original first factor and
projection compose to multiplication by r. The projection is already a fine
quasi-isomorphism. The quotient is `quotientToCone`, including the actual sign
isomorphism from `Cone(-r)` to `Cone(r)`. The native categorical cofiber is
identified with this cone by the original quotient square, not by an arbitrary
isomorphism. Acyclic support follows from the specified forward unit after
restriction.

## Complete square and boundaries

The square's two transformation faces retain the whole identity and scalar
based-additivity paths. Its additivity-zero face retains the whole rebased
inclusion cylinder on first-half restriction. Its additivity-one face retains
the whole quotient-first normalized zero-to-cone plus identity cylinder. The
entire two-time chosen-zero surface is constant. Every face theorem quantifies
over every spatial point and its remaining interval parameter.

The supplied same-degree K-maps evaluate on the original cone object in degree
zero. This contribution does not identify the connecting boundary, perform
projection/null alignment, establish fine-open localization, or assert a sign
for the Laurent/Bass boundary.

## Source correspondence and ownership

Implementation source is Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `AlgebraicGeometry/PerfectComplexes/ScalarCofiber.lean`: actual cofiber,
  signed quotient comparison, acyclic isomorphism and object class.
- `ScalarConeFunctor.lean`: actual fine/support/acyclic exact functors and K-maps.
- `ScalarCofiberFunctor.lean`: original middle and signed quotient sequence,
  including the relative cofibration proof.
- `ScalarCofiberPrism.lean:38-93`: original object-level factorization inputs.
- `ScalarCofiberSequenceMap.lean:34-86`: actual identity-to-scalar map.
- `ScalarCofiberAdditivitySquare.lean:34-182`: full square, four whole faces
  and chosen-zero surface.
- `Waldhausen/Additivity/IdentitySequence.lean`: the general chosen-zero
  identity sequence, unchanged.

The missing cone-square quasi-isomorphism lemma is adapted from
`Aglib/Algebra/Homology/MappingCone/WeakMap.lean` at revision
`e83191c34d63c2bfc15a57634cc46a8837d1fe51` (source SHA-256
`336476d0843055ffb1fc1b62c31cc9c8747a2bb020892e768f572a412b254e12`). Its
short-exact extension proof is reused from Colib, and its imports are native
Mathlib and Colib only.

Geometric functors and actual cofibers belong to `AlgebraicGeometry/Modules`.
K-maps and continuous additivity squares belong to `AlgebraicGeometry/KTheory`.
The general identity sequence stays at the existing K-theory owner of the
chosen-zero functor. No Aglib or Quillen module is imported.

Author source comparison, local Lean compilation, remote lint/axiom audit,
and independent mathematical review remain distinct evidence.
