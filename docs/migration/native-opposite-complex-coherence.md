# Native opposite complex cylinders

## Exact source and retained scope

The source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `Waldhausen/Duality/ExactCategory.lean` and `ComplexSubcategory.lean`: admissible
  epimorphism cofibrations on the literal opposite, actual pullback gluing, and
  zero-corner kernel/cokernel compatibility.
- `Aglib/CategoryTheory/ExactCategory/ZeroSquare.lean`: the two universal-property
  arguments identifying actual admissible zero-corner fiber and cofiber squares.
- `Aglib/Algebra/Homology/CochainComplex/OppositeSubcategory.lean` and
  `OppositeQuasiIsoCompatibility.lean`: actual degree reversal, negative shift,
  extension and cone closure, and quasi-isomorphism preservation/reflection.
- `Waldhausen/Fibration/Rows/ComplexRelativeJoint.lean`, `EquivalenceJoint.lean`,
  `OppositeComplexJoint.lean`, `OppositeComplexJointInclusion.lean` and
  `OppositeComplexJointMap.lean`: original joint arrows, counit endpoint maps,
  biproduct and identity-cone comparisons, full naturality and the three endpoint
  equations in each orientation.
- `AlgebraicGeometry/PerfectComplexes/OppositeJointData.lean`: the perfect-complex
  structural application. The strict-to-perfect application is not claimed here.

General constructions live in `CategoryTheory/Waldhausen`; opposite homological
comparisons live in `Algebra/Homology`; the native perfect applications live in
`AlgebraicGeometry/Modules`. No Quillen or Aglib module is imported.

The mathematical objects remain the actual cochain complexes and full subcategories.
The opposite functor is Mathlib's `CochainComplex.opEquivalence`, including its genuine
unit/counit and its literal component maps. Quasi-isomorphism preservation is proved
by identifying the native short-complex maps at the reversed indices and using
Mathlib's opposite-homology theorem. No auxiliary representation category is introduced.

## Native perfect application

`PerfectKernel` obtains first-vertex perfectness from Stacks 08CR applied to the native
derived triangle of the actual short exact sequence, then uses native representative
independence (08CN). The actual kernel of an epimorphism between perfect complexes
is therefore perfect. This proves admissible epimorphisms are exactly ambient epis;
it is not an identification by name. Existing ambient-monomorphism cofibrations stay
unchanged, using the established cokernel-perfectness comparison in `PerfectExactFunctor`.

The existing `perfectComplexesRestrictOpenImmersion` is retained. Exactness follows
from the native exact additive degreewise restriction functor. Its joint comparison
is constructed from the actual additive biproduct and cone maps. Full naturality,
both endpoints and the projection are proved, with all three inverse equations needed
by the opposite weak-arrow construction. `PerfectOppositeWeakArrow` then constructs
the actual opposite weak-arrow joint data using COL-0310, supplying every component,
exactness and coherence input with these proved native results. The category still
stores actual quasi-isomorphisms and strictly commuting squares of chain maps.
There is no remaining scheme-specific cylinder-compatibility assumption.
No qcqs localization or K-equivalence is asserted.

## Strict predicate boundary

The exact Aglib pin in Quillen's manifest is
`2c34f185fa859e862661f939cd216b07bcccfb26`. Its
[`Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Strict.lean)
has blob `69091ab6f4866a97717ab2e0c30a31249a72c4bf` and SHA-256
`4cfd15796c6de0759e0b370e62b81d300153082084c7a0f0986eb04e6fd08525`.
Lines 44-50 define strict perfection as global term bounds and finite local freeness
in each degree. Lines 80-100 prove extension closure from degreewise short exactness
and the locally free extension theorem, without an affine hypothesis.

At the pinned Stacks revision `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`,
`StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/FiniteFreeSummands.lean`
lines 209-214 define a global retract of a finite free sheaf. Lines 298-305 use
this stronger termwise property in `StrictlyPerfect.IsStrictlyPerfect`, explicitly
cited as an SGA special case. It is not substituted for the source's finite-locally-free
predicate. The strict inclusion instance uses the native bounded finite-locally-free predicate
and its actual local closure/comparison proofs. COL-0313 supplies that instance in
this integrated topic; it is outside COL-0311's owned mathematical scope.

## Dependency direction and verification

The two unused imports `Colib.KTheory.Waldhausen.Map` and
`Colib.CategoryTheory.Waldhausen.SMap` are removed from the existing
`ComplexSubcategory` module. Its four public declarations are unchanged and purely
structural. No declaration is duplicated or forwarded. The 75 affected existing
consumers are computed from the full source graph and genuinely re-elaborated, even
when an intermediate module retains the same artifact bytes. This checks loss of
transitive K-theory API visibility, not just content-addressed reuse. Unrelated
dependencies remain reused with their exact source and direct artifact hashes.

At component freeze, COL-0306, COL-0308, COL-0309 and COL-0310 were immutable reused
dependencies, with ownership separate from this item, over the exact
d67b69cc1289c326508f481f8aca2758946c7f19 baseline. The integrated topic instead starts
from published main 8fc02d4a4fdd9b82b610166143b75310184b624e and preserves its later
generic-source formatting repair. Shared root, chapter and migration-index changes
are now included. Fresh compilation, reused artifacts, source correspondence and
independent mathematical review remain separate evidence; the exact integration
receipts record their scope.

The final direct-import check uses Lean 4.35's own `Elab.parseImports` and
`headerToImports`, including multiline imports. An earlier generic producer receipt
omitted one multiline `NestedRestriction` import. This task reuses the independently
fresh, complete producer receipt after checking its exact source and all direct
artifact families. The old receipt is not retroactively enlarged. The corrected
producer's five output hashes agree with the prior outputs.
