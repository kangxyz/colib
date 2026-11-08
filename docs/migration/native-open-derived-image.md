# Native open-derived image and strict incoming factorization

## Exact mathematical scope

The source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The implementation uses Mathlib cochain complexes, homotopies, mapping cocones,
derived localization and `ObjectProperty.FullSubcategory`, together with the pinned
Stacks predicate `RingedSpace.IsPerfectComplex`. No Aglib predicate, category,
adapter or production import remains in this contribution.

The honest image consists of actual complexes derived-isomorphic to restrictions
of global native perfect complexes. Its full subcategory has one wrapper around
the original complex and retains every original chain map. Membership implies
native perfectness. Derived-isomorphism invariance, quasi-isomorphism invariance
and an actual cospan of quasi-isomorphisms require no geometric roof hypothesis.

`HasDerivedRoofs j` states a specific remaining geometric input: a derived arrow
between the restrictions of two global perfect complexes is represented by two
actual global chain maps from a native perfect source, with the denominator a
quasi-isomorphism after restriction. This is a proposition describing geometric
roofs, not a structure assuming approximation, closure or localization.

Given that input, a global mapping cone represents the third vertex of the actual
open distinguished triangle. Rotation gives the other two vertices. Applying these
facts to the actual short-exact triangle proves extension, quotient and kernel
closure without replacing any endpoint. The image inherits ambient monomorphisms
and quasi-isomorphisms; inclusion and actual restriction corestriction are exact.

The strict incoming factorization follows the original two-pullback proof:

1. A genuine common post-quasi-isomorphism turns two derived equalities into two
   actual homotopies. Derived equality is never treated as a strict square.
2. The source is the literal homotopy pullback of the global numerator and the
   identity of the original source target. Its first projection is a
   quasi-isomorphism, proving native perfectness of this actual source.
3. The target is the literal homotopy pullback of the common-target arrows.
   Its two lifts satisfy the original strict chain-map equations. Both required
   projections are degreewise split epimorphisms.
4. Native first-vertex perfectness and honest-image short-exact kernel closure
   prove membership of the actual categorical kernels of those projections.

This is incoming dual factorization. No strict outgoing App2 is claimed.

## Native ownership and source crosswalk

| Original source | Native owner and covered result |
| --- | --- |
| `Quillen/Aglib/Algebra/Homology/DerivedCategory/EqualityDenominators.lean` | `Colib/Algebra/Homology/DerivedCategory/EqualityDenominators.lean`: one and two actual post-denominator homotopies in any abelian category |
| `Quillen/Aglib/Algebra/Homology/HomotopyPullback/{Basic,QuasiIso}.lean` | Corresponding `Colib/Algebra/Homology/HomotopyPullback` modules: literal mapping-cocone projections, lifts, strict equations, degreewise sections and quasi-isomorphism gluing |
| `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Basic.lean` | `Colib/AlgebraicGeometry/Modules/OpenDerivedImage/Basic.lean`: honest image, full category, corestriction and weak cospans |
| The same original family, `Roofs.lean` | Native `OpenDerivedImage/Roofs.lean`: exact geometric roof proposition and its genuine common-target homotopy consequences |
| The same original family, `Closure.lean` | Native `OpenDerivedImage/Closure.lean`: three distinguished-triangle and three actual short-exact endpoint closures, conditional on the specified roofs |
| The same original family, `Exact.lean`, and `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Structure.lean` | Native `OpenDerivedImage/Exact.lean`: actual full subcategory, ambient Mono/QuasiIso structure and exact inclusion/corestriction |
| The same original Aglib family, `DualFactorization.lean` | Native `OpenDerivedImage/DualFactorization.lean`: both strict incoming equations, degreewise split epis and actual kernel membership |
| `Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean:25-36` | `Colib/AlgebraicGeometry/KTheory/PerfectOpenRestrictionRange.lean`: the actual coarse and fine restriction K₀ maps have equal ranges |

`PerfectKernel.lean` is the independently owned COL-0311 dependency. Its native
Stacks first-vertex and shift lemmas are reused rather than reintroducing a
second perfectness model. The source-pullback perfectness proof uses its actual
quasi-isomorphic first projection; no separate global strict model is required.

The source-level full subcategory is flattened from the outset. This does not
claim the original nested-category flattening or its K-equivalence has been
separately migrated.

## Remaining geometric and K-theoretic work

The generic chain-map representative bridge from COL-0307 does not itself prove
geometric roof existence. The qcqs roof and complement candidates still require
the separately owned native Stacks compact/perfect dependency closure and actual
compilation. Once those geometric theorems are established, they must instantiate
the precise `HasDerivedRoofs` proposition above, with the original hypotheses.

COL-0311 supplies the opposite exact structures and coherent endpoint comparison.
In this integrated topic, COL-0314 combines them with the image's proved closure
and incoming factorization to construct actual image application instances and a
relative corestriction K-equivalence. Its exact HasDerivedRoofs input remains
explicit. Those application theorems have their separate COL-0314 owner; neither
item proves global density, complement/cofinality, the fine-open K-equivalence or
the final localization sequence.

The K₀ range equality is unconditional for every open immersion. It follows from
the proved surjectivity onto the relative coarse group and the actual restriction
factorization. Its common range need not be all of perfect K₀ of the open.

No extra Noetherian, regular, separated or resolution-property hypothesis is added.
No globally strictly perfect representative or K-projectivity is used. Compilation,
author source comparison, independent mathematical review and remote lint/axiom
checks are distinct verification categories.
