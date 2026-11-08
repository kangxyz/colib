# Native honest-image cofinality and fine restriction endpoints

COL-0315 works with the existing full category of native Stacks perfect chain complexes,
its ambient monomorphisms and quasi-isomorphisms, and the existing relative-open K-map.
There is no Aglib compatibility category or substitute perfectness predicate.

## Exact geometric boundary

For an arbitrary open immersion `j : U ⟶ X` and arbitrary chosen derived-category model on U,
two geometric inputs are explicit:

1. `OpenDerivedImage.HasDerivedRoofs j`, the existing global-perfect-model morphism-roof property.
2. `OpenDerivedImage.HasPerfectComplements j`: for every actual native perfect complex P on U,
   there are actual native perfect complexes R on X and C on U with
   `Q(restrict R) ≅ Q(P ⊞ C)`.

The second input is exactly the actual-complex conclusion intended by COL-0307's geometric
complement theorem. Its qcqs existence is not proved or imported here. In the future that
geometric theorem must have compact X, quasi-separated X, compact U and an open immersion,
without adding Noetherian, regular, separated or resolution-property assumptions. This
conditional theorem adds none of those assumptions and does not claim to have discharged them.

## Constructed categorical inputs

Native finite-product closure and preadditivity supply actual binary coproducts in the original
perfect category. An explicit binary cofan and its genuine colimit comparison identify each
chosen categorical coproduct with the actual complex biproduct appearing in the complement
statement. This is a proved isomorphism, not a definitional equality of independent choices.

For an original perfect cofibration and zero pushout, the exact ambient inclusion supplies its
actual pushout. The zero vertex constructs a cokernel universal property on the original
injection and quotient, hence the original short exact sequence. Honest-image extension and
quotient closure then retain the original endpoints. Together with zero, quasi-isomorphism
invariance and actual complements this constructs all fields of `denseCofiberData`.

The dense full subcategory carries a redundant perfect wrapper. `flattenEquivalence` forgets
only that wrapper, preserving the original complexes, arrows and inclusion literally. Both
functors are exact. Their K-equivalence therefore intertwines the original inclusion K-map.
The actual native perfect fine joint cylinder and its existing second-endpoint section supply
all inputs of general-universe cofinality. No density, JointData, approximation property or
K-equivalence is assumed.

## Original maps and endpoint

The existing all-degree honest-image approximation equivalence factors the unchanged
`perfectOpenKRestrict`. Cofinality gives injectivity in every connective degree and bijectivity
in degree n + 1 for both the honest-image inclusion and that relative restriction.
`relativeKRestrictEquiv` has precisely the original positive restriction K-map as forward map.

`PerfectOpenKZeroImage` is the range of the original fine restriction from X, not the full
K-zero group of U. The existing unconditional coarse/fine range equality defines the literal
codomain-restricted map. `relativeKZeroImageEquiv` proves it bijective under the two geometric
inputs. Forgetting subgroup membership is definitionally the original degree-zero restriction.
The equality of the honest-image inclusion range with the fine restriction range needs only
the roof hypothesis, not complements.

This item does not assert ordinary outgoing App2, final qcqs localization, strict-to-perfect
K-equivalence, Q/S or Gillet-Waldhausen comparison, or a surjectivity theorem onto all K-zero of U.
No coarse boundary, signed-cone convention or Bass endpoint is changed.

## Pinned source correspondence

Implementation source: Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The accompanying source-correspondence evidence records exact verified line spans and hashes.

- `Quillen/Aglib/CategoryTheory/Abelian/ZeroPushout.lean`: actual zero pushout to original short exact sequence.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Complements.lean`: actual coproduct comparison.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Flatten.lean`: literal category equivalence.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Dense.lean` and `GlobalDense.lean`: dense closure, now with the precise unresolved native complement input.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Flatten.lean`: exact flattening and original inclusion cofinality.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KTheory.lean`: original relative restriction endpoints, with categorical inputs constructed.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/KZeroCover.lean:29-41`: only the actual inclusion-range clause, not covering-pair reflection.
- `Quillen/AlgebraicGeometry/PerfectComplexes/OpenKZeroImage.lean`: the actual fine restriction-image subgroup and literal codomain restriction.

Local compilation, exact-source correspondence, independent mathematical review and remote
lint/axiom/Library checks are distinct evidence. This note itself makes no claim that an
unrun validation stage has passed.
