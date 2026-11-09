# Native perfect restriction roofs and complements

## Source crosswalk

The original revision is Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/Roofs.lean`
defines `HasDerivedRoofs`: for two global locally perfect complexes and a morphism
between their restricted derived objects, there are actual maps from a globally
locally perfect complex, the first invertible after restriction, satisfying the
original derived equation. `OpenDerivedImage/GlobalRoofs.lean` proves
`qcqs_hasDerivedRoofs` for every compact open immersion into a qcqs scheme.

`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalDensity.lean`
proves `locallyPerfect_exists_global_perfect_complement` and its arbitrary-open-
immersion version. These produce actual complexes P on X and C on U with a
specified derived isomorphism between the original restriction of P and E ⊞ C.
`OpenDerivedImage/GlobalComplements.lean` consumes that result to give complement
membership and chosen coproduct density. The present scope reaches the actual
native complex complement, not the entire later dense Waldhausen interface.

## Native proof

All external mathematics is at Stacks revision
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7` and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

1. A native perfect complex K determines a perfect object QK with quasi-coherent
   cohomology. Package QK and QE as objects of the existing D_QCoh full subcategory.
2. `Stacks.Duality.SupportedGeneration.kernelDetected` supplies compact kernel
   generators for restriction along the quasi-compact open immersion.
3. `Stacks.Duality.isCompactObject_of_isPerfect`, from `CompactPerfect.lean`, makes
   QK compact. `CategoryTheory.Pretriangulated.exists_roof` gives a compact roof
   source and its actual derived numerator and denominator. The target QE need
   not be compact or perfect.
4. `Stacks.Duality.isPerfect_of_isCompactObject` identifies the resulting source
   as native perfect. Unpack its definition to choose an actual native perfect
   complex and transport both outgoing maps through its representing isomorphism.
5. Apply Mathlib `DerivedCategory.right_fac` twice. Their quasi-isomorphic
   denominators compose, giving a common actual complex and two actual chain maps.
   Stacks native quasi-isomorphism invariance preserves perfectness. The natural
   isomorphism `mapDerivedCategoryFactors` transfers the restricted roof equation
   to the literal degreewise restriction; invertibility of its denominator is
   equivalent to quasi-isomorphism of that restricted chain map.
6. The final chain-map equation passes to any chosen derived-category model on U
   through Mathlib `Localization.uniq` and `compUniqFunctor`. The actual complexes,
   chain maps, original morphism and quasi-isomorphism property remain unchanged.
7. For complements, compact kernel generation and compact generation of D_QCoh
   feed `exists_isCompactObject_iso_biprod_shift`. This yields j*Q ≅ P ⊞ P[1].
   The compact/perfect comparison supplies an actual global native perfect
   representative. Choose a native perfect representative C of P[1] and use the
   canonical localization/biproduct comparison to obtain Q(j*R) ≅ Q(P ⊞ C).
   The first injection and projection also give the restriction retract (09IQ).

The source references are Stacks [08EH](https://stacks.math.columbia.edu/tag/08EH)
(first roof assertion, with the qcqs argument supplied by compact generation),
[0A9A](https://stacks.math.columbia.edu/tag/0A9A) (compact kernel generation),
[09M1](https://stacks.math.columbia.edu/tag/09M1) (compact/perfect comparison),
[08EK](https://stacks.math.columbia.edu/tag/08EK) (compact lifting construction),
[09IQ](https://stacks.math.columbia.edu/tag/09IQ) (restriction retract), and
[08CN](https://stacks.math.columbia.edu/tag/08CN) (native perfect representatives).

## Scope boundaries

A roof is not a strict factorization of an outgoing chain map into its fixed
chain-complex target. No strict App2 statement follows here. Nor does a perfect
complement alone prove extension and quotient closure of a dense Waldhausen
subcategory, cofinality, fine-open localization, or a nonconnective result.
The tensor/supported-source clause of 08EH is not asserted.

## Native honest-image inputs

`AlgebraicGeometry.Scheme.Modules.OpenDerivedImage.hasDerivedRoofs_of_qcqs` and
`hasPerfectComplements_of_qcqs` apply the actual geometry theorems to the existing
honest-image interfaces. Neither property is assumed. The roof retains the original
fixed target complexes and the original restricted derived morphism in any chosen
open derived-category model.

These geometric results are inputs to connective localization. TT Section 5.1 uses
the K-zero image cover, whereas TT Section 7.4 concerns the Bass nonconnective fiber
sequence. Those conclusions and their respective naturality statements belong to
separate mathematical items; they are not claimed merely by roofs and complements.
