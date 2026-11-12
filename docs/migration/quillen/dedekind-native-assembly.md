# Native Dedekind residue assembly

## Fixed source

`kangxyz/quillen-k-theory`, commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`,
`Quillen/GTheory/Dedekind/ResidueFieldAssembly.lean` and `Localization.lean`.

## Mathematical boundary

The intended endpoint identifies the direct sum of the positive-degree native
residue-field G-groups with the original torsion-supported G-group. Its forward
map is the finite sum of the actual scalar-restriction pushforwards. The
quotient-ring and native residue-field comparison uses their canonical algebra
map. Degree zero is not included in the direct-sum equivalence.

The residue-coordinate localization statements retain the original connecting
homomorphism. Finite G1-family lifting retains the explicit injectivity
hypothesis on the original generic G1 map. No unconditional arithmetic
surjectivity is inferred. Comparison with local-DVR and scheme principal-open
boundaries remains a separate endpoint.

## Native definitions

- Mathlib's `FGModuleCat`, `Ideal.primaryComponent`, quotient module action and
  `SmallModel` supply the actual objects.
- `FGModuleCat.localizationTorsionProperty` and `FGModuleCat.Localization.supported`
  are the existing large and small scalar-localization kernels.
- All exact structures are the native `abelianExactStructure` on the actual
  category. No compatibility category, adapter or alternate G-theory model is introduced.
- The primary-category equivalence retains the original finite-support coordinate
  functors, original submodule inclusions and canonical direct-sum summation.

Weibel, *The K-book*, Chapter V, 6.6–6.7.3 provides the classical localization
context. The implementation source specifies the actual finite-module maps and
zero normalizations; citation alone is not a sign comparison.

## Verification

The complete local proof closure and all three original ring-theoretic consumers
compile: the empty height-one spectrum of a field, generic G₂ injectivity for the
integers, and lower G₂ vanishing over F₂, F₃ and F₅. Tests use modern public module
imports, so they depend only on the published interfaces. The final incremental
build completed all 4775 dependency jobs.

The same-category `smallKUniverseEquiv` preserves the original Q-map and its
canonical zero-object path. It supplies lower finite-field G₂ vanishing and the
finite-residue generic injectivity theorem without changing module-carrier
categories. Neither this theorem nor the conditional G₁-family lifting theorem
asserts an arithmetic generic G₁ injectivity result.

The 133 Python tests, native source text lint, catalog validation, generated-root
check and whitespace check pass. Whole-library declaration lint and the independent
production axiom audit remain integration checks. Source correspondence is
`author_checked`; it is not an independent mathematical review.

## Remaining original consumers

The coherent-scheme pullback clauses of `FiniteResidueLocalization`, the
`LocalDvrSupport` and `LocalDvrComparison` constructions,
`LocalDvrBoundaryNaturality`, and `PrincipalDvrBoundaryComparison` remain separate
migration endpoints. In particular this contribution does not identify native
residue coordinates with local-DVR or scheme principal-open boundaries.
