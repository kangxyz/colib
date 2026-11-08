# Actual algebraic simplices and ordinary A¹-invariant singular chains

This topic constructs algebraic simplices and ordinary singular chains on the existing smooth category, then proves that the original restriction along `U × Δ¹ → U` is a chain homotopy equivalence. The interval is the actual barycentric affine line, not an assumed abstract interval.

## Final mathematical statement

Let `R` be any commutative ring, `U` a smooth, separated, finite-type scheme over `Spec R`, and `P` an ordinary presheaf on this category with values in a preadditive category `A`. The evaluated chain complex of the existing `AlgebraicSimplex.singularChainsFunctor R` admits a native `HomotopyEquiv` under projection `U × Δ¹ → U`. Its forward map is exactly the original contravariant projection restriction and its inverse is exactly the original barycentric vertex-zero restriction.

If `A` has homology, these original maps induce mutually inverse isomorphisms in every homology degree. Thus the objectwise ordinary singular-homology presheaves are A¹-invariant. Neither `P` nor its values are assumed homotopy invariant. There is no field, reducedness, affineness of `U`, or sheaf hypothesis. The coefficient category's object and morphism universes are independent of the base-ring universe.

## Construction and native reuse

1. `Colib/RingTheory/AlgebraicSimplex/{Basic,Polynomial,CoefficientPushout}.lean` uses the single barycentric quotient ring, its finite-ordinal maps, its polynomial chart, and the actual coefficient pushout for arbitrary ring homomorphisms.
2. `Colib/AlgebraicGeometry/Simplex/{AlgebraicSimplexScheme,BaseChange}.lean` takes the actual spectra and proves the literal coefficient square Cartesian. `Sites/Smooth/Products.lean` and `Sites/Smooth/Simplex/Basic.lean` provide the actual relative products and smooth cosimplicial simplex.
3. `Simplex/OrdinaryChains.lean` applies Mathlib's native `alternatingFaceMapComplex` directly to the presheaves `P(U × Δⁿ)`. The differential, restrictions, and coefficient maps are the original ones. The native normalized Moore comparison is exercised in the consumers, not reimplemented as a new complex.
4. `AlgebraicTopology/SimplexCategory/Prism.lean` reuses Mathlib's `toMk₁`, rather than copying the source's separate cut map. `Simplex/Prism.lean` proves the actual geometric prism identities, and `EndpointHomotopy.lean` applies native `SimplicialObject.Homotopy.toChainHomotopy`. Mathlib's evaluation/alternating-face interchange isomorphism retains the original chain presheaf and restriction maps.
5. `Simplex/IntervalMultiplication.lean` uses the native Γ–Spec adjunction and the existing quotient's universal property to construct actual multiplication with coordinates `(1 − s·t, s·t)`. This works without an affineness assumption on the source. Its actual contraction on `(U × Δ¹) × Δ¹` has the zero-section composite and identity as its two endpoints.
6. `Simplex/HomotopyInvariance.lean` combines this contraction with the prism to construct the native `HomotopyEquiv`, native homology isomorphisms, and the `IsIso` assertion for the original projection-induced homology map.

## Endpoint and sign conventions

Barycentric vertex zero is `(t₀,t₁)=(1,0)` and vertex one is `(0,1)`. Multiplication uses `t₁`, so vertex zero is absorbing and vertex one is the unit. The existing polynomial chart retains `t₀`, whose values at these vertices are respectively one and zero. No endpoint is silently exchanged. The prism chain homotopy retains the native negative alternating sum convention.

## References and source correspondence

The software source is [kangxyz/motivic at a6805c4a87cdfd7717dd7a94039246a167f15380](https://github.com/kangxyz/motivic/tree/a6805c4a87cdfd7717dd7a94039246a167f15380). The actual simplex, ordinary-chain and prism source correspondence is recorded in the accompanying machine ledger. The source's generic interval parameters and duplicate singular-complex carriers are not copied.

The direct published references are Mazza–Voevodsky–Weibel, *Lecture Notes on Motivic Cohomology* (2006): the simplex paragraph and Definition 2.14, printed p. 16; Lemma 2.16 and its multiplication proof, p. 17; Definition 2.17 and Lemma 2.18, pp. 17–18; and Corollary 2.19, p. 18. The implementation generalizes the ordinary argument to commutative base rings and preadditive coefficients and keeps the stronger chain-level homotopy-equivalence data. Corollary 2.19 itself states homology-presheaf invariance. This is not a migration claim for the covariant representable-presheaf-with-transfers theorem in Corollary 2.24.

## Scope boundary

No category of finite correspondences, transfer action, transfer-preserving sheafification, transfer-valued Suslin complex, Nisnevich cohomology-invariance theorem, or motivic-derived comparison is assumed or asserted here. Those remain separate tasks. The topology on the smooth category is not needed for this ordinary-presheaf theorem.

## Validation boundary

All thirteen production modules and forty-eight assertions in four consumer files passed
native Lean 4.35 on their final registered source bytes. The 25 public Library bindings
use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` under ordinary
Lean axiom inspection. The official Mathlib root-generator check reported no update necessary.
Pinned provider artifacts were reused; no provider proof was rebuilt.

The Library registers the complete topic as COL-0318 (simplices and coefficient change),
COL-0319 (ordinary chains), and COL-0320 (prism and A¹ invariance). These are source-bound
local checks and author source comparisons, not independent mathematical review or the
full production axiom auditor. Full-root build, declaration lint and exact-commit CI remain
pending. No main merge is claimed.

## CI normalization repair

The first complete CI passed the full production build, all consumers and the
production axiom audit, but found three ordinary-topic simp-normal-form issues.
The repair retains the identity-restriction theorem without its redundant simp
registration and writes the two multiplication-coordinate formulas with explicit
native pullback and spectrum parameters. Their original statement forms still
accept the repaired theorems directly. No linter or mathematical hypothesis changed.

The two affected production modules and their ten-example consumer passed native
recompilation. Native simpNF inspected all 299 public declarations in the thirteen
owned production modules, including the 82 remaining active simp rules, with no
failures. Actual compiled bindings and precise references for all three Library
items were checked, as were the 25 bound declarations' standard axiom closures.
These targeted checks are not the full repaired-tree CI, which remains pending.
