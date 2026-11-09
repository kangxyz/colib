# Actual affine-section global and Laurent units

## Source and native choices

Original implementation: Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native mathematical baseline: Colib `bd838f93b5767ee58554b8c7374fd6239463ec20`.
The later main `79879cea5ef4ff66fe087945b420af8cabc47d79` changes infrastructure only.
Mathlib is pinned at `56a005855ea17e0b0958f73ec801ae140b0a1679`, Stacks at
`5ed82d14634e8d9576bb844c7bd4e3da66d450e7`, and Lean at 4.35.0.

The scalar is the native `Stacks.RegularSequence.globalSmulCenter`. Its complex action is the
existing `complexGlobalUnitIso`. The perfect category is the actual full subcategory of native
perfect complexes with a global upper degree bound and termwise sheaf flatness. Sections,
identity evaluation, every-arrow evaluation, and coefficient reindexing are the existing native
bounded-above-flat affine constructions. The Laurent unit is the existing `laurentCoordinate`.
No Aglib import, compatibility bundle or replacement model is introduced.

## Correspondence

All original paths below are relative to `Quillen/` at the revision above.

- `Aglib/AlgebraicGeometry/Modules/Scalar/Pullback.lean:22-54`: native componentwise
  pushforward compatibility and injectivity of the actual pullback-pushforward adjunction.
  This proves compatibility for arbitrary scheme morphisms, without flatness assumptions.
- `Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/GlobalUnit.lean:25-28`
  and `GlobalUnitPullback.lean:22-36`: actual fully faithful restriction and degreewise
  pullback compatibility. Both forward and inverse terms use the native sheaf scalar.
- `Aglib/CategoryTheory/Functor/IdentityAutomorphism.lean:20-74`: the small categorical
  lifting/evaluation infrastructure, now under `CategoryTheory.Functor.IdentityAutomorphism`.
- `Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/SectionUnitAction.lean:28-59`:
  lift through actual fully faithful evaluation, with both component formulas.
- `Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/SectionUnitNaturality.lean:31-99`:
  actual evaluation-transition cancellation proves every-arrow scalar identification.
  Faithfulness at the new base ring then proves strict coefficient naturality.
- `AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentUnit.lean:33-95`: the actual
  forward Laurent unit, its arbitrary-arrow evaluation, strict coefficient naturality,
  and independent forward/inverse degree formulas.

The new native Laurent coordinate-image proof uses `ΓSpecIso_inv_naturality` directly.
Its inverse formula follows by uniqueness of the inverse and `T 1 * T (-1) = 1`, rather
than unfolding a legacy unit implementation. Coefficient change is the native additive
monoid-algebra ring map. Whole-isomorphism and inverse coefficient laws follow from
isomorphism extensionality applied to the proved forward natural-transformation equality.

## Scope and boundaries

COL-0359 is a categorical action/naturality milestone. It is independent of the unfinished
COL-0358 prespectrum relative coherence. It does not assert a supported action, a
prespectrum self-homotopy, a Bass seed, negative localization, or TT 7.4.

The consumers retain arbitrary rings, an arbitrary section, arbitrary Under-arrow,
arbitrary coefficient morphisms (including nonflat morphisms), arbitrary degree,
both global-unit directions, arbitrary Laurent target morphisms, both Laurent monomials,
whole whiskered natural-isomorphism equality, identity evaluation, and both reindexing
and geometric-transition evaluation routes. These are not zero-only or K-group-only checks.

## Validation boundary

New compilation uses the pinned local Lean, `-j1 -M6000`, `autoImplicit=false`,
`warningAsError=true`, and production `weak.linter.mathlibStandardSet=true`.
All proof builds serialize on the existing lock and use complete standard native artifact maps.
Historical imported providers retain their original receipts; in particular PolynomialLaurent's
producer used the first two options, not the later weak linter option. No historical receipt is
upgraded to a new build claim. Failed attempts are retained and never selected as providers.
Focused local compilation is distinct from independent review, whole-library validation,
remote lint and CI. Integration and publication belong to the coordinator.

Whole-root validation has a separate explicit input boundary: the old-provider selection is
retained, supplemented by 811 already standard-admitted whole bundles, 17 non-root Telescope
reference-repair bundles, and this topic's seven new production bundles. The three repaired
Telescope source attributes match the exact current-main source; the older root artifact is
not reused as the new root. This root-only supplement does not retroactively change the
provider selection of the seven leaf compilations.
