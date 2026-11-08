# Native global-unit K-one and forward scalar restriction

## Exact scope

COL-0305 defines the fine class of the actual global-unit automorphism on the existing
native full subcategory of Stacks perfect complexes. It proves isomorphism invariance,
inversion and compatibility with the original canonically rebased fine restriction K-map.
The existing coarse restriction map then sends the independently defined forward scalar
class of COL-0304 to this independent fine unit class. No comparison is supplied as a
hypothesis or used as the definition of either class.

The generic data are an arbitrary open immersion `j : U → X`, a native perfect complex
`K`, a global section `r` on `X`, a unit `q` on `U`, and `j.appTop r = q`. There is no
quasi-compactness, quasi-separatedness, Noetherianity, regularity, nonzerodivisor or
nontriviality hypothesis. The actual structure-sheaf restriction isomorphism supplies
rank-one comparisons. The affine specialization is over every commutative ring, including
the zero ring. The relative specialization is over every scheme, not just affine bases.

The original source is Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native provider baseline for this work is scalar topic commit
`5eca54b0b939d2cd8ca2674c4bbd01e1f93528ab`, tree
`aa5a506976be5416e2b4a93fe4eea0c6746aeb1e`.

## Actual objects and proof route

- `Modules.PerfectGlobalUnit` proves equality of the existing native unit isomorphisms
  under inversion and literal restriction. The scalar action remains the existing
  `Stacks.RegularSequence.globalSmulCenter`, lifted degreewise.
- `KTheory.PerfectGlobalUnitKOne` defines the fine class using the existing
  `automorphismKOneClass`. Its inverse-prefix object-component normalization is retained.
  Inversion uses the native `Aut` wrapper through `asIso`; restriction uses the existing
  `KMap_automorphismKOneClass`, with its canonical chosen-zero rebase.
- `KTheory.PerfectScalarUnitComparison` applies existing weak-endomorphism K-map
  naturality to the actual coarse scalar arrow. The existing equality
  `perfectRestrict_scalar_eq_globalUnit` identifies its image with the native unit arrow.
  The rank-one formula uses `rankOnePerfectComplexRestrictIso`, not a matrix presentation.
- `Scheme.PolynomialLaurent` supplies only the actual `Spec.map Polynomial.toLaurent`
  morphism and its sections from `ΓSpecIso`. The target is the literal forward `T 1`
  unit. `KTheory.PerfectPolynomialUnitComparison` specializes the proved general theorem.
- `KTheory.PerfectLaurentUnitComparison` uses the existing Stacks
  `additiveGroupBaseChange` and `multiplicativeGroupBaseChange` schemes and their native
  positive-open map and coordinates from COL-0298. These are actual pullbacks over the
  integral terminal scheme. The integral factor is first in the Stacks pullback, whereas
  the earlier Aglib product presentation placed it second. The native projection equation
  and coordinate equality identify the actual forward map and section in this presentation;
  no definitional equality with the removed Aglib presentation is claimed or required.

The forward class restricts to the unit class. The scalar-cofiber boundary class restricts
to its inverse, by the already proved cofiber normalization. This does not reverse the
positive relative supported-cone formula of COL-0304: that is a different map, whose
additional loop-transpose inverse cancels the cofiber inverse.

## Source correspondence

Paths in the first five rows are relative to
`Quillen/AlgebraicGeometry/PerfectComplexes/`.

| Original source | Native result and retained content |
| --- | --- |
| `ScalarLaurentClassComparison.lean:36-83` | Independent fine class, object-isomorphism invariance, actual coarse restriction, inverse cofiber orientation and rank one |
| `ScalarLaurentClassComparison.lean:85-107` | Actual affine polynomial-to-Laurent comparison for all commutative rings, including rank one |
| `GlobalUnitKOneInversion.lean:32-48` | Inverse fine unit class and restriction of a scalar representing the inverse unit |
| `GlobalUnitKOneRestriction.lean:33-49` | Canonical fine restriction, actual pulled-back unit and rank-one restriction isomorphism |
| `NativeLaurentClassComparison.lean:40-71` | Native relative affine-line and Laurent base-change comparison, positive forward unit and inverse cofiber class |
| `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalUnitInversion.lean:26-37` | Equality of the literal inverse scalar automorphism and inverse isomorphism, now in the native full subcategory |
| `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalUnitRestriction.lean:26-43` | Actual restricted unit isomorphism; native scalar/unit equality is definitional |

The migration imports no Aglib or Quillen module and introduces no replacement perfect
category, scalar action, K-group or K-map. The generic canonical-map naturality of COL-0299
and all existing scalar-boundary providers are reused without mathematical source changes.

## Boundaries

This is a degree-one class comparison. It does not prove that the coarse restriction
K-map is an equivalence, construct a fine-open connecting map, identify a zero-section
pushforward, establish a Bass sign, or supply a negative-degree or all-degree scalar formula.
The geometry and approximation needed for fine-open localization remain separate work.
The relative and affine Laurent coordinate specializations do not identify the old Aglib
models with native objects by a new adapter layer.

## Validation contract

`ColibTest.PerfectGlobalUnitKOne` checks the literal actual automorphism, fine class,
inversion, object-isomorphism invariance, general fine restriction, rank one and the
existing opens-only public K-map. `ColibTest.PerfectScalarUnitComparison` checks the
independent coarse input, positive unit image, inverse cofiber image, inverse-unit case,
coexistence with the positive COL-0304 relative boundary, actual affine `Spec.map` and
`T 1` sections, and native relative rank-one formulas.

Local compilation uses Lean 4.35.0 with the pinned Mathlib and Stacks dependencies,
`autoImplicit=false` and `warningAsError=true`. Final receipts distinguish new compilation
from exact reused provider artifacts, including every direct dependency fingerprint.
Full style/lint and production axiom checks are left to remote CI as requested.
Source correspondence, local compilation and independent review remain distinct facts.
