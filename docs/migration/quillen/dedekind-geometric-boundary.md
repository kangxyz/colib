# Original geometric principal boundaries and Dedekind local DVRs

Source: `kangxyz/quillen-k-theory`, revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

This topic completes the original geometric consumers of the finite-module
Dedekind results. It is coherent G-theory on noetherian affines, not an additional
perfect-complex model or a restatement of Thomason–Trobaugh localization.

## Original endpoints and native owners

| Original source | Native owner / retained endpoint |
| --- | --- |
| `Scheme/Coherent/Affine/GTheory.lean`, `UniverseComparison.lean` | `CoherentAffineComparison.publicSpecGRingEquiv`, actual affine global sections and the canonical comparison of small universes of the same category |
| `Scheme/Coherent/Affine/LocalizationNaturality.lean`, `RingIsoNaturality.lean` | `CoherentAffineLocalization`, `CoherentAffineRingIso`, original geometric pullbacks versus the specified scalar maps |
| `GTheory/SmallModelBoundaryNaturality.lean` | `KTheory/Quillen/Localization/SmallModelBoundaryNaturality`, complete same-universe and universe boundary naturality |
| `Scheme/Coherent/Affine/PrincipalLocalization.lean` | `CoherentAffineLocalizationSequence`, actual geometric localization and its actual kernel, in the public universe |
| `Scheme/Coherent/Affine/ClosedDevissage.lean` | `CoherentPrincipalClosedDevissage`, actual closed direct image lifted into that kernel; forward map identified before using the equivalence |
| `Scheme/PrincipalClosedGTheory.lean` | `PrincipalClosedLocalization`, all exactness positions and the degree-zero surjection, with original open-restriction consumers |
| `Scheme/Coherent/Affine/PrincipalBoundaryComparison.lean` | `CoherentPrincipalBoundaryComparison.publicSpecGRingEquiv_principalClosed_boundaryG` |
| `GTheory/Dedekind/PrincipalDvrBoundaryComparison.lean` | ring `PrincipalBoundaryComparison.principalBoundary_nativeBoundary`; scheme `DedekindPrincipalBoundary.principalSchemeBoundary_nativeBoundary` and `_field` |
| `GTheory/Dedekind/FiniteResidueLocalization.lean`, final coherent consumers | scheme `DedekindFiniteResidue.spec_genericGTwo_pullback_injective` and `_field_injective`, actual generic pullback with the supplied fraction field |
| `KTheory/Field/FiniteFieldKTwo.lean`, final coherent consumers | scheme `FiniteField.specGTwo_subsingleton` and `specGTwo_eq_one` |

Scheme source paths in the first column are relative to
`Quillen/AlgebraicGeometry/`; G-theory and field paths are relative to `Quillen/`.
The shortened native owners are under `Colib/AlgebraicGeometry/KTheory` unless
otherwise specified. Lean declarations retain native namespaces, not filename namespaces.

## Mathematical choices retained

- Sheaves are Stacks/Mathlib's actual coherent module sheaves, not a recreated
  finite-type sheaf category. On an affine noetherian scheme the actual tilde and
  global-sections functors give the equivalence.
- Public scheme G-theory continues to use `SmallModel.{u+1}`. Finite-module
  G-theory uses its existing base universe. The canonical functor between the
  small models of the same category supplies the comparison.
- Ordinary affine pullback uses the native tilde/pullback square. Exact coherent
  pullback requires flatness. Closed direct image uses the actual native
  pushforward and its global-sections square.
- The supported category is the kernel of the original localization functor.
  Objects annihilated by the principal ideal form the smaller quotient-image
  category; image-filtration devissage, not an asserted category equivalence,
  passes to all supported objects.
- `closedSupportGEquiv_toMonoidHom` identifies the forward equivalence with the
  actual closed-to-supported K-map. `closedSupportGEquiv_pushforward` identifies
  its composite with supported inclusion with actual geometric direct image.
- The boundary is the original supported connecting map followed by the inverse
  of that identified devissage map. Its affine comparison uses the complete
  supported functor square and boundary universe naturality, not cancellation
  of an ambient G-group inclusion.
- The native universe homotopy promotion is constructed through the actual
  simplicial realization cylinder. The whole nullhomotopy and lifted path-space
  map are preserved, not just their induced group maps.
- At a height-one prime, the chosen irreducible element identifies the principal
  open with the canonical fraction ring and the principal quotient with the
  residue field. The arbitrary-field theorem retains its supplied field,
  algebra structure and fraction-ring instance, and the actual inverse scalar
  restriction. Boundary direction and sign are unchanged.
- The all-degree local comparison does not require generic G1 injectivity.
  That hypothesis remains explicit in the separate finite-family lifting
  theorem COL-0610. The global residue direct-sum assembly remains a
  positive-degree assertion; this topic does not enlarge it to degree zero.

## Consumers and review

`ColibTest.DedekindPrincipalBoundary` checks the original finite-module equality.
`ColibTest.DedekindGeometricFiniteResidue` checks the original generic G2 pullback
with a supplied fraction field and actual residue-field finiteness.
`ColibTest.DedekindPrincipalSchemeBoundary` checks the supplied-field geometric
consumer with the actual pullbacks and scalar restriction, and prints its
transitive axioms. The principal localization owner includes consumers written
with the original geometric `restrictG`, via the proved native comparison with
flat pullback.

COL-0611 through COL-0614 record the four mathematical items in the coherent
G-localization section of the schemes chapter. Source correspondence has been
checked against the pin above. Local compilation, source correspondence and the
whole-library CI are distinct checks; no external mathematical review is claimed.
