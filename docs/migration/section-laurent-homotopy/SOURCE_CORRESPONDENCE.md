# Actual affine-section Laurent self-homotopy

Original source: Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native prerequisite: current main plus the seven COL-0359 categorical unit-action modules.
No COL-0358 evaluation-comparison module is used.

## Correspondence

- `Quillen/Aglib/CategoryTheory/Functor/IdentityAutomorphismSquare.lean:19-33` becomes
  `CategoryTheory.Functor.IdentityAutomorphism.onFunctor_whisker_square` under its categorical
  owner. The arbitrary comparison lemma is proved by components and naturality.
- `Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentPullback.lean:26-32`
  becomes the actual pointwise reindexed Laurent unit isomorphism. The later evaluation
  comparison in that original file is intentionally outside this item.
- `Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:33-43`
  becomes the strict equality in native chosen-zero-preserving exact model morphisms.
  Its ring input is proved directly for the existing coefficient map and actual constant
  Laurent inclusion; no unavailable Aglib base-change theorem is presumed.
- The same file, lines 51-66, becomes the actual unit square with precisely the comparison
  `eqToHom (congrArg (fun k ↦ k.hom.toFunctor) h)`. There is no freely supplied comparison.
- Lines 68-73 become the native `prespectrumIsoHomotopy` of the actual forward unit.
- Lines 75-90 become all-level same-time coefficient naturality. The new whole-map time-slice
  equation and equality of endpoint-cast homotopies follow by extensionality from that track.

## Preserved strength and limits

Rings, ring maps, sections and cohomological degrees remain arbitrary. The native section
category already has matching object and morphism universes, so no old-model conversion is
needed. The degree-zero space is the original Path space, not omitted or replaced by K-groups.
The homotopy time, loop parameter and structure parameter are independent. Both endpoints,
basedness, structure compatibility and forward/inverse scalar evaluation are exercised by
in-package consumers. The inverse scalar formula is not substituted for the forward generator.

This item supplies the actual natural unit track needed by a later Bass seed. It does not
construct the polynomial two-chart ring square or seed, nor prove support, negative
localization, evaluation stable equivalence or Thomason--Trobaugh 7.4.

Compilation, source correspondence and independent review are separate gates; local receipts
and the final external review record their actual results.
