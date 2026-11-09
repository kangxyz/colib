# Native supported qcqs geometry

## Owner and exact mathematical scope

COL-0333 belongs to the existing `k-theory-of-schemes` Library section. It is
an independently owned geometric component following COL-0307 and COL-0332.
It is not a completion claim for the supported fine localization topic.

Fix an open immersion j: U → X, an open T of X, and W = j(U) ∪ T.
Assume X is quasi-compact and quasi-separated and W is quasi-compact.
The union-compact roof, stabilized isomorphism, and actual-complement endpoints
do not require U quasi-compact. The compact-T corollaries do require U
quasi-compact: compactness of U and T then implies compactness of W.
Compact T is not a hidden assumption of the union-compact form. Support means actual acyclicity on T, equivalently
derived vanishing, and means support in X minus T, not K-theory of a closed
subscheme. The union factorization and support transport need no compactness.

The roof retains the original global complexes A and B. A is native perfect
and acyclic on T. B only needs quasi-coherent cohomology, with no boundedness,
perfectness or support premise. For every arrow α between their restrictions
in any chosen derived-category model on U, the conclusion supplies a native
perfect R acyclic on T and actual maps q: R → A, a: R → B. Restriction of q
is a quasi-isomorphism and Q(q|U) followed by α equals Q(a|U).

The extension theorem starts with a native perfect E on U acyclic on j⁻¹T.
Its specified conclusion is a native global perfect R acyclic on T and an
isomorphism Q(R|U) ≅ Q(E) ⊞ Q(E)[1]. The actual supported-complement
packaging in `PerfectSupportedQcqsStabilization.lean` takes C = E[1], proves C perfect and acyclic on j⁻¹T, and uses the
actual Q/shift/biproduct comparisons to obtain Q(R|U) ≅ Q(E ⊞ C).
Its public union-compact and compact-T endpoints allow any chosen local
derived model, using the genuine quasi-isomorphism-roof comparison. A derived biproduct alone is not an actual-complex
complement endpoint; the actual-complex packaging has its own successful local receipt.

## Replacement proof and native owners

1. `SupportedUnionGeometry.lean` constructs the actual factorization
   U → W → X, its cover by U and T pulled back to W, and the restriction
   composition isomorphism. Its neighborhood lemma detects support on X
   after restriction to W, and transports support backwards across a
   denominator that is a quasi-isomorphism on W.
2. `SupportedFractionLift.lean` uses `DerivedCategory.right_fac` to represent
   the arbitrary local arrow, applies actual `Complex.extensionByZero`, and
   composes both maps with the genuine adjunction counits. The denominator
   is a quasi-isomorphism because A is supported. No invertibility of the
   counit at B is needed. The unit and triangle identity prove the restricted
   fraction equation. The extended fraction representative is not asserted
   perfect.
3. `SupportedDerivedLift.lean` inverts that denominator and proves the
   derived lift equation through `mapDerivedCategoryFactors`, not an assumed
   lifting property. `PerfectSupportedQcqsRoof.lean` applies COL-0307 to the
   original A and B across W → X; support of its new roof source follows
   because the denominator is invertible on a neighborhood of T.
4. `SupportedDerivedVanishing.lean` relates actual acyclicity to native
   derived zero and to actual derived restriction.
5. `PerfectSupportedQcqsComplement.lean` applies supported extension by zero
   to E across U → W. COL-0307 gives the specified stabilization of this
   extension across W → X. Both summands vanish on the pulled-back T, so R
   is supported. Restriction and the genuine extension-by-zero unit identify
   the local stabilization with E ⊞ E[1]. Replacing this step by an arbitrary
   ordinary complement would not establish vanishing of that complement.

6. `PerfectSupportedQcqsStabilization.lean` proves `perfectSupported_shift`,
   packages the actual complex E ⊞ E[1], and transfers the isomorphism to any
   chosen local derived model through actual quasi-isomorphism roofs.

This replaces the old `SourceSupportedDenominators` and finite-affine
`GlobalSupportedDensity` proof chains. It does not import Aglib or assume
supported compact generation or general two-nonzero-piece derived gluing.
The mathematical source correspondence is distinct from code provenance.

## Exact original-source correspondence

Inspected original Git revision:
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, matching the existing `quillen`
bibliography record. All ranges below are inclusive and repository-relative.
The adjacent `source-correspondence.json` at the component root records hashes
of the original files and machine-readable declarations and ranges.

- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/SupportedRoofs.lean:36-102`: `Quillen.PerfectComplexes.OpenDerivedImage.exists_source_supported_derived_roof` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_chainMap_roof_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsRoof.lean`. Replacement proof. Native perfectness and actual acyclicity replace locallyPerfect and derived IsZero; target B needs only quasi-coherent cohomology, not perfectness or support; both original global endpoints and the given local arrow are retained.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/SupportedRoofs.lean:106-117`: `Quillen.PerfectComplexes.OpenDerivedImage.HasSupportedDerivedRoofs` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_chainMap_roof_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsRoof.lean`. Mathematical input sufficient for the predicate after specializing B to supported perfect. No native predicate declaration or supported-image-category assembly is asserted here.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/OpenDerivedImage/SupportedRoofs.lean:120-125`: `Quillen.PerfectComplexes.OpenDerivedImage.qcqs_hasSupportedDerivedRoofs` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_chainMap_roof_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsRoof.lean`. Same compact-T geometric specialization, with an arbitrary chosen local derived-category model. The native union-compact endpoint is more general in T.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalSupportedDensity.lean:46-99`: `Quillen.PerfectComplexes.exists_supported_perfect_retract_on_finite_affine_union` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsComplement.lean`. Old proof mechanism replaced, not ported: genuine extension by zero on W followed by ordinary qcqs stabilization; no finite-affine induction theorem is claimed migrated.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalSupportedDensity.lean:105-138`: `Quillen.PerfectComplexes.locallyPerfect_exists_global_supported_derived_retract` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_restrict_iso_biprod_shift_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsComplement.lean`. Stronger specified stabilization supplies the geometric retract via the first summand; the old chart-by-chart retract proof is not retained.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalSupportedDensity.lean:143-158`: `Quillen.PerfectComplexes.locallyPerfect_exists_global_supported_perfect_complement` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_restrict_stabilization_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsStabilization.lean`. Open-subscheme specialization of the replacement construction. Actual complement packaging C=E[1] needs native Q/shift/biproduct comparison; do not confuse a derived biproduct with Q(E biprod C). The actual-complex stabilization and support of E[1] are now present in source, with arbitrary chosen local derived model; its exact-source local compilation is successful.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/GlobalSupportedDensity.lean:159-199`: `Quillen.PerfectComplexes.locallyPerfect_exists_global_supported_perfect_complement_of_openImmersion` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_restrict_stabilization_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsStabilization.lean`. Arbitrary open immersion version. Replacement uses specified C=E[1]; support of both global R and local C must be retained. The actual-complex stabilization and support of E[1] are now present in source, with arbitrary chosen local derived model; its exact-source local compilation is successful.
- `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/SupportedOpenDerivedImage/Basic.lean:87-109`: `Quillen.PerfectComplexes.SupportedOpenDerivedImage.exists_supported_perfect_complement` → `AlgebraicGeometry.Scheme.Modules.exists_perfectSupported_restrict_stabilization_of_qcqs` in `Colib/AlgebraicGeometry/Modules/PerfectSupportedQcqsStabilization.lean`. Downstream correspondence only. Original result additionally packages the genuine globally supported saturated restriction image and orders summands C biprod E. Native image-category construction remains separate. The actual-complex stabilization and support of E[1] are now present in source, with arbitrary chosen local derived model; its exact-source local compilation is successful.

The old roof requires both global endpoints locally perfect. The native
replacement weakens B to quasi-coherent cohomology and replaces derived-zero
support with actual acyclicity. The old complement proof permits growing
shift multiplicities in finite-affine induction. The native construction
uses the specified single-shift stabilization instead. These are explicit
replacement/specialization relations, not claims of identical statements or
line-by-line code ports. The original supported-image complement additionally
packages membership in a saturated image with a supported global witness;
that categorical packaging is not part of these geometry files.

## Local validation and frozen dependencies

All eight owned production modules and the complete-signature consumer have actual
successful local Lean receipts. The consumer checks the fixed original A/B roof with
only QC homology on B, both compactness forms, the literal shift-complement support
predicate in an arbitrary local derived model, and the actual unit/counit equality.
The proof receipts bind exact source, direct input five-artifact families, output five-artifact
families, compiler and real package options. New production uses autoImplicit=false,
weak.linter.mathlibStandardSet=true and warningAsError=true; the test uses its separate
actual options. All failed and restart-interrupted attempts remain retained.

The native copyright/module checks cover all nine files. Mathlib mk_all generated the
root, and a second run reported no update necessary. The compiled metadata owner has six
COL-0333 endpoint bindings and exact Quillen source citations. Exported declaration metadata
is checked separately in the component evidence; it is not a private axiom audit.
These are author-owned local validation facts, not independent mathematical review.
Independent review, latest-main aggregate integration and full private Library/axiom/lint
remote gates remain separate. No remote publication was performed by this component.

COL-0307 dependency freeze:
`FINAL-OWNED-GEOMETRY-FREEZE.json`, supplied SHA256
`5ef9af591af3cd92cb25dc58aa5664b689e0ba5503acf91f6ddf2798a6ad8fc5`.
COL-0332 supplied frozen source tree:
`bf11e2c11a0eacde080a78beeb81bcb9862ac5ff`.
These identify the assigned dependency boundary, not new independent review.

## Remaining work and publication boundary

- Retain the component's exact local receipts and native header/root evidence, then
  arrange independent review and the later topic integration gates.
- `SupportedQcqsGeometry.lean` owns the compiled `colib_tag` and `colib_ref` registrations.
  The existing `quillen` bibliography identity is reused without a new or changed pin.
- Assemble the genuine globally supported saturated restriction image, its
  closure, exact category, literal strict factorization and cofinality later.
- Positive-degree equivalences, degree-zero image/injection comparisons,
  fixed-pair full TT 5.1.2 and its fine LES remain separate. COL-0331 retains
  ownership of the existing coarse forward restriction and LES.
- General cover reflection for two nonzero local complexes with a specified
  overlap isomorphism is not zero-on-T excision. Its K-zero reflection and
  arbitrary-cover naturality consumers remain separate, as does Bass theory.

Shared chapter and migration-index text is proposed in the component-root
`docs-proposals.json`; this contribution does not mutate those shared files.
