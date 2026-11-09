# Native Nisnevich sites and distinguished-square descent

## Mathematical endpoint

COL-0340 constructs the big Nisnevich topology on native schemes and the smooth
separated finite-type site over an arbitrary base. Covers are etale families
with the actual unchanged-residue-field lifting property. The family criterion
permits an independent indexing universe; comparison with the native coproduct
family predicate retains its precise `Small` hypothesis. Smooth objects have
smooth, separated and quasi-compact structure maps, and morphisms are all
morphisms over the base. Arbitrary pullbacks in the smooth category are not
asserted. Cover-specific etale pullbacks and continuous sheaf restriction are
constructed using the native morphism-property over-category.

COL-0341 proves ordinary-sheaf pullback gluing for actual geometric distinguished
squares. An open immersion, an etale neighborhood, a specified closed complement
and its actual base-change isomorphism produce both the original cover and the
diagonal/self-overlap cover. The etale arrow is not assumed monic. The
coefficient category has independent object and hom universes. The original
square is bundled directly as Mathlib's `MayerVietorisSquare`; the additional
weak sheafification assumption for types is needed for that bundle only.

The generic gluing result belongs to `CategoryTheory.Sites.DistinguishedSquare`;
geometry and the smooth-site specialization remain at their actual owners.
Existing Stacks completely decomposed families and residue fields, and Mathlib
precoverages, pullbacks, sheaves and squares are used directly. No second cover
predicate, field-lifting topology or compatibility facade is maintained.

## Implementation and literature

The source is the separate [kangxyz/motivic repository](https://github.com/kangxyz/motivic/tree/a6805c4a87cdfd7717dd7a94039246a167f15380)
at revision `a6805c4a87cdfd7717dd7a94039246a167f15380`.
Exact per-declaration file-and-line locators are compiled in `colib_ref`
attributes and collected in `motivic-nisnevich.json`. The software bibliography
key is `motivic_source_a6805c4`.

The inspected published MVW 2006 edition is registered as `MVW2006`:

- Lecture 12, printed p. 89, opening unnumbered definition: the Nisnevich cover
  condition. Example 12.1 is an example, not the definition's number. Our site
  construction generalizes the book's smooth-over-a-field context.
- Example 12.2, p. 89: splitting over a field. The native result is used on the
  actual smooth base object by the separate field-evaluation item COL-0343.
- Definition 12.5 and Lemma 12.7, p. 90: distinguished squares and the
  sheaf-to-pullback implication. The converse criterion is not claimed.
- Porism 12.8, p. 91: the generic diagonal/self-overlap-cover gluing criterion,
  here generalized to arbitrary coefficient categories.

Stacks Tags 0GTI, 0GTJ and 0GTK describe the reused completely decomposed family
inputs; they are not cited as an existing proof of this complete site theorem.
No PDF content hash is claimed without an actual byte-level record.

## Completion boundary

The site/descent component has eight production modules and twenty-eight
consumer examples. Its final tagged bytes passed native Lean 4.35 locally.
The full combined milestone also includes native unbounded hypercohomology,
exact field evaluation and positive ordinary cohomology vanishing; see
`motivic-hypercohomology.md`. Full-root build, tests, generated imports, text
and declaration lint, axiom audit and Library export are separate CI gates
for the integrating commit.

This does not establish the converse sheaf criterion, noetherian-induction
descent, a cohomological long exact sequence, finite-correspondence composition,
a correspondence category, transfers or transfer sheafification.
