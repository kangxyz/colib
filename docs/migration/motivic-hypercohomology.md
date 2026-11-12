# Native unbounded sheaf hypercohomology

## Sources and target objects

- Independent Motivic source: a6805c4a87cdfd7717dd7a94039246a167f15380.
- Its locked Aglib dependency: 2c34f185fa859e862661f939cd216b07bcccfb26.
- Target Stacks: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7.
- Target Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.

The native source is
`Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda`. Its section equivalence,
ordinary cohomology presheaf and degree-zero comparison are reused, not copied.
Colib's new declarations extend that namespace and use Mathlib's actual
`DerivedCategory`, `Q`, shifts and `Ext`.

## Exact direct-reuse crosswalk

| Source declaration or family | Native target and disposition |
| --- | --- |
| `Hypercohomology.freeAbelianSheafFunctor`, `freeAbelianSheaf` | `FreeYonedaUnivLE.freeYoneda` and its object; direct use |
| `Hypercohomology.sectionsEquiv`, `sectionsAddEquiv` | Same suffixes in `FreeYonedaUnivLE`; direct use |
| `sectionsEquiv_naturality`, source-object section naturality | `sectionsEquiv_naturality`, `sectionsEquiv_naturality_left`; direct use |
| `LargeCohomology.presheafFunctor`, `presheaf`, `H` | `cohomologyPresheafFunctor`, `cohomologyPresheaf`, actual object value; direct use |
| `LargeCohomology.restriction_apply` | `cohomologyPresheaf_map_apply`; direct use |
| `LargeCohomology.zeroSections` and both naturalities | `extSectionsAddEquiv`, `extSectionsAddEquiv_naturality`, `extSectionsAddEquiv_naturality_left`; direct use |

These names are in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE`.
No legacy facade or alias is introduced for the source namespace.

## New production leaves

1. `Colib.CategoryTheory.Sites.Hypercohomology.Basic`.
   The native free representing sheaf is projective when evaluation sends
   epimorphisms to surjections. The unbounded derived-Hom presheaf is constructed
   on that same source. Its site restriction is actual precomposition and its
   coefficient map is postcomposition by the shifted localized map.
   Quasi-isomorphisms give actual presheaf isomorphisms.

2. `Colib.CategoryTheory.Sites.Hypercohomology.SheafComparison`.
   `singleHypercohomologyEquivCohomology` is Mathlib's
   `Ext.homAddEquiv.symm` at the native representing sheaf. The target is
   Stacks' existing ordinary cohomology presheaf. The derived morphism, site
   restriction and coefficient maps are explicitly preserved.

3. `Colib.CategoryTheory.Sites.Hypercohomology.Shift`.
   Actual cochain/localization shift isomorphisms yield an additive comparison
   and a presheaf isomorphism, in every pair of integer degrees. Original
   restrictions commute with that comparison.

4. `Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation`.
   Every covering sieve of the actual smooth base object `Spec k` is maximal.
   The section in the splitting is an actual morphism over the base. Consequently,
   local surjectivity and local injectivity give surjectivity and injectivity
   at this object. The actual abelian sheafification unit is an isomorphism
   there, and Mathlib's existing `sheafSections` preserves epimorphisms, homology
   and exact sequences. No new evaluation functor is defined.

5. `Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.FieldEvaluation`.
   The actual native free representing sheaf at this smooth base object is
   projective. Mathlib's `Ext.eq_zero_of_projective` then proves positive-degree
   ordinary cohomology vanishes, for every original abelian coefficient sheaf
   and with independent Ext universe. The result is also given as a subsingleton
   group and a zero group object.

The three generic hypercohomology leaves retain arbitrary site object and morphism universes,
coefficient universe `max v t`, explicit `HasSheafify`, the chosen
`HasDerivedCategory` universe, and an independent `HasExt` universe where
needed. The field consumers retain the original coefficient universe `u + 1`
on the actual smooth site; the field is arbitrary. No boundedness or
enough-injectives premise is added to the unbounded
construction or single-sheaf comparison.

## Why not the bounded-below Stacks construction?

`Stacks.Cohomology.derivedSectionsPlus` and its abelian-sheaf
`hypercohomology` take objects of `DerivedCategory.Plus`.
The original Suslin complex is generally unbounded below, so it is not an
input to that interface without an additional mathematical theorem.
The unbounded Stacks ringed-site API acts on `SheafOfModules`, not the original
abelian-sheaf coefficient category. This milestone does not assert an
unproved equivalence of coefficient categories or any derived-section
comparison beyond the single-sheaf statement actually supplied.

## Literature correspondence

- [Stacks, Lemma 18.5.2, Tag 03AB](https://stacks.math.columbia.edu/tag/03AB):
  the free sheaf on a representable corepresents sections, naturally. This is
  reused through Stacks' native API; no new proof of the literature statement
  is claimed.
- [Stacks, Definition 13.27.1, Tag 06XQ](https://stacks.math.columbia.edu/tag/06XQ):
  Ext is shifted Hom in the actual derived category. The new functor is the
  specialization to the native representing sheaf.
- [Stacks, Section 13.11, Tag 05RR](https://stacks.math.columbia.edu/tag/05RR):
  unbounded localization and signed-shift conventions. Localization and shift
  identities are reused from Mathlib.
- Tag 015A concerns bounded-below right-derived functors. It is not cited as
  the exact statement of this unbounded construction.
- Mazza--Voevodsky--Weibel, *Lecture Notes on Motivic Cohomology* (2006),
  Lecture 12, Definition 12.11 and Lemma 12.12, printed p. 92:
  [published edition](https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/Lecture_notes_on_motivic_cohology_published.pdf).
  The free abelian representable sheaf corepresents sections, and its Ext groups
  compute ordinary Nisnevich cohomology. This is background for the construction,
  not an exact attribution of its arbitrary-site unbounded scope. The surrounding
  text explicitly uses the cohomologically bounded-above category `D^-`.

Implementation provenance is attached through `aglib` and the coordinated
`motivic_source_a6805c4` bibliography keys. It is distinct from mathematical
literature attribution.

## Boundaries

This is the ordinary-sheaf prerequisite with its actual base-field consumer.
The field computation is at `Spec k` on its own smooth site, not a general
extension field, affine-line cylinder or henselian stalk. It does not yet construct
finite correspondences, transfer sheaves, ordinary-cohomology transfer actions,
the motivic complex, strict \(\mathbb A^1\)-invariance, or the weight-one
and diagonal comparisons.

## Validation

All five production leaves passed focused final-byte compilation under Lean
4.35.0 and the locked Mathlib/Stacks revisions above on 2026-11-08. The three
hypercohomology leaves passed together (`motivic-hypercohomology-all-v6`, exit 0,
2039 dependency jobs, mostly reused). The two actual base-field consumer leaves
passed together (`motivic-field-cohomology-v4`, exit 0, 3176 dependency jobs,
mostly reused). The existing resource-limited environment was reused, with
one compiler at a time. No proof-checking or elaboration option was relaxed.

Independent static mathematical review checked the native target objects,
restriction and coefficient maps, signed shifts, the actual over-base section,
and the field/universe boundaries. It found no substantive mathematical
mismatch in this scope. That review does not replace compilation or full-tree
integration checks.

These initial five-leaf receipts are distinct from the final combined milestone.
The latter registers COL-0340 through COL-0343, the shared bibliography and
production root, and its thirteen production modules and three consumer modules
(thirty-seven examples) all passed final-byte native compilation. The new nine-case
consumer includes the actual single-sheaf hypercohomology/field-vanishing
comparison with independent Ext and derived-category universes. Its only repair
made the existing coefficient-universe parameters explicit.

The final owned sources retain the same pinned dependencies on the reconciled
main tree. Full-root build, all repository tests, generated-entry checking,
text/declaration lint, axiom audit and Library export are separate gates in the
integrating revision's normal CI. No kernel replay or separate downstream-client
check is claimed.
