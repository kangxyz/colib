# Transfer chapters: dependency and scope map

The Library chapter files own the reading order; Lean imports own proof dependencies.
The original reorganization was audited against main `e03556e`; this version
includes the generic Day/PST/NST integration based on `9fb806e`. It does not
claim that unrelated active mathematical branches have been integrated.

## Cycles and Correspondences

1. **Finite correspondences.** COL-0374 and COL-0363–0367 construct admissible
   signed cycles, incidence-Tor composition, identities, the preadditive category
   and graph functor. Their geometric multiplicities remain part of the model.
2. **Symmetric tensor.** COL-1296–1297 give arbitrary-field exterior interchange
   and the symmetric monoidal preadditive structure. Products of integral
   supports retain their associated-cycle lengths over imperfect fields.
3. **Fixed parameters.** COL-0386, 0388, 0387, 0389 retain the older geometrically
   integral parameter construction and its graph-incidence calculations. These
   are useful explicit comparisons, not duplicate definitions of the general
   tensor. In particular the restricted scope of COL-0387/0388 is unchanged.
4. **Degree and descent.** COL-1088, 1091, 1232 have their own section. Finite-flat
   transposes, radicial degree identities and finite étale descent are no longer
   interleaved with construction of the category.
5. **Geometric applications.** Relative principal cuts, Cartier correspondences
   and principal polynomial families retain their detailed proof routes. The
   latter's five topics distinguish support construction, image degrees, signed
   identities, whole endpoint fibres and global endpoint evaluation. These are
   support for cancellation and rigidity, not prerequisites for tensor coherence.

## Presheaves with Transfers

1. COL-0368/0390: additive presheaves, graph restriction and sectionwise cokernels.
2. COL-1302: the generic integral coend, Day comparison and symmetric tensor;
   its PST specialization uses COL-1297 and `TransferCoefficients k`. The generic
   category may vary; coefficients remain integral. This is not pointwise tensor.
3. COL-0397/1030: Suslin complexes and homotopy-invariant singular homology.
4. COL-1039/1045: the actual reduced-torus comparison and cancellation before
   sheafification. Its proof still owns its individual hypotheses.
5. COL-1094/1098/1103/1106: radicial invariance and Frobenius, using
   prime-to-characteristic torsion without a homotopy-invariance assumption.
6. COL-1211/1105: homotopy-invariant endpoint and finite-pair actions, with their
   geometric moving inputs. The étale rigidity chapter is a consumer.

## Shared abstraction and specialization boundaries

`CategoryTheory/Preadditive/IntegralConvolutionMonoidal.lean` supplies the
symmetric monoidal structure for additive presheaves on a preadditive symmetric
monoidal category with binary biproducts and monoidal preadditivity. Object and
Hom universes are independent; coefficients use their maximum with a separate
coefficient-universe parameter. The represented unit retains actual Hom-group
addition. This is an integral API, not an arbitrary-coefficient-ring theorem or
a minimal-hypothesis theorem for nonsymmetric monoidal categories.

The underlying integral coend, output additivity and represented right unit
are developed with weaker hypotheses. Binary biproducts enter the ordinary
pointwise Kan/Mathlib Day comparison used for the associator. Symmetry enters
the left-unit and symmetric coherence construction. `PSTGenericConvolution`
checks that PST's four structure entries are definitionally the generic ones.

The joint NST client uses these exact PST structures in the existing Nisnevich
monoidal localization and checks the original torus adjunction. Ordinary sheaf
tensor is not derived tensor; affine-line localization and cancellation retain
their own arguments. The separate étale branch is not made complete merely by
this common input. Its topology-specific arguments still require independent
verification and integration.

## Primary literature crosswalk

[Mazza–Voevodsky–Weibel, *Lecture Notes on Motivic Cohomology*](https://www.claymath.org/library/monographs/cmim02c.pdf):
Lecture 1, Definition 1.9 (p. 6) gives the correspondence tensor convention;
Lecture 2, Definition 2.1 (p. 13) introduces additive transfer presheaves;
Definition 2.14 and Corollary 2.19 (pp. 16–18) guide the singular route;
Lecture 8, Definition 8.2 and Lemma 8.3 (p. 56) guide the tensor convention.
The book's order is not copied: common tensor input is placed before the two
sheaf theories. These references explain the architecture, not an independent
review certificate for every Lean proof. Existing precise entry references and
compiled references remain the statement-level source records.

## Preservation contract

No existing permanent ID is retired or recreated. All pre-existing entry
statements, scopes, primary declarations and references remain unchanged.
Only COL-1088/1091/1232 change section membership; unrelated chapters retain
both their contents and relative order. New COL-1302 supplies the previously
missing PST tensor entry, with explicit specialization boundaries.
