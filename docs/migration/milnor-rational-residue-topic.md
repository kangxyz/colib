# Native rational Milnor residues

## Complete mathematical scope

The topic uses the original Stacks Milnor groups, polynomial filtration, total residue,
constant inclusion and constant retraction. Its three Library items are:

- COL-0315: whole-ring filtration detection and bounded single-residue lifting.
- COL-0316: quotient/product decomposition and bounded lifts with prescribed constant component.
- COL-0317: finite residue prescription, the exact infinity coordinate, and the norm-sum
  solvability condition. Prescribing the native constant component gives an actual unique lift.

All fields and residue degrees n >= 0 are included. Finite indexed data allow an independent
index universe and empty support. Native F_0 contains constants. Without a prescribed constant
component uniqueness is only modulo F_0. No replacement model, total norm, norm-independence
hypothesis or equality with Aglib's origin specialization is introduced.

## Validation boundary

Six production modules and six consumers with 24 examples passed stock Lean 4.35.0 against
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 and Stacks
5ed82d14634e8d9576bb844c7bd4e3da66d450e7. Ordinary Lean axiom inspection of the 33 top-level
mathematical declarations used only propext, Classical.choice and Quot.sound.

The final catalog attributes, references and generated root are part of this integration.
All twelve final source files, including the formal reference and catalog attributes,
passed native local revalidation. The 33-declaration ordinary axiom check passed again,
and the official Mathlib root-generator check reported no update necessary.
Full project checks and exact-commit CI remain pending. Ordinary axiom inspection is not the independent
production auditor, and source correspondence is not independent mathematical review.

## Literature and implementation provenance

## Primary literature checked on 2026-11-08

[Milnor 1970, published scan](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/milnorktheoryforms.pdf):
Section 2 starts on printed p. 322. Theorem 2.3 is on p. 325, PDF page 8;
it gives the rational-function split exact sequence. Lemma 2.4 begins on that
page; Lemma 2.5 is on p. 326. The finite-stage quotient and limiting argument
finish on p. 327. The text extraction's inequality glyphs are unreliable, so
no strict-versus-weak degree claim about the printed paper is based on OCR.

[Stacks 0EAY](https://stacks.math.columbia.edu/tag/0EAY) is Remark 42.6.4:
it describes Milnor groups and tame symbols, not this rational split sequence.
Do not register an exactness correspondence to that tag merely because the
pinned native file's comment does. It is background only.

The finite-infinity prescription is a proved consequence of the exact native
inputs below. No direct paper locator for that formula is asserted.

## Exact code provenance, not a model-identification claim

[Aglib RationalExactness](https://github.com/kangxyz/aglib/blob/101dbb8564fb0e29f28cfcb79168d878b5ab489f/Aglib/KTheory/MilnorK/RationalExactness.lean)
was fetched at the exact revision. Its Git blob is
6ac8e24267eef4da8c30990341db7f04f6bd75e1. The actual residue-map, kernel, bounded
surjectivity and quotient statements are the migration source. The following
correspondence compares mathematical roles; it does not assert equality of
separate implementations.

- Source `residueAt_eq_zero_of_mem_lower` corresponds to vanishing above the
  native weak degree bound.
- Source `mem_lower_one_of_totalResidue_eq_zero` and
  `totalResidue_eq_zero_iff_mem_lower_one` correspond to native F0 descent and
  the total-residue kernel statement.
- Source `exists_mem_lower_totalResidue_eq` corresponds to native bounded
  residue lifting. Source positive strict bound d+1 matches native weak d.
- Source `quotientConstantEquivResidues` and its representative equation
  correspond to the actual native quotient equivalence and computation rule.
- Source `rational_short_exact` is consumed through existing native injectivity,
  kernel and surjectivity, not reproved with extra premises.

Source strict degree zero is not identified with native F0. The native product
decomposition preserves its original `constantRetraction`; no equation with
Aglib's separate origin specialization is claimed. Bounded normalized uniqueness,
whole-ring filtration detection, and finite-infinity prescription are explicitly
derived native API refinements.

## Native inputs

Pinned Stacks revision: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7.

- `Chow/MilnorNorm/FullExactness.lean`: filtration exhaustivity and middle exactness.
- `Chow/MilnorNorm/SingleResidue.lean`: native homogeneous single-residue lifting.
- `Chow/MilnorNorm/SimpleNorm.lean`: original simple norm and its negative-infinity rule.
- `Chow/MilnorNorm/MilnorExactSequence.lean`: original point index, total residue,
  constants, retraction, kernel and surjectivity.

Maintained Colib `Norm/FiniteReciprocity.lean` provides
`sum_simpleMilnorNorm_eq_neg_infinityResidueRing_of_residues`. The new finite
prescription proves solvability and quotient uniqueness by combining that exact
theorem with bounded native single lifts. It does not rename reciprocity or
claim new norm independence.

