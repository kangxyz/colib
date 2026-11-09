# Projective-completion components and the original Grothendieck group

Source implementation: Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Target source baseline: Colib `bf6993d8cd147533274fcd1300c164b610a8f8d2`, also the
production source of `678355cdbbb5181326efd542b6d4c6b6d10e6d74` (README-only difference).
The later catalog baseline `0acd0ff157ba54c643d1205e2bf0da279955760d` adds
independent correspondence modules and entries; none of the preexisting production
dependencies used here changed. Latest aggregate validation is a separate check.
Library item: COL-0378, in the ring K-theory section.

## Exact target and sign

`Quillen/KTheory/Plus/ProjectiveGroupCompletion.lean:58-97` already sends a pair
`(A, B)` to `coreClass B - coreClass A` in
`(FiniteProjectiveModule.exactStructure R).GrothendieckGroup`. Its native migrated
owner is `ModuleCat.FiniteProjective`, and the target is still
`(ModuleCat.FiniteProjective.exactStructure R).GrothendieckGroup`. Neither that
presentation nor its object classes are changed. The exact structure is inherited
from actual module short exact sequences; its existing `splittingOfConflation`
constructs a splitting inside the finite-projective full subcategory.

The former file proves only grading invariance. The new comparison proves a
reverse additive homomorphism and both composite identities. Its inverse sends an
original object class to the actual `(0, P)` component. The denominator-arrow
identity proves the second inverse equation on every actual pair.

Weibel IV, Remark 4.2.2 and Lemma 4.3.1 put the positive entry first. This
implementation keeps the source convention, with the denominator first. Its
formula is therefore `[B] - [A]`; the coordinate reversal is part of the
comparison, not a change of Grothendieck generators. The diagonal arrow is used
only to prove equality of components, not claimed to be a natural transformation.

## Source and native infrastructure correspondence

- `GroupCompletion/Symmetric.lean` adapts the source's coordinatewise braiding,
  common-denominator naturality and both hexagons, in the existing native namespace.
- `GroupCompletion/Switch.lean` adapts the source switch on the actual quotient
  category. A direct `switch_map_switch` lemma replaces the source's dependence on
  global backward-definitional-equality options when proving its equivalence.
- `GroupCompletion/ConnectedComponents.lean` adapts the source of the same name,
  including the actual tensor addition, switched inverse, diagonal arrow and pair
  difference. Mathlib's native `CategoryTheory.ConnectedComponents` and `Zigzag`
  remain the underlying quotient and relation.
- `GroupCompletion/ConnectedComponentsMap.lean` proves additivity of the original
  `monoidalMap` on components using its actual unit and tensor isomorphisms.
- `ProjectiveCompletionGrothendieck.lean` is the new comparison. It applies the
  preexisting `ExactStructure.grothendieckLift`, `grothendieck_hom_ext`, native
  projective splitting and the original `completionGrading`. It introduces no
  replacement Grothendieck group and assumes no cancellation or rank theorem.
- `ClassifyingSpace/ZerothHomotopy.lean` identifies native categorical components
  with Mathlib's `ZerothHomotopy` of the unchanged nerve realization. It uses the
  existing `classifyingSpaceComponentSigmaHomeomorph`, the original vertex map
  and the theorem joining every realized point to a vertex. The inverse is the
  categorical index in that actual decomposition. Naturality uses the actual
  `classifyingSpaceMap` of a functor.
- `ProjectiveCompletionPiZero.lean` composes those proved equivalences, retaining
  the value at every original pair vertex and the inverse at every object class.
- `ProjectiveCompletionPiZeroNaturality.lean` identifies the induced map of the
  original `monoidalMap (rightBaseChange f).core` with
  `(rightBaseChangeExact f).grothendieckMap`, first on categorical components and
  then on actual path components. Right modules are represented by modules over
  opposite rings, exactly as in the existing base-change construction.

Mathlib's `Algebra.GrothendieckGroup` is the group completion of a commutative
monoid, not the source's chosen exact-category presentation. StacksCore's native
`CategoryTheory.GrothendieckGroup` uses its own short-exact presentation; replacing
the source target with it would require another proved comparison. No such
replacement is used here. The native quotients, core, direct-sum monoidal data,
classifying space and existing exact-category group are used directly.

## Literature correspondence checked on 2026-11-09

- Weibel, *The K-book*, IV, Lemma 3.3: categorical zigzags describe the components
  of the actual classifying space.
- IV, Definition 4.2, Remark 4.2.2 and Lemma 4.3.1: simultaneous-translation pairs,
  their component group and the difference comparison, with the stated coordinate
  reversal.
- II, Definition 7.1 and Examples 7.1.1–7.1.2: the conflation presentation and
  splitting for finite projective modules.

The actual inspected documents are the existing bibliography's chapter II and IV
PDFs. The comparison is degree zero only. It makes no additional assertion about
plus acyclicity, higher homotopy groups, Q-construction comparison or homology
localization. Compilation, source correspondence and independent mathematical
review are recorded separately.
