# Actual cocartesian-section evaluation equivalence

COL-0353 implements generic category theory, not yet the geometric coefficient row. It uses native Mathlib pseudofunctors, Grothendieck constructions, functor fibers, and full subcategories. No old Model or compatibility adapter is imported.

## Source correspondence

The source is the existing `quillen` bibliography record at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Author, Apache license and implementation attribution remain in every adapted header. The following original files are under `Quillen/Aglib/CategoryTheory/FiberedCategory/`; their native counterparts are under `Colib/CategoryTheory/FiberedCategory/`.

- `StrictSections.lean`: complete original file, lines 1–120. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `CocartesianSections.lean`: complete original file, lines 1–82. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `CocartesianSectionEvaluation.lean`: complete original file, lines 1–55. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `CocartesianSectionFullness.lean`: complete original file, lines 1–118. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckCocartesian.lean`: complete original file, lines 1–79. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckFiber.lean`: complete original file, lines 1–118. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckCocartesianIso.lean`: complete original file, lines 1–65. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckFiberMap.lean`: complete original file, lines 1–145. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckSections.lean`: complete original file, lines 1–96. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckSectionEquivalence.lean`: complete original file, lines 1–72. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `CocartesianSectionTransition.lean`: complete original file, lines 1–102. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.
- `GrothendieckZeroSections.lean`: complete original file, lines 1–83. Native imports and namespaces replace the old source owner. Original backward-inference settings are removed, with explicit native proof repairs where needed.

## Mathematical scope

Strict sections are actual functors over a fixed diagram, with vertical natural transformations. Cocartesian sections retain actual strongly cocartesian transitions. Literal coslice restriction has proved identity and composition functor equalities. Identity evaluation is faithful by cocartesian uniqueness and full by extending each vertical identity component.

For a Cat-valued pseudofunctor, the identity-fiber lift of each base arrow is strongly cocartesian. Its universal factorizations construct the canonical section, whose value is the actual pseudofunctor image. The original pseudofunctor unit supplies the evaluated-object isomorphism and essential surjectivity. The concrete original-fiber functor changes no object except transport along its actual base equality. The forward equivalence functor is exactly this identity evaluation.

Every actual section transition yields the natural comparison between evaluation followed by the pseudofunctor map and evaluation at the coefficient arrow. Reindexing followed by evaluation is identified with this actual evaluation; no strict geometric pullback equality is asserted.

A family of specified zero objects, whose images under every transition functor are zero, gives one global section. Its coslice restrictions evaluate and reindex to the same specified zero literally. Full faithful evaluation proves the section is itself zero.

## Boundary

The pseudofunctor is genuine generic input, not a supplied equivalence profile. The separate native geometric bounded-flat pseudofunctor can instantiate it. Waldhausen classes and exactness, universe-small realization, coefficient prespectra, supported sections and Thomason–Trobaugh 7.4 are not asserted here. Compilation, source correspondence, exported metadata and independent mathematical review are separate checks.
