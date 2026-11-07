# Native perfect open-support fiber and long exact sequence

## Mathematical range

For any open immersion, the existing category of native Stacks perfect chain
complexes carries its original ambient-monomorphism cofibrations. The fine weak
equivalences are quasi-isomorphisms. The relative coarse weak equivalences are
detected by actual restriction to the open.

The canonical acyclic-to-homotopy-fiber comparison is a weak homotopy equivalence.
The genuine supported inclusion, change-weak map, and connecting map give all
three recurring positions of the connective long exact sequence. Degree zero
surjects onto the relative coarse group. This does not identify that group with
fine perfect-complex K-theory of the open, or claim that fine open restriction is
surjective on K₀.

## Actual structural inputs

The extension axiom is inherited from actual ambient short exact sequences and
then from the genuine restriction functor. The cylinder is literally
`Cone(id K) ⊞ L`. Its joint inclusion is ambient monic, its relative comparison
map is proved ambient monic, and the second endpoint is a section of the original
projection. The inherited full-subcategory Waldhausen structure is never
replaced by an exact-inflation model.

The supported category is the actual native perfect complexes whose restriction
is acyclic. Its previously constructed exact equivalence with the relative
acyclic category transports the same canonical fiber map and original boundary.
No theorem-shaped comparison or fibration hypothesis is introduced.

## Source and ownership

Implementation correspondence is with pinned Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`,
`AlgebraicGeometry/PerfectComplexes/OpenFibration.lean:97-117` and the complete
`OpenLongExactSequence.lean`. The joint-cylinder argument adapts the generic
factorization proof to the already selected native ambient-Mono structure.
Waldhausen, Section 1.6, Theorem 1.6.4 and proof, pages 350–352, supplies the
general fiber theorem consumed by the application.

Generic closure/cylinder inputs belong to CategoryTheory. Native sheaf-complex
constructions belong to AlgebraicGeometry/Modules, and the K-theory endpoints
belong to AlgebraicGeometry/KTheory. No Aglib imports or parallel perfect-complex
models are used.

## Validation boundary

This source-only continuation is independently reviewed but has not yet been
elaborated or compiled. Its eventual publication requires the exact candidate's
original native build, tests, declaration lint, axiom audit and Library checks.
Source review and static checks are not proof-compilation claims.
