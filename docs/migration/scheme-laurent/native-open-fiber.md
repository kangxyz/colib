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

## Subsequent relative scalar boundary

The relative sequence here is the unchanged one used by
[COL-0304](../quillen-scalar-supported-boundary.md). For an arbitrary open immersion,
a native perfect complex and a scalar restricting to a specified unit, its
original K₁-to-K₀ connecting map sends the independent forward scalar class to
the positive supported class of the actual signed cone. This separate result
does not identify fine-open K-theory, specialize the Laurent-coordinate or
T-first Bass sign, or assert an all-degree scalar boundary formula.

## Validation boundary

At the earlier source-only preparation stage, independent review had been
reported but native elaboration and compilation had not yet been run. That
review retains its recorded scope and is distinct from native validation.

The integrated sources and tests at
[`ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01`](https://github.com/kangxyz/colib/commit/ea4dc640a5bec4e7eb49e0268c08c9f1fed1fc01)
passed the repository's native checks in
[CI run 42435539991](https://github.com/kangxyz/colib/actions/runs/42435539991):
the `Build` and `Test, lint and axiom audit` jobs both succeeded. This
supersedes the uncompiled preparation status. `author_checked` continues to record source
correspondence only; independent mathematical review retains its own evidence
and checked span. No kernel-replay pass is claimed.
