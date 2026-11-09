# Finite-stage representatives and stable colimits of reduced telescopes

COL-0350 continues COL-0339 using its actual reduced quotient and actual stage maps.
Implementation source: Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`,
`Quillen/Topology/Compactness/CountableFinal.lean` and the ten prespectrum modules below.
Copyright and authorship are retained in every adapted module. This is implementation
correspondence, not an assertion of independently reviewed literature correspondence.

## Reading order and exact correspondence

The native paths replace `Quillen/Topology` by `Colib/Topology`:

1. `Compactness/CountableFinal`: `IsCompact.subset_finite_initial_ranges`.
2. `Prespectrum/TelescopeSeparation`: normal forms and complete closed singleton fibers.
3. `Prespectrum/TelescopeStageEmbedding`: injective inclusions and closed embeddings.
4. `Prespectrum/TelescopeCompactness`: finite cylinder support for maps and whole homotopies.
5. `Prespectrum/TelescopeContraction`: finite transitions, sweeps, collapse and inclusion tracks.
6. `Prespectrum/TelescopeRepresentability`: continuous lift after collapse and relative representatives.
7. `Prespectrum/TelescopeEventualHomotopy`: exact finite-transition relative homotopies and equality.
8. `Prespectrum/TelescopeHomotopyColimit`: actual homotopy-set cocone and colimit comparison.
9. `Prespectrum/TelescopeStableRepresentability`: stable-stage and stable representatives/equality.
10. `Prespectrum/TelescopeStableEquivalence`: strict naturality and stagewise stable equivalences.
11. `Prespectrum/TelescopeStableColimit`: actual AddCommGrpCat colimit and canonical naturality.

All original declaration bodies and hypotheses are retained subject to native namespace/API
adaptation and explicit continuity proofs. `Quillen.Topology` becomes `Topology`,
`Quillen.LoopPrespectrum` becomes `Topology.LoopPrespectrum`, `homotopyGroupMap` becomes
`HomotopyGroup.map` and `genLoopPostcomp` becomes `GenLoop.postcomp`, with the corresponding
identity/composition API. Original permissive elaboration options are removed.

## Topology and relative hypotheses

The reduced quotient collapses the whole base ray. Cylinder height therefore does not
descend to a real-valued function. The compactness argument instead uses the final topology
of a countable cover and the T1 property. An escaping sequence has every subset closed:
each source sees only finitely many singleton fibers. Its range would be a compact discrete
infinite set, a contradiction. Closed fibers retain both incoming upper endpoints and the
base fiber, including upper endpoints mapped to the next basepoint.

Stage inclusions are injective without separation. Their closed embedding property and
compact-support results assume T1 at the relevant stage spaces. Finite sweeps and collapse
need no separation. They descend into continuous interval-map spaces and then evaluate;
no claim that arbitrary quotient maps remain quotient after products is used.

For compact A, an arbitrary subset S and a continuous g constant at the basepoint on S,
g admits a stage representative up to homotopy relative to S. S need not be closed or a
cofibration. Only the collapsed map literally lifts to a finite stage. A nonbase interior
cylinder point is generally in no stage image. A homotopy has its own uniform support
bound. Eventual relative homotopy retains exactly the finite transition composites at
both endpoints, and requires no additional basepoint condition on its relative subset.

## Homotopy sets and stable groups

The homotopy-set comparison is in Type for every natural degree, including degree zero.
No degree-zero group is postulated. The stable comparison is in AddCommGrpCat for every
integer d. Its stable-stage degree is d.toNat + n + 2 and space level is
(-d).toNat + n + 2; n is a stabilization index, separate from telescope stage i.
The original Additive/ofMul conversions and inclusion-induced maps are retained.
Representatives prove surjectivity; eventual equality proves injectivity. The actual
comparison is the colimit descent of the inclusion cocone, not an arbitrary isomorphism.
Naturality is for strict diagram maps, including stable-equivalence invariance.

The consumer constructs the constant discrete Bool prespectrum based at false, with
identity transitions. Projection to Bool detects the true component; a midpoint verifies
why literal stage factorization is false. Relative compact-cylinder representability,
exact eventual endpoints and degree-zero colimit components are checked. Generic tests
retain three independent sweep/height/structure parameters and arbitrary integer stable
representatives, eventual equality and canonical naturality. No nonzero stable group of
this discrete constant example is claimed, and no unverified sphere model is assumed.

## Scope and validation boundaries

This does not assert arbitrary parameter-looping commutation, chosen nonbasepoint
transport, cone/fiber excision, Bass localization or Thomason--Trobaugh 7.4. Cone/fiber
excision has additional finite-stage equivalence inputs.

Local compilation uses pinned Lean 4.35, Mathlib 56a00585 and Stacks 5ed82d14, serialized
with one Lean thread and a 6000 MB memory limit, without an artificial wall-clock timeout.
Production has autoImplicit=false, warningAsError=true and the standard Mathlib linter
set. Tests use native test options. Exact source and all five direct/output artifact
identities are recorded. External cache identity checks do not constitute a fresh build
or kernel replay. Remote lint, private Library export, whole-graph axiom audit and
independent mathematical review are separate gates. This component source intentionally
predates COL0337/338; integration must retain newer union results.
