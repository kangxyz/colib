# The original image-quotient cone in degree zero

This slice migrates the specified image-quotient cone comparison and completes the original
first relative-cylinder construction from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. It extends the general K-theory layer, without
adding ring or scheme dependencies, alternative models or compatibility adapters.

## Actual degree-zero comparison: COL-0290

For an exact functor `F : C ⥤ D` between the original Waldhausen structures `W` and `V`,
the native `imageQuotientConeMap W F hF` has source the literal reduced mapping cone of
`exactOriginalPrespectrumMap W V hF`. Its target is the unshifted original prespectrum of
the image-quotient coarse structure. The target face remains the original change-of-weak
prespectrum map. The whole nullhomotopy is the reversed zero-to-normalized-image family,
with endpoint-only transport and its independent structure parameter retained.

With genuine `FunctorialFactorization V.asSmall`, the actual map is bijective on stable
degree zero. The proof uses the existing original K-zero image/kernel equality and
surjectivity, natural original-K/stable-K comparison, source negative-degree vanishing and
proved S-model cone excision. Generic cone naturality and the canonical cokernel comparison
are supporting results at `Topology.Prespectrum`.

Only target factorization is assumed. There is no source-factorization, density,
full-faithfulness, extension, saturation or localization-fibration premise. The two original
categories retain their common independent object and morphism universe pair. This is not
an all-degree stable equivalence of the arbitrary-functor cone map, nor a Bass nonconnective
or arbitrary-functor cofinality theorem.

Thomason--Trobaugh, Sections 1.5.6-1.5.7, p. 261, provides K-zero relations and object
representatives as an ingredient. The displayed cone comparison is a derived result from
the pinned implementation, not a verbatim theorem in that source. Its graded cofinality
Theorem 1.10.1 uses a full zero-grade subcategory and a different cylinder hypothesis package;
it must not be identified with an arbitrary exact source functor.

## The first relative cylinder and degree raising: COL-0282

The original `RelativeCylinder` and `LoopWeakEquivalence` files now live under
`KTheory.Waldhausen.Iterated`. The ordinal time construction remains at its existing
categorical owner. The actual relative rows retain their acyclicity witnesses, lifted
one-row functor and original tail map. The complete cylinder and realized square commute
at every time. The fiber homeomorphism preserves its original source coordinate and the
entire path postcomposed with the original witness-forgetting map.

The existing actual Omega-spectrum theorem supplies weakness of precisely the first loop
map on the original small category, without an alternative category or AsSmall transport.
`degreeRaisingEquiv W n` has exactly `degreeRaisingMap W n` as its forward group homomorphism,
including `n = 0`. Only the original small-category and Waldhausen-structure assumptions
are used. No new cylinder, factorization or Omega assumption is added.

Waldhausen, Section 1.5, Lemmas 1.5.1-1.5.2 and Proposition 1.5.3, pp. 341-342, supplies
the explicit path construction, chosen loop comparison and delooping theorem. The literal
relative lift is recorded as an adaptation; the unchanged degree-raising consequence uses
the delooping theorem as an ingredient.

## Source correspondence and verification scope

Seven image-cone/support production modules preserve the pinned implementations' native
objects, original maps, signed connecting convention and universe parameters. The relative
companion maps all 29 original declarations: 23 adapted, five ordinal-time declarations
reused at their existing owner, and the already established first-loop weakness theorem
reused without a redundant alias. Four equalities expose the original full square, fiber
coordinates and forward homomorphism.

Before final Library annotations, all nine new production modules and the 48 regression
examples in three test modules passed strict Lean 4.35 compilation. The image endpoint
required an actual 49-module dependency rebuild against its current input families;
matching outputs were reused only after source, ABI and complete input-family checks.
The relative companion's test environment uses the same two elaboration settings as its
production files. Independent source reviews found no mathematical correspondence or
hypothesis gap; reference review is separate from compilation.

After Library annotations, the actual three-production/two-test inverse dependency closure
passed strict compilation. The unchanged native simp-normal-form linter detected one
redundant `simp` attribute on the new forward-homomorphism equality. Removing only that
attribute retained its exact declaration, proof and consumers; the affected production leaf
and regression consumer were recompiled. The final nine-production environment then passed
all 15 existing native linters over 13,983 declarations with no messages. Independent axiom
auditing of the same 13,983 declarations found only `propext`, `Classical.choice` and
`Quot.sound`. All 12 source files passed native text checks; the existing and added Library
bindings and three precise literature annotations were checked together.

Original root generation/check, 95 Python script tests, 34 CI-cache tests and the 282-item
source catalog also passed. The exact original candidate `433698e3` passed the complete
[original CI](https://github.com/kangxyz/colib/actions/runs/42406983526), including production
build, tests, all native linters, axiom audit and Library export. Concurrent main `cfbfd99e`
published a different result under COL-0289, so this comparison is now registered as
COL-0290. Its statements and proofs are unchanged. All concurrent norm-residue sources
and catalog entries are preserved. The retagged endpoint and its regression consumer
passed strict recompilation; root generation/check, all 95 script tests, 34 CI-cache tests
and the combined 283-item catalog also passed. The exact integration candidate requires
its own complete CI before main publication. The focused local checks are not a local full
`check.sh` pass, independent recompilation or kernel replay. Internal validation records
stay outside the repository.
