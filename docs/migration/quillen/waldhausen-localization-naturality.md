# Original fibration naturality and actual stable localization

This complete slice migrates six native production modules from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving 54 original declarations.
The categorical restriction belongs to `CategoryTheory.Waldhausen.Fibration`,
the original K-theory maps to `KTheory.Waldhausen`, and the generic localization
construction to `Topology.Prespectrum`. It adds no ring or scheme dependency.

## The actual connecting-map square: COL-0291

A functor exact for both fine and coarse nested Waldhausen structures restricts
to the actual acyclic categories. Its inclusion and change-of-weak squares commute
with the original maps. The original whole cylinder square and full reversed null
path are retained; the fiber-map comparison fixes both its source coordinate and
its entire path coordinate, rather than merely identifying endpoints.

The final theorem `changeWeakConnectingHom_natural` retains explicit hypotheses
that both original canonical acyclic-to-fiber maps are weak equivalences. These
are not consequences of exactness alone. The existing structural fibration theorem
can discharge them separately with coarse two-out-of-three, extension, genuine
joint-cylinder data and the independent second-endpoint section on each side.
The final connecting-map equality covers every natural degree, including the
K-one to K-zero boundary, with the original sign. Canonical zero rebasing removes
strict preservation of chosen zero from this final theorem; intermediate actual
fiber-map formulas explicitly retain the chosen-zero equality they use. Both
categories share the original independent object and morphism universe pair.

Waldhausen Theorem 1.6.4 and Thomason--Trobaugh Sections 1.8.1-1.8.2 supply the
classical fiber-sequence background and zero-to-object convention. TT Section
1.5.4 supplies exact-functor maps and homotopies from weak natural transformations.
The complete rebased naturality formulas are implementation-level derived results,
not literal quotations or a newly assumed connecting square.

## A constructed stable localization: COL-0292

The native loop-prespectrum category is first quotiented by the congruence
**generated** by its whole coherent based homotopies. It is then localized at
quotient arrows inducing isomorphisms on every integer stable group. Both steps
use Mathlib's actual category quotient and arbitrary-morphism-property localization.
No separate prespectrum model or adapter category is introduced.

The descended original integer stable-group functors detect that an original arrow
becomes invertible exactly when it is an original stable equivalence. Any functor
respecting the whole coherent homotopies and inverting those stable equivalences
has a constructed lift, with a strict factorization and strict uniqueness. Its
target category has independent object and morphism universes.

For the original Waldhausen prespectra, the normalized exact-functor maps therefore
give identity, composition and weak-transformation invariance in this localization.
The actual localized map is invertible exactly when the original `KMap` is bijective
in every nonnegative degree, **including K-zero**. Its stable-group and original-K
comparisons retain the actual maps. Positive-degree equivalences alone do not suffice.
Canonical zero rebasing introduces no strict chosen-zero premise. The inverse is a
morphism in the categorical localization, not a claimed continuous inverse prespectrum
map. No stable model structure, triangulation or nonconnective completion is asserted.

The precise pinned Mathlib quotient and localization constructions are implementation
ingredients. TT Sections 1.5.3-1.5.4 provide connective K-spectrum and functoriality
background, not the actual-localized-map invertibility criterion proved here. The
Stacks calculus-of-fractions universal property additionally assumes a multiplicative
system; it is not used as a direct proof for this arbitrary morphism property.

## Verification scope

All six production modules and three consumer modules with 72 regression examples
passed strict Lean 4.35 compilation before catalog annotations. The exact 2,989-module
input closure was checked by source, compiler ABI, complete artifact family and direct
input-family matching; only the nine new leaves required compilation. The unchanged
15 native linters passed on the actual 10,937-declaration production environment with
zero messages. Independent axiom auditing found only `propext`, `Classical.choice`
and `Quot.sound`. All nine source modules passed native text checks.

Independent source/API review preserves all 54 pinned declarations, full paths,
original hypotheses and universal-property scope. Primary-reference review is distinct
from compilation. One proposed regression used `letI` for a propositional instance;
replacing it with the native linter's preferred `let` left its statement and goal unchanged.

After the catalog and reference annotations, the three changed production leaves and
all three dependent test modules passed strict recompilation. The final annotated
production environment again passed all 15 native linters and the independent
10,937-declaration axiom audit. Native text checks and the exact six catalog bindings
and eight literature annotations also passed. These checks do not replace the exact
integration candidate's original whole-repository CI, required before main publication.
They are not a local full `check.sh` pass or kernel replay. Internal validation records
are not part of the repository.
