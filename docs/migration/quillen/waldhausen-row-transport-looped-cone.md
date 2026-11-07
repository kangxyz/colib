# Actual row stabilization, AsSmall boundary transport and looped-cone excision

This complete slice adapts 85 original declarations from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd` into 18 native production modules.
Generic homotopy and prespectrum constructions remain in `Topology`; the actual
Waldhausen constructions remain in general `KTheory`. Ring and scheme applications
are not introduced here.

## Actual distinguished-row stabilization: COL-0293

The target prespectrum uses the actual quotient-row transpose. Its positive spaces
are the original based loop spaces, and degree zero is the genuine double based
loop space. The comparison is the original `rowStabilizationMap`, not an ordinary
loop-tail replacement. Every level is a weak homotopy equivalence, so this actual
map is a stable equivalence in every integer degree.

Strict functoriality retains the original exact chosen-zero-preserving maps.
For a pointwise weak natural transformation, the finite simplicial square, complete
cylinder and realized homotopy retain independent structure and homotopy times.
The final compatibility is equality of entire coherent homotopies, including the
original endpoint casts, precomposition and postcomposition. Equality merely after
passing to stable groups or categorical localization would be a weaker statement.
The original common small universe is retained through the existing native strict
chosen-zero subcategory; no additional model or Omega assumption is introduced.

## AsSmall transport of the original boundary: COL-0294

The actual delooping and canonical-fiber homeomorphisms preserve both fiber
coordinates, the whole reversed path and the specified basepoint. Their induced
K-equivalences commute with the original change-of-weak connecting homomorphism.
The evaluation endpoint uses source and target object universe `u + 1`, source
hom universe `u + 1` and target hom universe `u`.

Fine and coarse exactness, the specified acyclic functor and its literal inclusion
square remain explicit. Weakness of both original canonical acyclic-to-fiber maps
is also explicit; it is not inferred from exactness. The final equality retains
the actual AsSmall K-equivalences and original K-maps, with canonical zero rebasing
and no strict preservation-of-zero premise or new sign. It is not a replacement
boundary or an arbitrary four-universe naturality theorem.

## Stable loop-cofiber comparison: COL-0295

The map from the cone of the parameter-looped arrow to the parameter loop of its
cone is the original descent of the whole looped nullhomotopy. Its cylinder sends
the independent cylinder and loop parameters to the corresponding original cone
point, without identifying those parameters. Its inclusion, strict-square
naturality, actual fiber-loop transpose and descent through a specified full
nullhomotopy are retained.

The generic stable theorem keeps the two cone-to-fiber excision hypotheses
separate. Linear all-point connectivity and chosen-point homotopy extension prove
both, with the original one-degree loss for parameter looping. For the actual
iterated-S prespectra, existing finite vanishing, T1 topology and chosen-point HEP
discharge these hypotheses. Consequently every morphism between those prespectra
has the stated stable loop-cofiber comparison in all integer degrees; the morphism
need not arise from an exact functor.

The boundary equation uses the original cone boundary and actual stable-shift
isomorphism, including its alternating correction. It introduces no second sign.
No unrestricted cone-loop equivalence, stable model structure, triangulation or
nonconnective completion is asserted.

## Literature and exact scope

Waldhausen Proposition 1.5.3 and the following paragraph on page 342 provide the
iterated S-loop equivalences used in row stabilization. Thomason--Trobaugh Section
1.5.4 provides the weak-transformation homotopy mechanism. The exact row transpose,
independent times and equality of the whole composite tracks are retained by the
implementation, rather than quoted as a classical formula.

Waldhausen Theorem 1.6.4 and Thomason--Trobaugh Sections 1.8.1-1.8.2 are background
for AsSmall boundary transport, not statements about Lean universes. Hatcher
Theorem 4.23 is the classical CW-pair excision background for the loop-cofiber
argument, not a theorem asserting this actual all-integer comparison or its sign.
Thomason--Trobaugh Section 1.5.3 supplies the K-spectrum context. Its printed
negative-degree bound is not strengthened here by quotation; the native finite
connectivity results are the separate inputs used by these proofs.

## Source comparison and validation

All original constructions and proofs are retained after the explicit native
owner, API and category substitutions. Independent source and mathematical/API
reviews cover all three complete endpoint packages. Four regression modules
contain 100 examples, including whole-map identities, independent times, degree
zero, the signed boundary and the precise universe restrictions.

This slice was prepared under the local resource limit without a new native
compilation batch. Source correspondence and independent review are not compiler
or kernel evidence. Acceptance requires the original whole-repository CI on the
exact integrated candidate, including production, tests, native lint, axiom audit
and Library export. No local full `check.sh` pass or kernel replay is claimed.
Internal validation records are not part of the repository.
